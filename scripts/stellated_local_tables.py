#!/usr/bin/env python3
"""Generate the 61 shared local-view tables of the stellated tetrahedron.

One table per depth-3 chamber subtriangle, except the three corner
triangles.  Tables run in parallel, one process each.  The tube radius of a
table is chosen from its distance to the corner view (1,1,0)/sqrt2, where
the first-order local rate vanishes; a failed table can be rerun with a
smaller radius via --only and --radius.

    stellated_local_tables.py OUTDIR [--jobs 15] [--only 5,7] [--radius 1/1000]
"""
import argparse
import json
import math
import multiprocessing
import os
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import stellated_certificate_search as st  # noqa: E402

Q = st.Q
CORNER = (1 / math.sqrt(2), 1 / math.sqrt(2), 0.0)


def corner_distance(triangle):
    out = []
    for corner in triangle:
        norm = math.sqrt(sum(float(q) ** 2 for q in corner))
        out.append(math.dist([float(q) / norm for q in corner], CORNER))
    return min(out)


def default_radius(index):
    return (Q(1, 100) if corner_distance(st.DEPTH3_TRIANGLES[index]) >= 0.15
            else Q(1, 1000))


# Views where two vertices project to the same point: V0 - V5 is parallel to
# (31, 9, 9).  (The other vertex differences give the chamber vertex
# (1,1,1)/3 and the corner.)  A local certificate cannot straddle such a view,
# so triangles containing it are cut there first (`Row.cut` in Lean).
SPECIAL_VIEWS = [(Q(31, 49), Q(9, 49), Q(9, 49))]


def solve3(m, v):
    """Solve the 3x3 rational system m x = v (m given by columns)."""
    a = [[m[j][i] for j in range(3)] + [v[i]] for i in range(3)]
    for col in range(3):
        piv = next(r for r in range(col, 3) if a[r][col] != 0)
        a[col], a[piv] = a[piv], a[col]
        for r in range(3):
            if r != col and a[r][col] != 0:
                f = a[r][col] / a[col][col]
                a[r] = [x - f * y for x, y in zip(a[r], a[col])]
    return [a[i][3] / a[i][i] for i in range(3)]


_P = [(1, 1, 1), (1, -1, -1), (-1, 1, -1), (-1, -1, 1)]
VERTICES = ([tuple(Q(c, 2) for c in p) for p in _P] +
            [tuple(Q(-11, 40) * c for c in p) for p in _P])


def _sub(a, b):
    return tuple(x - y for x, y in zip(a, b))


def _cross(a, b):
    return (a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2],
            a[0] * b[1] - a[1] * b[0])


def _dot(a, b):
    return sum(x * y for x, y in zip(a, b))


# The silhouette near a special view changes along the planes spanned by the
# coincident pair's direction and a third vertex: lines through the view.
SPECIAL_PAIRS = {SPECIAL_VIEWS[0]: (0, 5)}
TIE_NORMALS = {
    view: [_cross(_sub(VERTICES[k], VERTICES[i]), _sub(VERTICES[j], VERTICES[i]))
           for k in range(8) if k not in (i, j)]
    for view, (i, j) in SPECIAL_PAIRS.items()}


def special_cut(triangle):
    """Cut weights for `triangle`: at a special view inside it, or, when a
    special view is a corner, along a tie line through that corner."""
    for point in SPECIAL_VIEWS:
        if point in triangle:
            m = triangle.index(point)
            a, b = (triangle[i] for i in range(3) if i != m)
            for normal in TIE_NORMALS[point]:
                va, vb = _dot(normal, a), _dot(normal, b)
                if va * vb < 0:
                    t = va / (va - vb)
                    weights = [Q(0)] * 3
                    others = [i for i in range(3) if i != m]
                    weights[others[0]], weights[others[1]] = 1 - t, t
                    return weights
            continue
        weights = solve3(triangle, point)
        if all(w >= 0 for w in weights):
            return weights
    return None


# Planes of views where three vertices project onto one line.  Near such a
# view a silhouette vertex crosses a hull edge; a local certificate can
# handle the tie on a triangle's boundary (exact support ties) but not in
# its interior.
import itertools as _it
TIE_PLANES = []
for _i, _j, _k in _it.combinations(range(8), 3):
    _n = _cross(_sub(VERTICES[_j], VERTICES[_i]), _sub(VERTICES[_k], VERTICES[_i]))
    if any(_n) and _n not in TIE_PLANES and tuple(-x for x in _n) not in TIE_PLANES:
        TIE_PLANES.append(_n)
TIE_CUT_DEPTH = 10


def tie_cut(triangle):
    """Weights cutting `triangle` at a point where the tie plane nearest to
    its centroid crosses an edge, or None if no plane crosses the interior."""
    centroid = tuple(sum(c[i] for c in triangle) / 3 for i in range(3))
    best = None
    for n in TIE_PLANES:
        values = [_dot(n, c) for c in triangle]
        if not (any(v > 0 for v in values) and any(v < 0 for v in values)):
            continue
        score = abs(float(_dot(n, centroid))) / sum(float(x) ** 2 for x in n) ** 0.5
        if best is None or score < best[0]:
            best = (score, values)
    if best is None:
        return None
    values = best[1]
    for a, b in ((0, 1), (1, 2), (2, 0)):
        if values[a] * values[b] < 0:
            t = values[a] / (values[a] - values[b])
            weights = [Q(0)] * 3
            weights[a], weights[b] = 1 - t, t
            return weights
    return None


def cut_triangle(triangle, weights, k):
    point = tuple(sum(w * corner[c] for w, corner in zip(weights, triangle))
                  for c in range(3))
    return tuple(point if i == k else triangle[i] for i in range(3))


def shrink(triangle, factor=Q(1, 2)):
    center = tuple(sum(corner[c] for corner in triangle) / 3 for c in range(3))
    return tuple(tuple(center[c] + factor * (corner[c] - center[c])
                       for c in range(3)) for corner in triangle)


def local_candidate(triangle, depth, target_c, radius, nearby):
    base = st.base
    for certificate in nearby:
        result = base.projective_local_reaudit_candidates(
            (triangle, [certificate], target_c, radius))
        if result is not None:
            return result
    result, _ = base.projective_local_candidate((triangle, depth, target_c))
    if result is not None and result["c"] >= target_c:
        return result
    if depth >= 12:
        # The #214 cascade defers its stronger pools to depth >= 27; on the
        # tie plane of vertices 0, 3, 5 (and its parallel edges 3-5, 4-7)
        # they are what finds the margin, so try them here directly.
        zero = (Q(0), Q(0), Q(0))
        for kw in (dict(cone_samples=6, trials=5000, include_boundaries=True),
                   dict(cone_samples=8, trials=20000, include_boundaries=True,
                        include_corner_cycles=True)):
            strong = base.atlas_projective_local_triangle(
                0, zero, zero, 0, triangle, 0, **kw)
            if strong is not None and strong["c"] >= target_c:
                return strong
    # Candidate generation reads the silhouette at the corners, which is
    # ambiguous at a special view; take candidates from a shrunken triangle
    # and re-audit them on the real one.
    if depth < 20 or not any(point in triangle for point in SPECIAL_VIEWS):
        return None
    inner, _ = base.projective_local_candidate(
        (shrink(triangle), 28, target_c))
    if inner is not None:
        certificate = [base.compact_projective_local_axis_artifact(axis)
                       for axis in inner["certificates"]]
        return base.projective_local_reaudit_candidates(
            (triangle, [certificate], target_c, radius))
    return None


def generate_table(path, root, max_nodes, max_depth, target_c, radius):
    """Depth-first local-view table with special-view cuts."""
    base = st.base
    rows = [None]
    stack = [(0, root, 0)]
    failures = []
    counts = {"view_split": 0, "view_cut": 0, "certificate": 0}
    nearby = []
    while stack and len(rows) < max_nodes:
        row_id, triangle, depth = stack.pop()
        weights = special_cut(triangle)
        if weights is not None:
            children = []
            for k in range(3):
                if weights[k] > 0:
                    children.append(len(rows))
                    rows.append(None)
                    stack.append((children[-1],
                                  cut_triangle(triangle, weights, k), depth))
                else:
                    children.append(None)
            rows[row_id] = {"id": row_id, "kind": "view_cut", "root": 0,
                            "triangle": triangle, "depth": depth,
                            "children": children, "weights": weights}
            counts["view_cut"] += 1
            continue
        center = base.projective_triangle_center_float(triangle)
        near = [cert for _, cert in sorted(
            nearby[-4096:], key=lambda item: sum(
                (a - b) ** 2 for a, b in zip(center, item[0])))[:2]]
        result = local_candidate(triangle, depth, target_c, radius, near)
        if (result is not None and result["c"] >= target_c and
                radius * radius * (1 + result["c"] ** 2) <=
                4 * result["c"] ** 2):
            certificate = [base.compact_projective_local_axis_artifact(axis)
                           for axis in result["certificates"]]
            rows[row_id] = {"id": row_id, "kind": "view_local", "root": 0,
                            "triangle": triangle, "depth": depth,
                            "symmetry_index": 0, "r": radius,
                            "certificate": certificate,
                            "c": result["c"], "delta": result["delta"]}
            counts["certificate"] += 1
            nearby.append((center, certificate))
        elif depth >= TIE_CUT_DEPTH and depth < max_depth and \
                tie_cut(triangle) is not None:
            weights = tie_cut(triangle)
            children = []
            for k in range(3):
                if weights[k] > 0:
                    children.append(len(rows))
                    rows.append(None)
                    stack.append((children[-1],
                                  cut_triangle(triangle, weights, k), depth))
                else:
                    children.append(None)
            rows[row_id] = {"id": row_id, "kind": "view_cut", "root": 0,
                            "triangle": triangle, "depth": depth,
                            "children": children, "weights": weights}
            counts["view_cut"] += 1
        elif depth < max_depth:
            children = list(range(len(rows), len(rows) + 4))
            rows.extend([None] * 4)
            rows[row_id] = {"id": row_id, "kind": "view_split", "root": 0,
                            "triangle": triangle, "depth": depth,
                            "children": children}
            counts["view_split"] += 1
            for child, sub in zip(children,
                                  base.split_projective_triangle(triangle)):
                stack.append((child, sub, depth + 1))
        else:
            failures.append({"id": row_id, "triangle": triangle,
                             "depth": depth})
        processed = sum(counts.values())
        if processed % 5000 == 0:
            with open(path + ".tmp", "w") as out:
                json.dump({"complete": False, "target_c": target_c,
                           "tube_radius": radius, "max_depth": max_depth,
                           "initial_child": None, "rows": rows,
                           "pending": stack, "counts": counts,
                           "failures": failures}, out, default=str)
            os.replace(path + ".tmp", path)
        if processed % 200 == 0:
            print(json.dumps({"rows": len(rows), "pending": len(stack),
                              "failures": len(failures), "counts": counts}),
                  flush=True)
    complete = not stack and not failures and all(r is not None for r in rows)
    with open(path + ".tmp", "w") as out:
        json.dump({"complete": complete, "target_c": target_c,
                   "tube_radius": radius, "max_depth": max_depth,
                   "initial_child": None, "rows": rows, "pending": stack,
                   "counts": counts, "failures": failures}, out, default=str)
    os.replace(path + ".tmp", path)
    return {"complete": complete, "rows": rows, "failures": failures}


C_FACTOR = Q(2, 3)   # target margin c >= C_FACTOR * r (Lean needs about r <= 2c)


def run_table(job):
    index, radius, outdir, max_nodes, max_depth = job
    st.install_stellated_search()
    st.base.UPPER_WEDGE_PROJECTIVE_ROOT = st.DEPTH3_TRIANGLES[index]
    target_c = radius * C_FACTOR
    path = os.path.join(outdir, f"local-{index:02d}.json")
    log = open(os.path.join(outdir, f"local-{index:02d}.log"), "w")
    sys.stdout = log
    result = generate_table(path, st.DEPTH3_TRIANGLES[index], max_nodes,
                            max_depth, target_c, radius)
    sys.stdout = sys.__stdout__
    return {"index": index, "radius": str(radius),
            "complete": result["complete"], "rows": len(result["rows"]),
            "failures": len(result["failures"])}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("outdir")
    parser.add_argument("--jobs", type=int, default=15)
    parser.add_argument("--only")
    parser.add_argument("--radius")
    parser.add_argument("--max-nodes", type=int, default=40000)
    parser.add_argument("--max-depth", type=int, default=12)
    parser.add_argument("--c-factor", default="2/3")
    args = parser.parse_args()
    global C_FACTOR
    C_FACTOR = Q(args.c_factor)
    os.makedirs(args.outdir, exist_ok=True)
    indices = ([int(i) for i in args.only.split(",")] if args.only else
               [i for i in range(64) if i not in st.CORNER_TABLES])
    jobs = [(i, Q(args.radius) if args.radius else default_radius(i),
             args.outdir, args.max_nodes, args.max_depth) for i in indices]
    with multiprocessing.get_context("fork").Pool(args.jobs) as pool:
        for summary in pool.imap_unordered(run_table, jobs):
            print(json.dumps(summary), flush=True)


if __name__ == "__main__":
    main()
