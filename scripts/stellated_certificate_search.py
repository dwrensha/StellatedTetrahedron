#!/usr/bin/env python3
"""Certificate search for Zeng's stellated tetrahedron P_{11/20}.

Thin wrapper over ``nopert214_certificate_search``, as for Nopert #76.  The
vertices are exact rationals: the paper's

    p_i = (1,1,1), (1,-1,-1), (-1,1,-1), (-1,-1,1),   q_i = -a p_i,

with a = 11/20, scaled by 1/2 so that every vertex has norm sqrt(3)/2 < 1
(the Rupert property is similarity-invariant).  There is no approximation
layer: the checker model and the exact solid coincide.

Symmetry.  The rotation group T (12 signed permutation matrices, even
permutations with an even number of sign changes) preserves the solid, and
every element of O \\ T maps it to its negative.  See
``.artifacts/stellated/README.md`` for the resulting pose reduction.
"""
import itertools
import math
import os
import sys
from fractions import Fraction as Q
from pathlib import Path

if os.environ.get("NOPERT_GMPY2"):
    from gmpy2 import mpq as Q  # noqa: F811 (see nopert214_certificate_search)

sys.path.insert(0, str(Path(__file__).resolve().parent))
import nopert214_certificate_search as base
import snub_certificate_search as exact_certificate

A = Q(11, 20)
TETRAHEDRON = ((1, 1, 1), (1, -1, -1), (-1, 1, -1), (-1, -1, 1))
VERTICES_Q = tuple(
    tuple(Q(c, 2) for c in p) for p in TETRAHEDRON) + tuple(
    tuple(-A * Q(c, 2) for c in p) for p in TETRAHEDRON)
_INDEX = {v: i for i, v in enumerate(VERTICES_Q)}


def _apply(m, v):
    return tuple(sum(m[r][c] * v[c] for c in range(3)) for r in range(3))


def _det(m):
    return (m[0][0] * (m[1][1] * m[2][2] - m[1][2] * m[2][1])
            - m[0][1] * (m[1][0] * m[2][2] - m[1][2] * m[2][0])
            + m[0][2] * (m[1][0] * m[2][1] - m[1][1] * m[2][0]))


def _signed_permutations():
    for perm in itertools.permutations(range(3)):
        for signs in itertools.product((1, -1), repeat=3):
            m = tuple(tuple(signs[r] if c == perm[r] else 0
                            for c in range(3)) for r in range(3))
            if _det(m) == 1:
                yield m


IDENTITY = ((1, 0, 0), (0, 1, 0), (0, 0, 1))
# T: rotations preserving the solid.  FLIP: O \ T, rotations negating it.
T_MATRICES = []
FLIP_MATRICES = []
for _m in _signed_permutations():
    images = [_apply(_m, v) for v in VERTICES_Q]
    if all(w in _INDEX for w in images):
        T_MATRICES.append(_m)
    else:
        assert all(tuple(-c for c in w) in _INDEX for w in images), _m
        FLIP_MATRICES.append(_m)
T_MATRICES.sort(key=lambda m: m != IDENTITY)
assert len(T_MATRICES) == 12 and len(FLIP_MATRICES) == 12
assert T_MATRICES[0] == IDENTITY

# Install the tables into the shared machinery.
base.SEEDS_Q = None
base.VERTICES_Q = VERTICES_Q
base.VERTICES = [tuple(map(float, vertex)) for vertex in VERTICES_Q]
base.PUBLISHED_STL_SHA256 = None
exact_certificate.VERTICES_Q = [list(vertex) for vertex in VERTICES_Q]

# The vertices are exact, so the Lean checker's vertex error
# (tightVertexErrorQ) is zero.  Rows generated with the old #76 constant
# 2/10^15 remain valid: every use is a one-sided margin.
base.PROJECTIVE_LOCAL_VERTEX_ERROR = Q(0)
base.PROJECTIVE_SUPPORT_ERROR = 10 * base.PROJECTIVE_LOCAL_VERTEX_ERROR

# Outer views reduce (by O and the view antipode) to the chamber
# x >= y >= z >= 0, i.e. this rational triangle in the +++ projective root.
CHAMBER_TRIANGLE = (
    (Q(1), Q(0), Q(0)),
    (Q(1, 2), Q(1, 2), Q(0)),
    (Q(1, 3), Q(1, 3), Q(1, 3)),
)


# ---------------------------------------------------------------------------
# Exact prunes mirroring Noperts/Stellated/{AtlasProjectiveSolutionTree,
# FlipPrune}.lean.

def _load_flip_coefficients():
    """Read `flipCoeff` from the generated Lean file, so signs agree."""
    import re
    text = (Path(__file__).resolve().parents[1] /
            "Noperts/Stellated/FlipPrune.lean").read_text()
    table = []
    for k in range(12):
        match = re.search(
            r"theorem flipCoeff_%d : flipCoeff %d = !!\[([^\]]*)\]" % (k, k),
            text)
        rows = [[Q(int(entry)) for entry in row.split(",")]
                for row in match.group(1).split(";")]
        assert len(rows) == 3 and all(len(row) == 4 for row in rows)
        table.append(rows)
    return table


FLIP_COEFF = _load_flip_coefficients()


def outside_octahedron(center, widths):
    """Mirror `Interval.outsideOctahedron`."""
    total = Q(0)
    for value, width in zip(center, widths):
        lo, hi = value - width, value + width
        total += Q(0) if lo <= 0 <= hi else min(abs(lo), abs(hi))
    return total > 1


def flip_corner_lower(form, negate, corner, center, widths):
    """Mirror `FlipPrune.Box.cornerLower`."""
    sign = Q(-1) if negate else Q(1)
    a = [sign * sum(corner[c] * FLIP_COEFF[form][c][j] for c in range(3))
         for j in range(4)]
    return (a[0] + sum(a[j + 1] * center[j] for j in range(3)) -
            sum(abs(a[j + 1]) * widths[j] for j in range(3)))


def flip_prune_certificate(center, widths, triangle):
    """Return (form, negate) if some flip form prunes the box exactly.

    Mirrors `FlipPrune.Box.Valid`: L > 0 and L^2 > 2 max_i |t_i|^2."""
    max_norm_sq = max(sum(c * c for c in corner) for corner in triangle)
    for form in range(12):
        for negate in (False, True):
            lower = min(flip_corner_lower(form, negate, corner, center, widths)
                        for corner in triangle)
            if lower > 0 and lower * lower > 2 * max_norm_sq:
                return form, negate
    return None


# Shared local-view tables live on the 64 depth-3 subtriangles of the
# chamber (index 16*a + 4*b + c for split path a, b, c).  The three nearest
# the corner view (1,1,0)/sqrt2 get no table; small relative rotations there
# are deferred to the corner (blow-up) treatment.
def _depth3_triangles():
    split = base.split_projective_triangle
    out = []
    for a in range(4):
        ta = split(CHAMBER_TRIANGLE)[a]
        for b in range(4):
            tb = split(ta)[b]
            for c in range(4):
                out.append(split(tb)[c])
    return out


DEPTH3_TRIANGLES = _depth3_triangles()
CORNER_TABLES = frozenset((16 * 1 + 4 * 1 + c) for c in (1, 2, 3))
# Cells in this table (the depth-3 triangle at the corner view) with relative
# reach <= CORNER_EPS are closed by the corner blow-up (Lean row `corner`,
# `cornerEps = 1/8`).  Tables 22, 23 have ordinary local tables.
CORNER_BLOWUP_TABLE = 16 * 1 + 4 * 1 + 1
# Table 23 lies inside the corner view square too (S, T <= 1/8 at all its
# corners), and its local margin collapses toward the corner.
CORNER_BLOWUP_TABLES = frozenset({CORNER_BLOWUP_TABLE, 16 * 1 + 4 * 1 + 3})
CORNER_EPS = Q(3, 16)
CORNER_RELATIVE_REACH = Q(1, 8)
NEAR_ORIGIN_REACH = Q(1, 8)
# per-table tube radii (None for corner tables); set by the driver
TUBE_RADII = [None] * 64


def barycentric(point, triangle):
    """Exact weights w with sum_j w_j t_j = point (points on x+y+z = 1)."""
    m = [[triangle[j][c] for j in range(3)] + [point[c]] for c in range(3)]
    for col in range(3):
        pivot = next(r for r in range(col, 3) if m[r][col] != 0)
        m[col], m[pivot] = m[pivot], m[col]
        for r in range(3):
            if r != col and m[r][col] != 0:
                factor = m[r][col] / m[col][col]
                m[r] = [x - factor * y for x, y in zip(m[r], m[col])]
    return [m[i][3] / m[i][i] for i in range(3)]


def within_weights(small, big):
    """Mirror `TriangleWithin`: convex weights of small's corners in big."""
    weights = [barycentric(corner, big) for corner in small]
    for row, corner in zip(weights, small):
        if any(w < 0 for w in row) or sum(row) != 1:
            return None
        for c in range(3):
            if sum(w * big[j][c] for j, w in enumerate(row)) != corner[c]:
                return None
    return weights


def depth3_index(triangle):
    for index, big in enumerate(DEPTH3_TRIANGLES):
        if within_weights(triangle, big) is not None:
            return index
    return None


def relative_reach(center, widths):
    return max(abs(c) + w for c, w in zip(center, widths))


_base_state_action = base.atlas_projective_state_action


def tie_cut_weights(triangle):
    """Cut weights along the tie plane (three vertices collinear in
    projection) nearest the triangle's centroid, if one crosses its
    interior.  Near such a plane certificates on straddling triangles need
    microscopic Cayley boxes; after the cut the tie lies on an edge."""
    import stellated_local_tables as lt
    return lt.tie_cut(triangle)


def in_corner_square(triangle):
    """Mirror of the view part of Lean `CornerOk`: every corner has
    0 <= w0 - w1 <= cornerEps and 0 <= 2 w2 <= cornerEps."""
    return all(0 <= c[0] - c[1] <= CORNER_EPS and 0 <= 2 * c[2] <= CORNER_EPS
               for c in triangle)


def rescue_with_wide_cones(chart, center, widths, root, triangle):
    """Last resort before recording a failure: 24-, 32- and 48-sample
    contact cones (seconds per cell) close the few silhouette near-ties that
    the engine's cascade misses at its depth limits."""
    for samples in (24, 32, 48):
        screen = base.atlas_projective_global_float_screen(
            chart, center, widths, triangle, cone_samples=samples,
            candidate_limit=64, candidates=None)
        if screen is None or screen["lower_bound"] <= 1e-8:
            continue
        exact = base.atlas_projective_global_triangle(
            chart, center, widths, root, triangle,
            selected_candidate=screen["candidate"])
        if exact is not None and exact["accepted"]:
            axis = exact["certificate"]
            keys = ("edge_start", "edge_finish", "edge_start2", "edge_finish2",
                    "mix", "support_index", "nonzero_witness", "B")
            return {"action": "terminal", "row_kind": "global", "extra": {
                "certificate": {
                    "axis": {key: axis[key] for key in keys},
                    "inner_index": exact["inner_index"],
                    "ball_multiplier": exact["ball_multiplier"]}}}
    return None


def stellated_state_action(task):
    (chart, center, widths, root, triangle, view_depth, shared_index,
     inherited, max_view_depth, min_relative_half_width,
     restricted_fundamental_root, tube_radii) = task
    zero = {"exact_rejections": 0, "fundamental_audit": 0,
            "global_audit8": 0, "global_audit64": 0, "global_audit4096": 0,
            "global_cone5": 0, "global_cone6": 0, "global_cone10": 0,
            "global_cone16": 0, "global_mixed": 0}
    if outside_octahedron(center, widths):
        return {"action": "terminal", "count_deltas": zero,
                "row_kind": "radius", "extra": {"prune": "octahedron"}}
    certificate = flip_prune_certificate(center, widths, triangle)
    if certificate is not None:
        form, negate = certificate
        return {"action": "terminal", "count_deltas": zero,
                "row_kind": "fundamental_prune",
                "extra": {"prune": "flip", "form": form, "negate": negate}}
    reach = relative_reach(center, widths)
    if reach <= NEAR_ORIGIN_REACH and view_depth < 3:
        # route small relative rotations to a depth-3 table triangle first
        return {"action": "view_split", "count_deltas": zero,
                "assign_shared": False, "inherited": None}
    index = depth3_index(triangle) if view_depth >= 3 else None
    if reach <= CORNER_EPS and view_depth >= 3 and in_corner_square(triangle):
        return {"action": "terminal", "count_deltas": zero,
                "row_kind": "fundamental_prune",
                "extra": {"prune": "corner"}}
    if (index in CORNER_TABLES and TUBE_RADII[index] is None and
            reach <= CORNER_RELATIVE_REACH):
        return {"action": "failure", "count_deltas": zero,
                "extra": {"reason": "corner", "table": index}}
    # Ten- and sixteen-sample cones close silhouette near-ties just outside
    # the small tubes (e.g. vertex 0 near hull edge 5-3 by table 31), but cost
    # ~1 s per cell; use them only on deep cells, where cheaper cells failed.
    base.CONE10_CHART0 = view_depth >= 14 or max(widths) <= Q(1, 2048)
    radius = None if index is None else TUBE_RADII[index]
    if radius is None:
        base_task = (chart, center, widths, root, triangle, view_depth, None,
                     inherited, max_view_depth, min_relative_half_width,
                     restricted_fundamental_root, None)
    else:
        radii = tuple(r if r is not None else Q(0) for r in TUBE_RADII)
        base_task = (chart, center, widths, root, triangle, view_depth, index,
                     inherited, max_view_depth, min_relative_half_width,
                     restricted_fundamental_root, radii)
    action = _base_state_action(base_task)
    if (action.get("action") == "relative_split" and view_depth >= 3 and
            max(widths) <= Q(1, 256)):
        weights = tie_cut_weights(triangle)
        if weights is not None:
            return {"action": "view_cut", "weights": weights,
                    "count_deltas": action["count_deltas"],
                    "inherited": action.get("inherited")}
    if (action.get("action") == "relative_split" and view_depth < 12 and
            64 * max(widths) < max(abs(c) for c in center)):
        # The box is already tiny next to its distance from the identity, so
        # the certificate is limited by the view triangle, not the box.
        return {"action": "view_split", "assign_shared": False,
                "count_deltas": action["count_deltas"],
                "inherited": action.get("inherited")}
    if action.get("action") == "failure":
        rescued = rescue_with_wide_cones(chart, center, widths, root, triangle)
        if rescued is not None:
            rescued["count_deltas"] = action["count_deltas"]
            return rescued
    if action.get("row_kind") == "symmetry_tube":
        action["extra"]["within"] = within_weights(
            triangle, DEPTH3_TRIANGLES[index])
    return action


def install_stellated_search():
    """Point the shared generator at the stellated domain and prunes."""
    base.NEAR_TUBE_GLOBAL_AUDIT = True
    base.EARLY_CONE10_NEAR_TUBE = True

    assert chart_zero_only_ok()
    base.UPPER_WEDGE_PROJECTIVE_ROOT = CHAMBER_TRIANGLE
    base.atlas_projective_state_action = stellated_state_action
    # The fivefold Dirichlet machinery must never fire here.
    base.atlas_fundamental_status = \
        lambda chart, centers, radii: ("inside", None, [])
    base.atlas_fundamental_outside_float = lambda chart, centers, radii: None


def chart_zero_only_ok():
    # Chart half-turns are T elements 1..3, so the T-cell lies in chart 0.
    return T_MATRICES[1:4] == [((1, 0, 0), (0, -1, 0), (0, 0, -1)),
                               ((-1, 0, 0), (0, 1, 0), (0, 0, -1)),
                               ((-1, 0, 0), (0, -1, 0), (0, 0, 1))]


def main():
    install_stellated_search()
    base.main()


if __name__ == "__main__":
    main()
