#!/usr/bin/env python3
"""Emit a packed stellated local-view table (`local-NN.pack`).

Format (see `PackedLocalViewTree`): header `count symmetryIndex r`, then the
rows.  A row's triangle is a path from the table's depth-3 base triangle:
steps `0..3` are midpoint children, step `4 + k` followed by three rational
weights is child `k` of a cut.  Row tags: `0` split, `1` certificate, `2` cut
(three children, then three weights; a zero-weight child is written as 0).

    stellated_emit_local.py TABLE.json OUT.pack [--radius R]

`--radius` may lower the table radius below the one used for the search:
every certificate leaf only needs `table.r ≤ box.r`.
"""
import argparse
import json
from fractions import Fraction as Q

from nopert214_emit_packed_local_view_lean import encode_axis, encoded_rat


def paths(rows):
    out = {0: []}
    stack = [0]
    while stack:
        i = stack.pop()
        row = rows[i]
        if row["kind"] == "view_split":
            for k, child in enumerate(row["children"]):
                out[child] = out[i] + [(k,)]
                stack.append(child)
        elif row["kind"] == "view_cut":
            weights = [Q(w) for w in row["weights"]]
            for k, child in enumerate(row["children"]):
                if child is not None:
                    out[child] = out[i] + [(4 + k, weights)]
                    stack.append(child)
    missing = [i for i in range(len(rows)) if i not in out]
    if missing:
        raise ValueError(f"rows unreachable from the root: {missing[:10]}")
    return out


def encode_path(path):
    out = [len(path)]
    for step in path:
        out.append(step[0])
        if step[0] >= 4:
            for w in step[1]:
                out += encoded_rat(w)
    return out


def encode_row(row, path):
    common = [int(row["id"]), int(row["root"])] + encode_path(path)
    kind = row["kind"]
    if kind == "view_split":
        return [0] + common + [int(c) for c in row["children"]]
    if kind == "view_cut":
        children = [0 if c is None else int(c) for c in row["children"]]
        weights = []
        for w in row["weights"]:
            weights += encoded_rat(Q(w))
        return [2] + common + children + weights
    if kind == "view_local":
        out = [1] + common + [int(row["symmetry_index"])]
        for axis in row["certificate"]:
            out += encode_axis(axis)
        out += encoded_rat(row["c"]) + encoded_rat(row["delta"]) + encoded_rat(row["r"])
        return out
    raise ValueError(f"unsupported row kind {kind}")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("input")
    parser.add_argument("output")
    parser.add_argument("--radius")
    args = parser.parse_args()
    data = json.load(open(args.input))
    if not data.get("complete"):
        raise SystemExit("refusing to emit an incomplete table")
    rows = data["rows"]
    radius = Q(args.radius) if args.radius else Q(data["tube_radius"])
    if radius > Q(data["tube_radius"]):
        raise SystemExit("the table radius can only be lowered")
    ps = paths(rows)
    symmetry = next(r["symmetry_index"] for r in rows if r["kind"] == "view_local")
    values = [len(rows), int(symmetry)] + encoded_rat(radius)
    for i, row in enumerate(rows):
        values += encode_row(row, ps[i])
    with open(args.output, "w") as out:
        out.write(",".join(str(v) for v in values) + ",")
    print(f"{args.input}: {len(rows)} rows, r = {radius}, {len(values)} naturals")


if __name__ == "__main__":
    main()
