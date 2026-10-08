#!/usr/bin/env python3
"""Emit the packed chart-0 table for the stellated tetrahedron.

Same format as `nopert214_emit_packed_global.py` except for the rows whose
semantics changed (see Noperts/Stellated/PackedSolutionTree.lean):

* tag 6 `symmetry_tube`: ..., symmetry, r, table (Fin 64), root, triangle,
  then the nine containment weights of the triangle in its table triangle;
* tag 7 (`radius` rows): the octahedron prune, ..., root, triangle;
* tag 8 (`fundamental_prune` rows): the flip prune, ..., form, negate,
  triangle;
* tag 10 (`fundamental_prune` rows with prune "corner"): the corner row,
  ..., triangle;
* tag 11 `view_cut`: ..., root, triangle, three children (0 when the weight
  is zero), three weights.
"""
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import nopert214_emit_packed_global as base  # noqa: E402
from nopert214_emit_lean import interval_key, triangle_key  # noqa: E402
from nopert214_emit_packed_local_view_lean import encoded_rat  # noqa: E402

_base_encode_row = base.encode_row

# Tube rows must carry exactly the radius of the shared table they use
# (Lean: tube.r = table.r).  A row found with a smaller radius stays valid
# with the table's larger one, since its mismatch bound is unchanged.
RADIUS_OVERRIDE = {}


def encode_row(row, interval_ids, triangle_ids):
    kind = row["kind"]
    if kind == "view_cut":
        children = [0 if c is None else int(c) for c in row["children"]]
        weights = []
        for w in row["weights"]:
            weights.extend(encoded_rat(w))
        return [11, int(row["id"]), interval_ids[interval_key(row)],
                int(row["root"]), triangle_ids[triangle_key(row)],
                *children, *weights]
    if kind not in ("symmetry_tube", "radius", "fundamental_prune"):
        return _base_encode_row(row, interval_ids, triangle_ids)
    result = [base.TAGS[kind], int(row["id"]), interval_ids[interval_key(row)]]
    root = int(row["root"])
    triangle_id = triangle_ids[triangle_key(row)]
    if kind == "radius":
        if row.get("prune") != "octahedron":
            raise ValueError("radius rows must be octahedron prunes")
        return [*result, root, triangle_id]
    if kind == "fundamental_prune" and row.get("prune") == "corner":
        if root != 0:
            raise ValueError("corner rows live in root 0")
        return [10, int(row["id"]), interval_ids[interval_key(row)], triangle_id]
    if kind == "fundamental_prune":
        if row.get("prune") != "flip" or root != 0:
            raise ValueError("fundamental_prune rows must be flip prunes")
        return [*result, int(row["form"]), 1 if row["negate"] else 0,
                triangle_id]
    within = row.get("within")
    if within is None or len(within) != 3:
        raise ValueError("symmetry_tube rows need containment weights")
    weights = []
    for corner in within:
        for value in corner:
            weights.extend(encoded_rat(value))
    radius = RADIUS_OVERRIDE.get(int(row["shared_index"]), row["radius"])
    return [*result, int(row["symmetry_index"]), *encoded_rat(radius),
            int(row["shared_index"]), root, triangle_id, *weights]


base.encode_row = encode_row

if __name__ == "__main__":
    import os
    if os.environ.get("STELLATED_TABLE_RADII"):
        with open(os.environ["STELLATED_TABLE_RADII"]) as source:
            RADIUS_OVERRIDE.update({int(k): v for k, v in json.load(source).items()})
    base.main()
