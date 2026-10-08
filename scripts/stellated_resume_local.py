#!/usr/bin/env python3
"""Resume an unfinished stellated local-view table from its checkpoint with a
larger node budget (tables started by the #214 generator).

    stellated_resume_local.py TABLE_INDEX CHECKPOINT.json [--max-nodes N]
"""
import argparse
import json
import os
import sys
from fractions import Fraction as Q
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import stellated_certificate_search as st  # noqa: E402


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("index", type=int)
    parser.add_argument("checkpoint")
    parser.add_argument("--max-nodes", type=int, default=2_000_000)
    parser.add_argument("--workers", type=int, default=1)
    parser.add_argument("--tube-radius",
                        help="lower the table radius for new rows (existing rows keep "
                             "their larger r; Lean only needs table r <= row r)")
    parser.add_argument("--target-c",
                        help="override the saved target margin for new rows "
                             "(Lean needs r^2 (1 + c^2) <= 4 c^2)")
    args = parser.parse_args()
    st.install_stellated_search()
    st.base.UPPER_WEDGE_PROJECTIVE_ROOT = st.DEPTH3_TRIANGLES[args.index]
    while True:
        with open(args.checkpoint) as source:
            saved = json.load(source)
        target_c = Q(args.target_c or saved["target_c"])
        radius = Q(args.tube_radius or saved["tube_radius"])
        max_depth, initial_child = saved["max_depth"], saved.get("initial_child")
        if saved["failures"]:
            # the resumed generator stops at its first failures; repair them
            # with the stellated generator's tie-plane cuts and resume
            if not repair_failures(saved, target_c, radius):
                print(json.dumps({"index": args.index, "repair": "failed",
                                  "failures": saved["failures"]}, default=str), flush=True)
                return
            with open(args.checkpoint + ".tmp", "w") as out:
                json.dump(saved, out, default=str)
            os.replace(args.checkpoint + ".tmp", args.checkpoint)
            del saved
        else:
            del saved
        result = st.base.generate_projective_local_view_table(
            args.checkpoint, args.max_nodes, max_depth,
            target_c, radius, 500, True, initial_child, args.workers)
        print(json.dumps({"index": args.index, "complete": result["complete"],
                          "rows": len(result["rows"]),
                          "failures": len(result["failures"])}), flush=True)
        if result["complete"] or not result["failures"]:
            return


def repair_failures(saved, target_c, radius):
    """Repair failed rows with the stellated generator's stronger search: a
    certificate on the whole triangle, else certified pieces of a tie-plane
    cut, else certified children of an ordinary 4-split (rows appended)."""
    import stellated_local_tables as lt
    base = st.base
    rows = saved["rows"]

    def certify(tri, depth):
        result = lt.local_candidate(tri, depth, target_c, radius, [])
        if (result is None or result["c"] < target_c or
                radius * radius * (1 + result["c"] ** 2) > 4 * result["c"] ** 2):
            return None
        return {"kind": "view_local", "root": 0, "triangle": tri, "depth": depth,
                "symmetry_index": 0, "r": radius,
                "certificate": [base.compact_projective_local_axis_artifact(a)
                                for a in result["certificates"]],
                "c": result["c"], "delta": result["delta"]}

    for failure in saved["failures"]:
        tri = tuple(tuple(Q(x) for x in v) for v in failure["triangle"])
        depth = failure["depth"]
        whole = certify(tri, depth)
        if whole is not None:
            whole["id"] = failure["id"]
            rows[failure["id"]] = whole
            print(json.dumps({"repaired": failure["id"], "whole": float(whole["c"])}), flush=True)
            continue
        weights = lt.tie_cut(tri)
        if weights is not None:
            subs = [tuple(tuple(v) for v in lt.cut_triangle(tri, weights, k)) if weights[k] > 0
                    else None for k in range(3)]
            kind_row = {"kind": "view_cut", "weights": weights}
        else:
            subs = [tuple(tuple(v) for v in sub) for sub in base.split_projective_triangle(tri)]
            kind_row = {"kind": "view_split"}
        pieces = [None if sub is None else certify(sub, depth + 1) for sub in subs]
        if any(sub is not None and piece is None for sub, piece in zip(subs, pieces)):
            return False
        children = []
        for piece in pieces:
            if piece is None:
                children.append(None)
                continue
            piece["id"] = len(rows)
            children.append(piece["id"])
            rows.append(piece)
        rows[failure["id"]] = {"id": failure["id"], "root": 0, "triangle": tri, "depth": depth,
                               "children": children, **kind_row}
        print(json.dumps({"repaired": failure["id"], "kind": kind_row["kind"],
                          "pieces": [None if p is None else float(p["c"]) for p in pieces]},
                         default=str), flush=True)
    saved["failures"] = []
    saved["complete"] = False
    return True


if __name__ == "__main__":
    main()
