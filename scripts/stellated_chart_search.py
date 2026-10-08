#!/usr/bin/env python3
"""Generate (or resume) the chart-0 table for the stellated tetrahedron.

Tube radii come from the shared local tables' default policy
(`stellated_local_tables.default_radius`), 0 for the corner tables, which
have no local table.  Corner cells are recorded as failures with reason
"corner" and are left for the blow-up rows.

    stellated_chart_search.py OUTPUT [--resume] [--workers 15]
"""
import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import stellated_certificate_search as st  # noqa: E402
import stellated_local_tables as lt  # noqa: E402

Q = st.Q


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("output")
    parser.add_argument("--resume", action="store_true")
    parser.add_argument("--workers", type=int, default=15)
    parser.add_argument("--max-nodes", type=int, default=50_000_000)
    parser.add_argument("--max-view-depth", type=int, default=16)
    parser.add_argument("--min-relative-half-width", default="1/4096")
    parser.add_argument("--checkpoint-every", type=int, default=20000)
    parser.add_argument("--checkpoint-min-seconds", type=int, default=600)
    parser.add_argument("--radii", help="JSON map table index -> tube radius")
    args = parser.parse_args()
    st.install_stellated_search()
    table = json.load(open(args.radii)) if args.radii else {}
    radii = []
    for index in range(64):
        if index in st.CORNER_TABLES and str(index) not in table:
            st.TUBE_RADII[index] = None
            radii.append(Q(0))
        else:
            st.TUBE_RADII[index] = (Q(table[str(index)]) if str(index) in table
                                    else lt.default_radius(index))
            radii.append(st.TUBE_RADII[index])
    result = st.base.generate_atlas_projective_table(
        0, args.max_nodes, args.max_view_depth,
        Q(args.min_relative_half_width), args.output,
        args.checkpoint_every, args.resume, False, tuple(radii),
        args.workers, args.checkpoint_min_seconds)
    print(json.dumps({"complete": result["complete"],
                      "rows": len(result["rows"]),
                      "pending": len(result["pending"]),
                      "counts": result["counts"],
                      "failures": len(result["failures"])},
                     default=str), flush=True)


if __name__ == "__main__":
    main()
