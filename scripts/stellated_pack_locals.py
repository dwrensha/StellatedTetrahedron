#!/usr/bin/env python3
"""Pack the local-view tables used by chart 0 (those listed in the final
radii map), choosing for each the complete run whose radius is at least the
final table radius; the pack carries the final radius.

    stellated_pack_locals.py RADII.json OUTDIR [--dry-run]
"""
import argparse
import glob
import json
import os
import subprocess
import sys
from fractions import Fraction as Q

ART = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".artifacts", "stellated")
DIRS = ["local", "local-300", "local-1000", "local-cut", "local-r400", "local-r400c", "local-r100b"]


def header(path):
    """complete flag and tube radius, read from the head of a large JSON."""
    with open(path) as f:
        head = f.read(400)
    complete = '"complete": true' in head
    import re
    m = re.search(r'"tube_radius": "([^"]+)"', head)
    return complete, (Q(m.group(1)) if m else None)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("radii")
    ap.add_argument("outdir")
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()
    radii = {int(k): Q(v) for k, v in json.load(open(args.radii)).items()}
    missing = []
    for index in sorted(radii):
        best = None
        for d in DIRS:
            path = os.path.join(ART, d, f"local-{index:02d}.json")
            if not os.path.exists(path):
                continue
            complete, r = header(path)
            if complete and r is not None and r >= radii[index]:
                best = path
        if best is None:
            missing.append(index)
            continue
        out = os.path.join(args.outdir, f"local-{index:02d}.pack")
        print(index, best, radii[index])
        if not args.dry_run and not os.path.exists(out):
            subprocess.run([sys.executable, os.path.join(os.path.dirname(__file__), "stellated_emit_local.py"),
                            best, out, "--radius", str(radii[index])], check=True)
    print("missing (not yet complete):", missing)


if __name__ == "__main__":
    main()
