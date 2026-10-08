#!/usr/bin/env python3
"""Assemble the progress dashboard documents from run artifacts.

Reads `.artifacts/stellated/dashboard-state.json` (headline, stages, notes,
and which logs to read) plus the run logs, and writes summary.json and
history.json for the artifact database (progress/summary, progress/history).

    stellated_dashboard.py OUTDIR [--note "text"]
"""
import argparse
import math
from fractions import Fraction
import datetime
import glob
import json
import os

ROOT = os.path.join(os.path.dirname(__file__), "..")
STATE = os.path.join(ROOT, ".artifacts/stellated/dashboard-state.json")
CORNER = {21, 23}
OPEN_HISTORY = os.path.join(ROOT, ".artifacts/stellated/chart-open-history.json")
CHAMBER = ((1, 0, 0), (0.5, 0.5, 0), (1 / 3, 1 / 3, 1 / 3))


def _area(tri):
    a, b, c = tri
    u = [b[i] - a[i] for i in range(3)]
    v = [c[i] - a[i] for i in range(3)]
    cr = (u[1] * v[2] - u[2] * v[1], u[2] * v[0] - u[0] * v[2],
          u[0] * v[1] - u[1] * v[0])
    return math.sqrt(sum(x * x for x in cr)) / 2


def _num(x):
    return float(Fraction(x))


def _area2(tri):
    """Twice the area, up to a fixed factor, of a triangle in x+y+z = 1:
    the (1,1,1) component of the cross product (exact)."""
    a, b, c = tri
    u = [b[i] - a[i] for i in range(3)]
    v = [c[i] - a[i] for i in range(3)]
    return abs((u[1] * v[2] - u[2] * v[1]) + (u[2] * v[0] - u[0] * v[2]) +
               (u[0] * v[1] - u[1] * v[0]))


def open_snapshot(checkpoint):
    """Open (pending) chart-0 cells: count, unexplored domain fraction
    (view area x Cayley volume, relative to the root, exact), depth
    histograms."""
    data = json.load(open(checkpoint))
    chamber = _area2([[Fraction(x) for x in c] for c in
                      (("1", "0", "0"), ("1/2", "1/2", "0"), ("1/3", "1/3", "1/3"))])
    remaining = Fraction(0)
    view, rel = {}, {}
    for state in data["pending"]:
        widths = [Fraction(w) for w in state[2]]
        tri = [[Fraction(x) for x in corner] for corner in state[4]]
        remaining += widths[0] * widths[1] * widths[2] * _area2(tri) / chamber
        vd = str(state[5])
        rd = str(round(-math.log2(max(widths))))
        view[vd] = view.get(vd, 0) + 1
        rel[rd] = rel.get(rd, 0) + 1
    return {"t": iso(os.path.getmtime(checkpoint)), "open": len(data["pending"]),
            "remaining": float(remaining),
            "remainingPct": f"{float(100 * remaining):.10f}",
            "exploredPct": f"{float(100 * (1 - remaining)):.10f}",
            "viewDepth": view, "relDepth": rel}


def update_open_history(checkpoint, logs):
    """Append the current snapshot; back-fill bare open counts from logs."""
    try:
        history = json.load(open(OPEN_HISTORY))
    except (OSError, ValueError):
        history = []
        for log in logs:
            path = os.path.join(ROOT, log)
            if os.path.exists(path):
                for line in open(path):
                    if line.startswith('{"output'):
                        d = json.loads(line)
                        history.append({"t": iso(d["time"]), "open": d["pending"]})
    if os.path.exists(checkpoint) and not (
            history and history[-1]["t"] == iso(os.path.getmtime(checkpoint))
            and "remaining" in history[-1]):
        snap = open_snapshot(checkpoint)
        if not history or history[-1]["t"] != snap["t"]:
            history.append(snap)
        elif "remaining" not in history[-1]:
            history[-1] = snap
    json.dump(history, open(OPEN_HISTORY, "w"))
    return history


def iso(t):
    return datetime.datetime.fromtimestamp(t, datetime.timezone.utc).isoformat()


LOCAL_CACHE = os.path.join(ROOT, ".artifacts", "stellated", "local-status-cache.json")


def _local_file_status(path, cache):
    """(complete, has_failures, rows) for a local table file, without parsing
    multi-GB in-progress checkpoints: `complete` is the first key and
    `failures` the last; finished tables are parsed once and cached."""
    st = os.stat(path)
    key = f"{st.st_size}:{int(st.st_mtime)}"
    hit = cache.get(path)
    if hit and hit["key"] == key:
        return hit["complete"], hit["failures"], hit["rows"]
    with open(path, "rb") as f:
        head = f.read(64).decode(errors="ignore")
        f.seek(max(0, st.st_size - 4096))
        tail = f.read().decode(errors="ignore")
    complete = head.startswith('{"complete": true')
    k = tail.rfind('"failures": ')
    failures = k >= 0 and not tail[k + len('"failures": '):].startswith("[]")
    rows = 0
    if complete:
        try:
            rows = len(json.load(open(path)).get("rows", []))
        except (OSError, ValueError):
            pass
    cache[path] = {"key": key, "complete": complete, "failures": failures, "rows": rows}
    return complete, failures, rows


def local_status(dirs):
    status = {}
    rows = 0
    try:
        cache = json.load(open(LOCAL_CACHE))
    except (OSError, ValueError):
        cache = {}
    for d in dirs:
        for path in glob.glob(os.path.join(ROOT, d, "local-*.json")):
            name = os.path.basename(path)[len("local-"):-len(".json")]
            if not name.isdigit():
                continue
            try:
                done, failed, n = _local_file_status(path, cache)
            except OSError:
                continue
            index = int(name)
            if done:
                rows += n
            if status.get(index) != "done":
                status[index] = "done" if done else ("retry" if failed else "running")
    with open(LOCAL_CACHE + ".tmp", "w") as out:
        json.dump(cache, out)
    os.replace(LOCAL_CACHE + ".tmp", LOCAL_CACHE)
    try:
        used = set(json.load(open(os.path.join(ROOT, ".artifacts", "stellated",
                                               "chart-local-tables.json")))["used"])
    except (OSError, ValueError, KeyError):
        used = set(range(64))
    table = ["corner" if i in CORNER else (status.get(i, "running") if i in used else "unused")
             for i in range(64)]
    return table, rows


def chart_points(logs):
    points = []
    for log in logs:
        path = os.path.join(ROOT, log)
        if not os.path.exists(path):
            continue
        for line in open(path):
            if line.startswith('{"output'):
                d = json.loads(line)
                points.append({"t": iso(d["time"]), "rows": d["rows"]})
    return points


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("outdir")
    parser.add_argument("--note")
    args = parser.parse_args()
    state = json.load(open(STATE))
    now = datetime.datetime.now(datetime.timezone.utc).isoformat()
    if args.note:
        state["notes"].append({"t": now, "text": args.note})
        json.dump(state, open(STATE, "w"), indent=1, ensure_ascii=False)
    table, local_rows = local_status(state["localDirs"])
    points = chart_points(state["chartLogs"])
    import stellated_progress as sp
    corner_done, corner_left = sp.corner_status()
    local_left = sp.local_status([i for i, st in enumerate(table) if st not in ("done", "corner")])
    notes = state["metricNotes"]
    summary = {
        "updatedAt": now,
        "headline": state["headline"],
        "metrics": {
            "chartRows": points[-1]["rows"] if points else 0,
            "chartNote": notes.get("chartNote", ""),
            "localComplete": sum(1 for s in table if s == "done"),
            "localTotal": sum(1 for s in table if s not in ("corner", "unused")),
            "localNote": notes.get("localNote", f"{local_rows:,} rows"),
            "cornerFacesDone": corner_done,
            "cornerFacesTotal": sp.CORNER_TOTAL,
            "cornerNote": notes.get("cornerNote", ""),
            "sorries": state["sorries"],
            "leanNote": notes.get("leanNote", ""),
            "leanChecked": state.get("leanChecked", 0),
            "checkNote": notes.get("checkNote", "Final native check not run yet"),
        },
        "stages": state["stages"],
        "localTables": table,
        "remaining": {"corner": corner_left, "local": local_left},
        "notes": state["notes"][-40:],
    }
    os.makedirs(args.outdir, exist_ok=True)
    json.dump(summary, open(os.path.join(args.outdir, "summary.json"), "w"))
    checkpoint = os.path.join(ROOT, state.get(
        "chartCheckpoint", ".artifacts/stellated/chart2/chart0.json"))
    open_history = update_open_history(checkpoint, state["chartLogs"])
    json.dump({"points": points[-400:], "open": open_history[-400:]},
              open(os.path.join(args.outdir, "history.json"), "w"))
    print(json.dumps(summary["metrics"]))


if __name__ == "__main__":
    main()
