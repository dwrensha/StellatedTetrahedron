#!/usr/bin/env python3
"""Quick terminal summary of the stellated-tetrahedron data runs.

    python3 scripts/stellated_status.py

Reads only logs and small checkpoint files; safe to run while jobs are live.
"""
import glob
import json
import os
import subprocess
import time

import stellated_progress as sp

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
ART = os.path.join(ROOT, ".artifacts/stellated")
LOCAL_DIRS = ["local", "local-300", "local-1000", "local-cut", "local-r400", "local-r400c", "local-t23"]
CORNER_ONLY = {21, 23}


def ago(t):
    m = int((time.time() - t) / 60)
    return f"{m} min ago" if m < 120 else f"{m / 60:.1f} h ago"


CHART_DIR = "chart4"   # current chart-0 (chart2 with table-29 tubes reopened)


def chart():
    path = os.path.join(ART, CHART_DIR, "run.log")
    lines = [json.loads(l) for l in open(path) if l.startswith('{"output')]
    if not lines:
        print("chart-0: no checkpoints yet")
        return
    last = lines[-1]
    if last.get("complete"):
        pack = os.path.join(ART, "packs", "chart0.pack")
        packed = (f"; packed {ago(os.path.getmtime(pack))}" if os.path.exists(pack) and
                  os.path.getmtime(pack) >= last["time"] else "; NOT yet re-packed")
        print(f"chart-0: complete, {last['rows']:,} rows, {last['failures']} failures "
              f"({CHART_DIR}{packed})")
        return
    rate = ""
    recent = [l for l in lines if last["time"] - l["time"] <= 3600 and l is not last]
    if recent:
        first = recent[0]
        per_min = (last["rows"] - first["rows"]) / max(1, (last["time"] - first["time"]) / 60)
        rate = f", {per_min:,.0f} rows/min over the last hour"
    print(f"chart-0: {last['rows']:,} rows, {last['pending']:,} open, "
          f"{last['failures']} failures (checkpoint {ago(last['time'])}{rate})")
    hist_path = os.path.join(ART, "chart-open-history.json")
    if os.path.exists(hist_path):
        snaps = [h for h in json.load(open(hist_path)) if "remaining" in h]
        if snaps:
            s = snaps[-1]
            first = snaps[0]
            print(f"         explored {100 * (1 - s['remaining']):.10f}%  "
                  f"(unexplored {100 * s['remaining']:.10f}%; first sample: "
                  f"explored {100 * (1 - first['remaining']):.10f}%)")


def local():
    done = set()
    # per-batch summary lines: {"index": i, "complete": true, ...}
    for path in glob.glob(os.path.join(ART, "local*.log")):
        for line in open(path):
            if line.startswith('{"index"'):
                d = json.loads(line)
                if d.get("complete"):
                    done.add(int(d["index"]))
    latest = {}
    for d in LOCAL_DIRS:
        for path in glob.glob(os.path.join(ART, d, "local-*.log")):
            name = os.path.basename(path)[6:8]
            if name.isdigit():
                i, t = int(name), os.path.getmtime(path)
                if i not in latest or t > latest[i][0]:
                    latest[i] = (t, path)
    status = {}
    for i, (t, path) in latest.items():
        last = ""
        with open(path, "rb") as f:
            f.seek(0, 2)
            f.seek(max(0, f.tell() - 4000))
            lines = f.read().decode(errors="ignore").splitlines()
        for line in reversed(lines):
            if line.startswith("{"):
                last = line
                break
        info = ""
        if last:
            try:
                d = json.loads(last)
                if d.get("complete"):
                    done.add(i)
                info = f"{d['rows']:,} rows, {d.get('pending', '?')} open, {d['failures']} failures, "
            except (ValueError, KeyError):
                pass
        status[i] = f"running ({info}{os.path.basename(os.path.dirname(path))}, updated {ago(t)})"
    try:
        used = json.load(open(os.path.join(ART, "chart-local-tables.json")))
        wanted = used["used"]
        dropped = [i for i in range(64) if i not in wanted]
        note = f" (tables {', '.join(map(str, dropped))} unused by {used['chart']}, not needed)"
    except (OSError, ValueError, KeyError):
        wanted = [i for i in range(64) if i not in CORNER_ONLY]
        note = ""
    print(f"local tables: {sum(i in done for i in wanted)} / {len(wanted)} needed done{note}")
    detail = {d["index"]: d for d in sp.local_status([i for i in wanted if i not in done])}
    for i in wanted:
        if i not in done:
            d = detail.get(i)
            if d and "unexplored" in d:
                rate = (f", {100 * d['rate_per_h']:.3f}%/h, ETA {sp.fmt_h(d.get('eta_h'))}"
                        if "rate_per_h" in d else ", rate pending (needs 10+ min of history)")
                print(f"   table {i:2d}: {d.get('rows', 0):,} rows, {d.get('pending')} open, "
                      f"{d.get('failures', 0)} failures, {100 * d['unexplored']:.3f}% of area "
                      f"unexplored{rate}")
            else:
                print(f"   table {i:2d}: {status.get(i, 'not started')}")


def _trend(r):
    """Open-box trend over the last hour (the honest clock for depth-first
    builders); the tree-fraction ETA only as a fallback."""
    if "open_trend_per_h" in r:
        t = r["open_trend_per_h"]
        eta = f", ETA ~{sp.fmt_h(r['eta_open_h'])}" if "eta_open_h" in r else ""
        return f"open {t:+.0f}/h{eta}"
    return f"ETA {sp.fmt_h(r.get('eta_h'))}"


def corner():
    built, remaining = sp.corner_status()
    print(f"corner tables: {built} / {sp.CORNER_TOTAL} built; remaining:")
    for r in remaining:
        if "nodes" in r:
            print(f"   #{r['index']:2d} {r['name']:<28} {100 * r['fraction']:10.6f}% of tree, "
                  f"{r['nodes']:,} boxes, {r['open']} open, {r['stuck']} stuck, "
                  f"{r['elapsed_h']:.1f} h, {_trend(r)} [{r['where']}]")
            c = r.get("counts", {})
            rate = f"{r['boxes_per_h']:,.0f} boxes/h" if "boxes_per_h" in r else "rate pending"
            kinds = ", ".join(f"{k} {c[k]:,}" for k in ("cert", "handoff", "flip", "split", "stellar") if c.get(k))
            print(f"       {rate}; {r.get('workers', 1)} workers; leaves/splits: {kinds}")
        else:
            also = f"; old run also in {', '.join(r['also'])}" if r.get("also") else ""
            print(f"   #{r['index']:2d} {r['name']:<28} running {sp.fmt_h(r.get('elapsed_h'))} "
                  f"[{r['where']}{also}]")


def machine():
    load = os.getloadavg()[0]
    out = subprocess.run(["ps", "-eo", "args"], capture_output=True, text=True).stdout
    jobs = {"local tables": "stellated_resume_local", "chart": "stellated_chart_search",
            "corner tree": "stellated_corner_tree"}
    procs = [l for l in out.splitlines() if "python" in l.split(" ", 1)[0]]
    counts = ", ".join(f"{k} {sum(v in l for l in procs)}" for k, v in jobs.items())
    print(f"machine: load {load:.1f} on {os.cpu_count()} cores; processes: {counts}")


if __name__ == "__main__":
    chart()
    local()
    corner()
    machine()
