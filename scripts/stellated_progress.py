"""Fine-grained remaining-work estimates for the stellated-tetrahedron runs.

Shared by `stellated_status.py` and `stellated_dashboard.py`.  Reads only
logs, small progress files and the tails of checkpoints.
"""
import glob
import json
import os
import time
from fractions import Fraction as F

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
ART = os.path.join(ROOT, ".artifacts/stellated")
CORNER_DIRS = ["corner-tree", "corner-tree-2", "corner-tree-3", "corner-tree-4", "corner-tree-5", "corner-tree-6", "corner-tree-7", "corner-tree-8", "corner-tree-9", "corner-tree-10", "corner-tree-11"]
CORNER_TOTAL = 86
LOCAL_HISTORY = os.path.join(ART, "local-progress-history.json")


def corner_name(i):
    """Human-readable name of corner root table `i` (`PackedCornerTree` order)."""
    if i < 36:
        seg = "B" if i >= 18 else "A"
        j = i % 18
        if j < 7:
            return f"plain {seg} face {j}"
        if j < 13:
            return f"tube {seg} face {j - 7}"
        if j == 13:
            return f"wedge {seg}"
        return f"wedge-tube {seg} face {j - 14}"
    if i == 36:
        return "skew"
    if i < 43:
        return f"corner view face {i - 37}"
    if i < 59:
        return f"cone orthant {i - 43}"
    if i < 68:
        k, m = divmod(i - 59, 3)
        return f"pocket {k} {('a=eps*alpha', 'a=+8eps+w', 'a=-8eps+w')[m]}"
    if i < 71:
        return f"skew pocket {('a=eps*alpha', 'a=+8eps+w', 'a=-8eps+w')[i - 68]}"
    if i < 77:
        k, m = divmod(i - 71, 3)
        return f"plain pocket {'BA'[k]} {('a=eps*alpha', 'a=+8eps+w', 'a=-8eps+w')[m]}"
    if i < 83:
        k, m = divmod(i - 77, 3)
        return f"tie pocket {('b+', 'c+')[k]} {('a=eps*alpha', 'a=+8eps+w', 'a=-8eps+w')[m]}"
    return f"plain pocket B c<0 {('a=eps*alpha', 'a=+8eps+w', 'a=-8eps+w')[i - 83]}"


CORNER_HISTORY = os.path.join(ROOT, ".artifacts", "stellated", "corner-progress-history.json")


def _corner_history(index, p):
    """(time, fraction) samples per corner table, appended on each call (at
    most one per progress update) and trimmed to the last 6 hours."""
    try:
        hist = json.load(open(CORNER_HISTORY))
    except (OSError, ValueError):
        hist = {}
    h = hist.setdefault(str(index), [])
    if h and h[-1][1] > p["done_fraction"] + 1e-12:
        h.clear()          # restarted build
    if not h or h[-1][0] < p["updated"]:
        h.append([p["updated"], p["done_fraction"], p["open"], p["nodes"]])
    h[:] = [x for x in h if x[0] > p["updated"] - 6 * 3600]
    with open(CORNER_HISTORY + ".tmp", "w") as out:
        json.dump(hist, out)
    os.replace(CORNER_HISTORY + ".tmp", CORNER_HISTORY)
    return h


def corner_status():
    """(built count, list of remaining-table dicts)."""
    built = set()
    for d in CORNER_DIRS:
        for path in glob.glob(os.path.join(ART, d, "table-*.json")):
            built.add(int(os.path.basename(path)[6:8]))
    progress = {}
    for d in CORNER_DIRS:
        for path in glob.glob(os.path.join(ART, d, "progress-*.json")):
            try:
                p = json.load(open(path))
            except ValueError:
                continue
            p["dir"] = d
            progress.setdefault(p["index"], []).append(p)
    builds = _corner_builds()
    remaining = []
    for i in range(CORNER_TOTAL):
        if i in built:
            continue
        # every build of this table active in the last two hours (e.g. the
        # parallel and serial builds of 45), else the most recent one
        ps = sorted(progress.get(i, []), key=lambda q: -q["updated"])
        live = [q for q in ps if time.time() - q["updated"] < 7200] or ps[:1]
        live.sort(key=lambda q: (q.get("par", 1) <= 1, q["dir"]))   # parallel first, stable
        for p in live or [None]:
            item = _corner_item(i, p, builds)
            if len(live) > 1 and p is not None:
                # several builds of one table (e.g. 45): name them apart
                item["name"] += " (parallel)" if p.get("par", 1) > 1 else " (serial)"
            remaining.append(item)
    return len(built), remaining


def _corner_item(i, p, builds):
    """Status dict for one build of corner table i (p: its progress file)."""
    if True:
        item = {"index": i, "name": corner_name(i)}
        if p:
            item.update(nodes=p["nodes"], open=p["open"], stuck=p["stuck"],
                        fraction=p["done_fraction"], elapsed_h=p["elapsed"] / 3600,
                        updated_min=(time.time() - p["updated"]) / 60, where=p["dir"],
                        counts=p.get("counts", {}), workers=p.get("par", 1))
            if p["stuck"] == 0:
                # rate over the last hour only: the tree fraction is front-loaded
                # (big easy regions close first), so a since-start average is
                # far too optimistic once only the hard branches remain
                hist = _corner_history(f"{i}@{p['dir']}", p)
                old = [h for h in hist if h[0] <= p["updated"] - 3000]
                if old:
                    t0, f0 = old[-1][:2]
                    rate = (p["done_fraction"] - f0) / max(p["updated"] - t0, 1)
                    if rate > 0:
                        item["eta_h"] = (1 - p["done_fraction"]) / rate / 3600
                    # depth-first builders close the frontier rather than tree
                    # weight; the open-box trend is the better clock for them
                    if len(old[-1]) > 3:
                        item["boxes_per_h"] = (p["nodes"] - old[-1][3]) / max(p["updated"] - t0, 1) * 3600
                    if len(old[-1]) > 2:
                        drop = (old[-1][2] - p["open"]) / max(p["updated"] - t0, 1)
                        item["open_trend_per_h"] = -drop * 3600
                        if drop > 0:
                            item["eta_open_h"] = p["open"] / drop / 3600
        else:
            runs = [b for b in builds if b["only"] is None or i in b["only"]]
            if runs:
                b = min(runs, key=lambda b: b["elapsed"])
                item["where"] = f"{b['dir']} (no progress reporting)"
                item["elapsed_h"] = b["elapsed"] / 3600
                item["also"] = [x["dir"] for x in runs if x is not b]
            else:
                item["where"] = "not running"
        return item


def _corner_builds():
    """Running corner-tree builds: output dir, table list, elapsed seconds."""
    import subprocess
    out = subprocess.run(["ps", "-eo", "etimes,args"], capture_output=True, text=True).stdout
    builds = {}
    for line in out.splitlines():
        parts = line.split()
        args = parts[1:]
        if (len(parts) < 3 or not args[0].endswith("python") or "pack" in args or
                not any(a.endswith("stellated_corner_tree.py") for a in args)):
            continue
        k = next(i for i, a in enumerate(args) if a.endswith("stellated_corner_tree.py"))
        d = os.path.basename(args[k + 1].rstrip("/"))
        only = None
        if "--only" in args:
            only = {int(x) for x in args[args.index("--only") + 1].split(",")}
        e = int(parts[0])
        if d not in builds or e > builds[d]["elapsed"]:
            builds[d] = {"dir": d, "only": only, "elapsed": e}
    return list(builds.values())


def _tail_pending(path):
    sz = os.path.getsize(path)
    with open(path, "rb") as f:
        f.seek(max(0, sz - 3_000_000))
        tail = f.read().decode(errors="ignore")
    i = tail.rfind('"pending":')
    j = tail.find('"counts"', i)
    if i < 0 or j < 0:
        return None
    return json.loads("{" + tail[i:j].rstrip().rstrip(",") + "}")["pending"]


def _area(tri):
    a = [[float(F(x)) for x in v] for v in tri]
    u = [a[1][k] - a[0][k] for k in range(3)]
    v = [a[2][k] - a[0][k] for k in range(3)]
    c = [u[1] * v[2] - u[2] * v[1], u[2] * v[0] - u[0] * v[2], u[0] * v[1] - u[1] * v[0]]
    return 0.5 * sum(x * x for x in c) ** 0.5


def local_status(tables, record=True):
    """Per unfinished local table: rows, pending, unexplored area, rate, ETA."""
    history = json.load(open(LOCAL_HISTORY)) if os.path.exists(LOCAL_HISTORY) else []
    now = time.time()
    out = []
    for t in tables:
        path = os.path.join(ART, "local-300", f"local-{t}.json")
        logp = os.path.join(ART, "local-300", f"local-{t}.log")
        if not os.path.exists(path):
            continue
        item = {"index": t}
        try:
            last = [l for l in open(logp).read().splitlines()[-5:] if l.startswith("{")][-1]
            d = json.loads(last)
            item.update(rows=d["rows"], pending=d.get("pending"), failures=d["failures"])
        except (IndexError, ValueError, KeyError, OSError):
            pass
        pend = _tail_pending(path)
        if pend is not None:
            with open(path, "rb") as f:
                head = f.read(3000).decode(errors="ignore")
            k = head.find('"triangle":')
            root = json.loads(head[k + 11:head.find("]]", k) + 2])
            item["unexplored"] = sum(_area(e[1]) for e in pend) / _area(root)
            mine = [h for h in history if h["table"] == t and now - h["t"] <= 6 * 3600]
            if mine and now - mine[0]["t"] > 600:
                rate = (mine[0]["unexplored"] - item["unexplored"]) / (now - mine[0]["t"])
                if rate > 0:
                    item["eta_h"] = item["unexplored"] / rate / 3600
                item["rate_per_h"] = rate * 3600
            if record and (not mine or now - max(h["t"] for h in mine) > 600):
                history.append({"t": now, "table": t, "unexplored": item["unexplored"]})
        out.append(item)
    if record:
        history = [h for h in history if now - h["t"] <= 48 * 3600]
        with open(LOCAL_HISTORY + ".tmp", "w") as f:
            json.dump(history, f)
        os.replace(LOCAL_HISTORY + ".tmp", LOCAL_HISTORY)
    return out


def fmt_h(h):
    if h is None:
        return "?"
    if h < 1:
        return f"{h * 60:.0f} min"
    if h < 48:
        return f"{h:.1f} h"
    return f"{h / 24:.1f} days"
