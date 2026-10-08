#!/bin/sh
# Restart every stellated search job from its on-disk checkpoint (e.g. after a
# reboot).  Safe to run only when none of these jobs is already running.
# Python env: ~/.venvs/stellated (numpy, scipy, gmpy2==2.2.1; /tmp is tmpfs).
cd "$(dirname "$0")/.." || exit 1
PY=$HOME/.venvs/stellated/bin/python
A=.artifacts/stellated
export NOPERT_GMPY2=1

if pgrep -f "[s]tellated_corner_tree.py" >/dev/null; then
  echo "stellated jobs already running; not starting duplicates" >&2
  exit 1
fi

# local table 29 is no longer needed: chart-0 (chart4) has no rows referencing it

# corner tables (resume from ckpt-XX.json in each directory)
corner() { dir=$1; shift; nohup nice -n 5 $PY scripts/stellated_corner_tree.py \
  $A/$dir --eps0 3/16 --max-boxes 2000000 "$@" >> $A/$dir/par.log 2>&1 & }
corner corner-tree-5 --only 18 --par 3
corner corner-tree-5 --only 29 --par 2
corner corner-tree-6 --only 71 --par 2
corner corner-tree-6 --only 74 --par 2
corner corner-tree-3 --only 68 --par 3
corner corner-tree-9 --only 45 --par 8
corner corner-tree-11 --only 45 --jobs 1   # serial twin of 45 (whichever finishes first)
echo "started corner 18, 29, 45, 68, 71, 74"
