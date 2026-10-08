#!/bin/sh
# Restart one running corner builder right after its next checkpoint.
#   stellated_restart_corner.sh DIR INDEX PAR
cd "$(dirname "$0")/.." || exit 1
dir=$1; i=$2; par=$3
A=.artifacts/stellated
ck=$A/$dir/ckpt-$(printf %02d "$i").json
m0=$(stat -c %Y "$ck")
while [ "$(stat -c %Y "$ck")" -le "$m0" ] || [ -e "$ck.tmp" ]; do sleep 2; done
for p in $(ps -eo pid,args | awk -v d="$A/$dir " -v o="--only $i " \
    'index($0, "stellated_corner_tree.py " d) && index($0 " ", o) {print $1}'); do
  kill "$p"
done
sleep 3
echo "$par" > "$A/$dir/par-$(printf %02d "$i")"
NOPERT_GMPY2=1 nohup nice -n 5 "$HOME/.venvs/stellated/bin/python" scripts/stellated_corner_tree.py \
  "$A/$dir" --eps0 3/16 --max-boxes 2000000 --only "$i" --par "$par" >> "$A/$dir/par.log" 2>&1 &
echo "restarted table $i in $dir with par $par at $(date +%T)"
