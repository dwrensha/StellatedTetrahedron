#!/usr/bin/env bash
# Generate the kernel-only proof `StellatedKernel/` from the certificate packs (fetch them with
# scripts/fetch_packs.sh). Takes about 1–1.5 hours on 16 cores, almost all of it the chart;
# then `lake build StellatedKernel` checks the proof (about 7 hours).
#
# The generated modules refer to their data by repo-relative paths, so `lake build` must be
# run from the repository root.
set -euo pipefail
cd "$(dirname "$0")/.."
P=${1:-packs}
[ -f "$P/chart0.pack" ] || { echo "no $P/chart0.pack: run scripts/fetch_packs.sh first" >&2; exit 1; }

lake build chartKernelGen localKernelGen kernelCorner cornerAffGen
bin=.lake/build/bin
# everything except the checked-in final module Main.lean is generated
find StellatedKernel -mindepth 1 -maxdepth 1 ! -name Main.lean -exec rm -rf {} + 2>/dev/null || true
mkdir -p StellatedKernel/data/corner StellatedKernel/logs
log=StellatedKernel/logs

# chart table (slow: rebuilds the chart trees from the packed rows), in the background
$bin/chartKernelGen "$P" StellatedKernel/Chart 8000 200000 novalidate > $log/chart.log 2>&1 &
chart=$!

# local tables
$bin/localKernelGen "$P" StellatedKernel/Local 200 4 > $log/local.log

# corner tables (scripts/kernel_corner_tables.tsv): integer tables, affine tables, and
# table 49 (a slice of nine specification-checked nodes)
corner() {
  local i=$1 gen=$2 root=$3 stage=$4
  case $gen in
    int) $bin/kernelCorner ktreegen "$P/corner-v5.pack" "$i" 600 30 "$root" "$stage" \
           StellatedKernel StellatedKernel/data/corner ;;
    aff) $bin/cornerAffGen emit "$P/corner-v5.pack" "$i" 6 "$root" \
           "$([ "$stage" = CornerCoverage.cpocketStage ] && echo cpocket || echo none)" \
           600 15000 StellatedKernel StellatedKernel/data/corner ;;
    slice) $bin/kernelCorner slice "$P/corner-v5.pack" "StellatedKernel/data/corner/T$i.slice3" "$i" 0 9 ;;
  esac
}
export -f corner
export P bin
grep -v '^#' scripts/kernel_corner_tables.tsv |
  xargs -P 6 -d '\n' -I{} bash -c 'IFS=$'"'"'\t'"'"' read -r i g r s <<< "{}"; corner "$i" "$g" "$r" "$s" > '"$log"'/T$i.log 2>&1 || { echo "table $i FAILED (see '"$log"'/T$i.log)"; exit 255; }'

python3 scripts/gen_kernel_extra.py

wait $chart || { echo "chart generation FAILED (see $log/chart.log)" >&2; exit 1; }
echo "generated $(find StellatedKernel -name '*.lean' | wc -l) modules in StellatedKernel/"
