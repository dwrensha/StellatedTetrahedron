#!/usr/bin/env bash
# Download the certificate packs (GitHub release `data-v1`) into `packs/`:
# chart0.pack, corner-v2.pack (read by constructStellated), corner-v5.pack (input to the
# kernel generators) and the 60 local-NN.pack files.
set -euo pipefail
cd "$(dirname "$0")/.."
tag=${1:-data-v1}
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
gh release download "$tag" -R dwrensha/StellatedTetrahedron -p stellated-packs.tar.gz -D "$tmp"
tar xzf "$tmp/stellated-packs.tar.gz" -C "$tmp"
(cd "$tmp/stellated-packs" && sha256sum --quiet -c SHA256SUMS)
rm -rf packs
mv "$tmp/stellated-packs" packs
echo "packs/: $(ls packs/*.pack | wc -l) packs, checksums verified"
