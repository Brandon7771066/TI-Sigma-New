#!/bin/bash
# Download one pair's EEG, extract LCC features, then delete the big .eeg to save disk.
# Usage: bash build_pair.sh <pair_int>
set -e
HERE="$(cd "$(dirname "$0")" && pwd)"
DATA="$HERE/data"
p=$1
sub=$(printf "sub-%02d" "$p")
d="$DATA/$sub"
mkdir -p "$d"
base="https://s3.amazonaws.com/openneuro.org/ds007471/$sub"
# fetch <relative-name> <dest>: try eeg/ subfolder first, fall back to subject root.
fetch() {
  local name="$1" dest="$2"
  [ -f "$dest" ] && return 0
  if curl -sf --max-time 115 "$base/eeg/$name" -o "$dest.tmp"; then :; \
  elif curl -sf --max-time 115 "$base/$name" -o "$dest.tmp"; then :; \
  else rm -f "$dest.tmp"; return 1; fi
  mv "$dest.tmp" "$dest"
}
if [ ! -f "$HERE/features/${sub}_features.csv" ]; then
  fetch "${sub}_task-jointaction_eeg.vhdr" "$d/${sub}_task-jointaction_eeg.vhdr" || { echo "SKIP $sub (no vhdr)"; exit 0; }
  fetch "${sub}_task-jointaction_eeg.vmrk" "$d/${sub}_task-jointaction_eeg.vmrk" || { echo "SKIP $sub (no vmrk)"; exit 0; }
  fetch "${sub}_task-jointaction_events.tsv" "$d/${sub}_task-jointaction_events.tsv" || { echo "SKIP $sub (no events)"; exit 0; }
  eeg="$d/${sub}_task-jointaction_eeg.eeg"
  rm -f "$eeg"
  fetch "${sub}_task-jointaction_eeg.eeg" "$eeg" || { echo "SKIP $sub (no eeg)"; exit 0; }
  python "$HERE/extract_features.py" "$p"
fi
# cleanup big files to save disk (keep small headers + features)
rm -f "$d/${sub}_task-jointaction_eeg.eeg" "$d"/IBS_*.eeg 2>/dev/null || true
echo "done $sub"
