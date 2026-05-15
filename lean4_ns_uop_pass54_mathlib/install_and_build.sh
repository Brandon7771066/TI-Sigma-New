#!/bin/bash
# Pass-54 mathlib4 install + skeleton upgrade.
# Runs as a Replit Workflow because mathlib4 download+build typically exceeds
# agent tool-call 2-min cap. Idempotent: skips finished stages on re-run.
#
# CRITICAL: elan installs to $HOME/.elan which is OUTSIDE the workspace and is
# NOT persistent across some Replit session resets. So we always re-check and
# re-bootstrap if missing.
set -e
cd "$(dirname "$0")"

ELAN_DIR="$HOME/.elan"
export PATH="$ELAN_DIR/bin:$PATH"

LOG=install_and_build.log
: > $LOG
echo "===== START $(date -u +%Y-%m-%dT%H:%M:%SZ) =====" | tee -a $LOG

if ! command -v lean >/dev/null 2>&1; then
    echo "[0/6] elan/lean not on PATH — bootstrapping elan..." | tee -a $LOG
    curl --proto '=https' --tlsv1.2 -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
        -o /tmp/elan-init.sh
    bash /tmp/elan-init.sh -y --default-toolchain leanprover/lean4:v4.10.0 2>&1 | tee -a $LOG | tail -20
    export PATH="$ELAN_DIR/bin:$PATH"
else
    echo "[0/6] elan already present at $(which lean)" | tee -a $LOG
fi

echo "[1/6] Lean toolchain:" | tee -a $LOG
lean --version 2>&1 | tee -a $LOG

if [ ! -f lake-manifest.json ] || [ ! -d .lake/packages/mathlib ]; then
    echo "[2/6] Running 'lake update' to fetch mathlib4 manifest..." | tee -a $LOG
    lake update 2>&1 | tee -a $LOG | tail -40
else
    echo "[2/6] lake-manifest.json + mathlib package present, skipping update" | tee -a $LOG
fi

CACHE_MARKER=.lake/packages/mathlib/.lake/build/lib/Mathlib.olean
if [ ! -f "$CACHE_MARKER" ]; then
    echo "[3/6] Running 'lake exe cache get' to fetch prebuilt mathlib oleans..." | tee -a $LOG
    (cd .lake/packages/mathlib && lake exe cache get) 2>&1 | tee -a $LOG | tail -40
else
    echo "[3/6] mathlib Mathlib.olean present, skipping cache get" | tee -a $LOG
fi

echo "[4/6] Building Pass-54 NavierStokes lib..." | tee -a $LOG
lake build 2>&1 | tee -a $LOG | tail -40 || {
    echo "(lake build returned non-zero; see log for details)" | tee -a $LOG
}

echo "[5/6] Running #print axioms on UOP_implies_NS_smoothness..." | tee -a $LOG
cat > AxiomsCheck.lean << 'EOF'
import NavierStokes.UOPGap
#print axioms NavierStokes.UOPGap.UOP_implies_NS_smoothness
EOF
lake env lean AxiomsCheck.lean 2>&1 | tee -a $LOG | tail -20 || {
    echo "(axioms check failed; see log)" | tee -a $LOG
}

echo "[6/6] DONE $(date -u +%Y-%m-%dT%H:%M:%SZ)" | tee -a $LOG
echo "===== STATUS REPORT =====" | tee -a $LOG
du -sh .lake 2>&1 | tee -a $LOG
echo "===== END =====" | tee -a $LOG
