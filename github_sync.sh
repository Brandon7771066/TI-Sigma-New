#!/bin/bash
# ============================================================
# TI Sigma — GitHub/Codespaces Sync Script
# ============================================================
# This pushes EVERYTHING from Replit to your GitHub repo so
# Codespaces always has the full, latest codebase.
#
# SETUP (one-time):
#   1. Go to: https://github.com/settings/tokens/new
#   2. Name: "TI Sigma Replit Sync"
#   3. Expiration: 1 year
#   4. Scopes: check "repo" (full repository access)
#   5. Click "Generate token" and copy it
#   6. In Replit Secrets, add: GITHUB_PAT = <your token>
#   7. Run: bash github_sync.sh
#
# USAGE:
#   bash github_sync.sh            # sync to main
#   bash github_sync.sh "message"  # custom commit message
# ============================================================

set -e

GITHUB_PAT="${GITHUB_PAT:-}"
REPO="Brandon7771066/TI-Sigma-New"
BRANCH="main"
MSG="${1:-Auto-sync from Replit: $(date '+%Y-%m-%d %H:%M')}"

echo ""
echo "=================================================="
echo "  TI Sigma — GitHub Sync to Codespaces"
echo "  Repo:   https://github.com/$REPO"
echo "  Branch: $BRANCH"
echo "  Msg:    $MSG"
echo "=================================================="

# Check for PAT
if [ -z "$GITHUB_PAT" ]; then
    echo ""
    echo "❌  GITHUB_PAT not set."
    echo ""
    echo "  Add it to Replit Secrets:"
    echo "  1. https://github.com/settings/tokens/new"
    echo "  2. Scope: repo"
    echo "  3. Copy token → Replit Secrets → GITHUB_PAT"
    echo ""
    exit 1
fi

# Configure authenticated remote
REMOTE_URL="https://${GITHUB_PAT}@github.com/${REPO}.git"
git remote set-url origin "$REMOTE_URL" 2>/dev/null || \
    git remote add origin "$REMOTE_URL"

echo ""
echo "  ✅ Remote configured."

# Stage all changes
git add -A

# Commit (skip if nothing to commit)
if git diff --staged --quiet; then
    echo "  ✅ Nothing new to commit — already up to date."
else
    git commit -m "$MSG"
    echo "  ✅ Committed: $MSG"
fi

# Push
echo "  Pushing to GitHub..."
git push origin "$BRANCH"

# Reset remote URL to not store PAT in config
git remote set-url origin "https://github.com/${REPO}.git"

echo ""
echo "  ✅ Synced! Open in Codespaces:"
echo "     https://github.com/${REPO}"
echo ""
echo "  To open in Codespaces:"
echo "  1. Go to https://github.com/${REPO}"
echo "  2. Click Code → Codespaces → Create codespace on main"
echo ""
