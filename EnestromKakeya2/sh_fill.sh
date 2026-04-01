#!/usr/bin/env bash
# sh_fill.sh — build the project, report the tactic found by `by sh`,
#              replace `by sh` with it, then verify with a second build.
#
# Usage:
#   ./sh_fill.sh                  # just build and show results
#   ./sh_fill.sh <file> <line>    # replace `by sh` at that line and verify
#
# Workflow (use ONE `by sh` per run):
#   1. Replace one `sorry` with `by sh` in a .thy file.
#   2. Run: ./sh_fill.sh <file> <line>
#   3. Script replaces `by sh` with the found tactic and rebuilds to verify.
#      If the verification build fails or times out, the replacement is undone.

set -euo pipefail

RESULTS="/tmp/isabelle_sh_results.txt"
DIR="$(cd "$(dirname "$0")" && pwd)"
TACTIC_TIMEOUT=60   # seconds per tactic for Sqrt2 only (catches looping metis etc.)
# NOTE: never use -f or global -o timeout (would break HOL cache)

# Clear previous results
rm -f "$RESULTS"

echo "[sh_fill] Building (step 1: sh search)..."
cd "$DIR"
isabelle build -D . 2>&1 || true

if [[ ! -f "$RESULTS" ]]; then
  echo "[sh_fill] No sh results recorded (proof may have failed or no \`by sh\` present)."
  exit 1
fi

echo
echo "[sh_fill] Results:"
cat "$RESULTS"
echo

# If file and line given, replace and verify
if [[ $# -ge 2 ]]; then
  THY_FILE="$1"
  LINE="$2"
  TACTIC=$(cut -d'|' -f3 "$RESULTS" | head -1 | sed 's/^ *//')

  if [[ -z "$TACTIC" ]]; then
    echo "[sh_fill] Could not extract tactic from results."
    exit 1
  fi

  echo "[sh_fill] Replacing line $LINE of $THY_FILE with: $TACTIC"
  sed -i '' "${LINE}s/by sh/${TACTIC}/" "$THY_FILE"

  echo
  echo "[sh_fill] Verifying (step 2: rebuild with replacement)..."
  if isabelle build -D . 2>&1; then
    echo "[sh_fill] Verification passed — replacement is good."
  else
    echo "[sh_fill] Verification FAILED (tactic may loop or be wrong). Reverting."
    sed -i '' "${LINE}s/${TACTIC}/by sh/" "$THY_FILE"
    exit 1
  fi
fi
