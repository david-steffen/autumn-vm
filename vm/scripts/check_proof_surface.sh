#!/usr/bin/env bash
# Verify curated public lemma names still exist in allowlisted modules.
# Golden: vm/tests/proof_surface.names (one theorem name per line).
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
GOLDEN="$ROOT/tests/proof_surface.names"
MODULES=(
  "$ROOT/Autumn/Step/Lemmas.lean"
  "$ROOT/Autumn/Step/PreserveInstr.lean"
  "$ROOT/Autumn/Step/ProgressInstr.lean"
  "$ROOT/Autumn/Step/Preserve.lean"
  "$ROOT/Autumn/Step/Progress.lean"
  "$ROOT/Autumn/Step/Schedule.lean"
  "$ROOT/Autumn/State/SchedLemmas.lean"
  "$ROOT/Autumn/State/LinkLemmas.lean"
  "$ROOT/Autumn/State/ProcessLemmas.lean"
  "$ROOT/Autumn/Heap/Lemmas.lean"
  "$ROOT/Autumn/Json/Lemmas.lean"
  "$ROOT/Autumn/Process/Lemmas.lean"
)

if [[ ! -f "$GOLDEN" ]]; then
  echo "missing golden: $GOLDEN" >&2
  exit 1
fi

TMP="$(mktemp)"
trap 'rm -f "$TMP"' EXIT

# Match `theorem name` even when preceded by attributes on the same line.
rg -N --no-filename -o 'theorem [A-Za-z0-9_'\'']+' "${MODULES[@]}" \
  | sed 's/^theorem //' | sort -u > "$TMP"

missing=0
count=0
while IFS= read -r name || [[ -n "$name" ]]; do
  [[ -z "$name" || "$name" =~ ^# ]] && continue
  count=$((count + 1))
  if ! grep -Fxq "$name" "$TMP"; then
    echo "missing theorem: $name" >&2
    missing=1
  fi
done < "$GOLDEN"

if [[ "$missing" -ne 0 ]]; then
  echo "proof surface check failed (update lemmas or $GOLDEN)" >&2
  exit 1
fi

echo "proof surface ok ($count names)"
