#!/usr/bin/env bash
# Sync check: vm/builtins.mfa ↔ Lean isBuiltinName ↔ Mix @builtins values.
# Process.* may appear in inventory + Lean without a Mix @builtins entry
# (Mix emits them as call MFAs via dedicated lowering). make_tuple/N is a
# Lean prefix rule only — not listed in the inventory.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
REPO="$(cd "$ROOT/.." && pwd)"
INVENTORY="$ROOT/builtins.mfa"
LEAN="$ROOT/Autumn/Instr.lean"
MIX="$REPO/compiler/lib/autumn_compiler/lower.ex"

if [[ ! -f "$INVENTORY" ]]; then
  echo "missing inventory: $INVENTORY" >&2
  exit 1
fi

TMP_INV="$(mktemp)"
TMP_LEAN="$(mktemp)"
TMP_MIX="$(mktemp)"
trap 'rm -f "$TMP_INV" "$TMP_LEAN" "$TMP_MIX"' EXIT

# Inventory names (skip blanks and # comments)
grep -vE '^\s*(#|$)' "$INVENTORY" | sort -u > "$TMP_INV"

# Lean: string literals compared in isBuiltinName
rg -N -o '"[^"]+/[0-9]+"' "$LEAN" | tr -d '"' | sort -u > "$TMP_LEAN"

# Mix @builtins map only (between @builtins %{ and the closing })
awk '
  /^  @builtins %\{/ {inb=1; next}
  inb && /^  \}/ {inb=0}
  inb {
    if (match($0, /=> "[^"]+"/, m)) {
      s = m[0]
      sub(/^=> "/, "", s)
      sub(/"$/, "", s)
      print s
    }
  }
' "$MIX" | sort -u > "$TMP_MIX"

missing=0

while IFS= read -r name || [[ -n "$name" ]]; do
  [[ -z "$name" ]] && continue
  if ! grep -Fxq -- "$name" "$TMP_LEAN"; then
    echo "inventory MFA missing from Lean isBuiltinName strings: $name" >&2
    missing=1
  fi
done < "$TMP_INV"

while IFS= read -r name || [[ -n "$name" ]]; do
  [[ -z "$name" ]] && continue
  if ! grep -Fxq -- "$name" "$TMP_INV"; then
    echo "Mix @builtins value not in inventory: $name" >&2
    missing=1
  fi
done < "$TMP_MIX"

if [[ "$missing" -ne 0 ]]; then
  echo "builtins sync check failed" >&2
  echo "--- inventory ---"; cat "$TMP_INV"
  echo "--- lean ---"; cat "$TMP_LEAN"
  echo "--- mix ---"; cat "$TMP_MIX"
  exit 1
fi

count=$(wc -l < "$TMP_INV" | tr -d ' ')
echo "builtins sync ok ($count inventory MFAs; Mix ⊆ inventory ⊆ Lean strings)"
