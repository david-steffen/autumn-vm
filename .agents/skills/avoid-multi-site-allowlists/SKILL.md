---
name: avoid-multi-site-allowlists
description: >-
  Avoid hand-copied MFA, opcode, or capability string lists that must be updated
  in multiple languages or modules on every feature. Prefer one inventory plus a
  sync check (or generation). Use when adding builtins, isBuiltinName ladders,
  @builtins maps, call-special towers, or compatibility matrices. Do not use for
  product feature flags or one-off local constants.
---

# Avoid multi-site allowlists

## Rules

1. **One inventory for cross-language names.** Builtin MFAs (and similar) live in a single checked-in list; Mix and Lean both must match it.
2. **CI fails on drift.** A script compares inventory ↔ emitter ↔ runtime recognizer. Do not rely on humans to keep three copies equal.
3. **Dispatch/proof code may still case-split** — that is real work. The **copied string matrix** is the theater to remove.
4. **New construct = one PR touching inventory + both sides + proofs**, not a drive-by update of AGENTS laundry lists.

## Decision table

| Situation | Approach |
| --- | --- |
| Same MFA strings in Mix + Lean | Inventory file + `check_*.sh` in CI |
| Per-opcode preserve/progress lemmas | Keep — real obligations, not allowlists |
| Docs restating the MFA table | Point at inventory / IR.md; don’t duplicate |
| Product feature flags | Out of scope |

## Good

```text
vm/builtins.mfa          # canonical names
Mix @builtins values ⊆ inventory
Lean isBuiltinName covers inventory (+ documented prefix rules)
CI: check_builtins.sh
```

## Bad

```text
@builtins %{…}
isBuiltinName: name == "ets_…" || …
AGENTS / PreserveInstr “Audit” bullet lists of the same MFAs
```

## Anti-patterns to refuse

- Growing parallel string ladders with no sync check
- “Documentation audits” that restate the inventory
- Adding a builtin in Lean only (or Mix only) without the inventory line
