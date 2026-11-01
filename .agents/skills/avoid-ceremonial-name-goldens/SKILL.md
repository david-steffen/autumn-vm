---
name: avoid-ceremonial-name-goldens
description: >-
  Avoid text-presence name goldens that claim to freeze a public API but only
  check that strings still appear. Keep at most a thin rename tripwire with
  honest docs. Use when adding proof_surface.names, export name dumps, or
  “public API” greps. Do not use for real behavioral tests or typechecked APIs.
---

# Avoid ceremonial name goldens

## Rules

1. **A grep for `theorem Foo` is a rename tripwire, not an API contract.** Docs and CI messages must say so.
2. **Do not expand the claim** to exhaustiveness, semantic stability, or “every lemma must be listed” unless you have a stronger checker.
3. **Prefer typed/public surfaces** when you truly need an API freeze (module exports, documented lemma sets with proofs that use them).
4. **Don’t duplicate the name list** in AGENTS / “Audit” comments — point at the golden file once.

## Decision table

| Goal | Mechanism |
| --- | --- |
| Catch accidental renames of curated lemmas | Thin name list + grep (honest labeling) |
| Prove lemmas still hold | `lake build` |
| Ensure every opcode has preserve/progress | Structural review / dispatcher exhaustiveness — not a name file |
| Freeze a wire format | Schema + decode tests — not theorem names |

## Good

```text
# check_proof_surface.sh header:
# Rename tripwire only — does not certify exhaustiveness or meaning.
```

## Bad

```text
AGENTS: “Public proof surface is frozen; CI enforces the API”
+ name file that only greps for substrings
+ duplicated Audit bullet list of the same names
```

## Anti-patterns to refuse

- Bidirectional “every theorem in these files must be listed” without a real public-export story (pure tax)
- Treating name presence as substitute for preserve/progress lemmas
- Meta dumps of all theorem names as a heavier version of the same theater
