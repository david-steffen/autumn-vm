---
name: avoid-committed-wire-goldens
description: >-
  Avoid committing derived IR/bytecode/JSON wire snapshots next to sources when
  the producer and consumer ship together. Prefer fresh compile plus behavioral
  checks (stdout, opcodes). Use when adding fixtures, goldens, smoke tests,
  .bc.json, snapshot IR, or lockstep compiler/VM tests. Do not use for checked-in
  runtime load targets that are true inputs (unless they can be generated in
  test setup), or for unrelated snapshot tests of UI/text.
---

# Avoid committed wire goldens

## Rules

1. **Derived wire is not source.** If Mix (or another lowerer) can rebuild the artifact from `.ex` / AST, do not commit the `.bc.json` (or equivalent) beside fixtures.
2. **Assert behavior, not byte-identity of the whole image.** Smoke: compile → run VM → compare stdout (or a small observable). Unit tests: compile-ok + targeted opcode/shape checks.
3. **Generate runtime load inputs in setup.** Programs that `load_file` a path should have that path written by the test/smoke prep step from a source fixture, then gitignored.
4. **Gitignore derived wire under fixtures** so it cannot sneak back in.

## Decision table

| Situation | Commit wire artifact? |
| --- | --- |
| Lockstep compiler + VM; fixture is source `.ex` | **No** — compile fresh in smoke/CI |
| Artifact only exists to freeze lowerer output | **No** — prefer opcode asserts / smoke |
| File is a true external input with no regenerable source | Yes (rare) |
| UI / changelog / proof-name tripwires | Out of scope (other skills) |

## Good

```text
tests/fixtures/add_main.ex
tests/fixtures/add_main.expect          # "3"
tests/fixtures/genserver_use.smoke.json # optional stdlib extras
# smoke: compile to tempfile → autumn → stdout == expect
```

## Bad

```text
tests/fixtures/*.bc.json committed
mix test: assert module == Jason.decode!(golden)
smoke: fail if compile ≠ golden file
```

Every lowerer rename or formatting tweak churns dozens of JSON files without catching VM bugs.

## Anti-patterns to refuse

- Full-image structural equality goldens as the primary compiler test
- Dual encode shapes “so goldens stay stable”
- Requiring contributors to regenerate bytecode on every IR comment change
