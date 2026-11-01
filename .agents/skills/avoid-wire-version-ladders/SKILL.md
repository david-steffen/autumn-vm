---
name: avoid-wire-version-ladders
description: >-
  Avoid linear wire/IR/schema version integers that bump per new opcode, field,
  or construct when producer and consumer ship together. Prefer named constructs
  in the payload and reject unknowns; bump a format id only on breaking shape
  changes. Use when designing or changing IR, bytecode, JSON schemas, fixture
  formats, compatibility matrices, needs_vN ladders, or lockstep compiler/VM
  (or client/server) pairs. Do not use for product feature flags, experiments,
  kill switches, project release tags, or library public API semver.
---

# Avoid wire version ladders

## Rules

1. **Named constructs, not version ladders.** Put the construct in the payload (`"op":"apply_mfa"`, a tagged field). Compatibility = “can this decoder handle these tags?”, not “does an integer match a matrix in two codebases?”
2. **Lockstep producers/consumers do not need per-construct wire versions.** If compiler and VM (or client and server) always ship together, extend decode/runtime in the same change. Do not add `needs_vN?` cascades or bump a format integer for every new opcode/builtin/field.
3. **Bump a format id only on breaking shape changes** (or dual-read during a migration). Additive constructs do not need a bump when both sides update together. Prefer a fixed `format: 1` (or omit the field) until a real break.
4. **Chronology is not a wire field.** “When did X land?” belongs in git, changelog, or roadmap — not in every artifact and comment as “v18”.

## Decision table

| Situation | Wire version? |
| --- | --- |
| Producer + consumer always ship together (mono-repo, lockstep release) | **No** per-construct versions. Self-describe; reject unknowns. |
| Independently released sides must coexist across releases | Rare **format/schema** id; prefer additive + dual-read; bump only on breaks. |
| “When did construct X land?” | Git / changelog / roadmap — not an artifact field. |
| Old-runtime gating you truly support | Capability negotiation (or a real min-engine), not a ceremonial ladder that nothing enforces. |
| Product feature flags / experiments / kill switches | **Out of scope** — unrelated to wire format versioning. |
| Project release tags / library API semver | **Out of scope** — fine and separate from in-band wire ladders. |

## Good

```json
{ "format": 1, "op": "apply_mfa", "mod": 0, "fun": 1, "args": 2 }
```

Unknown `op` → decode error. New ops land by extending the decoder; `format` stays `1` until the JSON shape itself breaks.

Document constructs by name (`apply_mfa`, `ets_heir`), not by the release number that introduced them.

## Bad

```text
needs_v21? → version 21
needs_v20? → version 20
…
Decode: accept version ∈ 1..21
Comments / ROADMAP / goldens: “IR v18”, “IR v21”
```

The integer claims a feature subset the runtime never checks. Every new construct pays tax in emitter, decoder allowlist, docs, and fixtures.

## Anti-patterns to refuse

- Growing `needs_vN?` / “min version for opcode X” ladders in lockstep codebases
- Comments and docs keyed as “IRvN” instead of construct names
- Goldens that churn solely because the version integer moved
- Well-formedness / decode allowlists that mirror the ladder without enforcing feature subsets
- `max(host, incoming, N)` version arithmetic on module merge when there is no real compatibility protocol

## Motivating anti-pattern

A teaching IR once carried versions 1–21 computed from opcode presence, while the VM only checked “is `v` in range?” Unknown opcodes already failed at decode. The ladder was compatibility theater — drop it; keep named ops and a rare format id.
