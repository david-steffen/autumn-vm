---
name: avoid-doc-dual-sot
description: >-
  Avoid restating the wire/feature encyclopedia in AGENTS, ROADMAP, and code
  comments. One source of truth for IR (e.g. IR.md); AGENTS stays layout/build/
  policy; chronology lives in git. Use when editing AGENTS, ROADMAP, IR docs,
  or Phase/IRvN tags in comments. Do not use for stdlib module headers that are
  the local API contract for that file.
---

# Avoid doc dual sources of truth

## Rules

1. **Wire/feature semantics live in one place** (for Autumn: `vm/IR.md`). Do not paste GenServer/ETS/binary encyclopedias into AGENTS.
2. **AGENTS = map + policy.** Layout, how to build/test, proof-surface rules, pointers — not a second IR manual.
3. **Chronology is not documentation.** “Phase 26”, “IR v18”, “IR bump” in comments and live ROADMAP checklists age into lies. Prefer construct names; history → git.
4. **Stdlib file headers may state that module’s contract** — that is local SoT, not a dual of IR.md’s opcode table.

## Decision table

| Content | Where |
| --- | --- |
| Opcodes, literals, builtins, scheduling | `IR.md` |
| Repo layout, build, agent policy | `AGENTS.md` |
| What’s next | Short `ROADMAP.md` |
| What shipped when | Git history (not live checklists) |
| Module API (GenServer callbacks, …) | That stdlib file’s header |

## Good

```markdown
AGENTS: See `vm/IR.md` for IR; `stdlib/ets.ex` for ETS API.
Comment: # Owner exit transfers the ETS table to the heir.
```

## Bad

```markdown
AGENTS: 40-line ETS/GenServer/binary dump duplicated from IR.md
ROADMAP: 30 checked-off phases titled “IR vN”
Comment: # Phase 6 / IR v18 ets_heir
```

## Anti-patterns to refuse

- “Document in AGENTS and IR.md” as a default checklist for every feature
- Phase numbers in test names and fixture headers
- Keeping a completed-phase archive as the primary ROADMAP body
