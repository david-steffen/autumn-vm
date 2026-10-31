# Autumn IR

Versioned bytecode exchanged as JSON between the Mix lowerer and the Lean VM.

Supported `version` values: `1` (literals/calls), `2` (lists, case ops, processes), `3` (`get_list_elem`, `list_size/1`), `4` (`get_list_rest` / cons patterns), `5` (maps), `6` (exceptions: `enter_try` / `leave_try` / `raise`), `7` (selective receive: `recv_peek` / `recv_drop` / `wait`), `8` (process links: `link`; exit signals), `9` (unique refs + process monitors: `monitor` / `demonitor`; DOWN signals), `10` (floats + strings as immediates), `11` (closures: `make_fun` / `apply`), `12` (first-class `modules[]`), `13` (`load_file` / dynamic install), and `14` (`Process.flag/2` / `Process.exit/2`; durable drain + OTP-shaped `trap_exit`).

## Module

Legacy (v1–11) flat image — still decoded by wrapping into one code module:

```json
{
  "version": 2,
  "entry": "Main.main/0",
  "functions": [ /* Function */ ]
}
```

IR v12 image — table of named code modules (Mix emits this when assembling two or more `defmodule`s):

```json
{
  "version": 12,
  "entry": "Main.main/0",
  "modules": [
    {
      "name": "Math",
      "functions": [ /* Function */ ]
    },
    {
      "name": "Main",
      "functions": [ /* Function */ ]
    }
  ]
}
```

- Function `name` fields remain full MFAs (`Math.add/2`). `call` / `spawn` / `apply` / `make_fun` look up by MFA across the image; no opcode changes.
- `entry` is one MFA that must exist in some module (typically `Main.main/0`).
- Decode: if `"modules"` is absent, wrap flat `"functions"` into a single `CodeModule` whose name is the prefix of `entry` before `.`.
- Encode (Lean) always writes `modules[]`. Mix keeps emitting flat `"functions"` for single-module images so existing goldens stay stable.
- Dynamic install: see **v13** `load_file` below.

## Function

```json
{
  "name": "Main.add/2",
  "arity": 2,
  "locals": 3,
  "code": [ /* Instr */ ]
}
```

Registers: dense `r0 .. r(locals-1)`. Params occupy `r0 .. r(arity-1)`.

## Literals

| JSON | Term |
| --- | --- |
| `null` | `nil` |
| `{"bool": true}` | boolean |
| `{"int": 42}` | integer |
| `{"atom": "ok"}` | atom |
| `{"tuple": [lit, ...]}` | tuple |
| `{"list": [lit, ...]}` | list (v2) |
| `{"map": [{"key": lit, "value": lit}, ...]}` | map (v5); keys sorted at alloc |
| `{"pid": 0}` | process id (v2, usually runtime-only) |
| `{"ref": 0}` | unique reference id (v9, usually runtime-only; distinct from heap pointers) |
| `{"float": 1.5}` | floating-point number (v10) |
| `{"string": "hi"}` | UTF-8 string / teaching binary (v10) |

## Instructions

### v1

- `{"op":"load_lit","reg":0,"lit":...}`
- `{"op":"move","dest":1,"src":0}`
- `{"op":"call","dest":2,"fun":"Main.add/2","args":[0,1]}`
- `{"op":"return","reg":2}`
- `{"op":"halt","reg":0}`

### v2 sequential

- `{"op":"jump","target":12}` — absolute instruction index
- `{"op":"jump_if_eq","target":12,"reg":0,"lit":...}` — jump if reg equals lit
- `{"op":"get_tuple_elem","dest":1,"tuple":0,"index":0}`
- `{"op":"is_tag","dest":1,"reg":0,"tag":"tuple"}` — tag ∈ nil\|bool\|int\|atom\|tuple\|list\|map\|pid\|ref\|float\|string\|fun

### v2 processes

- `{"op":"spawn","dest":0,"fun":"Main.worker/1","args":[1]}` — dest ← pid
- `{"op":"send","pid":0,"msg":1}`
- `{"op":"recv","dest":0}` — pop mailbox head or park until any message (non-selective)

### v7 selective receive

- `{"op":"recv_peek","dest":0,"index":1,"empty":12}` — if `index` (int reg) `< mailbox.size`, `dest ← mailbox[index]` and fall through; else jump to `empty` (no park)
- `{"op":"recv_drop","index":1}` — remove `mailbox[index]` (int reg)
- `{"op":"wait","retry":10,"after":20,"timeout":5}` — if the mailbox is non-empty, jump to `retry`. If a parked deadline is due, jump to `after`. Otherwise park until `send` wakes the process (re-executes `wait`) or the scheduler wakes it for timeout. `timeout` is clock ticks from now; `null`/omit means infinity; `0` jumps to `after` immediately.

`receive` / `after` is lowered to a mailbox scan loop (`recv_peek` + pattern tests + `recv_drop`) plus `wait`. The machine `clock` advances on each step and jumps to the next deadline when every process is waiting with a finite timeout.

### v3 list patterns

- `{"op":"get_list_elem","dest":1,"list":0,"index":0}` — 0-based list element (mirror of `get_tuple_elem`)

### v4 cons / list rest

- `{"op":"get_list_rest","dest":1,"list":0,"index":0}` — allocate a new list of elements after `index` (for `[h|t]`, head at 0 and rest uses `index` 0). May GC while allocating.

### v6 exceptions

- `{"op":"enter_try","rescue":12,"exc":3}` — push a handler; on `raise`, unwind to this frame, store the value in `exc`, set `ip` to `rescue`
- `{"op":"leave_try"}` — pop the innermost handler (normal try completion)
- `{"op":"raise","reg":0}` — unwind to innermost handler, or exit the process with that value as `result` if none

`after` is lowered as a shared join label (jumps from success and rescue paths), not a VM opcode. `try`/`after` without `rescue` still uses `enter_try` so `after` runs on an uncaught raise, then re-raises. Builtin `typeError` remains a stepper error (not a language exception).

Unmatched `case` / multi-clause fallthrough lowers to `raise` of atom `match_error` (not `nil`).

Match assignment `pat = expr` is lowerer-only (same pattern emitters as `case`): miss → `raise :match_error`; success value is the RHS. Bare `x = e` still just rebinds. Pin `^x` in patterns (including under `=` / `case` / `receive`) compares via `==/2` against the currently bound register (no new opcode).

**Language sugar (lowerer-only, no new opcodes):** multi-clause / patterned `fn` → synthetic `case` + `make_fun` (v11). `hd/1` → `get_list_elem` index 0; `tl/1` → `get_list_rest` index 0; `++/2` → per-module lifted `__list_append__/2` (case + `cons/2`).

`if` / `unless` / `cond` are lowerer-only (no new opcodes): truthiness is Elixir-like (`false` and `nil` falsy; everything else truthy) via `jump_if_eq` on those literals. Missing `else` yields `nil`. Exhausted `cond` raises atom `cond_clause_error`.

`rescue e in [lit, …]` (and `rescue lit ->`) stays **value-based**: the raised value is matched with `jump_if_eq` / patterns (no BEAM exception structs). `rescue e in [:a, :b]` is an or of literal tests that binds `e` on match.

### Catchable language exceptions vs stepper `typeError`

| Kind | Mechanism | Catchable? |
| --- | --- | --- |
| Language `raise` | `raise` opcode; value in a register | Yes — `enter_try` / rescue patterns |
| Match miss | Lowered to `raise` of atom `match_error` | Yes — same as `raise` |
| Builtin type mismatch | `raise` of atom `badarg` (v14) | Yes — same as `raise` |
| Linked peer exit (trapping) | `{:EXIT, from_pid, reason}` mailbox message (v8/v14) | Yes — via `receive` / patterns |
| Linked peer exit (non-trapping) | peer is killed with that reason (v14) | N/A — process exits |
| Monitored peer exit | `{:DOWN, ref, :process, pid, reason}` mailbox message (v9) | Yes — via `receive` / patterns |
| Stepper `typeError` | `StepError` (bad IP/register, empty stack, return through try, …) | **No** — aborts the step; not a process value |

Teaching rule: anything that should be handled in Elixir-shaped code goes through `raise` (including `:badarg`), EXIT, or DOWN messages. `typeError` means the IR/VM was asked to do something ill-typed at the stepper level.

### v8 process links

- `{"op":"link","pid":0}` — bidirectional link between the current process and the pid in the register. Linking an exited pid is a `typeError`. Self-link is a no-op.
- `spawn_link` lowers as `spawn` then `link` on the new pid.

When a process **exits** (uncaught `raise`, root `return`, or `halt`), linked peers are signaled (IR v14): if the peer has `trap_exit`, it receives mailbox `{:EXIT, from_pid, reason}` and is woken; otherwise it is **killed** with that reason (cascading). Links are cleared both ways. Default is non-trapping (OTP-shaped); use `Process.flag(:trap_exit, true)` for mailbox EXIT.

### v9 unique refs + monitors

- Unique refs are immediates (JSON `{"ref": N}` / tag `ref`), distinct from heap pointers. Machine counter `nextRef` allocates ids.
- `{"op":"monitor","dest":0,"pid":1}` — dest ← new ref; current process monitors the pid. Unidirectional. Monitoring an exited pid still returns a ref and **immediately** delivers `{:DOWN, ref, :process, pid, reason}` (reason = that process’s exit value, or `nil` if unknown). Self-monitor is allowed and delivers DOWN only when this process exits (to its own mailbox if somehow still alive — teaching: prefer not to self-monitor).
- `{"op":"demonitor","ref":0}` — drop the monitor for that ref if present (no-op if unknown / already fired). Does not flush a pending DOWN from the mailbox.
- Builtin `make_ref/0` — allocate a fresh ref without monitoring.

When a process **exits**, each monitorer in its inbound monitor list receives `{:DOWN, ref, :process, from_pid, reason}` (copied into their heap) and is woken if waiting; monitor entries are cleared both ways. Outbound monitors from the exiting process are dropped from targets (no DOWN for those). Monitors never auto-exit peers.

### v10 floats + strings

- Floats and strings are **immediates** (not heap nodes). Teaching subset: no binaries/bitstrings beyond UTF-8 strings; no float↔int coercion.
- `+/2` `-/2` `*/2` accept either two ints or two floats (mixed → catchable `:badarg`, IR v14).
- `</2` `>/2` `<=/2` `>=/2` likewise on two ints or two floats.
- `<>/2` concatenates two strings → string (mismatch → `:badarg`).

### v11 closures

- Closures are **heap nodes**: `{funName, env[]}` (tag `fun`). Env values are child refs/immediates (GC/copy like tuples).
- Each source `fn` is lifted to a synthetic MFA (e.g. `Main.__fn_0/2`). Params layout: **captures first**, then formal args (`arity = |captures| + |params|`).
- `{"op":"make_fun","dest":0,"fun":"Main.__fn_0/2","captures":[1,2]}` — dest ← closure; may GC while allocating.
- `{"op":"apply","dest":0,"fun":1,"args":[2,3]}` — call the closure in `fun` with `args` (push frame like `call`; regs = env ++ args).
- Elixir: `fn x -> … end` / `f.(x)`; free locals from the enclosing scope are captured. Teaching subset: single-clause `fn`, no `&Mod.fun/N`, no `spawn(fn …)`.

### v13 dynamic load

- `{"op":"load_file","dest":D,"path":P}` — `P` holds a **string** path to an Autumn IR JSON (`.bc.json`). On success `D` ← atom `:ok`. Host `entry` is unchanged; each incoming `CodeModule` **replaces** the same `name` or is appended; `version := max(host, incoming, 13)`.
- Teaching VM loads **bytecode images**, not Elixir source (no compiler in Lean). Mix lowers `Code.load_file(path)`.
- Soft-purge lite: frames already hold `Function` by value, so in-flight stacks keep old code; new `call` / `spawn` / `apply` see the updated MFA table.
- Catchable failures (same path as `raise`, so `try`/`rescue` works): non-string path → `:badarg`; missing/unreadable file → `:enoent`; bad JSON/decode **or** install that fails `Module.checkWF` / live-process stack WF under the new image → `:bad_bytecode`.
- The pure stepper stubs `load_file` as `:enoent`; `Step.runIO` / `autumn` exe services real `IO.FS.readFile`. See fixture `hot_load.ex`.

### v14 durable drain + `trap_exit` / `Process.exit`

- **Durable drain**: when the entry process exits, its value is *not* immediately the machine result. The scheduler keeps running until nothing can progress (no runnable process and no finite `wait` deadline), then materializes the entry process’s exit value as `State.result` for the CLI.
- `Process.flag/2` — currently only `Process.flag(:trap_exit, bool)`; returns the previous flag. Unknown flags → catchable `:badarg`. Mix lowers `Process.flag/2` (image version ≥ 14).
- `Process.exit/2` — `Process.exit(self(), reason)` is `raiseValue`; `Process.exit(other, reason)` force-exits the target (ignores `trap_exit`, like OTP `exit(Pid, kill)`), returns `true`, then yields. Mix lowers `Process.exit/2`.
- Default `trapExit := false` on new processes.

## Builtins

| MFA | Meaning |
| --- | --- |
| `+/2` `-/2` `*/2` | integer or float arithmetic (homogeneous; mismatch → `:badarg`) |
| `==/2` | structural equality → bool |
| `</2` `>/2` `<=/2` `>=/2` | int or float compare → bool (homogeneous; mismatch → `:badarg`) |
| `<>/2` | string concatenation (v10; mismatch → `:badarg`) |
| `tuple_size/1` | tuple length → int (bad tag → `:badarg`) |
| `list_size/1` | list length → int (v3; bad tag → `:badarg`) |
| `elem/2` | `(tuple, index)` → element (0-based; bad args / OOB → `:badarg`) |
| `map_size/1` | map entry count → int (v5; bad tag → `:badarg`) |
| `map_get/2` | `(map, key)` → value or nil (v5; bad tag → `:badarg`) |
| `map_put/3` | `(map, key, value)` → new map (v5; may GC; bad tag → `:badarg`) |
| `self/0` | current process pid (v2+) |
| `make_ref/0` | fresh unique ref (v9) |
| `cons/2` | `(head, list)` → new list `[head \| list]` (may GC; bad tail → `:badarg`) |
| `make_tuple/N` | `N` args → new tuple (may GC; lowered for non-literal `{…}`) |
| `Process.flag/2` | `(:trap_exit, bool)` → previous flag (v14; else `:badarg`) |
| `Process.exit/2` | force-exit other / raise self (v14) |

Guard helpers `is_integer/1`, `is_float/1`, `is_atom/1`, `is_list/1`, `is_tuple/1`, `is_map/1`, `is_boolean/1`, `is_pid/1`, `is_nil/1`, `is_reference/1`, `is_binary/1` (string tag), `is_function/1` (fun tag) lower to `is_tag` (not separate MFAs). Map patterns `%{lit_key => pat}` lower via `map_get/2` + value tests. Handler-stack bounds (`handlersWF`) are part of runnable/waiting `Process.WF`.

## Scheduling

Reduction-preemptive (Erlang-style): each process runs a fixed **reduction budget** (quantum) of instructions, then the scheduler forces a yield and round-robins to the next runnable process. Busy loops cannot starve siblings — see fixture `preempt_fair.ex`. Still single-threaded and cooperative at the instruction boundary (no mid-instruction OS preempt). `recv` / `wait` parks the process (`waiting`); `send` wakes a waiting target (IP unchanged so `wait`/`recv` re-runs). Finite `wait` deadlines use a machine `clock`; if nothing is runnable, the scheduler advances to the next deadline and makes those processes runnable so `wait` can take the `after` path. **Machine result** (IR v14): snapshot the entry process’s exit value only once the machine is idle (no runnable process and no finite wait deadline) — entry exit alone does not stop siblings (`drain_siblings.ex`).

## Runtime heap (Lean VM)

Compound terms (`tuple` / `list` / `map` / `closure`) are **heap-allocated** at runtime; immediates (`nil` / `bool` / `int` / `float` / `atom` / `string` / `pid` / unique `ref`) stay unboxed in registers.

- Each process owns a **generational heap**: a single `nodes` array laid out `old ++ young`. Refs `< oldSize` are old; the rest are the young **nursery**. Allocation bump-fills young only, up to `youngCapacity` (and total `capacity`).
- **Minor GC** (nursery full): evacuate only young objects reachable from the process roots (stack registers, mailbox, result) and **promote every survivor into old** (no aging; one minor survived ⇒ old). Old refs are leaves and the old prefix is kept verbatim, so old refs stay valid. Young is empty afterwards (`minorCount += 1`).
- **Major GC** (after a minor, if old can no longer hold a full nursery — `nodes.size + youngCapacity > capacity` — or young is still full): full-heap **Cheney** copy over old+young; the result is entirely old (`gcCount += 1`) and `capacity` is grown for headroom.
- **No remembered set**: heap nodes are immutable and children are always allocated before parents, so an old object can never point at a young one; roots plus tracing through young are sufficient.
- Allocation failure path (`allocNode` / `allocCompound`): `alloc?` → `gc` (minor, then major if needed) → `alloc?` → `growAlloc` (grow capacity/nursery, force-alloc).
- Registers, mailboxes, and process results hold `Value`s (immediate or `Ref`).
- **Nested compound allocation is GC-safe**: while building a `tuple`/`list` literal, already-built children are parked on the process mailbox (a GC root), and the parent node is rebuilt from the live (post-GC) mailbox suffix. A GC triggered mid-term therefore never leaves stale refs. `installHeap` never inflates `capacity`/`youngCapacity`, so a full nursery still triggers GC. `GCDemo` forces minor and major collections on tiny heaps (including retained roots filling old) and checks `toTerm` round-trips.
- Both collections share one root-rewriting pass (`collectWith`) and satisfy `GcRel` (`minorGc_rel`, `majorGc_rel`, `gc_rel`): they preserve immediates in registers/mailbox/result exactly (`{minor_gc,majorGc,gc}_frame_reg_immediate`, `*_mailbox_immediate`, `*_result_immediate`), process well-formedness (`minor_gc_preserves_process_WF`, `majorGc_preserves_process_WF`, `gc_preserves_process_WF`), and keep all root refs well-formed (`*_rootsWF` / `*_preserves_obs`).
- Compound observational equality uses total `Heap.toTermFuel` / `toTerm'` (sentinel on fuel/OOB). Lemmas: immediate roots via `GcRel.toTermFuel_*_immediate` / `*_mailbox_toTermFuel_immediate` / `*_result_toTermFuel_immediate`; flat compounds via `toTermFuel_flatCompound_congr`. Nested compounds are checked by `#guard` in `GCDemo` (including maps).
- **`send` / `spawn` copy** values into the target process heap (no cross-heap refs).
- IR JSON is unchanged: the Mix lowerer still emits term trees; the VM allocates them on `load_lit` / spawn args. Compound heap shapes are `tuple` / `list` / `map`.
