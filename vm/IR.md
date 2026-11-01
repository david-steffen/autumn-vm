# Autumn IR

Bytecode exchanged as JSON between the Mix lowerer and the Lean VM.

`format` is a rare wire-shape id. Current value: **`1`**. Bump only on breaking JSON shape changes (not when adding opcodes or builtins). Unknown opcodes fail at decode; unknown builtins fail at runtime. Mix always emits `"format": 1`.

## Module

Image shape (Mix and Lean encode both use `modules[]`; one or more named code modules):

```json
{
  "format": 1,
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
- `"modules"` must be non-empty. Decode rejects images without it.
- Dynamic install: see `load_file` below.
- Builtin MFA inventory (Mix ↔ Lean sync): [`vm/builtins.mfa`](builtins.mfa).

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
| `{"list": [lit, ...]}` | list |
| `{"map": [{"key": lit, "value": lit}, ...]}` | map; keys sorted at alloc |
| `{"pid": 0}` | process id (usually runtime-only) |
| `{"ref": 0}` | unique reference id (usually runtime-only; distinct from heap pointers) |
| `{"float": 1.5}` | floating-point number |
| `{"string": "hi"}` | UTF-8 string immediate |
| `{"binary": [1, 2]}` | aligned bitstring / binary |
| `{"bitstring": {"bytes": [1], "trailing_bits": 3}}` | partial bitstring |

## Instructions

### Core

- `{"op":"load_lit","reg":0,"lit":...}`
- `{"op":"move","dest":1,"src":0}`
- `{"op":"call","dest":2,"fun":"Main.add/2","args":[0,1]}`
- `{"op":"return","reg":2}`
- `{"op":"halt","reg":0}`

### Control + patterns

- `{"op":"jump","target":12}` — absolute instruction index
- `{"op":"jump_if_eq","target":12,"reg":0,"lit":...}` — jump if reg equals lit
- `{"op":"get_tuple_elem","dest":1,"tuple":0,"index":0}`
- `{"op":"is_tag","dest":1,"reg":0,"tag":"tuple"}` — tag ∈ nil\|bool\|int\|atom\|tuple\|list\|map\|pid\|ref\|float\|string\|binary\|bitstring\|fun
- `{"op":"get_list_elem","dest":1,"list":0,"index":0}` — 0-based list element
- `{"op":"get_list_rest","dest":1,"list":0,"index":0}` — allocate a new list of elements after `index` (for `[h|t]`, head at 0 and rest uses `index` 0). May GC while allocating.

### Processes

- `{"op":"spawn","dest":0,"fun":"Main.worker/1","args":[1]}` — dest ← pid
- `{"op":"send","pid":0,"msg":1}`
- `{"op":"recv","dest":0}` — pop mailbox head or park until any message (non-selective)
- `{"op":"link","pid":0}` — bidirectional link. Linking an exited pid is a `typeError`. Self-link is a no-op. `spawn_link` lowers as `spawn` then `link`.
- `{"op":"monitor","dest":0,"pid":1}` — dest ← new ref; unidirectional. Monitoring an exited pid still returns a ref and **immediately** delivers `{:DOWN, ref, :process, pid, reason}`.
- `{"op":"demonitor","ref":0}` — drop the monitor if present and **flush** any pending `{:DOWN, ref, …}` (Autumn always flushes).

When a process **exits** (uncaught `raise`, root `return`, or `halt`), linked peers are signaled: if the peer has `trap_exit`, it receives mailbox `{:EXIT, from_pid, reason}` and is woken; otherwise it is **killed** with that reason (cascading). Links are cleared both ways. Default is non-trapping; use `Process.flag(:trap_exit, true)` for mailbox EXIT.

Unique refs are immediates (JSON `{"ref": N}` / tag `ref`). Machine counter `nextRef` allocates ids. Builtin `make_ref/0` allocates a fresh ref without monitoring. On exit, each inbound monitorer receives `{:DOWN, ref, :process, from_pid, reason}` and is woken if waiting.

### Selective receive

- `{"op":"recv_peek","dest":0,"index":1,"empty":12}` — if `index` (int reg) `< mailbox.size`, `dest ← mailbox[index]` and fall through; else jump to `empty` (no park)
- `{"op":"recv_drop","index":1}` — remove `mailbox[index]` (int reg)
- `{"op":"wait","retry":10,"after":20,"timeout":5}` — if the mailbox is non-empty, jump to `retry`. If a parked deadline is due, jump to `after`. Otherwise park until `send` wakes the process (re-executes `wait`) or the scheduler wakes it for timeout. `timeout` is clock ticks from now; `null`/omit means infinity; `0` jumps to `after` immediately; `{"reg": R}` means register `R` holds a non-neg int (else type error).

`receive` / `after` is lowered to a mailbox scan loop (`recv_peek` + pattern tests + `recv_drop`) plus `wait`. Empty `do` (after-only) is allowed. The machine `clock` advances on each step and jumps to the next deadline when every process is waiting with a finite timeout. Mix emits the reg form for `receive … after t -> …` when `t` is not an integer literal.

`Process.hibernate/0` — teaching stand-in: run `Process.gc` on the current process and return `:ok` (GenServer `:hibernate` tails call it before `loop`).

### Exceptions

- `{"op":"enter_try","rescue":12,"exc":3}` — push a handler; on `raise`, unwind to this frame, store the value in `exc`, set `ip` to `rescue`
- `{"op":"leave_try"}` — pop the innermost handler (normal try completion)
- `{"op":"raise","reg":0}` — unwind to innermost handler, or exit the process with that value as `result` if none

`after` is lowered as a shared join label (jumps from success and rescue paths), not a VM opcode. `try`/`after` without `rescue` still uses `enter_try` so `after` runs on an uncaught raise, then re-raises. Builtin `typeError` remains a stepper error (not a language exception).

Unmatched `case` / multi-clause fallthrough lowers to `raise` of atom `match_error` (not `nil`).

Match assignment `pat = expr` is lowerer-only (same pattern emitters as `case`): miss → `raise :match_error`; success value is the RHS. Bare `x = e` still just rebinds. Pin `^x` in patterns (including under `=` / `case` / `receive`) compares via `==/2` against the currently bound register (no new opcode).

**Language sugar (lowerer-only, no new opcodes):** multi-clause / patterned `fn` → synthetic `case` + `make_fun`. `hd/1` → `get_list_elem` index 0; `tl/1` → `get_list_rest` index 0; `++/2` → per-module lifted `__list_append__/2` (case + `cons/2`).

`if` / `unless` / `cond` are lowerer-only: truthiness is Elixir-like (`false` and `nil` falsy; everything else truthy) via `jump_if_eq` on those literals. Missing `else` yields `nil`. Exhausted `cond` raises atom `cond_clause_error`.

`rescue e in [lit, …]` (and `rescue lit ->`) stays **value-based**: the raised value is matched with `jump_if_eq` / patterns (no BEAM exception structs).

### Catchable language exceptions vs stepper `typeError`

| Kind | Mechanism | Catchable? |
| --- | --- | --- |
| Language `raise` | `raise` opcode; value in a register | Yes — `enter_try` / rescue patterns |
| Match miss | Lowered to `raise` of atom `match_error` | Yes — same as `raise` |
| Builtin type mismatch | `raise` of atom `badarg` | Yes — same as `raise` |
| Linked peer exit (trapping) | `{:EXIT, from_pid, reason}` mailbox message | Yes — via `receive` / patterns |
| Linked peer exit (non-trapping) | peer is killed with that reason | N/A — process exits |
| Monitored peer exit | `{:DOWN, ref, :process, pid, reason}` mailbox message | Yes — via `receive` / patterns |
| Stepper `typeError` | `StepError` (bad IP/register, empty stack, return through try, …) | **No** — aborts the step; not a process value |

Teaching rule: anything that should be handled in Elixir-shaped code goes through `raise` (including `:badarg`), EXIT, or DOWN messages. `typeError` means the IR/VM was asked to do something ill-typed at the stepper level.

### Floats + strings

- Floats and strings are **immediates** (not heap nodes). No float↔int coercion.
- Runtime float is finite IEEE binary64 (`Autumn.Term.FiniteFloat`: `neg` / biased `exp < 2047` / 52-bit `frac`). Inf/NaN are unrepresentable.
- JSON lit: **Mix (producer)** emits `{"float": <number>}` (decoded via scientific rounding). **Lean encode** may emit exact fields `{"float": {"neg": bool, "exp": nat, "frac": nat}}` for bit-identical roundtrip proofs — proof/roundtrip-only, not a second Mix wire form.
- `+/2` `-/2` `*/2` accept either two ints or two floats (mixed → catchable `:badarg`). Float overflow / non-finite IEEE result → catchable `:badarg`.
- `</2` `>/2` `<=/2` `>=/2` likewise on two ints or two floats (IEEE order; `==/2` treats `+0` and `-0` as equal).
- `<>/2` concatenates two strings → string (mismatch → `:badarg`). UTF-8 `string` remains a separate immediate from raw binaries.

### Binaries / bitstrings

- `Term.bitstring` / `Value.bitstring` are **immediates** (`Autumn.Term.Bitstring`: `bytes` + `trailingBits`). `trailingBits = 0` is an aligned **binary**; `1…7` is a partial bitstring with unused low bits cleared (`Valid`).
- JSON: aligned `{"binary": [0–255, …]}`; partial `{"bitstring": {"bytes": […], "trailing_bits": k}}`.
- Mix: `<<1, 2, "ab">>` (integer bytes + UTF-8 chunks) → `binary` lit. Integer segments with `::N` / `::size(N)` for **N ∈ 1…8** (default 8); a trailing partial (**N ∈ 1…7**) packs MSB-first into `{"bitstring":{"bytes":[…],"trailing_bits":k}}` with unused low bits cleared. Mid-construct partials, sizes outside 1…8, and `::binary` are rejected.
- `<>/2` also concatenates two **aligned** bitstrings → bitstring (`trailingBits ≠ 0` → `:badarg`). String↔binary mix → `:badarg`.
- `is_binary/1` → `is_tag` `"binary"`: true for UTF-8 `string` **or** aligned bitstring (Elixir-like). `is_bitstring/1` → `"bitstring"`: true for `string` or any bitstring.

### Binary matching

Teaching subset (no new Instr — builtins only):

- `bit_size/1` — `Term.bitstring` → int bit count; else catchable `:badarg` (UTF-8 `string` is **not** accepted).
- `bs_get_integer/2` — `(bitstring, nbits)` MSB-first integer prefix; short / wrong type / negative `nbits` → `:badarg`.
- `bs_drop/2` — `(bitstring, nbits)` → remaining bitstring (`Valid`); short / wrong type → `:badarg`.
- Mix: `<<x::N, rest::binary>>` (literal `N ∈ 1…32`), exact lit `<<1,2>>`, and exact-size `<<x::N>>` in `case` / `=` / heads; miss → `:match_error`. Sizes **9…32** lower as repeated 1…8-bit `bs_get_integer` chunks combined MSB-first (construct side stays **N ∈ 1…8**). Patterns apply to raw bitstrings only (exclude `string` via `is_tag`).
- Construct: mid-partial integer segments (`<<1::3, 2::5>>`) when bits concatenate; byte/string segments still require alignment. `<<cp::utf8>>` packs a literal codepoint to UTF-8 bytes.
- Match: `<<x::size(n)>>` when `n` is a bound variable (runtime `bs_get_integer` / `bs_drop` with that register).
- Out of scope: comprehensions, `::utf8` **match**, `<>/2` of partials, full BEAM binary syntax.

### Closures

- Closures are **heap nodes**: `{funName, env[]}` (tag `fun`). Env values are child refs/immediates (GC/copy like tuples).
- Each source `fn` is lifted to a synthetic MFA (e.g. `Main.__fn_0/2`). Params layout: **captures first**, then formal args (`arity = |captures| + |params|`).
- `{"op":"make_fun","dest":0,"fun":"Main.__fn_0/2","captures":[1,2]}` — dest ← closure; may GC while allocating.
- `{"op":"apply","dest":0,"fun":1,"args":[2,3]}` — call the closure in `fun` with `args` (push frame like `call`; regs = env ++ args).
- Elixir: `fn x -> … end` / `f.(x)`; free locals from the enclosing scope are captured. Teaching subset: single-clause `fn`, no `&Mod.fun/N`, no `spawn(fn …)`.

### Dynamic load

- `{"op":"load_file","dest":D,"path":P}` — `P` holds a **string** path to an Autumn IR JSON (`.bc.json`). On success `D` ← atom `:ok`. Host `entry` and `format` are unchanged; each incoming `CodeModule` **replaces** the same `name` or is appended.
- Teaching VM loads **bytecode images**, not Elixir source (no compiler in Lean). Mix lowers `Code.load_file(path)`.
- Soft-purge lite: frames already hold `Function` by value, so in-flight stacks keep old code; new `call` / `spawn` / `apply` see the updated MFA table.
- Catchable failures (same path as `raise`, so `try`/`rescue` works): non-string path → `:badarg`; missing/unreadable file → `:enoent`; bad JSON/decode **or** install that fails `Module.checkWF` / live-process stack WF under the new image → `:bad_bytecode`.
- The pure stepper stubs `load_file` as `:enoent`; `Step.runIO` / `autumn` exe services real `IO.FS.readFile`. See fixture `hot_load.ex`.

### Durable drain + `trap_exit` / `Process.exit`

- **Durable drain**: when the entry process exits, its value is *not* immediately the machine result. The scheduler keeps running until nothing can progress (no runnable process and no finite `wait` deadline), then materializes the entry process’s exit value as `State.result` for the CLI.
- `Process.flag/2` — currently only `Process.flag(:trap_exit, bool)`; returns the previous flag. Unknown flags → catchable `:badarg`.
- `Process.exit/2` — `Process.exit(self(), reason)` is `raiseValue`; `Process.exit(other, reason)` force-exits the target (ignores `trap_exit`, like OTP `exit(Pid, kill)`), returns `true`, then yields.
- Default `trapExit := false` on new processes.

### Dynamic MFA (`apply_mfa`)

- `{"op":"apply_mfa","dest":D,"mod":M,"fun":F,"args":[…]}` — `M` and `F` must be **atoms**; arity = `len(args)`. Looks up MFA `"#{mod}.#{fun}/#{arity}"` across `modules[]` and pushes a frame like `call`.
- Catchable failures (`raiseValue`): non-atom mod/fun or arity mismatch → `:badarg`; missing MFA → `:undef`.
- Mix: bare module alias `Counter` → atom `"Counter"`; `apply(mod, :init, [arg])` with a literal arg list → `apply_mfa`. Used by stdlib `GenServer` / `Supervisor` for OTP-shaped callback dispatch.
- **Stdlib-only OTP** (no new opcodes): `Agent` (GenServer + closure messages), `Task` (`spawn` MFA trampoline + monitor/`await`; not `spawn_link` because Autumn link signals on normal exit), `Registry` unique keys (GenServer + ETS + `DOWN` cleanup), `Registry.via/2` → `{:via, "Registry", {reg, key}}` for `GenServer.start/3` + `call`/`cast` via `whereis/1`, thin `Task.Supervisor` (`async/2` → `Task.async`). Compile with `stdlib/*.ex` via smoke `extras` / `compile_files`.

### ETS

Teaching subset (not full OTP). Tables live in `State.etsTables`; tid = array index. Objects are `{key, val}` 2-tuples.

- **Kinds:** `:set` (one value per key; insert overwrites), `:bag` (multi-value; exact `{key,val}` dup ignored), `:duplicate_bag` (always append), `:ordered_set` (insert keeps keys sorted by `Term.lt`; overwrite same key like `:set`; match/select/lookup iterate in key order).
- **Named tables:** `ets_new/2` with an atom name; subsequent ops accept tid **int** or that **atom**. Anonymous name is `nil`. Duplicate name → `:badarg`.
- **`ets_lookup/2`:** returns a **list of values** for the key (empty list if none).
- **`ets_match_object/2`:** pattern-match objects; wildcards atoms `:_` and `:"$1"`…`:"$9"`; returns list of `{key,val}`.
- **`ets_select/2`:** match-spec = list of `{Head, Guards, Body}`. Body is a one-element list (`:'$_'` / `:'$$'` / `:'$N'` / nested lit). Teaching guards: comparisons `:'=='` `:'=/='` `:'<'` `:'>'` `:'=<'` `:'>='`; types `is_atom` `is_integer` `is_list` `is_tuple` `is_nil` `is_pid`; logic `:'not'` / `:'andalso'` / `:'orelse'`. Unsupported guard → `:badarg`.
- **`ets_delete_object/2`:** `(tab, {key,val})` removes one exact matching entry.
- **Owner / heir:** creator pid owns the table. `ets_heir/2` sets `{heirPid, data}` or `:none`. On owner exit: live heir → transfer ownership, clear heir, deliver `{:ETS-TRANSFER, tid, fromPid, data}` to heir mailbox; else mark table dead (`alive=false`, clear entries/name; tid slot kept). Ops on dead tid → `:badarg`.
- **`ets_first/1`:** first key in walk order, or atom `"$end_of_table"` if empty. `ordered_set` uses key order; other kinds use first-insert order of distinct keys.
- **`ets_next/2`:** `(tab, key)` → next distinct key, or `"$end_of_table"` (unknown key → end).
- **`ets_give_away/3`:** `(tab, pid, data)` — caller must be owner; target must be live; sets owner, clears heir, delivers `{:ETS-TRANSFER, tid, fromPid, data}`. → `:true`; else `:badarg`. Private tables still out of scope.

## Builtins

| MFA | Meaning |
| --- | --- |
| `+/2` `-/2` `*/2` | integer or float arithmetic (homogeneous; mismatch → `:badarg`) |
| `==/2` | structural equality → bool |
| `</2` `>/2` `<=/2` `>=/2` | int or float compare → bool (homogeneous; mismatch → `:badarg`) |
| `<>/2` | string++string or aligned binary++binary (mismatch → `:badarg`) |
| `tuple_size/1` | tuple length → int (bad tag → `:badarg`) |
| `list_size/1` | list length → int (bad tag → `:badarg`) |
| `elem/2` | `(tuple, index)` → element (0-based; bad args / OOB → `:badarg`) |
| `map_size/1` | map entry count → int (bad tag → `:badarg`) |
| `map_get/2` | `(map, key)` → value or nil (bad tag → `:badarg`) |
| `map_put/3` | `(map, key, value)` → new map (may GC; bad tag → `:badarg`) |
| `self/0` | current process pid |
| `make_ref/0` | fresh unique ref |
| `cons/2` | `(head, list)` → new list `[head \| list]` (may GC; bad tail → `:badarg`) |
| `make_tuple/N` | `N` args → new tuple (may GC; lowered for non-literal `{…}`) |
| `Process.flag/2` | `(:trap_exit, bool)` → previous flag (else `:badarg`) |
| `Process.exit/2` | force-exit other / raise self |
| `Process.hibernate/0` | GC current process → `:ok` (teaching hibernate) |
| `ets_new/0` | allocate anonymous `:set` table → tid (`int`) |
| `ets_new/2` | `(name \| nil, :set\|:bag\|:duplicate_bag\|:ordered_set)` → tid (dup name / bad type → `:badarg`) |
| `ets_insert/3` | `(tab, key, val)` → `:true` (tab = tid or name atom; kind rules; unknown/dead → `:badarg`) |
| `ets_lookup/2` | `(tab, key)` → **list of values** (empty if none) |
| `ets_delete/2` | `(tab, key)` → `:true` (drop all entries with key) |
| `ets_delete_object/2` | `(tab, {key,val})` → `:true` (drop one exact object) |
| `ets_match_object/2` | `(tab, pattern)` → list of matching `{key,val}` |
| `ets_first/1` | `(tab)` → first key or `"$end_of_table"` |
| `ets_next/2` | `(tab, key)` → next key or `"$end_of_table"` |
| `ets_give_away/3` | `(tab, pid, data)` → `:true` + `ETS-TRANSFER` (owner only) |
| `ets_select/2` | `(tab, match_spec)` → list of results (teaching guards; bad spec → `:badarg`) |
| `ets_heir/2` | `(tab, {pid, data} \| :none)` → `:true` (owner-exit transfer) |

Guard helpers `is_integer/1`, `is_float/1`, `is_atom/1`, `is_list/1`, `is_tuple/1`, `is_map/1`, `is_boolean/1`, `is_pid/1`, `is_nil/1`, `is_reference/1`, `is_binary/1` (string **or** aligned binary), `is_bitstring/1` (string or any bitstring), `is_function/1` (fun tag) lower to `is_tag` (not separate MFAs). Map patterns `%{lit_key => pat}` lower via `map_get/2` + value tests. Handler-stack bounds (`handlersWF`) are part of runnable/waiting `Process.WF`.

## Scheduling

Reduction-preemptive (Erlang-style): each process runs a fixed **reduction budget** (quantum) of instructions, then the scheduler forces a yield and round-robins to the next runnable process. Busy loops cannot starve siblings — see fixture `preempt_fair.ex`. Still single-threaded and cooperative at the instruction boundary (no mid-instruction OS preempt). `recv` / `wait` parks the process (`waiting`); `send` wakes a waiting target (IP unchanged so `wait`/`recv` re-runs). Finite `wait` deadlines use a machine `clock`; if nothing is runnable, the scheduler advances to the next deadline and makes those processes runnable so `wait` can take the `after` path. **Machine result**: snapshot the entry process’s exit value only once the machine is idle (no runnable process and no finite wait deadline) — entry exit alone does not stop siblings (`drain_siblings.ex`).

## Runtime heap (Lean VM)

Compound terms (`tuple` / `list` / `map` / `closure`) are **heap-allocated** at runtime; immediates (`nil` / `bool` / `int` / `float` / `atom` / `string` / `bitstring` / `pid` / unique `ref`) stay unboxed in registers.

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
