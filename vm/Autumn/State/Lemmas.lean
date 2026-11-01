import Autumn.State.ProcessLemmas
import Autumn.State.SchedLemmas
import Autumn.State.LinkLemmas

/-! # State / Process well-formedness lemmas (barrel, public proof surface)

Re-exports `State.ProcessLemmas`, `State.SchedLemmas`, and `State.LinkLemmas`.
Prefer this barrel (or those satellites) over unfolding `scheduleNext` /
`signalLink` / process update helpers. See `AGENTS.md` (“Public proof surface”).
-/
