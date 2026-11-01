# Autumn roadmap

Completed work lives in **git history**. This file is only “what’s next.”

## Later (deprioritized)

- **Verified compiler sketch** — design purity layers (`Except` / dispatcher / effectful result + law levels pure→concurrent) for compiled-program meaning; OTP-shaped Lean namespaces (`GenServer` / `Supervisor` lemmas) alongside stdlib (Lynx inspiration only; Autumn-authored)
- Induction principles over IR functions if program-level laws appear
- Full `runScheduled_preserves` / `_progress`; OTP-fixture schedule observational laws on the choice-tape API
- Richer Meta tooling for theorem exploration (not a heavier name-golden substitute)
