import MettaHyperonFull.Minimal.Stdlib
open Metta.Minimal

/-! # E2b engine-reduction feasibility record (Route B)  — 2026-07-03, empirical

Findings from probing the real LeaTTa engine (`MettaHyperonFull`) from this proof tree:

  * `MettaHyperonFull` is already a `require`d lake dependency here (`../externals/LeaTTa`); imports
    resolve, toolchains match `v4.31.0`.  No `lake update` needed.
  * The engine computes correctly (the `#eval`s below return `"[3]"` and `"[b]"`).
  * The whole Minimal interpreter is **total** (0 `partial def`), so it is kernel-reducible in principle.
  * **But** the full driver `runMinimalSource` / `evalOp` does **not** reduce in-kernel by `rfl`/`decide`:
    it threads a `Std.HashMap` for imports, parses a `String`, and pretty-prints to a `String` — none of
    which the kernel reduces cheaply — and `native_decide` is prohibited here.  So a
    corpus-through-the-real-HE-engine proof *by computation* (`decide`) is not available.

  Consequence — the feasible certified route for E2b (`∀ ts, ⟦lf-recognize⟧ ts = recognize ts`) is
  `MeTTaIL.eval`, the pure-rewriting normalizer carrying `eval_sound` ("trusted boundary: none"),
  which **is** kernel-reducible.  It cannot express grounded builtins, so it requires re-encoding the
  recognizer as pure rewrite rules (Peano fuel; `case`/`if`/`==` desugared to pattern rules).  Then the
  finite corpus is provable by `decide` over `MeTTaIL.eval`, and the universal `∀ ts` claim by induction
  over that clean normalizer — the honest multi-session build.

  The engine calls below run under `#eval` (compiler), as evidence, not as proofs. -/

#eval runMinimalSource "!(+ 1 2)" 100                 -- "[3]"   (grounded builtin path)
#eval runMinimalSource "(= (f a) b)\n!(f a)" 100      -- "[b]"   (bare user-rewrite path)
