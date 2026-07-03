/-
# E2b-universal — pilot simulation lemma: `eval pLF` computes `<` (2026-07-03)

The universal correspondence is a simulation of the verified `recognize` by the certified normalizer
`eval pLF`.  This file settles whether that simulation is *tractable* by proving the leaf case —
`lt`-correctness — symbolically (arbitrary Peano operands, not a fixed corpus value).

The bet the whole universal rests on: each `oneStep` dispatch on an encoded redex is `rfl` (the
encoded term's constructor structure is concrete, so `matchPat` picks the unique applicable rule and
only *binds* symbolic subterms, never compares them), and the recursion unrolls as an ordinary
induction closed with the `eval_stable` fixpoint brick.  `lt_sim` confirms it: the engine's `lt`
agrees with Lean's `<` on all naturals.

The identifier-equality dispatch (`ctxidx`'s `ctx-hit`) is the one place a `matchPat` *does* compare
two symbolic subterms; there the simulation must case-split on `a = b` (decidable) — flagged for the
`resolve` lemma, and not a wall.

Integrity: 0 sorry / 0 native_decide; `#print axioms` clean.
-/
import Mettapedia.GSLT.LanguageDef.LFRecognizerEncoding
import Mettapedia.GSLT.LanguageDef.LFEngineUniversal

namespace Mettapedia.GSLT.LanguageDef.LFSim

open MeTTaIL Mettapedia.GSLT.LanguageDef.LFEnc Mettapedia.GSLT.LanguageDef.LFUniv

set_option maxRecDepth 8000

/-! ## One-step dispatch facts for `lt` — each holds by `rfl` (concrete constructor structure). -/

theorem os_lt_ss (x y : AST) : oneStep pLF (ltT (S x) (S y)) = some (ltT x y) := by rfl
theorem os_lt_zs (y : AST) : oneStep pLF (ltT Z (S y)) = some (con0 "tt") := by rfl
theorem os_lt_zz : oneStep pLF (ltT Z Z) = some (con0 "ff") := by rfl
theorem os_lt_sz (x : AST) : oneStep pLF (ltT (S x) Z) = some (con0 "ff") := by rfl

/-- `tt` / `ff` are normal forms of `pLF`. -/
theorem norm_tt : IsNormal pLF (con0 "tt") := by rfl
theorem norm_ff : IsNormal pLF (con0 "ff") := by rfl

/-! ## The pilot: `eval pLF` computes strict `<` on Peano-encoded naturals, matching Lean `<`. -/

/-- **`lt`-correctness (simulation).** For all naturals `a b`, the certified normalizer reduces the
    encoded `lt (peano a) (peano b)` to `tt` iff `a < b`, else `ff` — exactly Lean's `<`. Proved by
    induction, each step a `rfl` dispatch closed by the `eval` fixpoint. -/
theorem lt_sim : ∀ (a b : Nat),
    ∃ N, eval pLF N (ltT (peano a) (peano b)) = con0 (if a < b then "tt" else "ff") := by
  intro a
  induction a with
  | zero =>
    intro b
    cases b with
    | zero =>
      refine ⟨1, ?_⟩
      simp only [peano, eval, os_lt_zz]
      simp
    | succ b' =>
      refine ⟨1, ?_⟩
      simp only [peano, eval, os_lt_zs]
      simp
  | succ a' ih =>
    intro b
    cases b with
    | zero =>
      refine ⟨1, ?_⟩
      simp only [peano, eval, os_lt_sz]
      simp
    | succ b' =>
      obtain ⟨N, hN⟩ := ih b'
      refine ⟨N + 1, ?_⟩
      simp only [peano, eval, os_lt_ss]
      rw [hN]
      simp only [Nat.succ_lt_succ_iff]

end Mettapedia.GSLT.LanguageDef.LFSim
