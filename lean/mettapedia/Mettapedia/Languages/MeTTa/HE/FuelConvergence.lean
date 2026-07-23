/-
# Fuel convergence

Existential-fuel completeness ("if the specification derives a result then
some fuel produces it") cannot be proved by fuel MONOTONICITY in the naive
inclusion sense: a low fuel budget emits a `StackOverflow` result that a
larger budget REPLACES rather than extends, so `f n ⊆ f (n+1)` is false.

The correct notion is CONVERGENCE STABILITY: a fuel-indexed family is
eventually constant, and the completeness induction takes the maximum of the
sub-derivation bounds and lifts each branch by stability at that bound.

This module is the reusable core of that argument, stated abstractly over any
fuel-indexed family so it applies to evaluator results, states, and readouts
alike.  The false monotonicity is recorded as an explicit negative witness
(`inclusion_monotonicity_fails`) so the trap cannot be re-entered by a later
reader.
-/
import Mathlib.Data.List.Basic

namespace Mettapedia.Languages.MeTTa.HE.FuelConvergence

/-- The family is constant from `bound` onward. -/
def StableFrom {α : Type _} (f : Nat → α) (bound : Nat) : Prop :=
  ∀ n, bound ≤ n → f n = f bound

/-- The family is eventually constant: the honest replacement for fuel
monotonicity. -/
def Converges {α : Type _} (f : Nat → α) : Prop :=
  ∃ bound, StableFrom f bound

/-! ## Raising the bound

Stability is upward closed, which is what lets independent sub-derivations be
combined at a common fuel budget. -/

theorem StableFrom.mono {α : Type _} {f : Nat → α} {bound bound' : Nat}
    (h : StableFrom f bound) (hle : bound ≤ bound') : StableFrom f bound' := by
  intro n hn
  rw [h n (Nat.le_trans hle hn), h bound' hle]

/-- At or above a stability bound the value is the stable one. -/
theorem StableFrom.eq_of_le {α : Type _} {f : Nat → α} {bound n : Nat}
    (h : StableFrom f bound) (hn : bound ≤ n) : f n = f bound := h n hn

/-- Any two points at or above a stability bound agree: the property the
completeness induction actually consumes when different branches pick
different budgets. -/
theorem StableFrom.eq_of_both {α : Type _} {f : Nat → α} {bound m n : Nat}
    (h : StableFrom f bound) (hm : bound ≤ m) (hn : bound ≤ n) : f m = f n := by
  rw [h m hm, h n hn]

theorem converges_const {α : Type _} (a : α) : Converges (fun _ => a) :=
  ⟨0, fun _ _ => rfl⟩

/-! ## Combining independent budgets

The completeness proof descends into sub-derivations, each with its own
bound, and must evaluate them all at ONE budget.  These lemmas are exactly
that step. -/

/-- Two families converge at a common bound. -/
theorem StableFrom.pair {α β : Type _} {f : Nat → α} {g : Nat → β}
    {bf bg : Nat} (hf : StableFrom f bf) (hg : StableFrom g bg) :
    StableFrom (fun n => (f n, g n)) (max bf bg) := by
  intro n hn
  have hfn : bf ≤ n := Nat.le_trans (Nat.le_max_left bf bg) hn
  have hgn : bg ≤ n := Nat.le_trans (Nat.le_max_right bf bg) hn
  have hfb : bf ≤ max bf bg := Nat.le_max_left bf bg
  have hgb : bg ≤ max bf bg := Nat.le_max_right bf bg
  simp only [Prod.mk.injEq]
  exact ⟨(hf.eq_of_both hfn hfb), (hg.eq_of_both hgn hgb)⟩

theorem Converges.pair {α β : Type _} {f : Nat → α} {g : Nat → β}
    (hf : Converges f) (hg : Converges g) : Converges (fun n => (f n, g n)) := by
  obtain ⟨bf, hf⟩ := hf
  obtain ⟨bg, hg⟩ := hg
  exact ⟨max bf bg, hf.pair hg⟩

/-- Stability transports along any function of the value: readouts,
projections, and translations of a convergent family converge at the same
bound. -/
theorem StableFrom.map {α β : Type _} {f : Nat → α} {bound : Nat}
    (h : StableFrom f bound) (k : α → β) :
    StableFrom (fun n => k (f n)) bound := by
  intro n hn
  exact congrArg k (h n hn)

theorem Converges.map {α β : Type _} {f : Nat → α}
    (h : Converges f) (k : α → β) : Converges (fun n => k (f n)) := by
  obtain ⟨bound, h⟩ := h
  exact ⟨bound, h.map k⟩

/-- A finite family of convergent components converges at one common bound —
the `max` step of the completeness induction, for an arbitrary branching
factor. -/
theorem stableFrom_list {α : Type _} :
    ∀ (fs : List (Nat → α)) (bounds : List Nat),
      fs.length = bounds.length →
      (∀ i (hi : i < fs.length) (hb : i < bounds.length),
        StableFrom fs[i] bounds[i]) →
      ∃ bound, ∀ i (hi : i < fs.length), StableFrom fs[i] bound
  | [], _, _, _ => ⟨0, fun i hi => absurd hi (by simp)⟩
  | f :: fs, [], hlen, _ => by simp at hlen
  | f :: fs, b :: bs, hlen, hstable => by
    have hlen' : fs.length = bs.length := by
      simpa using hlen
    have htail : ∀ i (hi : i < fs.length) (hb : i < bs.length),
        StableFrom fs[i] bs[i] := by
      intro i hi hb
      exact hstable (i + 1) (by simpa using hi) (by simpa using hb)
    obtain ⟨bound, hbound⟩ := stableFrom_list fs bs hlen' htail
    refine ⟨max b bound, ?_⟩
    intro i hi
    match i, hi with
    | 0, _ =>
      have hb0 : StableFrom f b := hstable 0 (by simp) (by simp)
      exact hb0.mono (Nat.le_max_left b bound)
    | i + 1, hi =>
      have hi' : i < fs.length := by simpa using hi
      exact (hbound i hi').mono (Nat.le_max_right b bound)

/-! ## The trap, recorded

Naive fuel monotonicity is FALSE for the evaluator: a small budget yields a
`StackOverflow` result that a larger budget replaces.  The witness below is
abstract but faithful to that shape — a family that converges yet whose
successive values are unrelated by inclusion — so nobody re-derives
completeness from a false monotonicity premise. -/

/-- A convergent family whose early value is REPLACED, not extended.  Any
proof strategy assuming `f n ⊆ f (n+1)` fails on it, while convergence
stability succeeds. -/
def overflowThenAnswer : Nat → List String
  | 0 => ["StackOverflow"]
  | _ + 1 => ["answer"]

theorem overflowThenAnswer_converges : Converges overflowThenAnswer := by
  refine ⟨1, ?_⟩
  intro n hn
  match n, hn with
  | _ + 1, _ => rfl

/-- The negative witness: convergence does NOT give inclusion monotonicity,
so the completeness induction must use stability. -/
theorem inclusion_monotonicity_fails :
    ¬(∀ n, ∀ a ∈ overflowThenAnswer n, a ∈ overflowThenAnswer (n + 1)) := by
  intro h
  have hmem : "StackOverflow" ∈ overflowThenAnswer 0 := by
    simp [overflowThenAnswer]
  have := h 0 "StackOverflow" hmem
  simp [overflowThenAnswer] at this

end Mettapedia.Languages.MeTTa.HE.FuelConvergence
