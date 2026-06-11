import Mettapedia.Logic.HOL.WitnessedExtension
import Mettapedia.Logic.HOL.Syntax.FreshConst
import Mathlib.Tactic.Tauto

/-!
# Henkin saturation chain

Building on the single-step conservativity `consistent_addWitness`, this file
constructs, over the parameter-extended signature `WithParams Const`, a
**consistent theory that witnesses every existential** — the Henkin saturation.

Given a (param-free) consistent base theory `T₀` and an enumeration `enum` of all
one-variable bodies, we add at stage `n` the witness axiom `(∃x. enum n) →
(enum n)[c]`, where `c = param σ kₙ` is a parameter chosen *larger than every
parameter already used* (`kₙ = max (axiomBound …) (maxParam …)`).  Freshness is
therefore automatic, and `consistent_addWitness` keeps every finite stage
consistent.

This file (Piece 1) builds the chain, the per-stage consistency, and the bound
machinery.  The limit's consistency (finite character) and the existence property
are added on top.
-/

namespace Mettapedia.Logic.HOL

open Mettapedia.Logic.HOL.WithParams

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/-- An existential body to be witnessed: a type paired with a one-variable formula. -/
abbrev Body (Const : Ty Base → Type v) := (σ : Ty Base) × Formula (WithParams Const) [σ]

/-- A strict upper bound on the parameter indices occurring in a finite list of
closed formulas. -/
def axiomBound : List (ClosedFormula (WithParams Const)) → Nat
  | [] => 0
  | ψ :: l => max (maxParam ψ) (axiomBound l)

theorem maxParam_le_axiomBound :
    ∀ {l : List (ClosedFormula (WithParams Const))} {ψ},
      ψ ∈ l → maxParam (Const := Const) ψ ≤ axiomBound l
  | [], _, h => by simp at h
  | a :: l, ψ, h => by
      simp only [axiomBound]
      rcases List.mem_cons.mp h with rfl | h'
      · exact le_max_left _ _
      · exact le_trans (maxParam_le_axiomBound h') (le_max_right _ _)

/-- The witness index chosen at stage `n`: larger than every parameter already in
the accumulated axioms and in the body being witnessed. -/
def witnessIndex (chain : List (ClosedFormula (WithParams Const))) (b : Body Const) : Nat :=
  max (axiomBound chain) (maxParam b.2)

/-- The witness axioms accumulated through the first `n` stages of the chain. -/
def witnessChain (enum : Nat → Body Const) :
    Nat → List (ClosedFormula (WithParams Const))
  | 0 => []
  | n + 1 =>
      witnessAxiom
        (param (enum n).1 (witnessIndex (witnessChain enum n) (enum n)))
        (enum n).2
      :: witnessChain enum n

/-- The theory at stage `n`: the base plus the stage-`n` witness axioms. -/
def witnessTheory (T₀ : ClosedTheorySet (WithParams Const))
    (enum : Nat → Body Const) (n : Nat) : ClosedTheorySet (WithParams Const) :=
  T₀ ∪ {ψ | ψ ∈ witnessChain enum n}

/-- The Henkin saturation: the base plus *all* witness axioms. -/
def witnessLimit (T₀ : ClosedTheorySet (WithParams Const))
    (enum : Nat → Body Const) : ClosedTheorySet (WithParams Const) :=
  T₀ ∪ {ψ | ∃ n, ψ ∈ witnessChain enum n}

theorem witnessTheory_zero (T₀ : ClosedTheorySet (WithParams Const))
    (enum : Nat → Body Const) : witnessTheory T₀ enum 0 = T₀ := by
  simp [witnessTheory, witnessChain]

theorem witnessTheory_succ (T₀ : ClosedTheorySet (WithParams Const))
    (enum : Nat → Body Const) (n : Nat) :
    witnessTheory T₀ enum (n + 1)
      = insert (witnessAxiom
          (param (enum n).1 (witnessIndex (witnessChain enum n) (enum n)))
          (enum n).2)
          (witnessTheory T₀ enum n) := by
  simp only [witnessTheory, witnessChain]
  ext x
  simp only [Set.mem_union, Set.mem_setOf_eq, List.mem_cons, Set.mem_insert_iff]
  tauto

/-- **Per-stage consistency.**  Every finite stage of the saturation chain is
consistent, by induction using `consistent_addWitness` and the fresh-index choice. -/
theorem witnessTheory_consistent (T₀ : ClosedTheorySet (WithParams Const))
    (enum : Nat → Body Const)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T₀)
    (hT0 : ∀ ψ ∈ T₀, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ) :
    ∀ n, ClosedTheorySet.Consistent (Const := WithParams Const)
      (witnessTheory T₀ enum n) := by
  intro n
  induction n with
  | zero => rw [witnessTheory_zero]; exact hCons
  | succ n ih =>
      rw [witnessTheory_succ]
      refine consistent_addWitness
        (c := param (enum n).1 (witnessIndex (witnessChain enum n) (enum n)))
        ih ?_ ?_
      · intro ψ hψ
        simp only [witnessTheory, Set.mem_union, Set.mem_setOf_eq] at hψ
        rcases hψ with hψ0 | hψc
        · exact hT0 ψ hψ0 (enum n).1 _
        · exact noConstOccurrence_param_of_ge _ ψ
            (le_trans (maxParam_le_axiomBound hψc) (le_max_left _ _))
      · exact noConstOccurrence_param_of_ge _ (enum n).2 (le_max_right _ _)

/-! ## Monotonicity and the limit -/

theorem witnessChain_subset_succ (enum : Nat → Body Const) (n : Nat) :
    witnessChain enum n ⊆ witnessChain enum (n + 1) := by
  intro x hx
  rw [witnessChain]
  exact List.mem_cons_of_mem _ hx

theorem witnessChain_mono (enum : Nat → Body Const) {m n : Nat} (h : m ≤ n) :
    witnessChain enum m ⊆ witnessChain enum n := by
  induction n, h using Nat.le_induction with
  | base => exact List.Subset.refl _
  | succ n hn ih => exact List.Subset.trans ih (witnessChain_subset_succ enum n)

theorem witnessTheory_mono (T₀ : ClosedTheorySet (WithParams Const))
    (enum : Nat → Body Const) {m n : Nat} (h : m ≤ n) :
    witnessTheory T₀ enum m ⊆ witnessTheory T₀ enum n := by
  intro ψ hψ
  simp only [witnessTheory, Set.mem_union, Set.mem_setOf_eq] at hψ ⊢
  rcases hψ with h0 | hc
  · exact Or.inl h0
  · exact Or.inr (witnessChain_mono enum h hc)

/-- **Finite character.**  Any finite set of formulas drawn from the saturation
limit already lives at a single finite stage. -/
theorem exists_stage (T₀ : ClosedTheorySet (WithParams Const)) (enum : Nat → Body Const) :
    ∀ (Γ : List (ClosedFormula (WithParams Const))),
      (∀ ψ ∈ Γ, ψ ∈ witnessLimit T₀ enum) →
      ∃ N, ∀ ψ ∈ Γ, ψ ∈ witnessTheory T₀ enum N
  | [], _ => ⟨0, by intro ψ hψ; cases hψ⟩
  | a :: Γ, hΓ => by
      obtain ⟨N, hN⟩ :=
        exists_stage T₀ enum Γ (fun ψ hψ => hΓ ψ (List.mem_cons_of_mem _ hψ))
      have ha := hΓ a (List.mem_cons_self)
      simp only [witnessLimit, Set.mem_union, Set.mem_setOf_eq] at ha
      rcases ha with ha0 | ⟨na, hna⟩
      · refine ⟨N, fun ψ hψ => ?_⟩
        rcases List.mem_cons.mp hψ with rfl | hψ'
        · exact Set.mem_union_left _ ha0
        · exact hN ψ hψ'
      · refine ⟨max N na, fun ψ hψ => ?_⟩
        rcases List.mem_cons.mp hψ with rfl | hψ'
        · exact Set.mem_union_right _ (witnessChain_mono enum (le_max_right N na) hna)
        · exact witnessTheory_mono T₀ enum (le_max_left N na) (hN ψ hψ')

/-- **Consistency of the Henkin saturation.**  The full witnessed theory is
consistent: any refutation uses finitely many axioms, hence lives at a consistent
finite stage. -/
theorem witnessLimit_consistent (T₀ : ClosedTheorySet (WithParams Const))
    (enum : Nat → Body Const)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T₀)
    (hT0 : ∀ ψ ∈ T₀, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ) :
    ClosedTheorySet.Consistent (Const := WithParams Const) (witnessLimit T₀ enum) := by
  intro hbot
  rcases hbot with ⟨Γ, hΓ, d⟩
  obtain ⟨N, hN⟩ := exists_stage T₀ enum Γ hΓ
  exact witnessTheory_consistent T₀ enum hCons hT0 N ⟨Γ, hN, d⟩

theorem subset_witnessLimit (T₀ : ClosedTheorySet (WithParams Const))
    (enum : Nat → Body Const) :
    ∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T₀ → ψ ∈ witnessLimit T₀ enum :=
  fun hψ => Set.mem_union_left _ hψ

theorem witnessAxiom_mem_witnessLimit (T₀ : ClosedTheorySet (WithParams Const))
    (enum : Nat → Body Const) (n : Nat) :
    witnessAxiom (param (enum n).1 (witnessIndex (witnessChain enum n) (enum n)))
        (enum n).2 ∈ witnessLimit T₀ enum := by
  refine Set.mem_union_right _ ?_
  refine ⟨n + 1, ?_⟩
  rw [witnessChain]
  exact List.mem_cons_self

/-- **Existence property (axiom form).**  For every body in the range of the
enumeration, the saturation contains a witness axiom `(∃x. φ) → φ[c]` whose witness
`c` is a closed parameter constant. -/
theorem exists_witnessAxiom (T₀ : ClosedTheorySet (WithParams Const))
    (enum : Nat → Body Const) (b : Body Const) (hb : ∃ n, enum n = b) :
    ∃ k : Nat, witnessAxiom (param b.1 k) b.2 ∈ witnessLimit T₀ enum := by
  obtain ⟨n, hn⟩ := hb
  subst hn
  exact ⟨witnessIndex (witnessChain enum n) (enum n),
    witnessAxiom_mem_witnessLimit T₀ enum n⟩

end Mettapedia.Logic.HOL
