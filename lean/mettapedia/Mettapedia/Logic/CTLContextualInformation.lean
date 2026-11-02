import Mettapedia.Logic.CTLFormula
import Mettapedia.GSLT.Dynamics.RegionObservations
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Powerset

/-!
# Exact information for nested CTL continuations

The retained state is a formula, and clients may put it under any admitted
one-hole CTL context before asking about a state. The satisfying-state set is
an exact summary for these clients, including negative and temporal contexts.
Formula syntax may be infinite even when the model's state space is finite.
The finite bound is therefore on reachable semantic summaries, not on syntax.

This does not identify minimum physical bytes or Kolmogorov descriptions.
Changing the model's edges or deadlock policy changes this observer family.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.CTLContextualInformation

open CTLFormula
open Mettapedia.GSLT.Dynamics.RegionObservations

inductive Context (Label : Type)
  | hole
  | neg (body : Context Label)
  | ex (body : Context Label)
  | eg (body : Context Label)
  | conjLeft (body : Context Label) (right : Formula Label)
  | conjRight (left : Formula Label) (body : Context Label)
  | disjLeft (body : Context Label) (right : Formula Label)
  | disjRight (left : Formula Label) (body : Context Label)
  | euLeft (body : Context Label) (goal : Formula Label)
  | euRight (holds : Formula Label) (body : Context Label)

variable {Label State : Type}

def Context.plug : Context Label → Formula Label → Formula Label
  | .hole, formula => formula
  | .neg body, formula => .neg (body.plug formula)
  | .ex body, formula => .ex (body.plug formula)
  | .eg body, formula => .eg (body.plug formula)
  | .conjLeft body right, formula => .conj (body.plug formula) right
  | .conjRight left body, formula => .conj left (body.plug formula)
  | .disjLeft body right, formula => .disj (body.plug formula) right
  | .disjRight left body, formula => .disj left (body.plug formula)
  | .euLeft body goal, formula => .eu (body.plug formula) goal
  | .euRight holds body, formula => .eu holds (body.plug formula)

theorem context_congr (domain : Set State) (relation : State → State → Prop) (atoms : Label → Set State)
    (context : Context Label) (first second : Formula Label)
    (same : meaning domain relation atoms first = meaning domain relation atoms second) :
    meaning domain relation atoms (context.plug first) = meaning domain relation atoms (context.plug second) := by
  induction context with
  | hole => exact same
  | neg body ih | ex body ih | eg body ih => simp only [Context.plug, meaning, ih]
  | conjLeft body right ih | conjRight left body ih | disjLeft body right ih | disjRight left body ih | euLeft body goal ih | euRight holds body ih =>
      simp only [Context.plug, meaning, ih]

def observers (domain : Set State) (relation : State → State → Prop) (atoms : Label → Set State) :
    Family (Formula Label) where
  Question := Context Label × State
  Answer _ := Prop
  read question formula := question.2 ∈ meaning domain relation atoms (question.1.plug formula)

theorem meaning_exact (domain : Set State) (relation : State → State → Prop) (atoms : Label → Set State) :
    (observers domain relation atoms).Exact (meaning domain relation atoms) := by
  intro first second
  constructor
  · intro same ⟨context, state⟩
    exact congrArg (fun states : Set State => state ∈ states) (context_congr domain relation atoms context first second same)
  · intro all
    ext state
    exact Iff.of_eq (all (.hole, state))

noncomputable def summary [Fintype State] (domain : Set State) (relation : State → State → Prop)
    (atoms : Label → Set State) (formula : Formula Label) : Finset State :=
  (meaning domain relation atoms formula).toFinite.toFinset

theorem summary_exact [Fintype State] (domain : Set State) (relation : State → State → Prop)
    (atoms : Label → Set State) : (observers domain relation atoms).Exact (summary domain relation atoms) := by
  intro first second
  rw [summary, summary, Set.Finite.toFinset_inj]
  exact meaning_exact domain relation atoms first second

/-- The semantic quotient is finite even though syntax has arbitrarily
deep redundant formulas. -/
theorem classes_finite [Fintype State] (domain : Set State) (relation : State → State → Prop)
    (atoms : Label → Set State) : Finite (observers domain relation atoms).Classes := by
  let equivalent := (observers domain relation atoms).exactEquiv (summary domain relation atoms)
    (summary_exact domain relation atoms)
  exact Finite.of_surjective equivalent equivalent.surjective

theorem classes_bound [Fintype State] (domain : Set State) (relation : State → State → Prop)
    (atoms : Label → Set State) : Nat.card (observers domain relation atoms).Classes ≤ 2 ^ Fintype.card State := by
  classical
  let equivalent := (observers domain relation atoms).exactEquiv (summary domain relation atoms)
    (summary_exact domain relation atoms)
  rw [← Nat.card_congr equivalent]
  calc
    _ ≤ Nat.card (Finset State) := Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    _ = _ := by simp [Nat.card_eq_fintype_card]

/-- Invalid encoded states consume no semantic classes. The upper bound
depends on the valid-state domain, not on the ambient encoding's spare codes. -/
theorem classes_bound_valid_domain [Fintype State] (domain : Set State)
    (relation : State → State → Prop) (atoms : Label → Set State) :
    Nat.card (observers domain relation atoms).Classes ≤ 2 ^ domain.toFinite.toFinset.card := by
  classical
  let codes := domain.toFinite.toFinset.powerset
  let embed : Set.range (summary domain relation atoms) → ↥codes := fun code =>
    ⟨code.val, by
      apply Finset.mem_powerset.mpr
      obtain ⟨formula, same⟩ := code.property
      rw [← same]
      intro state present
      have member : state ∈ meaning domain relation atoms formula := by
        simpa only [summary, Set.Finite.mem_toFinset] using present
      simpa only [Set.Finite.mem_toFinset] using meaning_within domain relation atoms formula member⟩
  have injective : Function.Injective embed := by
    intro first second same
    apply Subtype.ext
    exact congrArg (fun code : ↥codes => code.val) same
  let equivalent := (observers domain relation atoms).exactEquiv (summary domain relation atoms)
    (summary_exact domain relation atoms)
  rw [← Nat.card_congr equivalent]
  calc
    _ ≤ Nat.card ↥codes := Nat.card_le_card_of_injective embed injective
    _ = _ := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]; exact Finset.card_powerset _

/-- Every other sufficient finite code determines the canonical CTL class.
The factorization is on reachable codes, without invented unreachable values. -/
theorem every_sufficient_code_determines_class {Code : Type} (domain : Set State)
    (relation : State → State → Prop) (atoms : Label → Set State) (code : Formula Label → Code)
    (sufficient : (observers domain relation atoms).Sufficient code) :
    Mettapedia.GSLT.Core.NonFactorization.Factors (Set.rangeFactorization code)
      (observers domain relation atoms).classOf :=
  ((observers domain relation atoms).sufficient_iff_factors code).mp sufficient

theorem minimal_reachable_summary [Fintype State] {Code : Type} [Finite Code]
    (domain : Set State) (relation : State → State → Prop) (atoms : Label → Set State)
    (code : Formula Label → Code) (sufficient : (observers domain relation atoms).Sufficient code) :
    Nat.card (Set.range (summary domain relation atoms)) ≤ Nat.card (Set.range code) := by
  let equivalent := (observers domain relation atoms).exactEquiv (summary domain relation atoms)
    (summary_exact domain relation atoms)
  rw [Nat.card_congr equivalent]
  exact Nat.card_le_card_of_surjective _ ((observers domain relation atoms).recover_surjective code sufficient)

namespace Controls

def atoms : Bool → Set Bool := fun label => {label}

theorem same_cardinality_is_not_sufficient :
    ¬(observers Set.univ (fun _ _ : Bool => False) atoms).Sufficient
      (fun formula => (summary Set.univ (fun _ _ : Bool => False) atoms formula).card) := by
  intro sufficient
  have same : (summary Set.univ (fun _ _ : Bool => False) atoms (.atom false)).card =
      (summary Set.univ (fun _ _ : Bool => False) atoms (.atom true)).card := by
    simp [summary, meaning, atoms]
  have impossible := sufficient (.atom false) (.atom true) same (.hole, false)
  change (false ∈ meaning Set.univ (fun _ _ : Bool => False) atoms (.atom false)) =
    (false ∈ meaning Set.univ (fun _ _ : Bool => False) atoms (.atom true)) at impossible
  simp [meaning, atoms] at impossible

theorem syntactic_double_negation_is_forgotten :
    (observers Set.univ (fun _ _ : Bool => False) atoms).Equivalent (.atom false) (.neg (.neg (.atom false))) :=
  (meaning_exact _ _ _ _ _).mp (double_negation _ _ _ _).symm

end Controls

end Mettapedia.Logic.CTLContextualInformation
