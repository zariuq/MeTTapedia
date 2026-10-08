import Mettapedia.OSLF.Framework.FundedNuBudgetSeparation
import Mettapedia.GSLT.Core.NonFactorization

/-!
# Complete funded unfolding observation classes

A purse of size `budget` distinguishes exactly the finite chains shorter
than `budget`. All longer chains share the persistent loop's complete answer
and spending profile. This classification is derived from actual instruction
execution; the bounded code is not used to define the observations.

The resulting finite image has a universal consumer property. A state readout
factors through the actual profiles exactly when it is constant on the earned
classes. The observer language remains the declared continuation unfoldings.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.FundedNuObservationClasses

open FundedNuBudgetSeparation
open Mettapedia.GSLT.Core.NonFactorization

abbrev Class (budget : Nat) := Option (Fin budget)

def classify (budget : Nat) : Option Nat → Class budget
  | none => none
  | some length => if visible : length < budget then some ⟨length, visible⟩ else none

def representative (budget : Nat) : Class budget → Option Nat := Option.map Fin.val

@[simp] theorem classify_representative (budget : Nat) (code : Class budget) :
    classify budget (representative budget code) = code := by
  cases code with
  | none => rfl
  | some length => simp only [representative, Option.map_some, classify, length.isLt, dif_pos]

theorem representative_profiles (budget : Nat) (state : Option Nat) :
    view budget (representative budget (classify budget state)) = view budget state := by
  cases state with
  | none => rfl
  | some length =>
      by_cases visible : length < budget
      · simp only [classify, dif_pos visible, representative, Option.map_some]
      · simp only [classify, dif_neg visible, representative, Option.map_none]
        exact (bounded_views_agree length budget (by omega)).symm

theorem loop_never_refutes (budget index : Nat) :
    (observation budget index none).1 ≠ some false := by
  rw [loop_observation]
  split <;> simp

theorem finite_refutation_iff (budget index length : Nat) :
    (observation budget index (some length)).1 = some false ↔
      length < index ∧ length < budget := by
  rw [chain_observation]
  change (if min (index + 1) (length + 1) ≤ budget then some (decide (index ≤ length)) else none) =
    some false ↔ length < index ∧ length < budget
  by_cases before : index ≤ length
  · have notLater : ¬ length < index := by omega
    simp only [before, decide_true, notLater, false_and]
    split <;> simp
  · have price : min (index + 1) (length + 1) = length + 1 := by omega
    by_cases cheap : length + 1 ≤ budget
    · simp [price, cheap]
      omega
    · simp [price, cheap]
      omega

theorem profile_equality_classifies (budget : Nat) (first second : Option Nat) :
    view budget first = view budget second ↔ classify budget first = classify budget second := by
  constructor
  · intro same
    cases first with
    | none =>
        cases second with
        | none => rfl
        | some length =>
            have invisible : ¬ length < budget := by
              intro visible
              have refutes := (finite_refutation_iff budget (length + 1) length).mpr
                ⟨by omega, visible⟩
              have agrees := congrArg (fun profile => (profile (length + 1)).1) same
              exact loop_never_refutes budget (length + 1) (agrees.trans refutes)
            simp only [classify, dif_neg invisible]
    | some firstLength =>
        cases second with
        | none =>
            have invisible : ¬ firstLength < budget := by
              intro visible
              have refutes := (finite_refutation_iff budget (firstLength + 1) firstLength).mpr
                ⟨by omega, visible⟩
              have agrees := congrArg (fun profile => (profile (firstLength + 1)).1) same
              exact loop_never_refutes budget (firstLength + 1) (agrees.symm.trans refutes)
            simp only [classify, dif_neg invisible]
        | some secondLength =>
            by_cases firstVisible : firstLength < budget
            · have firstRefutes := (finite_refutation_iff budget (firstLength + 1) firstLength).mpr
                ⟨by omega, firstVisible⟩
              have firstAgrees := congrArg (fun profile => (profile (firstLength + 1)).1) same
              obtain ⟨secondBound, secondVisible⟩ :=
                (finite_refutation_iff budget (firstLength + 1) secondLength).mp
                  (firstAgrees.symm.trans firstRefutes)
              have secondRefutes := (finite_refutation_iff budget (secondLength + 1) secondLength).mpr
                ⟨by omega, secondVisible⟩
              have secondAgrees := congrArg (fun profile => (profile (secondLength + 1)).1) same
              have firstBound := ((finite_refutation_iff budget (secondLength + 1) firstLength).mp
                (secondAgrees.trans secondRefutes)).1
              have lengthsEqual : firstLength = secondLength := by omega
              exact congrArg (fun length => classify budget (some length)) lengthsEqual
            · have secondInvisible : ¬ secondLength < budget := by
                intro secondVisible
                have secondRefutes := (finite_refutation_iff budget (secondLength + 1) secondLength).mpr
                  ⟨by omega, secondVisible⟩
                have agrees := congrArg (fun profile => (profile (secondLength + 1)).1) same
                exact firstVisible ((finite_refutation_iff budget (secondLength + 1) firstLength).mp
                  (agrees.trans secondRefutes)).2
              simp only [classify, dif_neg firstVisible, dif_neg secondInvisible]
  · intro same
    calc
      view budget first = view budget (representative budget (classify budget first)) :=
        (representative_profiles budget first).symm
      _ = view budget (representative budget (classify budget second)) :=
        congrArg (fun code => view budget (representative budget code)) same
      _ = view budget second := representative_profiles budget second

def profile (budget : Nat) (code : Class budget) := view budget (representative budget code)

theorem profile_injective (budget : Nat) : Function.Injective (profile budget) := by
  intro first second same
  simpa only [classify_representative] using
    (profile_equality_classifies budget (representative budget first) (representative budget second)).mp same

abbrev ActualProfile (budget : Nat) := Set.range (view budget)

def realize (budget : Nat) (code : Class budget) : ActualProfile budget :=
  ⟨profile budget code, representative budget code, rfl⟩

theorem realize_bijective (budget : Nat) : Function.Bijective (realize budget) := by
  constructor
  · intro first second same
    exact profile_injective budget (congrArg Subtype.val same)
  · rintro ⟨supplied, state, rfl⟩
    exact ⟨classify budget state, Subtype.ext (representative_profiles budget state)⟩

/-- The actual funded profile image has exactly these finite classes. -/
noncomputable def imageEquivalence (budget : Nat) : Class budget ≃ ActualProfile budget :=
  Equiv.ofBijective (realize budget) (realize_bijective budget)

theorem actual_profile_cardinality (budget : Nat) : Nat.card (ActualProfile budget) = budget + 1 := by
  rw [← Nat.card_congr (imageEquivalence budget)]
  simp [Class, Nat.card_eq_fintype_card]

theorem state_readout_factors_iff {Value : Type*} (budget : Nat) (readout : Option Nat → Value) :
    Factors (view budget) readout ↔ ConstantOnFibers (classify budget) readout := by
  constructor
  · intro factor first second same
    exact factor.constantOnFibers first second ((profile_equality_classifies budget first second).mpr same)
  · intro invariant
    classical
    let consumer : (Nat → Option Bool × Nat) → Value := fun supplied =>
      if reachable : ∃ state, view budget state = supplied then readout reachable.choose else readout none
    refine ⟨consumer, ?_⟩
    intro state
    have reachable : ∃ actual, view budget actual = view budget state := ⟨state, rfl⟩
    dsimp only [consumer]
    rw [dif_pos reachable]
    exact invariant reachable.choose state
      ((profile_equality_classifies budget reachable.choose state).mp reachable.choose_spec)

/-- The universal readout is computed on representatives, and is unique
on every class. Invariance must be earned by the supplied consumer. -/
theorem class_consumer_universal {Value : Type*} (budget : Nat) (readout : Option Nat → Value)
    (invariant : ConstantOnFibers (classify budget) readout) :
    ∃! consumer : Class budget → Value, ∀ state, consumer (classify budget state) = readout state := by
  refine ⟨fun code => readout (representative budget code), ?_, ?_⟩
  · intro state
    exact invariant (representative budget (classify budget state)) state
      (classify_representative budget (classify budget state))
  · intro other correct
    funext code
    simpa only [classify_representative] using correct (representative budget code)

end Mettapedia.OSLF.Framework.FundedNuObservationClasses
