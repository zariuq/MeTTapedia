import Mettapedia.TypeTheory.ModeTheoryProducts
import Mathlib.Tactic

/-!
# Guarded time as a mode theory

Revision time forms a mode category whose arrows point from a current
revision to an available past revision.  Strictly earlier revisions define
the guarded `later` predicate, and its Löb rule is ordinary strong induction.

The modal category, guarded predicate, and cost grading are separate objects.
The same revision category admits distinct lawful cost gradings.  An arbitrary
second mode theory combines with guarded time by the categorical product, so
staging/contextual-code modes and productivity modes need not be identified.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.GuardedTimeModeTheory

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.ModeTheoryProducts

/-- Revisions with a modality from a current revision to every available
past revision. -/
abbrev revisionModes : ModeTheory where
  Mode := Nat
  Hom := fun current past => PLift (past ≤ current)
  id := fun revision => ⟨Nat.le_refl revision⟩
  comp := fun currentToMiddle middleToPast =>
    ⟨Nat.le_trans middleToPast.down currentToMiddle.down⟩
  id_comp := by
    intro current past modality
    exact Subsingleton.elim _ _
  comp_id := by
    intro current past modality
    exact Subsingleton.elim _ _
  comp_assoc := by
    intro first second third last earlier middle later
    exact Subsingleton.elim _ _

/-- The canonical one-tick guard from revision `r+1` to revision `r`. -/
def guard (revision : Nat) : revisionModes.Hom (revision + 1) revision :=
  ⟨Nat.le_succ revision⟩

/-- Strict temporal progress is a property of a revision modality, not an
additional primitive arrow. -/
def Strict {current past : Nat} (_modality : revisionModes.Hom current past) :
    Prop := past < current

theorem guard_strict (revision : Nat) : Strict (guard revision) := by
  exact Nat.lt_succ_self revision

/-- Identity modalities are never strict guards. -/
theorem identity_not_strict (revision : Nat) :
    ¬ Strict (revisionModes.id revision) :=
  Nat.lt_irrefl revision

/-- A strict first temporal phase remains strict after any further journey
into its past. -/
theorem comp_strict_of_first {current middle past : Nat}
    (earlier : revisionModes.Hom current middle)
    (later : revisionModes.Hom middle past)
    (strict : Strict earlier) :
    Strict (revisionModes.comp earlier later) := by
  exact lt_of_le_of_lt later.down strict

/-- A strict later temporal phase makes the whole composite strict. -/
theorem comp_strict_of_second {current middle past : Nat}
    (earlier : revisionModes.Hom current middle)
    (later : revisionModes.Hom middle past)
    (strict : Strict later) :
    Strict (revisionModes.comp earlier later) := by
  exact lt_of_lt_of_le strict earlier.down

/-- `Later P` at revision `r` means that `P` holds at every strictly earlier
revision. -/
def Later (predicate : Nat → Prop) (revision : Nat) : Prop :=
  ∀ past < revision, predicate past

/-- The order-theoretic and mode-theoretic readings of `Later` agree. -/
theorem later_iff_strict_modal (predicate : Nat → Prop) (revision : Nat) :
    Later predicate revision ↔
      ∀ (past : Nat) (_modality : revisionModes.Hom revision past),
        past ≠ revision → predicate past := by
  constructor
  · intro later past modality different
    exact later past (Nat.lt_of_le_of_ne modality.down different)
  · intro modal past earlier
    exact modal past ⟨Nat.le_of_lt earlier⟩ (Nat.ne_of_lt earlier)

/-- Löb induction for revision-guarded predicates. -/
theorem lob (predicate : Nat → Prop)
    (step : ∀ revision, Later predicate revision → predicate revision) :
    ∀ revision, predicate revision := by
  intro revision
  induction revision using Nat.strongRecOn with
  | ind current inductionHypothesis =>
      exact step current inductionHypothesis

/-! ## Finite validated horizons -/

/-- The full subcategory of revisions visible below a finite horizon. -/
abbrev finiteRevisionModes (horizon : Nat) : ModeTheory where
  Mode := Fin (horizon + 1)
  Hom := fun current past => PLift (past.val ≤ current.val)
  id := fun revision => ⟨Nat.le_refl revision.val⟩
  comp := fun currentToMiddle middleToPast =>
    ⟨Nat.le_trans middleToPast.down currentToMiddle.down⟩
  id_comp := by intros; exact Subsingleton.elim _ _
  comp_id := by intros; exact Subsingleton.elim _ _
  comp_assoc := by intros; exact Subsingleton.elim _ _

/-- Guarded truth over a finite revision horizon. -/
def FiniteLater {horizon : Nat}
    (predicate : Fin (horizon + 1) → Prop)
    (revision : Fin (horizon + 1)) : Prop :=
  ∀ past, past.val < revision.val → predicate past

/-- Löb induction also holds on every finite validated horizon. -/
theorem finite_lob {horizon : Nat}
    (predicate : Fin (horizon + 1) → Prop)
    (step : ∀ revision, FiniteLater predicate revision → predicate revision) :
    ∀ revision, predicate revision := by
  intro revision
  have allBelow : ∀ (value : Nat) (bound : value < horizon + 1),
      predicate ⟨value, bound⟩ := by
    intro value
    induction value using Nat.strongRecOn with
    | ind current inductionHypothesis =>
        intro bound
        apply step ⟨current, bound⟩
        intro past earlier
        have prior := inductionHypothesis past.val earlier past.isLt
        simpa only [Fin.eta] using prior
  exact allBelow revision.val revision.isLt

/-! ## Cost is additional structure -/

/-- Elapsed revision distance as a sequential cost grading. -/
abbrev distanceGrading : CostGrading revisionModes where
  Grade := Nat
  unit := 0
  add := Nat.add
  add_assoc := Nat.add_assoc
  unit_add := Nat.zero_add
  add_unit := Nat.add_zero
  gradeOf := fun {current past} _ => current - past
  gradeOf_id := by intro revision; simp
  gradeOf_comp := by
    intro current middle past currentToMiddle middleToPast
    have firstBound := currentToMiddle.down
    have secondBound := middleToPast.down
    exact (Nat.sub_add_sub_cancel firstBound secondBound).symm

/-- An equally lawful grading assigning twice the elapsed distance. -/
abbrev doubledDistanceGrading : CostGrading revisionModes where
  Grade := Nat
  unit := 0
  add := Nat.add
  add_assoc := Nat.add_assoc
  unit_add := Nat.zero_add
  add_unit := Nat.add_zero
  gradeOf := fun {current past} _ => 2 * (current - past)
  gradeOf_id := by intro revision; simp
  gradeOf_comp := by
    intro current middle past currentToMiddle middleToPast
    have firstBound := currentToMiddle.down
    have secondBound := middleToPast.down
    calc
      2 * (current - past) =
          2 * ((current - middle) + (middle - past)) := by
            rw [Nat.sub_add_sub_cancel firstBound secondBound]
      _ = 2 * (current - middle) + 2 * (middle - past) :=
        Nat.mul_add _ _ _

@[simp] theorem distance_guard (revision : Nat) :
    distanceGrading.gradeOf (guard revision) = 1 := by
  simp [distanceGrading]

@[simp] theorem doubledDistance_guard (revision : Nat) :
    doubledDistanceGrading.gradeOf (guard revision) = 2 := by
  simp [doubledDistanceGrading]

/-- The guarded mode theory does not determine its cost model. -/
theorem same_modes_distinct_guard_costs (revision : Nat) :
    distanceGrading.gradeOf (guard revision) ≠
      doubledDistanceGrading.gradeOf (guard revision) := by
  simp

/-! ## Orthogonal composition with another modal discipline -/

/-- Add guarded revision time as an independent axis to any other mode
theory. -/
abbrev withGuardedTime (other : ModeTheory) : ModeTheory :=
  product other revisionModes

/-- Any other modality commutes with one guarded tick in the product mode
theory. -/
theorem other_modality_commutes_with_guard
    {other : ModeTheory} {source target : other.Mode}
    (modality : other.Hom source target) (revision : Nat) :
    (withGuardedTime other).comp
        (product.alongFirst (first := other) (second := revisionModes)
          (revision + 1) modality)
        (product.alongSecond (first := other) (second := revisionModes)
          target (guard revision)) =
      (withGuardedTime other).comp
        (product.alongSecond (first := other) (second := revisionModes)
          source (guard revision))
        (product.alongFirst (first := other) (second := revisionModes)
          revision modality) :=
  product.axes_commute modality (guard revision)

#print axioms later_iff_strict_modal
#print axioms lob
#print axioms finite_lob
#print axioms same_modes_distinct_guard_costs
#print axioms other_modality_commutes_with_guard

end Mettapedia.TypeTheory.GuardedTimeModeTheory
