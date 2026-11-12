import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorCoreWeightChanceControls

/-!
# Control: separated runs whose survivals are correlated

Two runs that check the absence of the same label `9`, on disjoint configurations:

* `unlessNineRun` at the occurrence `5`, which makes the occurrence `7`;
* `eightRun` at the occurrence `6`, which makes the occurrence `8`.

They are **separated** (`separated`): disjoint spaces, each blind to the other's space, consistent
joint store. So they commute inside their tensor (`they_commute`), and the four-block law holds for
them: they need no coordination. Yet both forbid the fact `9`, so in a common random surrounding
where `9` has positive probability and no fact is certain, their survivals are **strictly
positively correlated** (`separated_yet_correlated`).

Probabilistic independence of survivals is therefore not the absence of a need for coordination.
The probabilistic face of separation is another independence: what one run writes is independent
of the other's survival (`write_read_eq_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore.SeparatedControls

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Logic.LinearLogic.KnowledgeTensorWeight
open AnnotatedRuns (Firing firstOrder firstOrderTransport)
open FirstOrderNativeRuns
open KnowledgeTensorFirstOrderControls (plain one)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore.Controls
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore.ChanceControls

/-- The occurrence `6` alone. -/
def six : Configuration Nat Nat := ⟨[], {6}⟩

/-- Checks that nothing labelled `9` is present, and makes the occurrence `8`. -/
def unlessNineEight : Firing Nat Unit Nat :=
  ⟨⟨[], [], [], [Check.absent 9], [8]⟩, [], ⟨[], [], [8]⟩⟩

theorem eight_admitted : unlessNineEight.Valid plain id six := by
  refine ⟨⟨List.nodup_nil, List.nodup_singleton 8, rfl, rfl, rfl, by decide, ⟨(), ?_⟩, ?_⟩, ?_⟩
  · intro equation member
    cases member
  · intro check member σ _
    have which : check = Check.absent 9 := List.mem_singleton.mp member
    subst which
    intro o present
    have same : o = 6 := Finset.mem_singleton.mp present
    rw [same]
    exact (by decide : (9 : Nat) ≠ 6)
  · intro query member
    cases member

/-- The run of `unlessNineEight` at the occurrence `6`. -/
def eightRun : (firstOrder plain id).toStep.Run six := .cons unlessNineEight eight_admitted (.nil _)

/-- Its one-firing grade beside a surrounding: neither the fact `8` nor `9`. -/
theorem eight_graded (S : Finset (Fin 10)) :
    ((contextualRunInterpretation plain id).domain (left := six) (right := surroundingOf S)
        PUnit.unit unlessNineEight ∧
      (contextualRunInterpretation plain id).check (left := six) (right := surroundingOf S)
        PUnit.unit unlessNineEight) ↔
    Disjoint S {8, 9} := by
  have solved : plain.Models () (unlessNineEight.selection.problem id unlessNineEight.rule
      (AnnotatedRuns.tensor six (surroundingOf S))) := by
    intro equation member
    cases member
  rw [Finset.disjoint_insert_right, Finset.disjoint_singleton_right]
  constructor
  · rintro ⟨_, fresh, _, guards, _⟩
    refine ⟨fun eight => ?_, fun nine => ?_⟩
    · have inside : (8 : ℕ) ∈ (surroundingOf S).present := mem_surroundingOf.mpr ⟨8, eight, rfl⟩
      exact Finset.disjoint_left.mp fresh (by decide) inside
    · have inside : (9 : ℕ) ∈ six.present ∪ (surroundingOf S).present :=
        Finset.mem_union_right _ (mem_surroundingOf.mpr ⟨9, nine, rfl⟩)
      exact guards (Check.absent 9) (List.mem_singleton_self _) () solved 9 inside rfl
  · rintro ⟨eight, nine⟩
    refine ⟨?_, ?_, ⟨(), solved⟩, ?_, ?_⟩
    · show Disjoint ([] : List ℕ).toFinset (surroundingOf S).present
      simp
    · show Disjoint ([8] : List ℕ).toFinset (surroundingOf S).present
      rw [Finset.disjoint_left]
      intro o made inside
      have isEight : o = 8 := by simpa using made
      subst isEight
      obtain ⟨a, member, value⟩ := mem_surroundingOf.mp inside
      have same : a = 8 := Fin.ext value
      exact eight (same ▸ member)
    · intro check member σ _
      obtain rfl := List.mem_singleton.mp member
      intro o inside matched
      have nineIs : (9 : ℕ) = o := matched
      subst nineIs
      rcases Finset.mem_union.mp inside with home | around
      · exact absurd home (by decide)
      · obtain ⟨a, member, value⟩ := mem_surroundingOf.mp around
        have same : a = 9 := Fin.ext value
        exact nine (same ▸ member)
    · intro query member
      cases member

theorem eight_absence_along :
    AbsenceAlong (contextualRunInterpretation plain id) surroundingOf (fun _ => PUnit.unit)
      eightRun {8, 9} := by
  have shape : ({8, 9} : Finset (Fin 10)) = {8, 9} ∪ ∅ := (Finset.union_empty _).symm
  rw [shape]
  exact AbsenceAlong.cons eight_graded (AbsenceAlong.nil _)

/-! ## Separated -/

/-- **The two runs are separated.** -/
theorem separated :
    AnnotatedRuns.Separated plain id one [unlessNineFiring] six [unlessNineEight] := by
  refine ⟨⟨unless_nine_admitted, ⟨(), fun _ member => by cases member⟩⟩,
    ⟨eight_admitted, ⟨(), fun _ member => by cases member⟩⟩, by decide, ?_, ?_,
    ⟨(), fun _ member => by cases member⟩⟩
  · intro f member
    obtain rfl := List.mem_singleton.mp member
    refine ⟨fun check inChecks pattern scanned σ o inSpace matched => ?_,
      fun query inQueries => by cases inQueries⟩
    obtain rfl := List.mem_singleton.mp inChecks
    have isNine : pattern = 9 := (Option.some.inj scanned).symm
    subst isNine
    have isO : (9 : ℕ) = o := matched
    subst isO
    exact absurd inSpace (by decide)
  · intro g member
    obtain rfl := List.mem_singleton.mp member
    refine ⟨fun check inChecks pattern scanned σ o inSpace matched => ?_,
      fun query inQueries => by cases inQueries⟩
    obtain rfl := List.mem_singleton.mp inChecks
    have isNine : pattern = 9 := (Option.some.inj scanned).symm
    subst isNine
    have isO : (9 : ℕ) = o := matched
    subst isO
    exact absurd inSpace (by decide)

/-- **They commute**: the two orders of their tensor are one trace. -/
theorem they_commute :
    AnnotatedRuns.RoundEquiv plain id (AnnotatedRuns.tensor one six)
      ([unlessNineFiring] ++ [unlessNineEight]) ([unlessNineEight] ++ [unlessNineFiring]) :=
  AnnotatedRuns.tensor_interchange plain id one [unlessNineFiring] six [unlessNineEight] separated

/-! ## Correlated -/

/-- The run of `unlessNine` survives a surrounding. -/
def survivesFive (S : Finset (Fin 10)) : Prop :=
  (contextualRunInterpretation plain id).Checks (left := one) (right := surroundingOf S)
    PUnit.unit unlessNineRun

/-- The run of `unlessNineEight` survives a surrounding. -/
def survivesSix (S : Finset (Fin 10)) : Prop :=
  (contextualRunInterpretation plain id).Checks (left := six) (right := surroundingOf S)
    PUnit.unit eightRun

theorem survivesFive_iff (S : Finset (Fin 10)) : survivesFive S ↔ Disjoint S {7, 9} :=
  AbsenceAlong.checks_iff (contextualRunInterpretation plain id) surroundingOf
    unless_nine_absence_along S

theorem survivesSix_iff (S : Finset (Fin 10)) : survivesSix S ↔ Disjoint S {8, 9} :=
  AbsenceAlong.checks_iff (contextualRunInterpretation plain id) surroundingOf eight_absence_along S

/-- **Separated, yet strictly correlated.** -/
theorem separated_yet_correlated (p : Fin 10 → ℝ) (probability : ∀ a, 0 ≤ p a ∧ p a ≤ 1)
    (uncertain : ∀ a, p a < 1) (nine : 0 < p 9) :
    AnnotatedRuns.Separated plain id one [unlessNineFiring] six [unlessNineEight] ∧
      measure p survivesFive * measure p survivesSix <
        measure p (fun S => survivesFive S ∧ survivesSix S) := by
  refine ⟨separated, ?_⟩
  rw [measure_congr p (G := survivesFive) (H := fun S => Disjoint S {7, 9}) survivesFive_iff,
    measure_congr p (G := survivesSix) (H := fun S => Disjoint S {8, 9}) survivesSix_iff,
    measure_congr p (G := fun S => survivesFive S ∧ survivesSix S)
      (H := fun S => Disjoint S {7, 9} ∧ Disjoint S {8, 9})
      (fun S => and_congr (survivesFive_iff S) (survivesSix_iff S))]
  refine lt_of_le_of_ne (harris_absence p probability _ _) fun same => ?_
  have zero := (harris_absence_eq_iff_of_uncertain p probability uncertain _ _).mp same 9
    (by decide)
  linarith

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore.SeparatedControls
