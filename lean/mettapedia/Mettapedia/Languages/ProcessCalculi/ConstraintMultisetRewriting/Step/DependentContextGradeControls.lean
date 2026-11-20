import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentContextRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RunRearrangementRawSuffix
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullControls

/-!
# A native dependent trace whose two orders have different context grades

The checker accepts at most one matching occurrence. The eraser consumes
occurrence zero. Both orders run from the one-row state. Beside occurrence
one, erasing first still runs, while checking first fails. The query is the
actual natural typed collect query with a bounded-cardinality answer.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ContextGradeControls

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull.Controls
open ContextPlacement

def atMost (bound : Nat) : NaturalQuery setting.levels Nat base :=
  { NaturalQuery.count setting.levels Nat (baseState.label 0) bound with answer := fun seen => seen.card ≤ bound }

theorem region_self (bound : Nat) {observer : Context Tower.rules} (solution : observer ⟶ base) :
    (atMost bound).toQuery.region solution (baseState.label 0) :=
  ⟨_, List.mem_singleton_self _, ((frames setting.levels).equivalence _).refl _⟩

theorem atMost_holds (bound : Nat) (present : Finset Nat) {observer : Context Tower.rules}
    (solution : observer ⟶ base) :
    (atMost bound).toQuery.Holds present baseState.label solution ↔ present.card ≤ bound := by
  constructor
  · rintro ⟨seen, members, accepted⟩
    have same : seen = present := Finset.ext fun occurrence =>
      ⟨fun member => ((members occurrence).mp member).1,
        fun member => (members occurrence).mpr ⟨member, region_self bound solution⟩⟩
    change seen.card ≤ bound at accepted
    exact same ▸ accepted
  · intro accepted
    exact ⟨present, fun occurrence =>
      ⟨fun member => ⟨member, region_self bound solution⟩, fun member => member.1⟩, accepted⟩

def start : State Tower.rules Nat := { baseState with present := {0} }

def checker : HelperFiring setting.levels Nat start :=
  ⟨.nil _, ⟨[], [], [], [], [], [], [], [atMost 1]⟩⟩

def eraser : HelperFiring setting.levels Nat start :=
  ⟨.nil _, ⟨[0], [], [start.label 0], [], [], [], [], []⟩⟩

theorem checker_admitted : (helperStep setting.levels Nat).Admits checker := by
  refine ⟨⟨List.nodup_nil, List.nodup_nil, rfl, rfl, fun _ member => absurd member List.not_mem_nil⟩,
    (enabled_iff _).mpr ?_, ⟨_, 𝟙 _, fun _ member => absurd member List.not_mem_nil⟩, ?_⟩
  · exact ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil,
      fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩
  · intro observer solution solved
    refine ⟨fun _ member => absurd member List.not_mem_nil, ?_⟩
    intro query member
    obtain rfl := List.mem_singleton.mp member
    exact (atMost_holds 1 {0} solution).mpr (by decide)

theorem eraser_admitted : (helperStep setting.levels Nat).Admits eraser := by
  refine ⟨⟨List.nodup_singleton _, List.nodup_nil, rfl, rfl,
      fun _ member => absurd member List.not_mem_nil⟩, (enabled_iff _).mpr ?_, ?_, ?_⟩
  · refine ⟨?_, fun _ member => absurd member List.not_mem_nil,
      fun _ _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩
    intro occurrence member
    obtain rfl := List.mem_singleton.mp member
    decide
  · refine ⟨_, 𝟙 _, ?_⟩
    intro equation member
    obtain rfl := List.mem_singleton.mp member
    exact ((frames setting.levels).equivalence _).refl _
  · exact fun _ _ _ => ⟨fun _ member => absurd member List.not_mem_nil,
      fun _ member => absurd member List.not_mem_nil⟩

def checkAfterErase := helperResidual eraser eraser_admitted checker
def eraseAfterCheck := helperResidual checker checker_admitted eraser

theorem checkAfterErase_admitted : (helperStep setting.levels Nat).Admits checkAfterErase := by
  refine ⟨⟨List.nodup_nil, List.nodup_nil, rfl, rfl, fun _ member => absurd member List.not_mem_nil⟩,
    (enabled_iff _).mpr ?_, ?_, ?_⟩
  · exact ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil,
      fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩
  · refine ⟨_, 𝟙 _, ?_⟩
    intro equation member
    obtain rfl := List.mem_singleton.mp member
    exact ((frames setting.levels).equivalence _).refl _
  · intro observer solution solved
    refine ⟨fun _ member => absurd member List.not_mem_nil, ?_⟩
    intro query member
    obtain rfl := List.mem_singleton.mp member
    exact (atMost_holds 1 ∅ solution).mpr (by decide)

theorem eraseAfterCheck_admitted : (helperStep setting.levels Nat).Admits eraseAfterCheck := by
  refine ⟨⟨List.nodup_singleton _, List.nodup_nil, rfl, rfl,
      fun _ member => absurd member List.not_mem_nil⟩, (enabled_iff _).mpr ?_, ?_, ?_⟩
  · refine ⟨?_, fun _ member => absurd member List.not_mem_nil,
      fun _ _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩
    intro occurrence member
    obtain rfl := List.mem_singleton.mp member
    decide
  · refine ⟨_, 𝟙 _, ?_⟩
    intro equation member
    obtain rfl := List.mem_singleton.mp member
    exact ((frames setting.levels).equivalence _).refl _
  · exact fun _ _ _ => ⟨fun _ member => absurd member List.not_mem_nil,
      fun _ member => absurd member List.not_mem_nil⟩

def goodRun : (helperStep setting.levels Nat).toStep.Run start :=
  .cons eraser eraser_admitted (.cons checkAfterErase checkAfterErase_admitted (.nil _))

def badRun : (helperStep setting.levels Nat).toStep.Run start :=
  .cons checker checker_admitted (.cons eraseAfterCheck eraseAfterCheck_admitted (.nil _))

def close : PlainIso setting.levels goodRun.last badRun.last where
  frame := Iso.refl _
  knowledge := Frames.Iso.equivalent_refl (X := frames setting.levels) goodRun.last.knowledge
  present := by decide
  label _ := rfl

noncomputable def comparison : (helperTransport setting.levels Nat).InterchangeWitness goodRun badRun :=
  Transport.InterchangeWitness.here (T := helperTransport setting.levels Nat)
    eraser_admitted checker_admitted checkAfterErase_admitted eraseAfterCheck_admitted close (.nil _)

theorem good_grade : RunSafe {1} goodRun := by
  refine ⟨⟨by decide, by decide, ?_⟩, ⟨⟨by decide, by decide, ?_⟩, True.intro⟩⟩
  · intro observer solution solved query member
    exact False.elim (List.not_mem_nil member)
  · intro observer solution solved query member old
    obtain rfl := List.mem_singleton.mp member
    exact (atMost_holds 1 {1} solution).mpr (by decide)

theorem bad_grade : ¬ RunSafe {1} badRun := by
  intro safe
  have old := (atMost_holds 1 {0} (𝟙 base)).mpr (by decide)
  have after := safe.1.queries base (𝟙 base) (fun _ member => absurd member List.not_mem_nil)
    (atMost 1).toQuery (List.mem_singleton_self _) old
  have impossible : ({0, 1} : Finset Nat).card ≤ 1 := (atMost_holds 1 {0, 1} (𝟙 base)).mp after
  exact (by decide : ¬ (({0, 1} : Finset Nat).card ≤ 1)) impossible

theorem grade_not_trace_invariant :
    (helperTransport setting.levels Nat).TraceEquiv start goodRun badRun ∧
      RunSafe {1} goodRun ∧ ¬ RunSafe {1} badRun :=
  ⟨.rel _ _ (.inl comparison.interchange.toSwap), good_grade, bad_grade⟩

theorem good_placed_run_exists :
    ∃ run : (helperStep setting.levels Nat).toStep.Run (place {1} start), run.last = place {1} goodRun.last :=
  ⟨placeRun {1} goodRun good_grade, placeRun_last {1} goodRun good_grade⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ContextGradeControls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ContextGradeControls.grade_not_trace_invariant
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ContextGradeControls.good_placed_run_exists
