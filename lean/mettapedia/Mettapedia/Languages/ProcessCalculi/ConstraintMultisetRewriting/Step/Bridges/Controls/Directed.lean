import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.DirectedRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationHeadBoundary

/-!
# Directed native execution and the universe-head stopping boundary

The existing two-addition computation runs through the same two native firings
under the directed restriction, reusing its old physical slot. The universe
head remains a directed answer with no outgoing firing, although the broader
conversion descriptor program admits a head-equality firing there.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.Directed

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual ContextualDependentEta DependentFull
open NativeTypesOnTheStep.Computing
open TowerVectorsModel (U0 zeroC numC)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (pkg level1)
open ComputationProfile.Controls (setting qualified start middle finish first second one_fresh old_slot_free)

abbrev descriptor := ComputationProgram.Controls.program

local instance headPolicy : DecidableRel setting.R.headEq := Classical.decRel _

theorem first_admitted :
    (Bridges.Directed.restricted descriptor qualified).Admits (first.compile qualified 1) :=
  ⟨(first.admitted_iff qualified 1).mpr one_fresh,
    Bridges.Directed.instruction_permitted descriptor qualified first rfl 1⟩

theorem second_admitted :
    (Bridges.Directed.restricted descriptor qualified).Admits (second.compile qualified 0) :=
  ⟨(second.admitted_iff qualified 0).mpr old_slot_free,
    Bridges.Directed.instruction_permitted descriptor qualified second rfl 0⟩

def actualRun : (Bridges.Directed.restricted descriptor qualified).Run start.state :=
  .cons (first.compile qualified 1) first_admitted
    (.cons (second.compile qualified 0) second_admitted (.nil finish.state))

theorem two_actual_firings : actualRun.word.length = 2 := rfl

/-- Restriction changes permission, not the two actual native operations. -/
theorem same_full_run :
    Spaces.toRun (step setting.levels Nat).toStep (Bridges.Directed.permits descriptor qualified) actualRun =
      ComputationProfile.Controls.program.toRun := rfl

theorem old_slot_reused : actualRun.last.present = {0} := by decide

theorem start_represented : Bridges.Directed.Represents (S := setting) start.code start.state :=
  Computation.represents_configuration start rfl

theorem zero_represented : Bridges.Directed.Represents (S := setting) (zeroC : Tower.Tm 0) actualRun.last := by
  refine ⟨0, old_slot_reused, finish.consistent, ?_⟩
  exact congrArg (Sigma.mk 0) (second.next_code qualified 0 old_slot_free)

theorem zero_normal : ContextualDependentExecutableJoin.Normal pkg (zeroC : Tower.Tm 0) :=
  DirectedAnswers.directedNormal_of_normal (Vectors.const_normal level1 (by decide))

theorem two_additions_answer_zero : DirectedAnswers.DirectedAnswer pkg start.code zeroC :=
  (Bridges.Directed.answers_by_run_iff descriptor qualified start_represented).mpr
    ⟨actualRun, zero_represented, zero_normal⟩

theorem delivered_zero_keeps_type : Typed pkg .nil (zeroC : Tower.Tm 0) numC :=
  (Bridges.Directed.run_keeps_type descriptor qualified rfl actualRun zero_represented).1

theorem head_represented :
    Bridges.Directed.Represents (S := setting) (U0 : Tower.Tm 0) ComputationProfile.HeadBoundary.input.state :=
  Computation.represents_configuration ComputationProfile.HeadBoundary.input rfl

theorem head_has_no_directed_firing :
    ¬ ∃ firing : Firing setting.levels ComputationProfile.HeadBoundary.input.state,
      (Bridges.Directed.restricted descriptor qualified).Admits firing :=
  (Bridges.Directed.normal_iff_no_firing descriptor qualified head_represented).mp
    ComputationProfile.HeadBoundary.head_directed_normal

/-- The very same native head-conversion candidate is admitted by the broad program and
refused by the directed program. This is a difference in execution policy, not in typing. -/
theorem head_conversion_excluded :
    (ComputationProgram.restricted descriptor qualified).Admits
        (ComputationProfile.HeadBoundary.instruction.compile qualified 1) ∧
      ¬ (Bridges.Directed.restricted descriptor qualified).Admits
        (ComputationProfile.HeadBoundary.instruction.compile qualified 1) :=
  ⟨ComputationProfile.HeadBoundary.conversion_program_head_firing_admitted,
    fun accepted => head_has_no_directed_firing ⟨_, accepted⟩⟩

theorem head_answers_without_a_firing :
    ∃ run : (Bridges.Directed.restricted descriptor qualified).Run ComputationProfile.HeadBoundary.input.state,
      run.word = [] ∧ Bridges.Directed.Represents (S := setting) (U0 : Tower.Tm 0) run.last ∧
        ContextualDependentExecutableJoin.Normal pkg (U0 : Tower.Tm 0) :=
  ⟨.nil _, rfl, head_represented, ComputationProfile.HeadBoundary.head_directed_normal⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.Directed

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.Directed.same_full_run
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.Directed.two_additions_answer_zero
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.Directed.delivered_zero_keeps_type
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.Directed.head_conversion_excluded
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.Directed.head_answers_without_a_firing
