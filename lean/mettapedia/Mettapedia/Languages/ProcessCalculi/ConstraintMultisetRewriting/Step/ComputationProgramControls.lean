import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationVectorProgram
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationAppendConsumer
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationBinderControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Vectors.QualifiedControls

/-!
# One fixed program, several computations, and an excluded native firing

The fourteen-row package table is the same for the addition, binder and
compiled-append consumers. All target runs are restricted by that program.
A native typed resource update from zero to one is admitted by the full
step but excluded by this program. Qualification has real content: the
already proved overlapping table cannot have a qualified setting.

The head-equality policy here is semantic. Root/binder replay controls in
the imported modules do not consult it. This does not claim an executable
algorithm for arbitrary semantic universe equations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProgram.Controls

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull
open NativeTypesOnTheStep.Computing
open TowerVectorsModel (zeroC succC)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (pkg D numType level1)

local instance headPolicy : DecidableRel setting.R.headEq := Classical.decRel _

theorem addition_has_program_run :
    ∃ run : (restricted program qualified).Run ComputationProfile.Controls.start.state,
      ∃ active, run.last.present = {active} ∧
        readout run.last active = ⟨0, zeroC⟩ ∧ ConstructorSystem.Normal pkg (zeroC : Tower.Tm 0) :=
  (answers_by_program_iff program qualified ComputationProfile.Controls.start rfl zeroC).mp
    ComputationProfile.Controls.source_answer_and_actual_run.1

theorem binder_program_keeps_events :
    (programRun program qualified ComputationProfile.BinderControls.program).word.length = 1 :=
  programRun_events program qualified ComputationProfile.BinderControls.program

theorem append_has_program_run :
    ∃ run : (restricted program qualified).Run ComputationProfile.CheckedDefinitions.appendInput.state,
      ∃ active, run.last.present = {active} ∧
        readout run.last active = ⟨0, ProgrammingOnTheStep.IndexedFamilies.ClosedCalls.twoThree⟩ ∧
        ConstructorSystem.Normal pkg (ProgrammingOnTheStep.IndexedFamilies.ClosedCalls.twoThree : Tower.Tm 0) :=
  (answers_by_program_iff program qualified ComputationProfile.CheckedDefinitions.appendInput rfl _).mp
    ComputationProfile.CheckedDefinitions.append_answer

abbrev finished := ComputationProfile.Controls.finish

def oneRow : TotalTerm finished.state.frame :=
  ⟨numType _, ⟨succC zeroC, D.succ_typed D.zero_typed⟩⟩

def unrelated : Firing setting.levels finished.state :=
  ComputationResources.firing setting.levels finished.state finished.active 1 oneRow

theorem unrelated_native_admitted : (step setting.levels Nat).Admits unrelated :=
  (ComputationResources.admitted_iff setting.levels _ _ _ _).mpr
    ⟨finished.present, by decide, finished.consistent⟩

theorem unrelated_program_refused : ¬ (restricted program qualified).Admits unrelated := by
  have normal : ConstructorSystem.Normal pkg finished.code := by
    change ConstructorSystem.Normal pkg ComputationProfile.Controls.program.term
    rw [ComputationProfile.Controls.result_zero]
    exact Vectors.const_normal level1 (by decide)
  exact fun accepted => (normal_iff_no_program_firing program qualified finished (by decide)).mp normal
    ⟨unrelated, accepted⟩

/-- Borrowed qualification counterexample, required before compiling a table. -/
theorem overlapping_table_has_no_qualified_setting {L : Type} [UniverseLevel.LevelOrder L]
    (candidate : Setting Tower.Head L) (same : candidate.R = Vectors.overlapRules level1) : ¬ Qualified candidate :=
  Vectors.overlap_not_qualified level1 candidate same

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProgram.Controls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProgram.Controls.append_has_program_run
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProgram.Controls.unrelated_program_refused
