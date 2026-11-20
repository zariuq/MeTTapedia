import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationVectorProgram
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationInputs
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentExecutableJoin

/-!
# Conversion-path normality and evaluator normality differ

StepCore includes semantic universe-head equalities, including a reflexive
one. Its ConstructorSystem.Normal therefore excludes a universe head. The
existing executable evaluator instead uses directed reductions, excluding
head equality, and returns that head unchanged. These are two different
normality contracts, not two contradictory normalization theorems.

The broad descriptor program represents conversion-path steps as declared.
It has a head-equality firing even at this evaluator normal form. A runtime
must use its evaluator's directed stopping contract, rather than equating
it with quiescence of this broader program.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.HeadBoundary

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull
open NativeTypesOnTheStep.Computing
open TowerVectorsModel (U0)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (pkg D level1)

abbrev setting := Controls.setting
abbrev qualified := Controls.qualified
abbrev presentation := Controls.presentation

local instance headPolicy : DecidableRel setting.R.headEq := Classical.decRel _

theorem head_reflexive : pkg.headEq (.sort (.const 0)) (.sort (.const 0)) := fun _ => rfl

theorem head_self_step : StepCore pkg.computation pkg.headEq (U0 : Tower.Tm 0) U0 :=
  .head head_reflexive

theorem head_not_conversion_path_normal : ¬ ConstructorSystem.Normal pkg (U0 : Tower.Tm 0) :=
  fun normal => normal head_self_step

theorem every_head_reflexive (head : Tower.Head) : pkg.headEq head head := by
  cases head with
  | legacyGround => trivial
  | sort level => exact fun _ => rfl

theorem head_reachable_only_head {target : Tower.Tm 0}
    (steps : ConversionCoherence.StepStar pkg U0 target) :
    ∃ head : Tower.Head, target = .head head := by
  induction steps with
  | refl => exact ⟨.sort (.const 0), rfl⟩
  | tail _ last ih =>
    obtain ⟨head, rfl⟩ := ih
    cases last with
    | head _ => exact ⟨_, rfl⟩
    | root root => exact False.elim ((Vectors.vectorConstructors level1).no_root_of_spineHead root rfl)

theorem head_has_no_conversion_path_answer : ¬ ∃ value, Answer pkg (U0 : Tower.Tm 0) value := by
  rintro ⟨value, reached, normal⟩
  obtain ⟨head, rfl⟩ := head_reachable_only_head reached
  exact normal (.head (every_head_reflexive head))

/-- The all-closed-terms premise of the older answer-existence reduction is false. -/
theorem full_answer_totality_false :
    ¬ (∀ {term type : Tower.Tm 0}, Typed pkg .nil term type → ∃ value, Answer pkg term value) :=
  fun total => head_has_no_conversion_path_answer (total D.tower.u0_typed)

theorem head_directed_normal : ContextualDependentExecutableJoin.Normal pkg (U0 : Tower.Tm 0) := by
  intro target reduction
  cases reduction with
  | head impossible => cases impossible
  | root root => exact (Vectors.vectorConstructors level1).no_root_of_spineHead root rfl

theorem evaluator_returns_head : Vectors.vecNormalize level1 1 (U0 : Tower.Tm 0) = some U0 := by
  decide +kernel

theorem normalizer_result_is_not_old_answer :
    Vectors.vecNormalize level1 1 (U0 : Tower.Tm 0) = some U0 ∧ ¬ Answer pkg (U0 : Tower.Tm 0) U0 :=
  ⟨evaluator_returns_head, fun answer => head_not_conversion_path_normal answer.2⟩

def input : Configuration (S := setting) := Configuration.ofTyped (empty pkg) D.tower.u0_typed

def instruction : Instruction presentation input :=
  ⟨⟨0, .hole, .head (.sort (.const 0)) (.sort (.const 0)) head_reflexive⟩, rfl⟩

theorem native_head_firing_admitted :
    (step setting.levels Nat).Admits (instruction.compile qualified 1) :=
  (instruction.admitted_iff qualified 1).mpr (by decide)

theorem conversion_program_head_firing_admitted :
    (ComputationProgram.restricted ComputationProgram.Controls.program qualified).Admits
      (instruction.compile qualified 1) :=
  ⟨native_head_firing_admitted,
    ComputationProgram.instruction_permitted ComputationProgram.Controls.program qualified instruction 1⟩

theorem directed_normality_does_not_mean_all_conversion_firings_halt :
    ContextualDependentExecutableJoin.Normal pkg input.code ∧
      (step setting.levels Nat).Admits (instruction.compile qualified 1) :=
  ⟨head_directed_normal, native_head_firing_admitted⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.HeadBoundary

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.HeadBoundary.normalizer_result_is_not_old_answer
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.HeadBoundary.directed_normality_does_not_mean_all_conversion_firings_halt
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.HeadBoundary.full_answer_totality_false
