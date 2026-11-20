import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Definitions.Extension

/-!
# The definition as a constant computes by its own rules

The package extended by addition by rows and by append over it (`addAppendDev`) runs its calls by its
own table: the first row that matches fires (`devRoot`), with β, the projections and the subterms in
source order (`devNormalize`); what the run returns is reached by the extended package's steps
(`devNormalize_sound`).

* `add 2 1` runs to `3`, and `append num 1 1 [2] [3]` runs to `[2, 3]` (`addAppend_runs`), by kernel
  evaluation.
* **That is the call's only answer** in the extended package (`append_answer`): `[2, 3]` is normal
  there, because a step of the extension from a term without the new constants is a step of the
  package (`dev_step_old`), and answers are unique because the extension is Church–Rosser.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.Definitions

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open AlgebraicSchema
open ConversionCoherence (StepStar)
open TowerVectorsModel (numC zeroC succC ttC)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (level1 pkg)
open ProgrammingOnTheStep.IndexedFamilies.ClosedCalls (one two three single twoThree)

/-- **The root evaluator of the extended package**: the first row of its table that matches fires. -/
def devRoot (dev : Development) (rows : SchemaTable Tower.Head) :
    ExecutableReduction.RootEvaluator (devPackage dev rows) := fun {_} source =>
  match ExecutableSchemaSelection.first (Vectors.vectorEquations ++ rows) source with
  | .fired receipt _ => some ⟨receipt.target, Or.inr receipt.semantic_step⟩
  | .unassigned _ _ => none
  | .missed => none

/-- The term the extended package's executable reduction reaches within a budget. -/
def devNormalize (dev : Development) (rows : SchemaTable Tower.Head) (fuel : Nat) {n : Nat}
    (t : Tower.Tm n) : Option (Tower.Tm n) :=
  ExecutableReduction.normalizeTerm (devPackage dev rows) (devRoot dev rows) fuel t

/-- **What the run returns is reached by the extended package's steps.** -/
theorem devNormalize_sound {dev : Development} {rows : SchemaTable Tower.Head} {fuel n : Nat}
    {t v : Tower.Tm n} (ran : devNormalize dev rows fuel t = some v) : StepStar (devPackage dev rows) t v :=
  ExecutableReduction.normalizeTerm_sound _ _ ran

/-- Addition by rows, then append over it. -/
abbrev addAppendDev : Development := [(addName, addDef), (appendName, appendOnAddDef)]

/-- Their rules. -/
abbrev addAppendRows : SchemaTable Tower.Head :=
  [⟨1, (spine (.const addName) [zeroC, .var 0], .var 0)⟩,
    ⟨2, (spine (.const addName) [succC (.var 1), .var 0], succC (spine (.const addName) [.var 1, .var 0]))⟩,
    ⟨4, (spine (.const appendName) [.var 3, zeroC, .var 2, .var 1, .var 0], .var 0)⟩,
    ⟨5, (spine (.const appendName) [.var 4, succC (.var 3), .var 2, .var 1, .var 0],
      .pair (.fst (.var 1)) (spine (.const appendName) [.var 4, .var 3, .var 2, .snd (.var 1), .var 0]))⟩]

/-- **The calls run by the new rules**: `add 2 1` to `3`, `append num 1 1 [2] [3]` to `[2, 3]`. -/
theorem addAppend_runs :
    devNormalize addAppendDev addAppendRows 30 (spine (.const addName) [two, one] : Tower.Tm 0) = some three ∧
    devNormalize addAppendDev addAppendRows 60
      (spine (.const appendName) [numC, one, one, single two, single three] : Tower.Tm 0) = some twoThree := by
  decide +kernel

/-- `[2, 3]` mentions neither new constant. -/
theorem twoThree_old : OldTerm addAppendDev (twoThree : Tower.Tm 0) := by
  intro e member
  simp only [addAppendDev, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact constFreeB_sound (by decide +kernel)
  · exact constFreeB_sound (by decide +kernel)

/-- **`append num 1 1 [2] [3]` has exactly one answer in the extended package, `[2, 3]`.** -/
theorem append_answer :
    Answer (devPackage addAppendDev addAppendRows)
        (spine (.const appendName) [numC, one, one, single two, single three] : Tower.Tm 0) twoThree ∧
      ∀ v, Answer (devPackage addAppendDev addAppendRows)
        (spine (.const appendName) [numC, one, one, single two, single three] : Tower.Tm 0) v → v = twoThree := by
  have found : devRules addAppendDev = some addAppendRows := addAppend_rules
  obtain ⟨rows', found', -, -, table⟩ := devCheck_parts addAppend_devCheck
  rw [found] at found'
  obtain rfl := Option.some.inj found'
  have normal : ConstructorSystem.Normal (devPackage addAppendDev addAppendRows) (twoThree : Tower.Tm 0) := by
    intro target step
    obtain ⟨baseStep, -⟩ := dev_step_old addAppend_devCheck found step twoThree_old
    exact Vectors.twoThree_normal baseStep
  have answer : Answer (devPackage addAppendDev addAppendRows)
      (spine (.const appendName) [numC, one, one, single two, single three] : Tower.Tm 0) twoThree :=
    ⟨devNormalize_sound addAppend_runs.2, normal⟩
  exact ⟨answer, fun v other => answer_unique (dev_churchRosser table) other answer⟩

end NativeTypesOnTheStep.Computing.Definitions

#print axioms NativeTypesOnTheStep.Computing.Definitions.devRoot
#print axioms NativeTypesOnTheStep.Computing.Definitions.devNormalize_sound
#print axioms NativeTypesOnTheStep.Computing.Definitions.addAppend_runs
#print axioms NativeTypesOnTheStep.Computing.Definitions.twoThree_old
#print axioms NativeTypesOnTheStep.Computing.Definitions.append_answer

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
