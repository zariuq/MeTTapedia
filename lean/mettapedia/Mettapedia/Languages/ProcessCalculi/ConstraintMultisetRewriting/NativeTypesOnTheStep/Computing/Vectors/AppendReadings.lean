import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Vectors.QualifiedControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgrammingOnTheStep.IndexedFamilies.ClosedCalls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableSchemaSelection

/-!
# The two readings of `append` in the qualified vectors package

**The rows, executed.** The tree's source-ordered schema selection matches a term against the fourteen
rows of the package and fires the first that matches (`vecRoot`); every firing is a step of the package,
by the rows' soundness (`table_step`). With β and the projections it is the package's executable
reduction (`vecReducer`, `vecNormalize`): what it returns within its budget is reached by computation
(`vecNormalize_sound`). Running out of budget is its own outcome (`ground_budget`), never a refusal.

**The two readings agree on this package**, because it is qualified, hence Church–Rosser:

* an answer reached by firings is exactly a conversion normal form (`vectors_answer_iff`);
* it is unique (`vectors_answer_unique`);
* it has the call's type and is typed-equal to the call (`Vectors.vectors_answer_typed`).

**Kernel-checked control.** The written-out call `append num 1 1 [2] [3]` is run by the executable
reduction, evaluated by the kernel, to `[2, 3]` (`ground_runs`). That is its answer
(`ground_answer`), its only one (`ground_answer_unique`; `[3, 2]` is not, `ground_not_swapped`),
equivalently its conversion normal form (`ground_two_readings`), and it is typed at the call's
declared type `vec num (add 1 1)`, typed-equal to the call there (`ground_answer_typed`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.Vectors

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open AlgebraicSchema AlgebraicParallel ConversionCoherence
open ConstructorSystem (ConstructorPresentation)
open TowerNumbersModel (num zero succ numRec ctors u)
open TowerVectorsModel (unit tt add U0 numC zeroC succC unitC ttC vecC addC)
open TowerVectorsPrograms (appendTm)

variable (lv : LevelExpr Nat)

/-! ## The rows, executed -/

/-- **A firing of a row is a step of the package.** -/
theorem table_step {n : Nat} {l r : Tower.Tm n}
    (step : (SchemaFamily.computation vectorEquations.family).step l r) :
    (TowerVectorsModel.rules lv).computation.step l r := by
  cases step with
  | instantiate rule σ => exact vector_sound lv rule σ

/-- **The root evaluator of the package**: the first row whose left side matches fires. -/
def vecRoot : ExecutableReduction.RootEvaluator (TowerVectorsModel.rules lv) := fun {_} source =>
  match ExecutableSchemaSelection.first vectorEquations source with
  | .fired receipt _ => some ⟨receipt.target, table_step lv receipt.semantic_step⟩
  | .unassigned _ _ => none
  | .missed => none

/-- **The executable reduction of the package**: rows at the root first, then β, the projections
and the subterms in source order, within a budget. -/
def vecReducer : ExecutableReduction.Reducer (TowerVectorsModel.rules lv) :=
  ExecutableReduction.normalize (TowerVectorsModel.rules lv) (vecRoot lv)

/-- The term reached within a budget. -/
def vecNormalize (fuel : Nat) {n : Nat} (t : Tower.Tm n) : Option (Tower.Tm n) :=
  ExecutableReduction.normalizeTerm (TowerVectorsModel.rules lv) (vecRoot lv) fuel t

/-- **What the reduction returns is reached by computation.** -/
theorem vecNormalize_sound {fuel n : Nat} {t v : Tower.Tm n} (ran : vecNormalize lv fuel t = some v) :
    StepStar (TowerVectorsModel.rules lv) t v :=
  ExecutableReduction.normalizeTerm_sound _ _ ran

/-! ## The two readings agree on the package -/

/-- **An answer by firings is exactly a conversion normal form.** -/
theorem vectors_answer_iff {n : Nat} {t v : Tower.Tm n} :
    Answer (TowerVectorsModel.rules lv) t v ↔
      Conv (TowerVectorsModel.rules lv).headEq t v (TowerVectorsModel.rules lv).computation ∧
        ConstructorSystem.Normal (TowerVectorsModel.rules lv) v :=
  answer_iff (vectors_churchRosser lv)

/-- **Answers are unique.** -/
theorem vectors_answer_unique {n : Nat} {t v v' : Tower.Tm n}
    (answer : Answer (TowerVectorsModel.rules lv) t v) (answer' : Answer (TowerVectorsModel.rules lv) t v') :
    v = v' :=
  answer_unique (vectors_churchRosser lv) answer answer'

/-! ## Normal forms of written-out vectors -/

/-- A constant that is not defined has no step. -/
theorem const_normal {n : Nat} {c : DeclName} (undefined : vectorDefined c = false) :
    ConstructorSystem.Normal (TowerVectorsModel.rules lv) (.const c : Tower.Tm n) := by
  intro target step
  cases step with
  | root h => exact no_root_of_undefined lv rfl undefined h

/-- The numerals are normal. -/
theorem succ_normal {n : Nat} {t : Tower.Tm n} (normal : ConstructorSystem.Normal (TowerVectorsModel.rules lv) t) :
    ConstructorSystem.Normal (TowerVectorsModel.rules lv) (succC t) := by
  intro target step
  cases step with
  | root h => exact no_root_of_undefined lv rfl (by decide) h
  | congAppFun inner => exact const_normal lv (by decide) inner
  | congAppArg inner => exact normal inner

/-- A pair of normal terms is normal. -/
theorem pair_normal {n : Nat} {a b : Tower.Tm n} (normalA : ConstructorSystem.Normal (TowerVectorsModel.rules lv) a)
    (normalB : ConstructorSystem.Normal (TowerVectorsModel.rules lv) b) :
    ConstructorSystem.Normal (TowerVectorsModel.rules lv) (.pair a b) := by
  intro target step
  cases step with
  | root h => exact (vectorConstructors lv).no_root_of_spineHead h rfl
  | congPairFst inner => exact normalA inner
  | congPairSnd inner => exact normalB inner

/-! ## Kernel-checked control: `append num 1 1 [2] [3]` -/

section Ground

open ProgrammingOnTheStep.IndexedFamilies.ClosedCalls (one two three single twoThree closedCall_typed)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (level1)

/-- The written-out call `append num 1 1 [2] [3]`. -/
abbrev groundCall : Tower.Tm 0 := appendTm numC one one (single two) (single three)

/-- **Run by the kernel**: the executable reduction takes the call to `[2, 3]`. -/
theorem ground_runs : vecNormalize level1 40 groundCall = some twoThree := by decide +kernel

/-- **A budget that runs out is its own outcome**: at budget three the run has not finished. -/
theorem ground_budget : vecNormalize level1 3 groundCall = none := by decide +kernel

theorem twoThree_normal : ConstructorSystem.Normal (TowerVectorsModel.rules level1) (twoThree : Tower.Tm 0) :=
  pair_normal level1
    (succ_normal level1 (succ_normal level1 (const_normal level1 (by decide))))
    (pair_normal level1
      (succ_normal level1 (succ_normal level1 (succ_normal level1 (const_normal level1 (by decide)))))
      (const_normal level1 (by decide)))

/-- **`[2, 3]` is the call's answer by firings.** -/
theorem ground_answer : Answer (TowerVectorsModel.rules level1) groundCall twoThree :=
  ⟨vecNormalize_sound level1 ground_runs, twoThree_normal⟩

/-- **It is the only answer.** -/
theorem ground_answer_unique (v : Tower.Tm 0) :
    Answer (TowerVectorsModel.rules level1) groundCall v ↔ v = twoThree :=
  ⟨fun answer => vectors_answer_unique level1 answer ground_answer, fun same => same ▸ ground_answer⟩

/-- **Negative control**: `[3, 2]` is not an answer of the call. -/
theorem ground_not_swapped :
    ¬ Answer (TowerVectorsModel.rules level1) groundCall (.pair three (single two)) := fun answer =>
  absurd ((ground_answer_unique _).mp answer) (by decide)

/-- **The two readings of the call coincide**: its answer by firings is its conversion normal form. -/
theorem ground_two_readings :
    Conv (TowerVectorsModel.rules level1).headEq groundCall twoThree
        (TowerVectorsModel.rules level1).computation ∧
      ConstructorSystem.Normal (TowerVectorsModel.rules level1) (twoThree : Tower.Tm 0) :=
  (vectors_answer_iff level1).mp ground_answer

/-- **The answer has the call's declared type**, `vec num (add 1 1)`, and is typed-equal to the call
there. -/
theorem ground_answer_typed :
    Typed (TowerVectorsModel.rules level1) .nil twoThree (vecC numC (addC one one)) ∧
      Equal (TowerVectorsModel.rules level1) .nil groundCall twoThree (vecC numC (addC one one)) :=
  vectors_answer_typed level1 .nil closedCall_typed ground_answer

end Ground

end NativeTypesOnTheStep.Computing.Vectors

#print axioms NativeTypesOnTheStep.Computing.Vectors.table_step
#print axioms NativeTypesOnTheStep.Computing.Vectors.vecRoot
#print axioms NativeTypesOnTheStep.Computing.Vectors.vecReducer
#print axioms NativeTypesOnTheStep.Computing.Vectors.vecNormalize_sound
#print axioms NativeTypesOnTheStep.Computing.Vectors.vectors_answer_iff
#print axioms NativeTypesOnTheStep.Computing.Vectors.vectors_answer_unique
#print axioms NativeTypesOnTheStep.Computing.Vectors.const_normal
#print axioms NativeTypesOnTheStep.Computing.Vectors.succ_normal
#print axioms NativeTypesOnTheStep.Computing.Vectors.pair_normal
#print axioms NativeTypesOnTheStep.Computing.Vectors.ground_runs
#print axioms NativeTypesOnTheStep.Computing.Vectors.ground_budget
#print axioms NativeTypesOnTheStep.Computing.Vectors.twoThree_normal
#print axioms NativeTypesOnTheStep.Computing.Vectors.ground_answer
#print axioms NativeTypesOnTheStep.Computing.Vectors.ground_answer_unique
#print axioms NativeTypesOnTheStep.Computing.Vectors.ground_not_swapped
#print axioms NativeTypesOnTheStep.Computing.Vectors.ground_two_readings
#print axioms NativeTypesOnTheStep.Computing.Vectors.ground_answer_typed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
