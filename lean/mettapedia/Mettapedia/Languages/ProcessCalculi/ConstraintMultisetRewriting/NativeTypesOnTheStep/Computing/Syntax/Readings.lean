import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Syntax.Qualified
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableSchemaSelection

/-!
# The interpreter, run by the package's rows

**The rows, executed.** The tree's source-ordered schema selection matches a term against the
thirty-six rows of the typed-syntax package and fires the first that matches (`syntaxRoot`); every
firing is a step of the package (`table_step`). With β and the projections it is the package's
executable reduction (`syntaxReducer`, `syntaxNormalize`), whose results are reached by computation
(`syntaxNormalize_sound`).

**Kernel-checked runs.** The interpreter at `add (lit 2) (lit 3)` runs to `5` (`eval_runs`), which is
the call's unique answer (`eval_answer`, `eval_answer_unique`), and `6` is not (`eval_not_six`); the
answer has the call's type `val tnum` and is typed-equal to the call (`eval_answer_typed`). A budget that
runs out is its own outcome (`eval_budget`). The conditional runs at the Booleans:
`eval (ite (iszero (lit 0)) (lit 2) (lit 3))` is `2` (`ite_runs`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.Syntax

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open AlgebraicSchema AlgebraicParallel ConversionCoherence
open ConstructorSystem (ConstructorPresentation)
open TowerNumbersModel (num zero succ numRec ctors u)
open TowerVectorsModel (unit tt unitRec void voidRec add unitCtors U0 numC zeroC succC unitC ttC addC
  unitRecC voidC voidRecC)
open TowerSyntaxModel

variable (lv : LevelExpr Nat)

/-! ## The rows, executed -/

/-- **A firing of a row is a step of the package.** -/
theorem table_step {n : Nat} {l r : Tower.Tm n}
    (step : (SchemaFamily.computation syntaxEquations.family).step l r) : (rules lv).computation.step l r := by
  cases step with
  | instantiate rule σ => exact syntax_sound lv rule σ

/-- **The root evaluator of the package**: the first row whose left side matches fires. -/
def syntaxRoot : ExecutableReduction.RootEvaluator (rules lv) := fun {_} source =>
  match ExecutableSchemaSelection.first syntaxEquations source with
  | .fired receipt _ => some ⟨receipt.target, table_step lv receipt.semantic_step⟩
  | .unassigned _ _ => none
  | .missed => none

/-- **The executable reduction of the package.** -/
def syntaxReducer : ExecutableReduction.Reducer (rules lv) :=
  ExecutableReduction.normalize (rules lv) (syntaxRoot lv)

/-- The term reached within a budget. -/
def syntaxNormalize (fuel : Nat) {n : Nat} (t : Tower.Tm n) : Option (Tower.Tm n) :=
  ExecutableReduction.normalizeTerm (rules lv) (syntaxRoot lv) fuel t

/-- **What the reduction returns is reached by computation.** -/
theorem syntaxNormalize_sound {fuel n : Nat} {t v : Tower.Tm n} (ran : syntaxNormalize lv fuel t = some v) :
    StepStar (rules lv) t v :=
  ExecutableReduction.normalizeTerm_sound _ _ ran

/-- **An answer by firings is exactly a conversion normal form**, and it is unique. -/
theorem syntax_answer_unique {n : Nat} {t v v' : Tower.Tm n} (answer : Answer (rules lv) t v)
    (answer' : Answer (rules lv) t v') : v = v' :=
  answer_unique (syntax_churchRosser lv) answer answer'

/-! ## Normal forms -/

/-- A root step of the package starts at a spine headed by a constant with rows. -/
theorem no_root_of_undefined {n : Nat} {t t' : Tower.Tm n} {c : DeclName} {count : Nat}
    (head : ConstructorSystem.spineHead t = some (c, count)) (undefined : syntaxDefined c = false)
    (step : (rules lv).computation.step t t') : False := by
  obtain ⟨name, k, defined, found⟩ := ConstructorSystem.computation_head (syntaxConstructors lv) step
  rw [head] at found
  cases found
  change syntaxDefined c = true at defined
  rw [undefined] at defined
  cases defined

/-- A constant without a row has no step. -/
theorem const_normal {n : Nat} {c : DeclName} (undefined : syntaxDefined c = false) :
    ConstructorSystem.Normal (rules lv) (.const c : Tower.Tm n) := by
  intro target step
  cases step with
  | root h => exact no_root_of_undefined lv rfl undefined h

/-- The successor of a normal term is normal. -/
theorem succ_normal {n : Nat} {t : Tower.Tm n} (normal : ConstructorSystem.Normal (rules lv) t) :
    ConstructorSystem.Normal (rules lv) (succC t) := by
  intro target step
  cases step with
  | root h => exact no_root_of_undefined lv rfl (by decide) h
  | congAppFun inner => exact const_normal lv (by decide) inner
  | congAppArg inner => exact normal inner

/-- The numerals are normal. -/
theorem numeral_normal {n : Nat} :
    ∀ k : Nat, ConstructorSystem.Normal (rules lv) (TowerSyntaxModel.numeral k : Tower.Tm n)
  | 0 => const_normal lv (by decide)
  | k + 1 => succ_normal lv (numeral_normal k)

/-! ## Kernel-checked runs -/

/-- The level of the runs: the recursors' motives land in the small types. -/
abbrev L0 : LevelExpr Nat := .const 0

/-- The written-out call `eval tnum (add (lit 2) (lit 3))`. -/
abbrev evalCall : Tower.Tm 0 :=
  evalC tnumC (addE (litE (TowerSyntaxModel.numeral 2)) (litE (TowerSyntaxModel.numeral 3)))

/-- **Run by the kernel**: the executable reduction takes the call to `5`. -/
theorem eval_runs : syntaxNormalize L0 200 evalCall = some (TowerSyntaxModel.numeral 5) := by decide +kernel

/-- **A budget that runs out is its own outcome**: at budget three the run has not finished. -/
theorem eval_budget : syntaxNormalize L0 3 evalCall = none := by decide +kernel

/-- **`5` is the call's answer by firings.** -/
theorem eval_answer : Answer (rules L0) evalCall (TowerSyntaxModel.numeral 5) :=
  ⟨syntaxNormalize_sound L0 eval_runs, numeral_normal L0 5⟩

/-- **It is the only answer.** -/
theorem eval_answer_unique (v : Tower.Tm 0) :
    Answer (rules L0) evalCall v ↔ v = TowerSyntaxModel.numeral 5 :=
  ⟨fun answer => syntax_answer_unique L0 answer eval_answer, fun same => same ▸ eval_answer⟩

/-- **Negative control**: `6` is not an answer of the call. -/
theorem eval_not_six : ¬ Answer (rules L0) evalCall (TowerSyntaxModel.numeral 6) := fun answer =>
  absurd ((eval_answer_unique _).mp answer) (by decide)

/-- **The answer has the call's declared type `val tnum`**, and is typed-equal to the call there. -/
theorem eval_answer_typed :
    Typed (rules L0) .nil (TowerSyntaxModel.numeral 5) (valC tnumC) ∧
      Equal (rules L0) .nil evalCall (TowerSyntaxModel.numeral 5) (valC tnumC) :=
  (sq L0).answer_typed .nil
    (TowerSyntaxModel.eval_typed L0 (TowerSyntaxModel.tnum_typed L0)
      (TowerSyntaxModel.add_typed L0
        (TowerSyntaxModel.lit_typed L0 (TowerSyntaxModel.numeral_typed L0 2))
        (TowerSyntaxModel.lit_typed L0 (TowerSyntaxModel.numeral_typed L0 3)))) eval_answer

/-- The conditional at the Booleans: `eval tnum (ite (iszero (lit 0)) (lit 2) (lit 3))`. -/
abbrev iteCall : Tower.Tm 0 :=
  evalC tnumC (iteE (iszeroE (litE (TowerSyntaxModel.numeral 0))) (litE (TowerSyntaxModel.numeral 2))
    (litE (TowerSyntaxModel.numeral 3)))

/-- **Run by the kernel**: the zero test answers true and the conditional takes its first branch. -/
theorem ite_runs : syntaxNormalize L0 200 iteCall = some (TowerSyntaxModel.numeral 2) := by decide +kernel

end NativeTypesOnTheStep.Computing.Syntax

#print axioms NativeTypesOnTheStep.Computing.Syntax.table_step
#print axioms NativeTypesOnTheStep.Computing.Syntax.syntaxNormalize_sound
#print axioms NativeTypesOnTheStep.Computing.Syntax.numeral_normal
#print axioms NativeTypesOnTheStep.Computing.Syntax.eval_runs
#print axioms NativeTypesOnTheStep.Computing.Syntax.eval_budget
#print axioms NativeTypesOnTheStep.Computing.Syntax.eval_answer
#print axioms NativeTypesOnTheStep.Computing.Syntax.eval_answer_unique
#print axioms NativeTypesOnTheStep.Computing.Syntax.eval_not_six
#print axioms NativeTypesOnTheStep.Computing.Syntax.eval_answer_typed
#print axioms NativeTypesOnTheStep.Computing.Syntax.ite_runs

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
