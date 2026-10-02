import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorFamilies
import Mettapedia.Logic.Saturation.RecursiveSynthesis

/-!
# Primitive recursion implemented by native Peano elimination

The source recursion is the executable program in `RecursiveSynthesis`.
The target is the existing Nat declaration and its beta/iota rules. Local
base and step implementations are sufficient to prove computation for every
natural input; no equation for the completed recursive program is assumed.

Directed computation is kept separate from typing and from semantic
universe-head equality. The theorem does not assert normalization of every
well-typed term, nor realization of these declarations by a C runtime.
-/

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativePrimitiveRecursion

open Presentation NativeNaturalVectorFamilies

namespace Source
export Mettapedia.Logic.Saturation.RecursiveSynthesis
  (primitiveRecursion primitiveRecursion_correct half double double_correct)
end Source

variable {n : Nat}

@[simp] private theorem subst0_wk (argument term : Tower.Tm n) :
    subst (subst0 argument) (rename wk term) = term := inst0_rename_wk _ _

/-- Peano representation in the actual native Nat constructors. -/
def numeral (value : Nat) : Tower.Tm n :=
  match value with
  | 0 => zeroTm
  | value + 1 => succApp (numeral value)

@[simp] theorem numeral_zero : (numeral 0 : Tower.Tm n) = zeroTm := rfl

@[simp] theorem numeral_succ (value : Nat) :
    (numeral (value + 1) : Tower.Tm n) = succApp (numeral value) := rfl

theorem numeral_typed (context : Tower.Ctx n) (value : Nat) :
    Presentation.HasType rules context (numeral value) natTm := by
  induction value with
  | zero => exact zeroTm_hasType
  | succ value ih => exact succApp_hasType ih

theorem numeral_injective : Function.Injective (numeral (n := n)) := by
  intro first
  induction first with
  | zero =>
      intro second same
      cases second with
      | zero => rfl
      | succ second => cases same
  | succ first ih =>
      intro second same
      cases second with
      | zero => cases same
      | succ second => exact congrArg Nat.succ (ih (Tm.app.inj same).2)

/-- Only the executable beta/iota relation, excluding universe equality. -/
abbrev Computes (left right : Tower.Tm n) : Prop :=
  Relation.ReflTransGen (StepCore rules.computation (fun _ _ => False)) left right

theorem Computes.appArg {left right : Tower.Tm n}
    (path : Computes left right) (function : Tower.Tm n) :
    Computes (.app function left) (.app function right) :=
  path.lift (Tm.app function) (fun _ _ edge => .congAppArg edge)

theorem Computes.appFun {left right : Tower.Tm n}
    (path : Computes left right) (argument : Tower.Tm n) :
    Computes (.app left argument) (.app right argument) :=
  path.lift (fun function => Tm.app function argument) (fun _ _ edge => .congAppFun edge)

theorem Computes.beta (body : Tower.Tm (n + 1)) (argument : Tower.Tm n) :
    Computes (.app (.lam body) argument) (inst0 argument body) :=
  .single (.betaPi body argument)

/-! ## Numerals are values

A root step of these rules is an eliminator firing, and no eliminator fires
at a constant or at a successor.  So no computation step leaves a numeral: a
computation that reaches a numeral has reached a value, and distinct numerals
are not related by computation. -/

/-- A root step of the Nat and Vec rules is an eliminator firing. -/
theorem root_step_iff {left right : Tower.Tm n} :
    rules.computation.step left right ↔ Nonempty (IotaEvidence n left right) := by
  constructor
  · intro step
    change Presentation.Declaration.RootStep Tower.rules rawSignature n left right at step
    cases step with
    | inherited impossible => exact impossible.elim
    | delta unfolding => simp at unfolding
    | declared evidence => exact evidence
  · exact fun evidence => Presentation.Declaration.RootStep.declared evidence

theorem constant_not_fired (name : DeclName) (next : Tower.Tm n) :
    ¬ rules.computation.step (.const name) next := by
  intro step
  obtain ⟨evidence⟩ := root_step_iff.mp step
  generalize shape : (Tm.const name : Tower.Tm n) = left at evidence
  cases evidence <;> simp [natEliminateApp, vecEliminateApp] at shape

theorem successor_not_fired (number next : Tower.Tm n) :
    ¬ rules.computation.step (succApp number) next := by
  intro step
  obtain ⟨evidence⟩ := root_step_iff.mp step
  generalize shape : succApp number = left at evidence
  cases evidence <;> simp [succApp, natEliminateApp, vecEliminateApp] at shape

theorem constant_irreducible (name : DeclName) (next : Tower.Tm n) :
    ¬ StepCore rules.computation (fun _ _ => False) (.const name) next := by
  intro step
  generalize shape : (Tm.const name : Tower.Tm n) = left at step
  cases step with
  | root fired =>
      subst shape
      exact constant_not_fired name next fired
  | _ => simp at shape

/-- **A numeral is a value**: no computation step leaves it. -/
theorem numeral_irreducible (value : Nat) :
    ∀ next : Tower.Tm n,
      ¬ StepCore rules.computation (fun _ _ => False) (numeral value) next := by
  induction value with
  | zero => exact constant_irreducible zeroName
  | succ value ih =>
      intro next step
      generalize shape : (numeral (value + 1) : Tower.Tm n) = left at step
      cases step with
      | root fired =>
          subst shape
          exact successor_not_fired (numeral value) next fired
      | congAppFun inner =>
          simp only [numeral, succApp, Tm.app.injEq] at shape
          obtain ⟨rfl, rfl⟩ := shape
          exact constant_irreducible succName _ inner
      | congAppArg inner =>
          simp only [numeral, succApp, Tm.app.injEq] at shape
          obtain ⟨rfl, rfl⟩ := shape
          exact ih _ inner
      | _ => simp [numeral, succApp] at shape

/-- A computation that starts at a numeral stays there. -/
theorem Computes.eq_of_numeral {value : Nat} {next : Tower.Tm n}
    (path : Computes (numeral value) next) : next = numeral value := by
  induction path with
  | refl => rfl
  | tail _ step same =>
      subst same
      exact (numeral_irreducible value _ step).elim

/-- Distinct numerals are not related by computation. -/
theorem numeral_eq_of_computes {first second : Nat}
    (path : Computes (numeral first : Tower.Tm n) (numeral second)) : first = second :=
  (numeral_injective path.eq_of_numeral).symm

/-- The native recursor applied to a motive, a base branch and a step branch
at the numeral of an input.  The branches are supplied as native terms;
nothing here translates a source program into them. -/
def run (motive base step : Tower.Tm n) (input : Nat) : Tower.Tm n :=
  natEliminateApp motive base step (numeral input)

/-- A first-class function term: the input is an ordinary lexical variable,
not a host-language natural-number parameter. -/
def program (motive base step : Tower.Tm n) : Tower.Tm n :=
  .lam (natEliminateApp (rename wk motive) (rename wk base) (rename wk step) (.var 0))

theorem program_applies (motive base step : Tower.Tm n) (input : Nat) :
    Computes (.app (program motive base step) (numeral input)) (run motive base step input) := by
  simpa only [program, run, natEliminateApp, inst0, subst, subst0_wk, subst0,
    Fin.cases_zero] using Computes.beta
      (natEliminateApp (rename wk motive) (rename wk base) (rename wk step) (.var 0))
      (numeral input)

theorem run_zero (motive base step : Tower.Tm n) :
    Computes (run motive base step 0) base :=
  .single (.root iota_natZero)

theorem run_succ (motive base step : Tower.Tm n) (input : Nat) :
    Computes (run motive base step (input + 1))
      (.app (.app step (numeral input)) (run motive base step input)) :=
  .single (.root iota_natSucc)

/-- The predecessor and its recursive result occur as distinct lexical
arguments of the successor branch. -/
def stepType (motive : Tower.Tm n) : Tower.Tm n :=
  .pi natTm (.pi (.app (rename wk motive) (.var 0))
    (.app (rename wk (rename wk motive)) (succApp (.var (Fin.succ 0)))))

/-- Native typing follows from the types of the three branches and the
input, rather than a premise asserting the type of the entire program. -/
theorem eliminate_typed {context : Tower.Ctx n}
    {motive base step input : Tower.Tm n}
    (motiveTyped : Presentation.HasType rules context motive
      (.pi natTm (sortTm motiveLevel)))
    (baseTyped : Presentation.HasType rules context base (.app motive zeroTm))
    (stepTyped : Presentation.HasType rules context step (stepType motive))
    (inputTyped : Presentation.HasType rules context input natTm) :
    Presentation.HasType rules context (natEliminateApp motive base step input)
      (.app motive input) := by
  have succAsStep : natSuccCaseType = stepType (.var (Fin.succ 0)) := by decide
  have resultAsStep : natEliminateResultType =
      .pi natTm (.app (.var (Fin.succ (Fin.succ (Fin.succ 0)))) (.var 0)) := by decide
  have constant := natEliminateConstant_hasType (context := context)
  rw [natEliminateType, succAsStep, resultAsStep] at constant
  have first := Presentation.HasType.appElim constant motiveTyped
  have first' : Presentation.HasType rules context (.app (.const natEliminateName) motive)
      (.pi (.app motive zeroTm)
        (.pi (rename wk (stepType motive))
          (.pi natTm (.app (rename wk (rename wk (rename wk motive))) (.var 0))))) := by
    simpa only [natMotiveType, natZeroCaseType,
      liftClosed, inst0, subst, subst0, liftSub, rename,
      liftRen, wk, stepType, natTm, zeroTm, succApp, sortTm,
      Fin.cases_zero, Fin.cases_succ, rename_comp] using first
  have second := Presentation.HasType.appElim first' baseTyped
  have second' : Presentation.HasType rules context
      (.app (.app (.const natEliminateName) motive) base)
      (.pi (stepType motive)
        (.pi natTm (.app (rename wk (rename wk motive)) (.var 0)))) := by
    simpa only [inst0, subst, subst_liftSub_wk, subst0_wk, subst_natTm,
      liftSub, Fin.cases_zero] using second
  have third := Presentation.HasType.appElim second' stepTyped
  have third' : Presentation.HasType rules context
      (.app (.app (.app (.const natEliminateName) motive) base) step)
      (.pi natTm (.app (rename wk motive) (.var 0))) := by
    simpa only [inst0, subst, subst_liftSub_wk, subst0_wk, subst_natTm,
      liftSub, Fin.cases_zero] using third
  simpa only [natEliminateApp, inst0, subst, subst0, subst0_wk,
    Fin.cases_zero] using Presentation.HasType.appElim third' inputTyped

/-- Nondependent result families still use a genuine native lambda motive. -/
def constantMotive (type : Tower.Tm n) : Tower.Tm n := .lam (rename wk type)

@[simp] theorem constantMotive_rename {m : Nat} (rho : Ren n m) (type : Tower.Tm n) :
    rename rho (constantMotive type) = constantMotive (rename rho type) := by
  simp only [constantMotive, rename, rename_comp]
  congr 1

theorem constantMotive_beta (type input : Tower.Tm n) :
    Conv rules.headEq (.app (constantMotive type) input) type rules.computation := by
  simpa only [constantMotive, inst0_rename_wk] using
    (Relation.EqvGen.rel _ _ (Step.betaPi (root := rules.computation)
      (headEq := rules.headEq) (rename wk type) input))

theorem constantMotive_typed {context : Tower.Ctx n} {type : Tower.Tm n}
    (typeTyped : Presentation.HasType rules context type (sortTm motiveLevel)) :
    Presentation.HasType rules context (constantMotive type)
      (.pi natTm (sortTm motiveLevel)) :=
  .lamIntro typeTyped.weaken

/-- A nondependent successor branch accepts a predecessor and a recursive
value of the result type. -/
def constantStepType (type : Tower.Tm n) : Tower.Tm n :=
  .pi natTm (.pi (rename wk type) (rename wk (rename wk type)))

@[simp] theorem constantStepType_rename {m : Nat} (rho : Ren n m) (type : Tower.Tm n) :
    rename rho (constantStepType type) = constantStepType (rename rho type) := by
  simp only [constantStepType, rename, rename_comp, rename_natTm]
  congr 1


theorem stepType_constantMotive (type : Tower.Tm n) :
    Conv rules.headEq (stepType (constantMotive type)) (constantStepType type)
      rules.computation := by
  simp only [stepType, constantStepType, constantMotive_rename]
  apply Conv.congPi (.refl _)
  exact Conv.congPi (constantMotive_beta _ _) (constantMotive_beta _ _)

theorem constant_eliminate_typed {context : Tower.Ctx n}
    {type base step input : Tower.Tm n}
    (typeTyped : Presentation.HasType rules context type (sortTm motiveLevel))
    (baseTyped : Presentation.HasType rules context base type)
    (stepTyped : Presentation.HasType rules context step (constantStepType type))
    (inputTyped : Presentation.HasType rules context input natTm) :
    Presentation.HasType rules context
      (natEliminateApp (constantMotive type) base step input) type := by
  have eliminated := eliminate_typed (constantMotive_typed typeTyped)
    (.conv baseTyped (constantMotive_beta _ _).symm)
    (.conv stepTyped (stepType_constantMotive _).symm) inputTyped
  exact .conv eliminated (constantMotive_beta _ _)

/-- The native recursive function itself is typed, independently of the
chosen input numeral used in the realization theorem. -/
theorem program_typed {context : Tower.Ctx n} {type base step : Tower.Tm n}
    (typeTyped : Presentation.HasType rules context type (sortTm motiveLevel))
    (baseTyped : Presentation.HasType rules context base type)
    (stepTyped : Presentation.HasType rules context step (constantStepType type)) :
    Presentation.HasType rules context (program (constantMotive type) base step)
      (SchemaElaboration.arrow natTm type) := by
  apply Presentation.HasType.lamIntro
  rw [constantMotive_rename]
  apply constant_eliminate_typed typeTyped.weaken baseTyped.weaken
  · simpa only [constantStepType_rename] using stepTyped.weaken (extension := natTm)
  · exact .var 0

universe u

/-- Compositional realization of the entire source primitive-recursive
program follows from independently checked branch realizations. -/
theorem realizes_primitiveRecursion {Output : Type u}
    (encode : Output → Tower.Tm n) (sourceBase : Output)
    (sourceStep : Nat → Output → Output) (motive base step : Tower.Tm n)
    (baseComputes : Computes base (encode sourceBase))
    (stepComputes : ∀ input output,
      Computes (.app (.app step (numeral input)) (encode output))
        (encode (sourceStep input output))) :
    ∀ input, Computes (run motive base step input)
      (encode (Source.primitiveRecursion sourceBase sourceStep input)) := by
  intro input
  induction input with
  | zero => exact (run_zero motive base step).trans baseComputes
  | succ input ih =>
      exact (run_succ motive base step input).trans
        ((ih.appArg (.app step (numeral input))).trans (stepComputes input _))

theorem program_realizes_primitiveRecursion {Output : Type u}
    (encode : Output → Tower.Tm n) (sourceBase : Output)
    (sourceStep : Nat → Output → Output) (motive base step : Tower.Tm n)
    (baseComputes : Computes base (encode sourceBase))
    (stepComputes : ∀ input output,
      Computes (.app (.app step (numeral input)) (encode output))
        (encode (sourceStep input output))) (input : Nat) :
    Computes (.app (program motive base step) (numeral input))
      (encode (Source.primitiveRecursion sourceBase sourceStep input)) :=
  (program_applies motive base step input).trans
    (realizes_primitiveRecursion encode sourceBase sourceStep motive base step
      baseComputes stepComputes input)

/-- A universal source specification and branch realization give a native
result satisfying that specification for every input. -/
theorem realizes_specification {Output : Type u}
    (encode : Output → Tower.Tm n) (spec : Nat → Output → Prop)
    (sourceBase : Output) (sourceStep : Nat → Output → Output)
    (motive base step : Tower.Tm n)
    (baseCorrect : spec 0 sourceBase)
    (stepCorrect : ∀ input output, spec input output →
      spec (input + 1) (sourceStep input output))
    (baseComputes : Computes base (encode sourceBase))
    (stepComputes : ∀ input output,
      Computes (.app (.app step (numeral input)) (encode output))
        (encode (sourceStep input output))) :
    ∀ input, ∃ output, Computes (run motive base step input) (encode output) ∧
      spec input output := by
  intro input
  exact ⟨_, realizes_primitiveRecursion encode sourceBase sourceStep motive base step
    baseComputes stepComputes input,
    Source.primitiveRecursion_correct spec sourceBase sourceStep baseCorrect stepCorrect input⟩

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativePrimitiveRecursion
