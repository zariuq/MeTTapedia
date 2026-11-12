import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.VectorAppend
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ConstructorSystemDevelopment

/-!
# Declared computation: orthogonal rules are confluent with β, overlapping ones are not

The vector package with addition declared computing (`VectorAppend.vrules`: `add 0 b ↦ b`,
`add (succ a) b ↦ succ (add a b)`) is a **constructor system**: each left side is the defined constant
`add` applied to two argument patterns built from the undefined constants `zero` and `succ` and
variables (`addSystem`); each left side is linear, every variable of a right side occurs on its left,
and two left sides with a common instance are one rule at one instantiation (`addSystem.determined`):
the rules are orthogonal. The declared root steps are exactly the instances of the two rules
(`addPresentation`).

So the tree's complete-development theorem for constructor systems applies: the conversion of the
declared package, β for functions, both projections of pairs, the universe-head equality and the two
declared rules together, is **Church–Rosser** (`add_churchRosser`). In particular distinct normal forms
stay apart: `1` and `0` are not convertible (`one_zero_apart`).

**Termination is the hypothesis for decidability** (`convDecidable`, `addConvDecidable`): in a
Church–Rosser package a normalizer decides conversion by comparing normal forms. This is the untyped
conversion of the package (β, projections, heads, declared rules); the typed βη equality of the step's
knowledge needs, in addition, the package's normalization model.

**Control.** The overlapping declaration `add 0 b ↦ b`, `add 0 b ↦ 0` (`VectorAppend.brules`) converts `1`
to `0`, two distinct normal forms, so it is not Church–Rosser (`bad_not_churchRosser`) and has no
presentation as a constructor system (`bad_no_constructorPresentation`). Root determinism, the check at
declaration time, refuses it as well (`VectorAppend.bad_not_rootDeterministic`); for constructor-pattern
declarations it is the decidable root part of determinedness.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.DeclaredConfluence

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open AlgebraicSchema AlgebraicParallel ConversionCoherence
open ConstructorSystem (System LeftSide Pattern ConstructorPresentation)
open ProgrammingOnTheStep.VectorPackage
open ProgrammingOnTheStep.VectorPrograms (one)
open NativeTypesOnTheStep.VectorAppend

/-! ## Addition as a constructor system -/

/-- **The two rules of addition**, as open equations: `add 0 x ↦ x` over one variable and
`add (succ x) y ↦ succ (add x y)` over two. -/
inductive AddSchema : {arity : Nat} → Tower.Tm arity → Tower.Tm arity → Prop
  | zero : AddSchema (arity := 1) (.app (.app (.const addN) (.const zeroN)) (.var 0)) (.var 0)
  | succ : AddSchema (arity := 2) (.app (.app (.const addN) (.app (.const succN) (.var 0))) (.var 1))
      (.app (.const succN) (.app (.app (.const addN) (.var 0)) (.var 1)))

/-- **The declared root steps are exactly the instances of the two rules.** -/
def addPresentation : SchemaPresentation vrules where
  schema := AddSchema
  sound := by
    intro arity ambient left right rule substitution
    cases rule with
    | zero => exact Or.inr (AddStep.zero (substitution 0))
    | succ => exact Or.inr (AddStep.succ (substitution 0) (substitution 1))
  cover := by
    intro n source target step
    rcases step with impossible | step
    · exact impossible.elim
    · exact match step with
        | .zero b => ⟨1, _, _, fun _ => b, .zero, rfl, rfl⟩
        | .succ a b => ⟨2, _, _, Fin.cases a (fun _ => b), .succ, rfl, rfl⟩

/-- **Addition is a constructor system**: linear constructor-pattern left sides, covered right sides,
and determined contraction. -/
def addSystem : System Tower.Head where
  schema := AddSchema
  defined name := name = addN
  arity _ := 2
  left := by
    intro m left right rule
    refine ⟨addN, rfl, by decide, ?_⟩
    cases rule with
    | zero =>
        exact .app (.app (.const addN) (.const (show ¬ zeroN = addN by decide))) (.var 0)
    | succ =>
        exact .app (.app (.const addN) (.app (.const (show ¬ succN = addN by decide)) (.var 0))) (.var 1)
  linear := by
    intro arity left right rule
    cases rule with
    | zero => unfold LeftLinear; decide
    | succ => unfold LeftLinear; decide
  covered := by
    intro m left right rule
    cases rule with
    | zero => decide
    | succ => decide
  determined := by
    intro m m' n n' left right left' right' rule rule' instantiation instantiation' same develop
    cases rule with
    | zero =>
        cases rule' with
        | zero =>
            have same' : Tm.app (.app (.const addN) (.const zeroN)) (instantiation 0) =
                Tm.app (.app (.const addN) (.const zeroN)) (instantiation' 0) := same
            obtain ⟨-, argument⟩ := Tm.app.inj same'
            show develop (instantiation 0) = develop (instantiation' 0)
            rw [argument]
        | succ =>
            have same' : Tm.app (.app (.const addN) (.const zeroN)) (instantiation 0) =
                Tm.app (.app (.const addN) (.app (.const succN) (instantiation' 0))) (instantiation' 1) :=
              same
            obtain ⟨function, -⟩ := Tm.app.inj same'
            obtain ⟨-, clash⟩ := Tm.app.inj function
            cases clash
    | succ =>
        cases rule' with
        | zero =>
            have same' : Tm.app (.app (.const addN) (.app (.const succN) (instantiation 0))) (instantiation 1) =
                Tm.app (.app (.const addN) (.const zeroN)) (instantiation' 0) := same
            obtain ⟨function, -⟩ := Tm.app.inj same'
            obtain ⟨-, clash⟩ := Tm.app.inj function
            cases clash
        | succ =>
            have same' : Tm.app (.app (.const addN) (.app (.const succN) (instantiation 0))) (instantiation 1) =
                Tm.app (.app (.const addN) (.app (.const succN) (instantiation' 0))) (instantiation' 1) := same
            obtain ⟨function, second⟩ := Tm.app.inj same'
            obtain ⟨-, successor⟩ := Tm.app.inj function
            obtain ⟨-, first⟩ := Tm.app.inj successor
            show Tm.app (.const succN) (.app (.app (.const addN) (develop (instantiation 0)))
                (develop (instantiation 1))) =
              Tm.app (.const succN) (.app (.app (.const addN) (develop (instantiation' 0)))
                (develop (instantiation' 1)))
            rw [first, second]

/-- Head equality of the tower is symmetric. -/
instance : Std.Symm vrules.headEq := ⟨fun _ _ same => Interface.DependentFull.Controls.setting.levels.headEq_symm same⟩

/-- **The declared package as a definition by constructor patterns.** -/
def addConstructorPresentation : ConstructorPresentation vrules where
  presentation := addPresentation
  system := addSystem
  same _ _ := Iff.rfl
  symmetric := inferInstance

/-- **Orthogonality gives confluence with β**: the conversion of the vector package with addition
declared computing is Church–Rosser. -/
theorem add_churchRosser : ChurchRosser vrules := addConstructorPresentation.churchRosser

/-! ## Distinct normal forms stay apart, unless the rules overlap -/

theorem one_normal : Normal vrules (one : Tower.Tm 0) := by
  intro t h
  cases h with
  | root h => rcases h with h | h <;> cases h
  | congAppFun h => cases h with
    | root h => rcases h with h | h <;> cases h
  | congAppArg h => cases h with
    | root h => rcases h with h | h <;> cases h

theorem zero_normal : Normal vrules (zeroC : Tower.Tm 0) := by
  intro t h
  cases h with
  | root h => rcases h with h | h <;> cases h

/-- A normal term reaches only itself. -/
theorem stepStar_normal {R : Rules Tower.Head} {n : Nat} {t u : Tower.Tm n} (normal : Normal R t)
    (steps : StepStar R t u) : u = t :=
  ConstructorSystem.Normal.stepStar (fun step => normal _ step) steps

/-- Computation steps are conversions. -/
theorem conv_of_stepStar {R : Rules Tower.Head} {n : Nat} {t u : Tower.Tm n} (steps : StepStar R t u) :
    Conv R.headEq t u R.computation := by
  induction steps with
  | refl => exact .refl _
  | tail _ step ih => exact .trans _ _ _ ih (.rel _ _ step)

/-- **Termination as the hypothesis for decidability**: in a Church–Rosser package, a normalizer (a
function reaching a normal form of every term) decides conversion by comparing normal forms. -/
def convDecidable {R : Rules Tower.Head} (churchRosser : ChurchRosser R)
    (normalize : ∀ {n : Nat}, Tower.Tm n → Tower.Tm n)
    (reaches : ∀ {n : Nat} (t : Tower.Tm n), StepStar R t (normalize t))
    (normal : ∀ {n : Nat} (t : Tower.Tm n), Normal R (normalize t)) {n : Nat} (t u : Tower.Tm n) :
    Decidable (Conv R.headEq t u R.computation) :=
  if same : normalize t = normalize u then
    isTrue (.trans _ _ _ (conv_of_stepStar (reaches t))
      (same ▸ .symm _ _ (conv_of_stepStar (reaches u))))
  else
    isFalse fun conversion => by
      have between : Conv R.headEq (normalize t) (normalize u) R.computation :=
        .trans _ _ _ (.symm _ _ (conv_of_stepStar (reaches t))) (.trans _ _ _ conversion (conv_of_stepStar (reaches u)))
      obtain ⟨common, left, right⟩ := churchRosser between
      exact same ((stepStar_normal (normal t) left).symm.trans (stepStar_normal (normal u) right))

/-- **The declared vector package decides its conversion, given a normalizer**: confluence is proved,
termination is the hypothesis. -/
def addConvDecidable (normalize : ∀ {n : Nat}, Tower.Tm n → Tower.Tm n)
    (reaches : ∀ {n : Nat} (t : Tower.Tm n), StepStar vrules t (normalize t))
    (normal : ∀ {n : Nat} (t : Tower.Tm n), Normal vrules (normalize t)) {n : Nat} (t u : Tower.Tm n) :
    Decidable (Conv vrules.headEq t u vrules.computation) :=
  convDecidable add_churchRosser normalize reaches normal t u

/-- **With the orthogonal declaration, `1` and `0` are not convertible.** -/
theorem one_zero_apart : ¬ Conv vrules.headEq (one : Tower.Tm 0) zeroC vrules.computation := by
  intro conversion
  obtain ⟨common, left, right⟩ := add_churchRosser conversion
  have fromOne := stepStar_normal one_normal left
  have fromZero := stepStar_normal zero_normal right
  exact absurd (fromOne.symm.trans fromZero) (by decide)

/-- **Control: the overlapping declaration converts `1` to `0`.** -/
theorem bad_one_zero : Conv brules.headEq (one : Tower.Tm 0) zeroC brules.computation :=
  .trans _ _ _ (.symm _ _ (.rel _ _ (.root (declare_step (BadStep.keep one)))))
    (.rel _ _ (.root (declare_step (BadStep.drop one))))

/-- **... so it is not Church–Rosser.** -/
theorem bad_not_churchRosser : ¬ ChurchRosser brules := by
  intro churchRosser
  obtain ⟨common, left, right⟩ := churchRosser bad_one_zero
  have fromOne := stepStar_normal bad_one_normal left
  have fromZero := stepStar_normal bad_zero_normal right
  exact absurd (fromOne.symm.trans fromZero) (by decide)

/-- **... and has no presentation as a constructor system.** -/
theorem bad_no_constructorPresentation : ConstructorPresentation brules → False :=
  fun presentation => bad_not_churchRosser presentation.churchRosser

end NativeTypesOnTheStep.DeclaredConfluence

#print axioms NativeTypesOnTheStep.DeclaredConfluence.addPresentation
#print axioms NativeTypesOnTheStep.DeclaredConfluence.addSystem
#print axioms NativeTypesOnTheStep.DeclaredConfluence.addConstructorPresentation
#print axioms NativeTypesOnTheStep.DeclaredConfluence.add_churchRosser
#print axioms NativeTypesOnTheStep.DeclaredConfluence.one_normal
#print axioms NativeTypesOnTheStep.DeclaredConfluence.one_zero_apart
#print axioms NativeTypesOnTheStep.DeclaredConfluence.bad_one_zero
#print axioms NativeTypesOnTheStep.DeclaredConfluence.bad_not_churchRosser
#print axioms NativeTypesOnTheStep.DeclaredConfluence.bad_no_constructorPresentation
#print axioms NativeTypesOnTheStep.DeclaredConfluence.convDecidable
#print axioms NativeTypesOnTheStep.DeclaredConfluence.addConvDecidable

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
