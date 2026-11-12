import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Qualification
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.RootDeterminism

/-!
# One `=`, two readings: where they agree and the smallest places where they cannot

One equation set has two readings.

* **Operational**: its rows fire. Here a row fires at any position of a term, and an **answer** of a
  call is a normal form its firings reach (`Answer`). This is the reduction relation of the declared
  package, not the whole step machinery: a firing of the step is a root step at a call row.
* **Definitional**: its rows are computing rules of conversion, and the knowledge solves equations
  modulo them.

**Inside the class they agree.**

* For every Church–Rosser package, an answer is exactly a conversion normal form of the call
  (`answer_iff`), and a call has at most one answer (`answer_unique`). So one notation serves both
  readings.
* On a qualified package an answer of a typed call has the call's type and is typed-equal to it
  (`Qualified.answer_typed`), so types may use the function.
* For the step's own declared addition, by recursion on its first argument, every ground call reaches
  exactly one answer, a numeral (`ground_answer`, `ground_answer_unique`), typed-equal to the call at
  `nat` (`ground_equal`). Structural recursion is what discharges termination here: the proof is an
  induction on the first argument.

**Outside the class they disagree**, with one smallest declaration per cause (`classification`):

* overlap: one call, two answers (`add 0 1` reaches `1` and `0`);
* non-termination: no answer, yet the knowledge equates the call with its successor;
* effects: no root-deterministic computation agrees with the store at two states;
* partiality: the call's only normal form is no value, and the refutation it supports does not survive
  the row that completes the definition.

So "definitional" is a checked property of an equation set, never a second syntax. In the Prime
decisions' terms, a row that may enter conversion has the discipline of an `Atom` (a value: total,
deterministic, closed under substitution, independent of the store), and any other row is a `Proc`
(a computation): it runs by firings and the knowledge treats its calls as rigid.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open ConversionCoherence (ChurchRosser StepStar)

/-! ## The operational reading -/

section Answers

variable {Head : Type}

/-- **An answer** of a call: a normal form its firings reach. -/
def Answer (R : Rules Head) {n : Nat} (t v : Tm Head n) : Prop :=
  StepStar R t v ∧ ConstructorSystem.Normal R v

/-- Firings are conversions. -/
theorem conv_of_stepStar {R : Rules Head} {n : Nat} {t u : Tm Head n} (steps : StepStar R t u) :
    Conv R.headEq t u R.computation := by
  induction steps with
  | refl => exact .refl _
  | tail _ step ih => exact .trans _ _ _ ih (.rel _ _ step)

/-- **The two readings agree on Church–Rosser packages**: evaluating a call by firings reaches `v`
exactly when `v` is a conversion normal form of the call. -/
theorem answer_iff {R : Rules Head} (church : ChurchRosser R) {n : Nat} {t v : Tm Head n} :
    Answer R t v ↔ Conv R.headEq t v R.computation ∧ ConstructorSystem.Normal R v := by
  constructor
  · exact fun answer => ⟨conv_of_stepStar answer.1, answer.2⟩
  · rintro ⟨conversion, normal⟩
    obtain ⟨common, left, right⟩ := church conversion
    have same := ConstructorSystem.Normal.stepStar normal right
    subst same
    exact ⟨left, normal⟩

/-- **At most one answer** on a Church–Rosser package. -/
theorem answer_unique {R : Rules Head} (church : ChurchRosser R) {n : Nat} {t v v' : Tm Head n}
    (answer : Answer R t v) (answer' : Answer R t v') : v = v' := by
  have conversion : Conv R.headEq v v' R.computation :=
    .trans _ _ _ (.symm _ _ (conv_of_stepStar answer.1)) (conv_of_stepStar answer'.1)
  obtain ⟨common, left, right⟩ := church conversion
  exact (ConstructorSystem.Normal.stepStar answer.2 left).symm.trans
    (ConstructorSystem.Normal.stepStar answer'.2 right)

end Answers

/-- **On a qualified package the answer of a typed call has its type** and is typed-equal to it. -/
theorem Qualified.answer_typed {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
    (q : Qualified S) {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {t v A : Tm Head n}
    (typing : Typed S.R Γ t A) (answer : Answer S.R t v) :
    Typed S.R Γ v A ∧ Equal S.R Γ t v A :=
  q.subjectReduction formed answer.1 typing

/-! ## Ground calls of the step's declared addition -/

section Ground

open ProgrammingOnTheStep.VectorPackage
open ProgrammingOnTheStep.VectorPrograms (one)
open NativeTypesOnTheStep.VectorAppend (AddStep vrules vtyped)
open NativeTypesOnTheStep.DeclaredConfluence (add_churchRosser)

/-- The numeral `succ^k 0`. -/
def numeral {n : Nat} : Nat → Tower.Tm n
  | 0 => .const zeroN
  | k + 1 => .app (.const succN) (numeral k)

/-- Ground calls of addition: `0`, `succ t`, `add t u`. -/
inductive Ground {n : Nat} : Tower.Tm n → Prop
  | zero : Ground (.const zeroN)
  | succ {t : Tower.Tm n} : Ground t → Ground (.app (.const succN) t)
  | add {t u : Tower.Tm n} : Ground t → Ground u → Ground (.app (.app (.const addN) t) u)

/-- Numerals are normal for the declared addition. -/
theorem numeral_normal {n : Nat} (k : Nat) : ConstructorSystem.Normal vrules (numeral k : Tower.Tm n) := by
  induction k with
  | zero =>
      intro t h
      cases h with
      | root h => rcases h with h | h <;> cases h
  | succ k ih =>
      intro t h
      cases h with
      | root h => rcases h with h | h <;> cases h
      | congAppFun h =>
          cases h with
          | root h => rcases h with h | h <;> cases h
      | congAppArg h => exact ih h

theorem stepStar_succ {n : Nat} {t t' : Tower.Tm n} (steps : StepStar vrules t t') :
    StepStar vrules (.app (.const succN) t) (.app (.const succN) t') := by
  induction steps with
  | refl => exact .refl
  | tail _ step ih => exact .tail ih (.congAppArg step)

theorem stepStar_addLeft {n : Nat} {t t' u : Tower.Tm n} (steps : StepStar vrules t t') :
    StepStar vrules (.app (.app (.const addN) t) u) (.app (.app (.const addN) t') u) := by
  induction steps with
  | refl => exact .refl
  | tail _ step ih => exact .tail ih (.congAppFun (.congAppArg step))

theorem stepStar_addRight {n : Nat} {t u u' : Tower.Tm n} (steps : StepStar vrules u u') :
    StepStar vrules (.app (.app (.const addN) t) u) (.app (.app (.const addN) t) u') := by
  induction steps with
  | refl => exact .refl
  | tail _ step ih => exact .tail ih (.congAppArg step)

/-- **Addition of numerals runs by structural recursion on the first argument.** -/
theorem add_numerals {n : Nat} (a b : Nat) :
    StepStar vrules (.app (.app (.const addN) (numeral a)) (numeral b) : Tower.Tm n)
      (numeral (a + b)) := by
  induction a with
  | zero =>
      rw [Nat.zero_add]
      exact .single (.root (declare_step (AddStep.zero (numeral b))))
  | succ a ih =>
      rw [Nat.add_right_comm]
      exact .head (.root (declare_step (AddStep.succ (numeral a) (numeral b)))) (stepStar_succ ih)

/-- **Every ground call has an answer, a numeral.** -/
theorem ground_answer {n : Nat} {t : Tower.Tm n} (ground : Ground t) :
    ∃ k, Answer vrules t (numeral k) := by
  induction ground with
  | zero => exact ⟨0, .refl, numeral_normal 0⟩
  | succ _ ih =>
      obtain ⟨k, steps, _⟩ := ih
      exact ⟨k + 1, stepStar_succ steps, numeral_normal (k + 1)⟩
  | add _ _ ihT ihU =>
      obtain ⟨a, stepsT, _⟩ := ihT
      obtain ⟨b, stepsU, _⟩ := ihU
      exact ⟨a + b, (stepStar_addLeft stepsT).trans ((stepStar_addRight stepsU).trans (add_numerals a b)),
        numeral_normal (a + b)⟩

/-- **... and exactly one.** -/
theorem ground_answer_unique {n : Nat} {t : Tower.Tm n} (ground : Ground t) :
    ∃ k, Answer vrules t (numeral k) ∧ ∀ v, Answer vrules t v ↔ v = numeral k := by
  obtain ⟨k, answer⟩ := ground_answer ground
  exact ⟨k, answer, fun v => ⟨fun answer' => answer_unique add_churchRosser answer' answer,
    fun same => same ▸ answer⟩⟩

theorem succConst_typed {n : Nat} (Γ : Tower.Ctx n) :
    Typed vrules Γ (.const succN) (.pi natC natC) :=
  vtyped (.const declared_succ succTy_typed (.sort _))

theorem addConst_typed {n : Nat} (Γ : Tower.Ctx n) :
    Typed vrules Γ (.const addN) (.pi natC (.pi natC natC)) :=
  vtyped (.const declared_add addTy_typed (.sort _))

theorem numeral_typed {n : Nat} (Γ : Tower.Ctx n) (k : Nat) : Typed vrules Γ (numeral k) natC := by
  induction k with
  | zero => exact vtyped (zero_typed _)
  | succ k ih => exact .appElim (succConst_typed Γ) ih

theorem ground_typed {n : Nat} {Γ : Tower.Ctx n} {t : Tower.Tm n} (ground : Ground t) :
    Typed vrules Γ t natC := by
  induction ground with
  | zero => exact vtyped (zero_typed _)
  | succ _ ih => exact .appElim (succConst_typed Γ) ih
  | add _ _ ihT ihU => exact .appElim (.appElim (addConst_typed Γ) ihT) ihU

theorem equal_succ {n : Nat} {Γ : Tower.Ctx n} {t t' : Tower.Tm n}
    (equal : Equal vrules Γ t t' natC) :
    Equal vrules Γ (.app (.const succN) t) (.app (.const succN) t') natC :=
  .appCong (.refl (succConst_typed Γ)) equal

theorem equal_add {n : Nat} {Γ : Tower.Ctx n} {t t' u u' : Tower.Tm n}
    (left : Equal vrules Γ t t' natC) (right : Equal vrules Γ u u' natC) :
    Equal vrules Γ (.app (.app (.const addN) t) u) (.app (.app (.const addN) t') u') natC :=
  .appCong (.appCong (.refl (addConst_typed Γ)) left) right

/-- Addition of numerals, as a typed equality. -/
theorem add_numerals_equal {n : Nat} (Γ : Tower.Ctx n) (a b : Nat) :
    Equal vrules Γ (.app (.app (.const addN) (numeral a)) (numeral b)) (numeral (a + b)) natC := by
  induction a with
  | zero =>
      rw [Nat.zero_add]
      exact .root (declare_step (AddStep.zero (numeral b)))
        (.appElim (.appElim (addConst_typed Γ) (numeral_typed Γ 0)) (numeral_typed Γ b))
        (numeral_typed Γ b)
  | succ a ih =>
      rw [Nat.add_right_comm]
      exact .trans (.root (declare_step (AddStep.succ (numeral a) (numeral b)))
          (.appElim (.appElim (addConst_typed Γ) (numeral_typed Γ (a + 1))) (numeral_typed Γ b))
          (.appElim (succConst_typed Γ)
            (.appElim (.appElim (addConst_typed Γ) (numeral_typed Γ a)) (numeral_typed Γ b))))
        (equal_succ ih)

/-- **The answer of a ground call is typed-equal to it**: the operational answer is the definitional
normal form, at `nat`, in every context. -/
theorem ground_equal {n : Nat} (Γ : Tower.Ctx n) {t : Tower.Tm n} (ground : Ground t) :
    ∃ k, Answer vrules t (numeral k) ∧ Equal vrules Γ t (numeral k) natC := by
  induction ground with
  | zero => exact ⟨0, ⟨.refl, numeral_normal 0⟩, .refl (vtyped (zero_typed _))⟩
  | succ _ ih =>
      obtain ⟨k, ⟨steps, _⟩, equal⟩ := ih
      exact ⟨k + 1, ⟨stepStar_succ steps, numeral_normal (k + 1)⟩, equal_succ equal⟩
  | add _ _ ihT ihU =>
      obtain ⟨a, ⟨stepsT, _⟩, equalT⟩ := ihT
      obtain ⟨b, ⟨stepsU, _⟩, equalU⟩ := ihU
      exact ⟨a + b,
        ⟨(stepStar_addLeft stepsT).trans ((stepStar_addRight stepsU).trans (add_numerals a b)),
          numeral_normal (a + b)⟩,
        .trans (equal_add equalT equalU) (add_numerals_equal Γ a b)⟩

/-- A positive example: `add 2 1` answers `3`. -/
theorem two_plus_one : Answer vrules (.app (.app (.const addN) (numeral 2)) (numeral 1) : Tower.Tm 0)
    (numeral 3) :=
  ⟨add_numerals 2 1, numeral_normal 3⟩

end Ground

/-! ## The classification -/

section Classification

open ProgrammingOnTheStep.VectorPackage
open ProgrammingOnTheStep.VectorPrograms (one oneVec)
open NativeTypesOnTheStep.VectorAppend (brules vrules BadStep)
open RootDeterminism

/-- The overlapping declaration's normal forms, in the normal form of the constructor theory. -/
theorem bad_one_normal' : ConstructorSystem.Normal brules (one : Tower.Tm 0) :=
  fun step => VectorAppend.bad_one_normal _ step

theorem bad_zero_normal' : ConstructorSystem.Normal brules (.const zeroN : Tower.Tm 0) :=
  fun step => VectorAppend.bad_zero_normal _ step

/-- **The classification of `=`.** Inside the class (the declared addition, a constructor system by
structural recursion) every ground call has exactly one answer, a numeral, typed-equal to the call.
Outside it, one smallest declaration per cause:
overlap gives one call two answers; non-termination gives no answer while the knowledge equates the
call with its successor; effects admit no root-deterministic computation that agrees with the store at
two states; partiality leaves a ground call whose only normal form is no value, and its refutation
of `add 1 0 ≡ 1` does not survive the completing row. -/
theorem classification :
    (∀ {t : Tower.Tm 0}, Ground t →
      ∃ k, (∀ v, Answer vrules t v ↔ v = numeral k) ∧ Equal vrules .nil t (numeral k) natC) ∧
    (Answer brules (addC zeroC one : Tower.Tm 0) one ∧
      Answer brules (addC zeroC one : Tower.Tm 0) (.const zeroN) ∧ (one : Tower.Tm 0) ≠ .const zeroN) ∧
    ((¬ ∃ v, Answer lrules loopCall v) ∧ (frames llevels).Solvable loopStore ∧
      ¬ (frames levels).Solvable rigidLoopStore) ∧
    (∀ d : RootComputation Tower.Head,
      d.step (lookupC one oneVec (fzC zeroC) : Tower.Tm 0) (.const zeroN) →
      d.step (lookupC one oneVec (fzC zeroC) : Tower.Tm 0) one → ¬ RootDeterministic d) ∧
    (Answer prules stuckCall stuckCall ∧ ¬ IsNumeral stuckCall ∧
      ¬ Conv prules.headEq stuckCall one prules.computation ∧
      Conv vrules.headEq stuckCall one vrules.computation) := by
  refine ⟨fun ground => ?_, ⟨⟨.single (.root (declare_step (BadStep.keep one))), bad_one_normal'⟩,
      ⟨.single (.root (declare_step (BadStep.drop one))), bad_zero_normal'⟩, by decide⟩,
    ⟨fun ⟨v, answer⟩ => loop_no_answer ⟨v, answer⟩, loop_solvable, rigid_loop_unsolvable⟩,
    fun d atZero atOne => effect_not_rootDeterministic d atZero atOne,
    ⟨⟨.refl, stuck_normal⟩, stuck_not_numeral, stuck_not_one, completed_converts⟩⟩
  obtain ⟨k, answer, equal⟩ := ground_equal .nil ground
  exact ⟨k, fun v => ⟨fun answer' => answer_unique DeclaredConfluence.add_churchRosser answer' answer,
    fun same => same ▸ answer⟩, equal⟩

end Classification

end NativeTypesOnTheStep.Computing

#print axioms NativeTypesOnTheStep.Computing.conv_of_stepStar
#print axioms NativeTypesOnTheStep.Computing.answer_iff
#print axioms NativeTypesOnTheStep.Computing.answer_unique
#print axioms NativeTypesOnTheStep.Computing.Qualified.answer_typed
#print axioms NativeTypesOnTheStep.Computing.numeral_normal
#print axioms NativeTypesOnTheStep.Computing.add_numerals
#print axioms NativeTypesOnTheStep.Computing.ground_answer
#print axioms NativeTypesOnTheStep.Computing.ground_answer_unique
#print axioms NativeTypesOnTheStep.Computing.ground_typed
#print axioms NativeTypesOnTheStep.Computing.add_numerals_equal
#print axioms NativeTypesOnTheStep.Computing.ground_equal
#print axioms NativeTypesOnTheStep.Computing.two_plus_one
#print axioms NativeTypesOnTheStep.Computing.classification

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
