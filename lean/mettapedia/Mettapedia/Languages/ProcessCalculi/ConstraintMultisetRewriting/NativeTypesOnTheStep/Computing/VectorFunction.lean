import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.TwoReadings

/-!
# A vector function in the definitional class: `append`, with its length argument inaccessible

The step's vector package declares `append : Π (m k : nat). vec m → vec k → vec (add m k)`. Declared
computing together with addition (`vecComputation`), its rows are

* `add 0 b ↦ b`, `add (succ a) b ↦ succ (add a b)`;
* `append m k nil ys ↦ ys`;
* `append m k (cons m' x xs) ys ↦ cons (add m' k) x (append m' k xs ys)`.

The length `m` is matched by a variable, not by a constructor: the vector argument fixes it. Writing
`append (succ m') k (cons m' x xs) ys` instead repeats `m'` and is not left-linear. With the length
inaccessible the rows are a **constructor system** (`appendConstructors`), so conversion with them is
**Church–Rosser** (`append_churchRosser`), and the declaration is root-deterministic
(`append_rootDeterministic`).

**Termination for ground calls** is structural recursion on the vector argument: appending two ground
vectors of numerals reaches a ground vector of the summed length (`append_answer`), its unique answer
(`append_answer_unique`). For example `append [2] [3]` answers `[2, 3]` (`append_example`).

The typing of each row is checked after its match: the row `append m k nil ys ↦ ys` is the clause
`vappend nil ys = ys` of the step, whose made row is typed after the match at `vec (add m k)`
(`VectorAppend.vappend_typedAfterMatch`): the match teaches `m ≐ 0`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.VectorFunction

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open AlgebraicSchema AlgebraicParallel ConversionCoherence
open ConstructorSystem (System LeftSide Pattern ConstructorPresentation)
open ProgrammingOnTheStep.VectorPackage

/-! ## The declaration -/

/-- The rows of addition and append. -/
inductive VecStep : {n : Nat} → Tower.Tm n → Tower.Tm n → Prop
  | addZero {n : Nat} (b : Tower.Tm n) : VecStep (.app (.app (.const addN) (.const zeroN)) b) b
  | addSucc {n : Nat} (a b : Tower.Tm n) :
      VecStep (.app (.app (.const addN) (.app (.const succN) a)) b)
        (.app (.const succN) (.app (.app (.const addN) a) b))
  | appendNil {n : Nat} (m k ys : Tower.Tm n) :
      VecStep (.app (.app (.app (.app (.const appendN) m) k) (.const nilN)) ys) ys
  | appendCons {n : Nat} (m k m' x xs ys : Tower.Tm n) :
      VecStep (.app (.app (.app (.app (.const appendN) m) k) (.app (.app (.app (.const consN) m') x) xs)) ys)
        (.app (.app (.app (.const consN) (.app (.app (.const addN) m') k)) x)
          (.app (.app (.app (.app (.const appendN) m') k) xs) ys))

def vecComputation : RootComputation Tower.Head where
  step l r := VecStep l r
  rename := by
    intro n m ρ left right h
    exact match h with
      | .addZero b => VecStep.addZero (Presentation.rename ρ b)
      | .addSucc a b => VecStep.addSucc (Presentation.rename ρ a) (Presentation.rename ρ b)
      | .appendNil m k ys =>
          VecStep.appendNil (Presentation.rename ρ m) (Presentation.rename ρ k) (Presentation.rename ρ ys)
      | .appendCons m k m' x xs ys =>
          VecStep.appendCons (Presentation.rename ρ m) (Presentation.rename ρ k) (Presentation.rename ρ m')
            (Presentation.rename ρ x) (Presentation.rename ρ xs) (Presentation.rename ρ ys)
  substitute := by
    intro n m σ left right h
    exact match h with
      | .addZero b => VecStep.addZero (subst σ b)
      | .addSucc a b => VecStep.addSucc (subst σ a) (subst σ b)
      | .appendNil m k ys => VecStep.appendNil (subst σ m) (subst σ k) (subst σ ys)
      | .appendCons m k m' x xs ys =>
          VecStep.appendCons (subst σ m) (subst σ k) (subst σ m') (subst σ x) (subst σ xs) (subst σ ys)

/-- The vector package with addition and append computing. -/
abbrev arules : Rules Tower.Head := declare rules vecComputation

theorem append_rootDeterministic : RootDeterministic vecComputation := by
  intro n l r r' h h'
  cases h with
  | addZero b => cases h' with
    | addZero => rfl
  | addSucc a b => cases h' with
    | addSucc => rfl
  | appendNil m k ys => cases h' with
    | appendNil => rfl
  | appendCons m k m' x xs ys => cases h' with
    | appendCons => rfl

/-! ## A constructor system -/

/-- The four rows, as open equations. -/
inductive VecSchema : {arity : Nat} → Tower.Tm arity → Tower.Tm arity → Prop
  | addZero : VecSchema (arity := 1) (.app (.app (.const addN) (.const zeroN)) (.var 0)) (.var 0)
  | addSucc : VecSchema (arity := 2) (.app (.app (.const addN) (.app (.const succN) (.var 0))) (.var 1))
      (.app (.const succN) (.app (.app (.const addN) (.var 0)) (.var 1)))
  | appendNil : VecSchema (arity := 3)
      (.app (.app (.app (.app (.const appendN) (.var 2)) (.var 1)) (.const nilN)) (.var 0)) (.var 0)
  | appendCons : VecSchema (arity := 6)
      (.app (.app (.app (.app (.const appendN) (.var 5)) (.var 4))
        (.app (.app (.app (.const consN) (.var 3)) (.var 2)) (.var 1))) (.var 0))
      (.app (.app (.app (.const consN) (.app (.app (.const addN) (.var 3)) (.var 4))) (.var 2))
        (.app (.app (.app (.app (.const appendN) (.var 3)) (.var 4)) (.var 1)) (.var 0)))

def vecPresentation : SchemaPresentation arules where
  schema := VecSchema
  sound := by
    intro arity ambient left right rule σ
    cases rule with
    | addZero => exact Or.inr (VecStep.addZero (σ 0))
    | addSucc => exact Or.inr (VecStep.addSucc (σ 0) (σ 1))
    | appendNil => exact Or.inr (VecStep.appendNil (σ 2) (σ 1) (σ 0))
    | appendCons => exact Or.inr (VecStep.appendCons (σ 5) (σ 4) (σ 3) (σ 2) (σ 1) (σ 0))
  cover := by
    intro n source target step
    rcases step with impossible | step
    · exact impossible.elim
    · exact match step with
        | .addZero b => ⟨1, _, _, fun _ => b, .addZero, rfl, rfl⟩
        | .addSucc a b => ⟨2, _, _, Fin.cases a (fun _ => b), .addSucc, rfl, rfl⟩
        | .appendNil m k ys => ⟨3, _, _, Fin.cases ys (Fin.cases k (fun _ => m)), .appendNil, rfl, rfl⟩
        | .appendCons m k m' x xs ys =>
            ⟨6, _, _, Fin.cases ys (Fin.cases xs (Fin.cases x (Fin.cases m' (Fin.cases k (fun _ => m))))),
              .appendCons, rfl, rfl⟩

/-- The defined constants: addition and append. -/
def Defined (name : DeclName) : Prop := name = addN ∨ name = appendN

theorem zero_free : ¬ Defined zeroN := by unfold Defined; decide
theorem succ_free : ¬ Defined succN := by unfold Defined; decide
theorem nil_free : ¬ Defined nilN := by unfold Defined; decide
theorem cons_free : ¬ Defined consN := by unfold Defined; decide

/-- Every left side is a defined constant at its arity over constructor patterns. -/
theorem vec_left {m : Nat} {left right : Tower.Tm m} (rule : VecSchema left right) :
    ∃ name count, LeftSide Defined left name count := by
  cases rule with
  | addZero => exact ⟨addN, 2, .app (.app (.const addN) (.const zero_free)) (.var 0)⟩
  | addSucc => exact ⟨addN, 2, .app (.app (.const addN) (.app (.const succ_free) (.var 0))) (.var 1)⟩
  | appendNil =>
      exact ⟨appendN, 4, .app (.app (.app (.app (.const appendN) (.var 2)) (.var 1)) (.const nil_free)) (.var 0)⟩
  | appendCons =>
      exact ⟨appendN, 4, .app (.app (.app (.app (.const appendN) (.var 5)) (.var 4))
        (.app (.app (.app (.const cons_free) (.var 3)) (.var 2)) (.var 1))) (.var 0)⟩

theorem vec_covered {m : Nat} {left right : Tower.Tm m} (rule : VecSchema left right) :
    ∀ index, 0 < variableMultiplicity index right → 0 < variableMultiplicity index left := by
  cases rule with
  | addZero => decide
  | addSucc => decide
  | appendNil => decide
  | appendCons => decide

/-- **The rows do not overlap**: two left sides with a common instance are one row. -/
theorem vec_disjoint {m m' : Nat} {left right : Tower.Tm m} {left' right' : Tower.Tm m'}
    (rule : VecSchema left right) (rule' : VecSchema left' right')
    (unifies : ConstructorSystem.unifiable left left' = true) :
    (⟨m, (left, right)⟩ : Σ arity : Nat, Tower.Tm arity × Tower.Tm arity) = ⟨m', (left', right')⟩ := by
  cases rule <;> cases rule' <;> first | rfl | exact absurd unifies (by decide)

/-- **Addition and append form a constructor system.** -/
def vecSystem : System Tower.Head where
  schema := VecSchema
  defined := Defined
  arity name := if name = appendN then 4 else 2
  left := by
    intro m left right rule
    cases rule with
    | addZero =>
        exact ⟨addN, Or.inl rfl, by decide,
          .app (.app (.const addN) (.const zero_free)) (.var 0)⟩
    | addSucc =>
        exact ⟨addN, Or.inl rfl, by decide,
          .app (.app (.const addN) (.app (.const succ_free) (.var 0))) (.var 1)⟩
    | appendNil =>
        exact ⟨appendN, Or.inr rfl, by decide,
          .app (.app (.app (.app (.const appendN) (.var 2)) (.var 1)) (.const nil_free)) (.var 0)⟩
    | appendCons =>
        exact ⟨appendN, Or.inr rfl, by decide,
          .app (.app (.app (.app (.const appendN) (.var 5)) (.var 4))
            (.app (.app (.app (.const cons_free) (.var 3)) (.var 2)) (.var 1))) (.var 0)⟩
  linear := by
    intro arity left right rule
    cases rule with
    | addZero => unfold LeftLinear; decide
    | addSucc => unfold LeftLinear; decide
    | appendNil => unfold LeftLinear; decide
    | appendCons => unfold LeftLinear; decide
  covered := vec_covered
  determined := ConstructorSystem.determined_of_disjoint vec_left vec_covered vec_disjoint

def appendConstructors : ConstructorPresentation arules where
  presentation := vecPresentation
  system := vecSystem
  same _ _ := Iff.rfl
  symmetric := ⟨fun _ _ same => Interface.DependentFull.Controls.setting.levels.headEq_symm same⟩

/-- **Conversion with addition and append declared computing is Church–Rosser.** -/
theorem append_churchRosser : ChurchRosser arules := appendConstructors.churchRosser

/-! ## Ground calls terminate: structural recursion on the vector -/

/-- Ground vectors of numerals, indexed by their length: `nil`, and `cons k x xs` with `xs` of
length `k`. -/
inductive VecValue : Nat → Tower.Tm 0 → Prop
  | nil : VecValue 0 (.const nilN)
  | cons {k : Nat} {xs : Tower.Tm 0} (x : Nat) :
      VecValue k xs → VecValue (k + 1) (.app (.app (.app (.const consN) (numeral k)) (numeral x)) xs)

theorem numeral_normal_append {n : Nat} (k : Nat) :
    ConstructorSystem.Normal arules (numeral k : Tower.Tm n) := by
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

/-- No root step starts at a spine headed by `cons`. -/
theorem no_root_cons {n count : Nat} {t u : Tower.Tm n}
    (head : ConstructorSystem.spineHead t = some (consN, count)) : ¬ arules.computation.step t u := by
  intro step
  obtain ⟨name, count', defined, head'⟩ := ConstructorSystem.computation_head appendConstructors step
  rw [head] at head'
  cases head'
  exact cons_free defined

/-- No root step starts at `nil`. -/
theorem no_root_nil {n : Nat} {u : Tower.Tm n} : ¬ arules.computation.step (.const nilN) u := by
  intro step
  obtain ⟨name, count, defined, head⟩ := ConstructorSystem.computation_head appendConstructors step
  cases head
  exact nil_free defined

/-- Ground vectors are normal. -/
theorem vecValue_normal {k : Nat} {v : Tower.Tm 0} (value : VecValue k v) :
    ConstructorSystem.Normal arules v := by
  induction value with
  | nil =>
      intro t h
      cases h with
      | root h => exact no_root_nil h
  | cons x _ ih =>
      intro t h
      cases h with
      | root h => exact no_root_cons rfl h
      | congAppFun h =>
          cases h with
          | root h => exact no_root_cons rfl h
          | congAppFun h =>
              cases h with
              | root h => exact no_root_cons rfl h
              | congAppFun h =>
                  cases h with
                  | root h => exact no_root_cons rfl h
              | congAppArg h => exact numeral_normal_append _ h
          | congAppArg h => exact numeral_normal_append _ h
      | congAppArg h => exact ih h

theorem stepStar_succArg {n : Nat} {t t' : Tower.Tm n} (steps : StepStar arules t t') :
    StepStar arules (.app (.const succN) t) (.app (.const succN) t') := by
  induction steps with
  | refl => exact .refl
  | tail _ step ih => exact .tail ih (.congAppArg step)

/-- Addition of numerals runs in the declared package. -/
theorem add_numerals_append {n : Nat} (a b : Nat) :
    StepStar arules (.app (.app (.const addN) (numeral a)) (numeral b) : Tower.Tm n)
      (numeral (a + b)) := by
  induction a with
  | zero =>
      rw [Nat.zero_add]
      exact .single (.root (declare_step (VecStep.addZero (numeral b))))
  | succ a ih =>
      rw [Nat.add_right_comm]
      exact .head (.root (declare_step (VecStep.addSucc (numeral a) (numeral b)))) (stepStar_succArg ih)

theorem stepStar_consLength {n : Nat} {k k' x xs : Tower.Tm n} (steps : StepStar arules k k') :
    StepStar arules (.app (.app (.app (.const consN) k) x) xs) (.app (.app (.app (.const consN) k') x) xs) := by
  induction steps with
  | refl => exact .refl
  | tail _ step ih => exact .tail ih (.congAppFun (.congAppFun (.congAppArg step)))

theorem stepStar_consTail {n : Nat} {k x xs xs' : Tower.Tm n} (steps : StepStar arules xs xs') :
    StepStar arules (.app (.app (.app (.const consN) k) x) xs) (.app (.app (.app (.const consN) k) x) xs') := by
  induction steps with
  | refl => exact .refl
  | tail _ step ih => exact .tail ih (.congAppArg step)

/-- **Appending two ground vectors reaches a ground vector of the summed length.** -/
theorem append_reaches {a b : Nat} {v w : Tower.Tm 0} (hv : VecValue a v) (hw : VecValue b w) :
    ∃ u, VecValue (a + b) u ∧
      StepStar arules (.app (.app (.app (.app (.const appendN) (numeral a)) (numeral b)) v) w) u := by
  induction hv with
  | nil =>
      refine ⟨w, by rw [Nat.zero_add]; exact hw, ?_⟩
      exact .single (.root (declare_step (VecStep.appendNil (numeral 0) (numeral b) w)))
  | @cons k xs x _ ih =>
      obtain ⟨u, hu, steps⟩ := ih
      refine ⟨.app (.app (.app (.const consN) (numeral (k + b))) (numeral x)) u, ?_, ?_⟩
      · rw [Nat.add_right_comm]
        exact .cons x hu
      · exact .head (.root (declare_step (VecStep.appendCons (numeral (k + 1)) (numeral b) (numeral k)
            (numeral x) xs w)))
          ((stepStar_consLength (add_numerals_append k b)).trans (stepStar_consTail steps))

/-- **Every ground call of append has an answer, a ground vector.** -/
theorem append_answer {a b : Nat} {v w : Tower.Tm 0} (hv : VecValue a v) (hw : VecValue b w) :
    ∃ u, VecValue (a + b) u ∧
      Answer arules (.app (.app (.app (.app (.const appendN) (numeral a)) (numeral b)) v) w) u := by
  obtain ⟨u, hu, steps⟩ := append_reaches hv hw
  exact ⟨u, hu, steps, vecValue_normal hu⟩

/-- **... and exactly one.** -/
theorem append_answer_unique {a b : Nat} {v w : Tower.Tm 0} (hv : VecValue a v) (hw : VecValue b w) :
    ∃ u, VecValue (a + b) u ∧
      ∀ u', Answer arules (.app (.app (.app (.app (.const appendN) (numeral a)) (numeral b)) v) w) u' ↔
        u' = u := by
  obtain ⟨u, hu, answer⟩ := append_answer hv hw
  exact ⟨u, hu, fun u' => ⟨fun answer' => answer_unique append_churchRosser answer' answer,
    fun same => same ▸ answer⟩⟩

/-- `[x]`, of length one. -/
abbrev single (x : Nat) : Tower.Tm 0 := .app (.app (.app (.const consN) (numeral 0)) (numeral x)) (.const nilN)

/-- **`append [2] [3]` answers `[2, 3]`.** -/
theorem append_example :
    Answer arules (.app (.app (.app (.app (.const appendN) (numeral 1)) (numeral 1)) (single 2)) (single 3))
      (.app (.app (.app (.const consN) (numeral 1)) (numeral 2)) (single 3)) := by
  refine ⟨?_, vecValue_normal (.cons 2 (.cons 3 .nil))⟩
  exact .head (.root (declare_step (VecStep.appendCons (numeral 1) (numeral 1) (numeral 0) (numeral 2)
      (.const nilN) (single 3))))
    ((stepStar_consLength (add_numerals_append 0 1)).trans
      (stepStar_consTail (.single (.root (declare_step (VecStep.appendNil (numeral 0) (numeral 1)
        (single 3)))))))

end NativeTypesOnTheStep.Computing.VectorFunction

#print axioms NativeTypesOnTheStep.Computing.VectorFunction.vecComputation
#print axioms NativeTypesOnTheStep.Computing.VectorFunction.append_rootDeterministic
#print axioms NativeTypesOnTheStep.Computing.VectorFunction.vecPresentation
#print axioms NativeTypesOnTheStep.Computing.VectorFunction.vec_disjoint
#print axioms NativeTypesOnTheStep.Computing.VectorFunction.vecSystem
#print axioms NativeTypesOnTheStep.Computing.VectorFunction.appendConstructors
#print axioms NativeTypesOnTheStep.Computing.VectorFunction.append_churchRosser
#print axioms NativeTypesOnTheStep.Computing.VectorFunction.vecValue_normal
#print axioms NativeTypesOnTheStep.Computing.VectorFunction.add_numerals_append
#print axioms NativeTypesOnTheStep.Computing.VectorFunction.append_reaches
#print axioms NativeTypesOnTheStep.Computing.VectorFunction.append_answer
#print axioms NativeTypesOnTheStep.Computing.VectorFunction.append_answer_unique
#print axioms NativeTypesOnTheStep.Computing.VectorFunction.append_example

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
