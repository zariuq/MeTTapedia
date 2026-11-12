import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgrammingOnTheStep.ConversionContrast

/-!
# Value types computed in conversion: the interpreter's answer meets its declared type

`TypedInterpreter` shows that a value type evaluated by firings never meets the type of the value:
`val tnat` and `nat` are apart. Here the value type computes in conversion instead. In the tree's
package of natural numbers with their recursor into level 1 (`TowerArithmeticModel.rules`), the
large elimination

`V t = num-rec (λ_. U0) num (λx T. T) t`

is a type for each `t : num`, and at `t = zero` it computes to `num` by the recursor's equation
(`value_type_computes`). So the answer `3 : num` has the declared type `V zero`
(`answer_has_declared_type`), and a hole of type `V zero` and the answer can be equated in the
knowledge (`return_solvable`), where in the rigid package the same return is refused
(`TypedInterpreter.return_refused`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ProgrammingOnTheStep.LargeElimination

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open TowerArithmeticModel
open TowerNumbersModel (num zero succ numRec ctors u)

/-- The recursor's motives land in level 1, so `λ_. U0` is a motive. -/
abbrev level1 : LevelExpr Nat := .succ Tower.zero

abbrev pkg : Rules Tower.Head := TowerArithmeticModel.rules level1

abbrev pkgLevels : LevelModel pkg ℕ := TowerArithmeticModel.levels level1 (fun _ => 0)

abbrev U0 {n : Nat} : Tower.Tm n := .head (.sort Tower.zero)
abbrev U1 {n : Nat} : Tower.Tm n := .head (.sort level1)

theorem num_typed' {n : Nat} (Γ : Tower.Ctx n) : Typed pkg Γ (.const num) U0 :=
  TowerNumbersModel.num_typed LevelTower.HeadTyping.sort LevelTower.IsUniverse.sort (declaredNum level1)

theorem zero_typed' {n : Nat} (Γ : Tower.Ctx n) : Typed pkg Γ (.const zero) (.const num) :=
  .const (declaredZero level1) (num_typed' .nil) (.sort _)

theorem succ_typed' {n : Nat} (Γ : Tower.Ctx n) :
    Typed pkg Γ (.const succ) (.pi (.const num) (.const num)) :=
  .const (declaredSucc level1) (.piForm (num_typed' _) (.sort _) (num_typed' _) (.sort _) (.sorts _ _))
    (.sort _)

theorem rec_typed {n : Nat} (Γ : Tower.Ctx n) :
    Typed pkg Γ (.const numRec) (liftClosed (recType num (.sort level1) ctors)) := by
  obtain ⟨w, hw, typed⟩ := TowerNumbersModel.recType_typed (lv := level1)
  exact .const (declaredRec level1) (Derivable.mono (sub₂ level1) typed) hw

/-! ## The motive `λ_. U0` -/

def motive {n : Nat} : Tower.Tm n := .lam U0

theorem motiveType_formed {n : Nat} (Γ : Tower.Ctx n) :
    Typed pkg Γ (.pi (.const num) U1) (.head (.sort (.max Tower.zero (.succ level1)))) :=
  .piForm (num_typed' Γ) (.sort _) (.headType (.sort _)) (.sort _) (.sorts _ _)

theorem motive_typed {n : Nat} (Γ : Tower.Ctx n) : Typed pkg Γ motive (.pi (.const num) U1) :=
  .lamIntro (motiveType_formed Γ) (.sort _) (.headType (.sort _))

/-- **The motive computes**: `(λ_. U0) t ≡ U0` at `U1`, by β. -/
theorem motive_beta {n : Nat} {Γ : Tower.Ctx n} {t : Tower.Tm n} (typed : Typed pkg Γ t (.const num)) :
    Equal pkg Γ (.app motive t) U0 U1 :=
  .betaPi (motiveType_formed Γ) (.sort _) (.headType (.sort _)) typed

/-- A small type is a value of the motive at any `t`. -/
theorem into_motive {n : Nat} {Γ : Tower.Ctx n} {a t : Tower.Tm n} (typedA : Typed pkg Γ a U0)
    (typedT : Typed pkg Γ t (.const num)) : Typed pkg Γ a (.app motive t) :=
  .conv typedA (.symm (motive_beta typedT)) (.sort _)

/-! ## The step method `λx T. T` -/

def stepMethod {n : Nat} : Tower.Tm n := .lam (.lam (.var 0))

theorem stepMethod_typed {n : Nat} (Γ : Tower.Ctx n) :
    Typed pkg Γ stepMethod
      (.pi (.const num) (.pi (.app motive (.var 0)) (.app motive (.app (.const succ) (.var 1))))) := by
  have x : Typed pkg (.snoc Γ (.const num)) (.var 0) (.const num) := Derivable.var 0
  have domain : Typed pkg (.snoc Γ (.const num)) (.app motive (.var 0)) U1 := by
    have typed := Derivable.appElim (motive_typed (.snoc Γ (.const num))) x
    exact typed
  have succX : Typed pkg (.snoc (.snoc Γ (.const num)) (.app motive (.var 0)))
      (.app (.const succ) (.var 1)) (.const num) :=
    .appElim (succ_typed' _) (Derivable.var 1)
  have codomain : Typed pkg (.snoc (.snoc Γ (.const num)) (.app motive (.var 0)))
      (.app motive (.app (.const succ) (.var 1))) U1 := by
    have typed := Derivable.appElim (motive_typed _) succX
    exact typed
  have inner : Typed pkg (.snoc Γ (.const num))
      (.pi (.app motive (.var 0)) (.app motive (.app (.const succ) (.var 1))))
      (.head (.sort (.max level1 level1))) :=
    .piForm domain (.sort _) codomain (.sort _) (.sorts _ _)
  have outer : Typed pkg Γ
      (.pi (.const num) (.pi (.app motive (.var 0)) (.app motive (.app (.const succ) (.var 1)))))
      (.head (.sort (.max Tower.zero (.max level1 level1)))) :=
    .piForm (num_typed' _) (.sort _) inner (.sort _) (.sorts _ _)
  have small : Typed pkg (.snoc (.snoc Γ (.const num)) (.app motive (.var 0))) (.var 0) U0 := by
    have here : Typed pkg (.snoc (.snoc Γ (.const num)) (.app motive (.var 0))) (.var 0)
        (.app motive (.var 1)) := Derivable.var 0
    exact .conv here (motive_beta (Derivable.var 1)) (.sort _)
  have body : Typed pkg (.snoc (.snoc Γ (.const num)) (.app motive (.var 0))) (.var 0)
      (.app motive (.app (.const succ) (.var 1))) := into_motive small succX
  exact .lamIntro outer (.sort _) (.lamIntro inner (.sort _) body)

/-! ## The value type -/

/-- `V zero = num-rec (λ_. U0) num (λx T. T) zero`. -/
def valueType {n : Nat} : Tower.Tm n :=
  .app (.app (.app (.app (.const numRec) motive) (.const num)) stepMethod) (.const zero)

theorem valueType_typed {n : Nat} (Γ : Tower.Ctx n) :
    Typed pkg Γ valueType (.app motive (.const zero)) := by
  have typed := Derivable.appElim (Derivable.appElim (Derivable.appElim (Derivable.appElim (rec_typed Γ)
    (motive_typed Γ)) (into_motive (num_typed' Γ) (zero_typed' Γ))) (stepMethod_typed Γ)) (zero_typed' Γ)
  exact typed

/-- The recursor's equation at `zero`. -/
theorem iota_zero {n : Nat} : pkg.computation.step (valueType : Tower.Tm n) (.const num) :=
  .inl ⟨motive, [.const num, stepMethod], 0, zero, [], [], .const num, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The value type computes to `num`**, in conversion. -/
theorem value_type_computes {n : Nat} (Γ : Tower.Ctx n) : TypeEq pkg Γ valueType (.const num) := by
  have atMotive : Equal pkg Γ valueType (.const num) (.app motive (.const zero)) :=
    .root iota_zero (valueType_typed Γ) (into_motive (num_typed' Γ) (zero_typed' Γ))
  exact ⟨.sort Tower.zero, .sort _, .convEq atMotive (motive_beta (zero_typed' Γ)) (.sort _)⟩

/-! ## The interpreter's answer -/

def three {n : Nat} : Tower.Tm n :=
  .app (.const succ) (.app (.const succ) (.app (.const succ) (.const zero)))

theorem three_typed {n : Nat} (Γ : Tower.Ctx n) : Typed pkg Γ three (.const num) :=
  .appElim (succ_typed' _) (.appElim (succ_typed' _) (.appElim (succ_typed' _) (zero_typed' _)))

/-- **The answer `3 : num` has the declared type `V zero`.** -/
theorem answer_has_declared_type {n : Nat} (Γ : Tower.Ctx n) : Typed pkg Γ three valueType := by
  obtain ⟨w, hw, same⟩ := value_type_computes Γ
  exact .conv (three_typed Γ) (.symm same) hw

/-- `V zero`, as a formed type of the empty frame. -/
def valueOver : TypeOver (empty pkg) :=
  ⟨valueType, .sort Tower.zero, .sort _, .conv (valueType_typed _) (motive_beta (zero_typed' _)) (.sort _)⟩

def numOver : TypeOver (empty pkg) := ⟨.const num, u, .sort _, num_typed' _⟩

/-- **The return is solvable**: the answer at its declared type equals the answer at `num`. -/
def returnStore : EquationStore (TotalTerm (empty pkg)) :=
  [(⟨valueOver, ⟨three, answer_has_declared_type _⟩⟩, ⟨numOver, ⟨three, three_typed _⟩⟩)]

theorem return_solvable : (frames pkgLevels).Solvable returnStore := by
  refine ⟨empty pkg, 𝟙 _, ?_⟩
  intro e member
  obtain rfl := List.mem_singleton.mp member
  show (frames pkgLevels).E (TotalTerm.reindex _ (𝟙 _)) (TotalTerm.reindex _ (𝟙 _))
  rw [reindex_id, reindex_id]
  exact (equivalent_iff pkgLevels _ _).mpr ⟨value_type_computes _, .refl (answer_has_declared_type _)⟩

end ProgrammingOnTheStep.LargeElimination

#print axioms ProgrammingOnTheStep.LargeElimination.value_type_computes
#print axioms ProgrammingOnTheStep.LargeElimination.answer_has_declared_type
#print axioms ProgrammingOnTheStep.LargeElimination.return_solvable

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
