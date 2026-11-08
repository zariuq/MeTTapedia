import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaLongReflection
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerDecidability

/-!
# η-long reflection in the cumulative tower: controls

In the tower every hypothesis of reflection is discharged (`tower_equal_iff_common`). Then:

* **Where both apply, they agree.** `(λy. y) x : Ground` is normalized by the executable
  β-normalizer to `x`, which is η-long; so `x` is its η-long normal form, and every η-long normal
  form of it is `x` up to heads.
* **Where only the normalizer applies, η-expansion is owed.** A variable `f : Ground → Ground` is
  already β-normal; the normalizer returns `f` unchanged, and `f` is not η-long at its function
  type. Its η-long normal form is `λx. f x`.
* **Reflection decides an equation.** `λx. f x` and `λx. x` are both η-long and distinct, so they
  are not equal in the typed βη equality.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEtaLong.Controls

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization

abbrev setting := TowerModel.setting (fun _ => (0 : Nat))

theorem rigid (name : DeclName) : setting.roles name = .rigid := rfl

/-- Reflection in the tower, with no hypotheses left. -/
theorem tower_equal_iff_common {n : Nat} {Γ : Tower.Ctx n} (formed : CtxFormed Tower.rules Γ)
    {t u A : Tower.Tm n} :
    Equal Tower.rules Γ t u A ↔
      ∃ v, NormalForm Tower.rules TowerModel.roles Γ t v A ∧
        NormalForm Tower.rules TowerModel.roles Γ u v A :=
  equal_iff_common (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra TowerModel.complete rigid formed

def ground {n : Nat} : Tower.Tm n := .head .legacyGround
def arrow {n : Nat} : Tower.Tm n := .pi ground ground

theorem ground_typed {n : Nat} (Γ : Tower.Ctx n) :
    Typed Tower.rules Γ ground (.head (.sort Tower.zero)) := .headType .legacyGround

theorem ground_isType {n : Nat} (Γ : Tower.Ctx n) : IsType Tower.rules Γ ground :=
  ⟨_, .sort _, ground_typed Γ⟩

theorem arrow_typed {n : Nat} (Γ : Tower.Ctx n) :
    Typed Tower.rules Γ arrow (.head (.sort (.max Tower.zero Tower.zero))) :=
  .piForm (ground_typed Γ) (.sort _) (ground_typed _) (.sort _) (.sorts _ _)

theorem arrow_isType {n : Nat} (Γ : Tower.Ctx n) : IsType Tower.rules Γ arrow :=
  ⟨_, .sort _, arrow_typed Γ⟩

theorem ground_base {n : Nat} {Γ : Tower.Ctx n} (formed : CtxFormed Tower.rules Γ) :
    Base Tower.rules Γ ground :=
  ⟨fun _ _ e => TypeEq.pi_ne_head TowerModel.facts formed e.symm,
    fun _ _ e => TypeEq.sigma_ne_head TowerModel.facts formed e.symm⟩

/-- A variable of type `Ground` is η-long. -/
theorem point_long {n : Nat} {Γ : Tower.Ctx n} (formed : CtxFormed Tower.rules Γ) (i : Fin n)
    (lookup : Ctx.lookup Γ i = ground) :
    Long Tower.rules TowerModel.roles (.term Γ (.var i) ground) := by
  have typed : Typed Tower.rules Γ (.var i) ground := lookup ▸ Derivable.var i
  have same : TypeEq Tower.rules Γ ground (Ctx.lookup Γ i) := by
    rw [lookup]; exact IsType.refl (ground_isType Γ)
  exact .neutral (.var i same)
    (IsType.below_refl (ground_isType Γ)) typed (ground_base formed)

/-! ## Where both apply -/

/-- The telescope `x : Ground`. -/
def points : Tower.Ctx 1 := .snoc .nil ground

theorem points_formed : CtxFormed Tower.rules points := .snoc .nil (ground_isType _)

def redex : Tower.Tm 1 := .app (.lam (.var 0)) (.var 0)

theorem redex_typed : Typed Tower.rules points redex ground :=
  .appElim (.lamIntro (arrow_typed _) (.sort _) (.var 0)) (.var 0)

theorem redex_normalized :
    ExecutableReduction.normalizeTerm Tower.rules (fun _ => none) 4 redex = some (.var 0) := by
  rfl'

/-- **The normalizer's result is the η-long normal form.** -/
theorem redex_normalForm :
    NormalForm Tower.rules TowerModel.roles points redex (.var 0) ground :=
  normalizer_normalForm (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    points_formed redex_typed redex_normalized (point_long points_formed 0 rfl)

theorem redex_agrees {v : Tower.Tm 1}
    (normal : NormalForm Tower.rules TowerModel.roles points redex v ground) :
    SameUpToHeads Tower.rules (.var 0) v :=
  normalizer_agrees (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra TowerModel.complete points_formed redex_typed redex_normalized
    (point_long points_formed 0 rfl) normal

/-! ## Where η-expansion is owed -/

/-- The telescope `f : Ground → Ground`. -/
def functions : Tower.Ctx 1 := .snoc .nil arrow

theorem functions_formed : CtxFormed Tower.rules functions := .snoc .nil (arrow_isType _)

def applied : Tower.Ctx 2 := .snoc functions ground

theorem applied_formed : CtxFormed Tower.rules applied := .snoc functions_formed (ground_isType _)

/-- `λx. f x`. -/
def expanded : Tower.Tm 1 := .lam (.app (.var 1) (.var 0))

/-- `λx. x`. -/
def identity : Tower.Tm 1 := .lam (.var 0)

theorem function_typed : Typed Tower.rules functions (.var 0) arrow := Derivable.var 0

theorem expanded_typed : Typed Tower.rules functions expanded arrow :=
  .lamIntro (arrow_typed _) (.sort _) (.appElim (A := ground) (B := ground) (Derivable.var 1) (Derivable.var 0))

theorem identity_typed : Typed Tower.rules functions identity arrow :=
  .lamIntro (arrow_typed _) (.sort _) (Derivable.var 0)

theorem function_normalized :
    ExecutableReduction.normalizeTerm Tower.rules (fun _ => none) 4 (.var 0 : Tower.Tm 1) =
      some (.var 0) := by
  rfl'

/-- The β-normal variable `f` is not η-long at its function type. -/
theorem function_not_long : ¬ Long Tower.rules TowerModel.roles (.term functions (.var 0) arrow) := by
  intro long
  obtain ⟨_, _, _, same, _⟩ := Long.lam_of_pi (S := setting) TowerModel.facts functions_formed long
  cases same

theorem expanded_long : Long Tower.rules TowerModel.roles (.term functions expanded arrow) := by
  have argument := point_long applied_formed 0 rfl
  have spine : Long Tower.rules TowerModel.roles (.spine applied (.app (.var 1) (.var 0)) ground) :=
    .app (.var 1 (IsType.refl (arrow_isType applied))) (IsType.refl (arrow_isType applied)) argument
      (IsType.refl (ground_isType applied))
  exact .lam (IsType.refl (arrow_isType functions)) (ground_isType _) expanded_typed
    (.neutral spine (IsType.below_refl (ground_isType applied))
      (.appElim (A := ground) (B := ground) (Derivable.var 1) (Derivable.var 0)) (ground_base applied_formed))

theorem identity_long : Long Tower.rules TowerModel.roles (.term functions identity arrow) :=
  .lam (IsType.refl (arrow_isType functions)) (ground_isType _) identity_typed
    (point_long applied_formed 0 rfl)

/-- Function η: `f` equals `λx. f x`. -/
theorem function_eta : Equal Tower.rules functions (.var 0) expanded arrow :=
  .etaPi function_typed expanded_typed
    (.symm (.betaPi (arrow_typed applied) (.sort _)
      (.appElim (A := ground) (B := ground) (Derivable.var 2) (Derivable.var 0)) (Derivable.var 0)))

/-- **The η-long normal form of `f` is `λx. f x`**, not the normalizer's result `f`. -/
theorem function_normalForm : NormalForm Tower.rules TowerModel.roles functions (.var 0) expanded arrow :=
  ⟨expanded_long, function_eta⟩

/-- **Reflection refutes an equation**: `λx. f x` and `λx. x` are distinct η-long forms. -/
theorem expanded_ne_identity : ¬ Equal Tower.rules functions expanded identity arrow := by
  intro equal
  have same := long_unique (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra TowerModel.complete functions_formed expanded_long identity_long equal
  cases same with
  | lam body => cases body

end ContextualDependentEtaLong.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
