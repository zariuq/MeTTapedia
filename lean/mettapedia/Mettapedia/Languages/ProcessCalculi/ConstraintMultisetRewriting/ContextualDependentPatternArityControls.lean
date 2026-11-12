import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPatternArity

/-!
# Controls of the derived arity

Over `A : U0, a : A, F : Π (X : U0). X`:

* **the arity read from the type is one** (`arity_one`);
* **under a local `X : U0` the pattern `F X` has one argument, by the theorem** (`pattern_arity`): the hypotheses of
  `tower_unknown_arity` hold and its conclusion is the count;
* **an argument that is not a variable breaks the count** (`applied_twice`): `F (A → A) a` is typed at `A`, which is
  not a function type, the type of `F` is normal, and the spine has two arguments. So the hypothesis that the
  arguments are variables cannot be dropped.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEtaDepth.ArityControls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentDynamicFragment ContextualDependentSpinesMany
open ContextualDependentPatternFiring.Controls
open ContextualDependentExecutableJoin (Normal)

/-- `A : U0, a : A`. -/
abbrev ctxAa := ContextualDependentInversion.Controls.small

/-- `Π (X : U0). X`, over `A a`. -/
def familyType : TypeOver ctxAa := formIn ctxAa (.pi (.head (.sort Tower.zero)) (.var 0)) (by decide +kernel)

/-- `A : U0, a : A, F : Π (X : U0). X`. -/
abbrev ctxF := extend ctxAa familyType

/-- `A`, over `A a F`. -/
def typeA : TypeOver ctxF := formIn ctxF (.var 2) (by decide +kernel)

/-- `F (A → A) a`, at `A`. -/
def twice : TotalTerm ctxF :=
  termIn ctxF typeA (.app (.app (.var 0) (.pi (.var 2) (.var 3))) (.var 1)) (by decide +kernel)

/-- A variable is not a function type. -/
theorem var_not_pi {n : Nat} {Γ : Tower.Ctx n} (formed : CtxFormed setting.R Γ) (index : Fin n) :
    ∀ domain codomain, ¬ TypeEq setting.R Γ (.var index) (.pi domain codomain) := fun _ _ equal =>
  (TypeEq.neutral_form (roles := setting.roles) TowerModel.facts equal formed (.var index)
    (.inr (.inl ⟨_, _, rfl⟩))).not_former.2.1 _ _ rfl

/-- **The arity read from the type of `F` is one.** -/
theorem arity_one : piCount (Ctx.lookup ctxF.raw (0 : Fin 3)) = 1 := by decide +kernel

theorem family_normal : Normal setting.R (Ctx.lookup ctxF.raw (0 : Fin 3)) :=
  (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)

/-- **An argument that is not a variable breaks the count**: `F (A → A) a` is typed at `A`, not a function type,
with a normal type of `F`, and has two arguments against one Π binder. -/
theorem applied_twice :
    TypedEquality.Typed setting.R ctxF.raw
        (appSpine (.var (0 : Fin 3)) [.pi (.var 2) (.var 3), .var 1]) (.var 2) ∧
      (∀ domain codomain, ¬ TypeEq setting.R ctxF.raw (.var (2 : Fin 3)) (.pi domain codomain)) ∧
      Normal setting.R (Ctx.lookup ctxF.raw (0 : Fin 3)) ∧
      ([.pi (.var 2) (.var 3), .var 1] : List (Tower.Tm 3)).length ≠ piCount (Ctx.lookup ctxF.raw (0 : Fin 3)) :=
  ⟨twice.2.typed, var_not_pi ctxF.formed 2, family_normal, by rw [arity_one]; decide⟩

/-! ### Under a local, the pattern has the arity -/

/-- `U0`, over `A a F`. -/
def universeF : TypeOver ctxF := formIn ctxF (.head (.sort Tower.zero)) (by decide +kernel)

/-- `A : U0, a : A, F : Π (X : U0). X, X : U0`. -/
abbrev ctxFX := extend ctxF universeF

/-- `X`, over `A a F X`. -/
def typeX : TypeOver ctxFX := formIn ctxFX (.var 0) (by decide +kernel)

/-- `F X`, at `X`. -/
def pattern : TotalTerm ctxFX := termIn ctxFX typeX (.app (.var 1) (.var 0)) (by decide +kernel)

/-- **The pattern `F X` has the arity read from the type of `F`**, by the theorem. -/
theorem pattern_arity : ([0] : List (Fin 4)).length = piCount (Ctx.lookup ctxFX.raw (1 : Fin 4)) :=
  tower_unknown_arity ctxFX.formed (h := 1) [0]
    (IsType.refl (Typed.isType (.var (1 : Fin 4)) ctxFX.formed))
    ((ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel))
    pattern.2.typed (var_not_pi ctxFX.formed 0)

end ContextualDependentEtaDepth.ArityControls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
