import Mettapedia.OSLF.Syntax.BindingSignature
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Types.Basic

/-!
# The syntactic category of a binding signature

A signature's contexts and substitutions form a category: objects are contexts,
morphisms are substitutions, the identity is the vector of variables and
composition is substitution.  This is the standard *category of contexts*, and
it is what a language definition's first component denotes.  Naming it is not
cosmetic: once it is a category, the change-of-signature layer is a functor
between categories rather than a collection of transport lemmas, and the terms
of a given sort are a presheaf on it rather than a family of types.

Everything needed was already proved for its own sake -- the unit and
associativity of substitution are the category's identity and associativity laws
-- so the category is a reading of existing results rather than new work.  What
is new here is the reading, the representability of terms, and the presheaf.

Neither Mathlib nor the classical-mathematics libraries carry this: Mathlib's
category theory is the pure machinery, with nothing about syntax.
-/

namespace Mettapedia.OSLF.Binding

open CategoryTheory

set_option autoImplicit false

variable {S : Signature}

namespace Syntactic

/-- An object of the syntactic category: a context of the signature. -/
structure Ctxt (S : Signature) where
  /-- The sorts the context assigns, in order. -/
  vars : Ctx S

/-- A morphism `Γ ⟶ Δ` fulfils the assumptions `Δ` requires by interpreting
them with terms over `Γ`.  That is a substitution, in the direction the source's
"classifying form" reads it. -/
instance syntacticCategory (S : Signature) : Category (Ctxt S) where
  Hom Γ Δ := Sub S Δ.vars Γ.vars
  id _ := fun _ v => Term.var v
  comp f g := fun _ v => bind f (g _ v)
  id_comp f := by
    funext s v
    exact bind_id (f s v)
  comp_id _ := rfl
  assoc f g h := by
    funext s v
    exact (bind_comp g f (h s v)).symm

@[simp] theorem id_apply (Γ : Ctxt S) {s : S.Srt} (v : Var Γ.vars s) :
    (𝟙 Γ : Γ ⟶ Γ) s v = Term.var v := rfl

@[simp] theorem comp_apply {Γ Δ Θ : Ctxt S} (f : Γ ⟶ Δ) (g : Δ ⟶ Θ)
    {s : S.Srt} (v : Var Θ.vars s) : (f ≫ g) s v = bind f (g s v) := rfl

/-! ## Terms are represented

The one-variable context represents terms of that sort: a morphism into it is
exactly a term.  So `Term` is not an auxiliary family beside the category, it is
what the category's hom-sets already are. -/

/-- The context with a single variable of sort `s`. -/
def single (s : S.Srt) : Ctxt S := ⟨[s]⟩

/-- **Terms of sort `s` over `Γ` are the morphisms `Γ ⟶ single s`.** -/
def termsRepresented (Γ : Ctxt S) (s : S.Srt) :
    (Γ ⟶ single s) ≃ Term S Γ.vars s where
  toFun f := f s Var.zero
  invFun t := fun _ v =>
    match v with
    | .zero => t
    | .succ w => nomatch w
  left_inv f := by
    funext r v
    cases v with
    | zero => rfl
    | succ w => exact nomatch w
  right_inv _ := rfl

/-! ## Terms are a presheaf

Substitution is the action, and its unit and associativity laws are exactly
functoriality. The presheaf laws here are `bind_id` and `bind_comp`, read on the
other side. `SyntacticTermPresheaf` packages this action as a
`CategoryTheory.Functor` into `Type` using its concrete hom structure. -/

/-- Substitution as the presheaf's action, named so that its type mentions no
categorical notation and the sort is fixed before elaboration. -/
def substAction (s : S.Srt) {X Y : (Ctxt S)ᵒᵖ} (f : X ⟶ Y) :
    Term S X.unop.vars s → Term S Y.unop.vars s :=
  fun t => bind f.unop t

/-- The action of the identity is the identity. -/
theorem substAction_id (s : S.Srt) (X : (Ctxt S)ᵒᵖ) :
    substAction s (𝟙 X) = id := by
  funext t
  exact bind_id t

/-- The action of a composite is the composite of the actions, in the order a
presheaf requires. -/
theorem substAction_comp (s : S.Srt) {X Y Z : (Ctxt S)ᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    substAction s (f ≫ g) = fun t => substAction s g (substAction s f t) := by
  funext t
  exact (bind_comp f.unop g.unop t).symm

/-! ## Renaming is the sub-category of variable-to-variable substitutions

The distinction the source needs between renaming and substitution is the
distinction between the morphisms that land in variables and all of them.  It
is recorded here so that the presheaf-over-renamings reading, which is the one
abstract syntax with variable binding uses, is available alongside. -/

/-- A morphism that sends every variable to a variable. -/
def IsRenaming {Γ Δ : Ctxt S} (f : Γ ⟶ Δ) : Prop :=
  ∀ (s : S.Srt) (v : Var Δ.vars s), ∃ w : Var Γ.vars s, f s v = Term.var w

theorem isRenaming_id (Γ : Ctxt S) : IsRenaming (𝟙 Γ) :=
  fun _ v => ⟨v, rfl⟩

theorem isRenaming_comp {Γ Δ Θ : Ctxt S} {f : Γ ⟶ Δ} {g : Δ ⟶ Θ}
    (hf : IsRenaming f) (hg : IsRenaming g) : IsRenaming (f ≫ g) := by
  intro s v
  obtain ⟨w, hw⟩ := hg s v
  obtain ⟨u, hu⟩ := hf s w
  exact ⟨u, by rw [comp_apply, hw]; exact hu⟩

/-- Every renaming in the categorical sense comes from a map on variables. -/
theorem ren_of_isRenaming {Γ Δ : Ctxt S} (f : Γ ⟶ Δ) (hf : IsRenaming f) :
    ∃ rho : Ren S Δ.vars Γ.vars, ∀ (s : S.Srt) (v : Var Δ.vars s),
      f s v = Term.var (rho s v) := by
  refine ⟨fun s v => (hf s v).choose, fun s v => ?_⟩
  exact (hf s v).choose_spec

end Syntactic

end Mettapedia.OSLF.Binding
