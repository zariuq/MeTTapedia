import Mathlib.CategoryTheory.Types.Basic
import Mettapedia.Logic.HOL.Embedding.ContextualStructure
import Mettapedia.Logic.HOL.Soundness

/-!
# Contextual Henkin semantics for the live HOL syntax

A Henkin model sends each syntactic context to its type of valuations and
each typed simultaneous substitution to semantic precomposition.  This is a
covariant functor from the HOL context/substitution category to `Type`.
Term denotation is compatible with that action: interpreting a substituted
term equals interpreting the original term in the transported valuation.

The functor need not be faithful.  In particular, substitutions selecting
syntactically distinct but extensionally equivalent propositions can induce
the same function on valuations.  This is why the syntactic `Scwf`, its
semantic models, and a replay checker remain separate objects in the
metatheory.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.ContextualHenkinSemantics

open CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.Logic.HOL.ContextualStructure

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Equality of valuations is pointwise equality on typed variables. -/
theorem valuation_ext (M : HenkinModel.{u, v, w} Base Const)
    {Γ : Ctx Base} {left right : HenkinModel.Valuation M Γ}
    (equal : ∀ {A : Ty Base} (boundVar : Var Γ A),
      left boundVar = right boundVar) :
    (fun {A : Ty Base} (boundVar : Var Γ A) => left boundVar) =
      (fun {A : Ty Base} (boundVar : Var Γ A) => right boundVar) := by
  funext A boundVar
  exact equal boundVar

/-- A Henkin model acts functorially on the category of HOL contexts and
typed substitutions. -/
def valuationFunctor (M : HenkinModel.{u, v, w} Base Const) :
    (holScwf Base Const).base.Context ⥤ Type (max (u + 1) w) where
  obj context := HenkinModel.Valuation M context.val
  map := fun {source target} substitution =>
    TypeCat.ofHom
      (fun (valuation : HenkinModel.Valuation M source.val) =>
        Soundness.substVal M substitution valuation)
  map_id context := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext valuation
    apply valuation_ext M
    intro A boundVar
    rfl
  map_comp earlier later := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext valuation
    apply valuation_ext M
    intro A boundVar
    change
      HenkinModel.denote M (subst earlier (later boundVar)) valuation =
        HenkinModel.denote M (later boundVar)
          (Soundness.substVal M earlier valuation)
    exact Soundness.denote_subst M earlier (later boundVar) valuation

/-- The underlying function of the semantic action is the existing
`substVal` operation. -/
theorem valuationFunctor_map_apply
    (M : HenkinModel.{u, v, w} Base Const)
    {Γ Δ : Ctx Base} (substitution : (holScwf Base Const).Sub Γ Δ)
    (valuation : HenkinModel.Valuation M Γ) {A : Ty Base}
    (boundVar : Var Δ A) :
    (valuationFunctor M).map substitution valuation boundVar =
      Soundness.substVal M substitution valuation boundVar := rfl

/-- Denotation is natural with respect to the packaged contextual
substitution action. -/
theorem denote_tmSub_natural
    (M : HenkinModel.{u, v, w} Base Const)
    {Γ Δ : Ctx Base} {A : Ty Base}
    (term : (holScwf Base Const).Tm Δ A)
    (substitution : (holScwf Base Const).Sub Γ Δ)
    (valuation : HenkinModel.Valuation M Γ) :
    HenkinModel.denote M
        ((holScwf Base Const).tmSub term substitution) valuation =
      HenkinModel.denote M term
        (fun {B : Ty Base} (boundVar : Var Δ B) =>
          (valuationFunctor M).map substitution valuation boundVar) := by
  exact Soundness.denote_subst M substitution term valuation

/-! ## Positive and negative semantic witnesses -/

/-- Positive: the semantic action of the identity contextual substitution
is literally the identity on valuations. -/
theorem substVal_id_apply
    (M : HenkinModel.{u, v, w} Base Const)
    {Γ : Ctx Base} (valuation : HenkinModel.Valuation M Γ) :
    (fun {A : Ty Base} (boundVar : Var Γ A) =>
      Soundness.substVal M
        (Subst.id (Base := Base) (Const := Const) (Γ := Γ))
        valuation boundVar) =
    (fun {A : Ty Base} (boundVar : Var Γ A) =>
      valuation boundVar) := by
  apply valuation_ext M
  intro A boundVar
  rfl

/-- The primitive truth term and its duplicated conjunction are distinct
HOL syntax. -/
theorem top_ne_and_top {Γ : Ctx Base} :
    (.top : Term Const Γ propTy) ≠ .and .top .top := by
  intro equal
  cases equal

/-- Negative: the same two distinct terms have equal denotation in every
Henkin model.  Semantic interpretation is therefore not automatically an
injective encoding of proof syntax. -/
theorem denote_top_eq_and_top
    (M : HenkinModel.{u, v, w} Base Const)
    {Γ : Ctx Base} (valuation : HenkinModel.Valuation M Γ) :
    HenkinModel.denote M (.top : Term Const Γ propTy) valuation =
      HenkinModel.denote M (.and .top .top) valuation := by
  apply congrArg ULift.up
  apply propext
  simp

/-- The one-proposition context as an object of the syntactic context
category. -/
def propositionContextObject : (holScwf Base Const).base.Context :=
  ⟨[propTy]⟩

/-- A contextual substitution selecting primitive truth. -/
def topSubstitution :
    emptyContextObject (Base := Base) (Const := Const) ⟶
      propositionContextObject :=
  extendSubst
    (toEmpty (Base := Base) (Const := Const) ([] : Ctx Base))
    (.top : Term Const [] propTy)

/-- A contextual substitution selecting duplicated conjunction. -/
def andTopSubstitution :
    emptyContextObject (Base := Base) (Const := Const) ⟶
      propositionContextObject :=
  extendSubst
    (toEmpty (Base := Base) (Const := Const) ([] : Ctx Base))
    (.and .top .top : Term Const [] propTy)

/-- The two substitutions remain distinct in the syntactic context
category. -/
theorem topSubstitution_ne_andTopSubstitution :
    (fun {A : Ty Base} (boundVar : Var [propTy] A) =>
      topSubstitution (Base := Base) (Const := Const) boundVar) ≠
    (fun {A : Ty Base} (boundVar : Var [propTy] A) =>
      andTopSubstitution (Base := Base) (Const := Const) boundVar) := by
  intro equal
  have equalTerms := congrArg
    (fun substitution =>
      substitution (.vz : Var [propTy] propTy)) equal
  exact top_ne_and_top equalTerms

/-- Henkin semantics maps the two distinct substitutions to the same
function on valuations. -/
theorem valuationFunctor_maps_top_and_andTop_equally
    (M : HenkinModel.{u, v, w} Base Const) :
    (valuationFunctor M).map topSubstitution =
      (valuationFunctor M).map andTopSubstitution := by
  apply TypeCat.Hom.ext
  apply TypeCat.Fun.ext
  funext valuation
  apply valuation_ext M
  intro A boundVar
  cases boundVar with
  | vz =>
      change
        HenkinModel.denote M (.top : Term Const [] propTy) valuation =
          HenkinModel.denote M (.and .top .top) valuation
      exact denote_top_eq_and_top M valuation
  | vs boundVar =>
      exact nomatch boundVar

/-- Hence the valuation functor is not injective on this hom-set.  This is
the precise categorical non-faithfulness boundary. -/
theorem valuationFunctor_not_injective_on_one_prop
    (M : HenkinModel.{u, v, w} Base Const) :
    ¬ Function.Injective
      (fun substitution :
          emptyContextObject (Base := Base) (Const := Const) ⟶
            propositionContextObject =>
        (valuationFunctor M).map substitution) := by
  intro injective
  have equalSubstitutions :=
    injective (valuationFunctor_maps_top_and_andTop_equally M)
  apply topSubstitution_ne_andTopSubstitution
  exact equalSubstitutions

/-- A concrete non-faithfulness witness for term denotation. -/
theorem exists_distinct_terms_with_equal_denotation
    (M : HenkinModel.{u, v, w} Base Const) (Γ : Ctx Base)
    (valuation : HenkinModel.Valuation M Γ) :
    ∃ left right : Term Const Γ propTy,
      left ≠ right ∧
      HenkinModel.denote M left valuation =
        HenkinModel.denote M right valuation :=
  ⟨.top, .and .top .top, top_ne_and_top,
    denote_top_eq_and_top M valuation⟩

#print axioms valuationFunctor
#print axioms valuationFunctor_map_apply
#print axioms denote_tmSub_natural
#print axioms substVal_id_apply
#print axioms top_ne_and_top
#print axioms topSubstitution_ne_andTopSubstitution
#print axioms valuationFunctor_maps_top_and_andTop_equally
#print axioms valuationFunctor_not_injective_on_one_prop
#print axioms exists_distinct_terms_with_equal_denotation

end Mettapedia.Logic.HOL.ContextualHenkinSemantics
