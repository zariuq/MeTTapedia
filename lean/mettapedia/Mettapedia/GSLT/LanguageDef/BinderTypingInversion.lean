import Mettapedia.GSLT.LanguageDef.TypingInversion

/-!
# Inversion of typing at a bound variable and at a binder

A bound variable is typed by the bound context at its index.  A binder node
is typed at an arrow, by typing its body under one more bound variable; a
multiple-binder node, under as many bound variables as its arity.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.WellSorted

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- A bound variable is typed by the bound context at its index. -/
theorem HasType.bvar_inv {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {index : Nat} {type : TypeExpr}
    (typed : HasType language free bound (.bvar index) type) :
    bound[index]? = some type := by
  generalize source : Pattern.bvar index = pattern at typed
  cases typed with
  | bvar lookup =>
      simp only [Pattern.bvar.injEq] at source
      subst source
      exact lookup
  | fvar _ => cases source
  | constructor _ _ _ => cases source
  | lambda _ => cases source
  | multiLambda _ => cases source
  | subst _ _ => cases source
  | collection _ => cases source
  | collectionConstructor _ _ _ => cases source

/-- A binder node is typed at an arrow: its body is typed at the codomain
under one more bound variable of the domain. -/
theorem HasType.lambda_inv {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {binder : Option String} {body : Pattern} {type : TypeExpr}
    (typed : HasType language free bound (.lambda binder body) type) :
    ∃ domain codomain, type = .arrow domain codomain ∧
      HasType language free (domain :: bound) body codomain := by
  generalize source : Pattern.lambda binder body = pattern at typed
  cases typed with
  | lambda bodyTyped =>
      simp only [Pattern.lambda.injEq] at source
      obtain ⟨-, rfl⟩ := source
      exact ⟨_, _, rfl, bodyTyped⟩
  | bvar _ => cases source
  | fvar _ => cases source
  | constructor _ _ _ => cases source
  | multiLambda _ => cases source
  | subst _ _ => cases source
  | collection _ => cases source
  | collectionConstructor _ _ _ => cases source

/-- A multiple-binder node is typed at an arrow out of a multiple binder: its
body is typed at the codomain under as many bound variables of the domain as
its arity. -/
theorem HasType.multiLambda_inv {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {arity : Nat} {binders : List String} {body : Pattern}
    {type : TypeExpr}
    (typed : HasType language free bound (.multiLambda arity binders body) type) :
    ∃ domain codomain, type = .arrow (.multiBinder domain) codomain ∧
      HasType language free (List.replicate arity domain ++ bound) body codomain := by
  generalize source : Pattern.multiLambda arity binders body = pattern at typed
  cases typed with
  | multiLambda bodyTyped =>
      simp only [Pattern.multiLambda.injEq] at source
      obtain ⟨rfl, -, rfl⟩ := source
      exact ⟨_, _, rfl, bodyTyped⟩
  | bvar _ => cases source
  | fvar _ => cases source
  | constructor _ _ _ => cases source
  | lambda _ => cases source
  | subst _ _ => cases source
  | collection _ => cases source
  | collectionConstructor _ _ _ => cases source

end Mettapedia.GSLT.LanguageDef.WellSorted
