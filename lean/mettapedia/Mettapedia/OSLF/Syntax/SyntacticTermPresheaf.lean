import Mettapedia.OSLF.Syntax.SyntacticCategory
import Mathlib.CategoryTheory.Yoneda

/-!
# Intrinsic terms as a presheaf on syntactic contexts

Terms of a fixed sort vary contravariantly with substitutions. This packages
the substitution action of `SyntacticCategory` as an actual presheaf, so it can
be used by the generic native dependent-predicate machinery. It is distinct
from a constant presheaf of erased raw patterns: substitution changes terms.
-/

namespace Mettapedia.OSLF.Binding.Syntactic

open CategoryTheory

set_option autoImplicit false

/-- The intrinsically scoped terms of a sort, reindexed by substitution. -/
def termPresheaf (S : Signature) (s : S.Srt) : (Ctxt S)ᵒᵖ ⥤ Type where
  obj X := Term S X.unop.vars s
  map f := TypeCat.ofHom (substAction s f)
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro t
    exact congrFun (substAction_id s X) t
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro t
    exact congrFun (substAction_comp s f g) t

@[simp] theorem termPresheaf_obj (S : Signature) (s : S.Srt) (X : (Ctxt S)ᵒᵖ) :
    (termPresheaf S s).obj X = Term S X.unop.vars s := rfl

@[simp] theorem termPresheaf_map (S : Signature) (s : S.Srt)
    {X Y : (Ctxt S)ᵒᵖ} (f : X ⟶ Y) (t : Term S X.unop.vars s) :
    (termPresheaf S s).map f t = bind f.unop t := rfl

/-- A fixed sort's intrinsic term presheaf is represented by its one-variable
context. The pointwise equivalence from `SyntacticCategory` is natural in
substitution, not merely a family of bijections. -/
def termPresheafYonedaIso (S : Signature) (s : S.Srt) :
    termPresheaf S s ≅ yoneda.obj (single s) where
  hom := {
    app X := TypeCat.ofHom (fun t => (termsRepresented X.unop s).symm t)
    naturality X Y f := by
      apply ConcreteCategory.hom_ext
      intro t
      funext sort position
      cases position with
      | zero => rfl
      | succ impossible => exact nomatch impossible }
  inv := {
    app X := TypeCat.ofHom (fun h => termsRepresented X.unop s h)
    naturality X Y f := by
      apply ConcreteCategory.hom_ext
      intro h
      rfl }
  hom_inv_id := by
    ext X t
    exact (termsRepresented X.unop s).right_inv t
  inv_hom_id := by
    ext X h
    exact (termsRepresented X.unop s).left_inv h

#print axioms termPresheafYonedaIso

end Mettapedia.OSLF.Binding.Syntactic
