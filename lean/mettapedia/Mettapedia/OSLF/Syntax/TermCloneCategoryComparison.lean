import Mettapedia.OSLF.Syntax.TermClone
import Mettapedia.GSLT.LanguageDef.MultiSortedCloneFiniteProducts
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Comparing the two context categories of a binding signature

The intrinsic syntax has two presentations of the same context/substitution
category: typed de Bruijn substitutions and positional environments of its
multisorted clone. The already-proved `envEquivSub` respects identities and
composition. Here it is assembled into a fully faithful and essentially
surjective functor, hence a categorical equivalence. In particular, the
finite-product laws of the generic clone are available to the intrinsic syntax
without a second product authority.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding

open CategoryTheory
open Mettapedia.GSLT.LanguageDef.MultiSortedClone

/-- Convert the positional clone category to the existing typed-substitution
category, using the same intrinsic terms on both sides. -/
def cloneContextToSyntactic (S : Signature) :
    ContextObject (termClone S) ⥤ Syntactic.Ctxt S where
  obj context := ⟨context.context⟩
  map {source target} environment :=
    envEquivSub S target.context source.context environment
  map_id context := envEquivSub_id S context.context
  map_comp first second := envEquivSub_comp S second first

/-- No two distinct positional environments become the same typed
substitution. -/
instance cloneContextToSyntactic_faithful (S : Signature) :
    (cloneContextToSyntactic S).Faithful where
  map_injective := by
    intro source target first second equal
    exact (envEquivSub S target.context source.context).injective equal

/-- Every typed substitution is represented by its positional environment. -/
instance cloneContextToSyntactic_full (S : Signature) :
    (cloneContextToSyntactic S).Full where
  map_surjective := by
    intro source target substitution
    exact ⟨(envEquivSub S target.context source.context).symm substitution,
      (envEquivSub S target.context source.context).apply_symm_apply substitution⟩

/-- Every intrinsic context is the image of its own ordered sort list. -/
theorem cloneContextToSyntactic_obj_surjective (S : Signature) :
    Function.Surjective (cloneContextToSyntactic S).obj := by
  intro context
  cases context with
  | mk sorts =>
      exact ⟨ContextObject.ofList (termClone S) sorts, rfl⟩

instance cloneContextToSyntactic_essSurj (S : Signature) :
    (cloneContextToSyntactic S).EssSurj :=
  Functor.essSurj_of_surj (cloneContextToSyntactic_obj_surjective S)

instance cloneContextToSyntactic_isEquivalence (S : Signature) :
    (cloneContextToSyntactic S).IsEquivalence where

/-- The two previously separate category presentations are equivalent,
with no quotient on terms or substitution arrows. -/
noncomputable def termCloneContextEquivalence (S : Signature) :
    ContextObject (termClone S) ≌ Syntactic.Ctxt S :=
  (cloneContextToSyntactic S).asEquivalence

/-- The intrinsic typed-substitution category inherits the clone's terminal
context through the proved equivalence of the two representations. -/
instance syntacticHasTerminal (S : Signature) :
    CategoryTheory.Limits.HasTerminal (Syntactic.Ctxt S) := by
  exact CategoryTheory.Adjunction.hasLimitsOfShape_of_equivalence
    (termCloneContextEquivalence S).inverse

/-- The intrinsic typed-substitution category inherits all binary context
products from the generic multisorted clone. -/
instance syntacticHasBinaryProducts (S : Signature) :
    CategoryTheory.Limits.HasBinaryProducts (Syntactic.Ctxt S) := by
  exact CategoryTheory.Adjunction.hasLimitsOfShape_of_equivalence
    (termCloneContextEquivalence S).inverse

#print axioms cloneContextToSyntactic_obj_surjective
#print axioms termCloneContextEquivalence
#print axioms syntacticHasBinaryProducts

end Mettapedia.OSLF.Binding
