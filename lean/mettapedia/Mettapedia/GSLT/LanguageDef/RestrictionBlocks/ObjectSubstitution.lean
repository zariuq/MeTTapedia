import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationObjects
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationSubstitution

/-!
# Substitution through the shapes of the laws

When a calculus's laws have shapes that read through object terms (`ObjectShapes`) and a substitution of terms that are
no abstractions keeps every shape, chains of laws through object terms are closed under substitution of object terms
of the variables' sorts (`ObjectShapes.objectChain_substitute`): a law in a context is carried to the substituted shape
in the transported context, the assignment lifted past the context's binders at the hole, and the substituted ends keep
their sorts.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextSubstitution (Assignment substitute)
open Mettapedia.GSLT.LanguageDef.WellSorted (isObjectPattern HasType FreeTypeContext)

variable {language : LanguageDef} {block : ReplicationBlock} [replication : ReplicationSignature language block]
  {Shape : Pattern → Pattern → Prop}

include replication in
/-- **Chains through object terms are closed under substitution** when a substitution of terms that are no
abstractions keeps every shape of the laws. -/
theorem ObjectShapes.objectChain_substitute (shapes : ObjectShapes language block Shape)
    (substituted : ∀ {assignment : Assignment} {source target : Pattern}, NoAbstractions assignment →
      Shape source target → Shape (substitute assignment source) (substitute assignment target))
    {free : FreeTypeContext} {bound target : List TypeExpr} (targetContext : BaseContext free target)
    {assignment : Assignment} (assigned : SortedAssignment language free bound target assignment)
    (plain : NoAbstractions assignment) {sort : String} {first second : Pattern}
    (chain : ObjectChain language free bound (.base sort) first second) :
    ObjectChain language free target (.base sort) (substitute assignment first) (substitute assignment second) := by
  induction chain with
  | rel first second step =>
      obtain ⟨⟨stepped, firstTyped, secondTyped⟩, firstObject, secondObject⟩ := step
      have firstTyped' := HasType.substituteBoundOnSupport firstTyped assignment
        (fun index type _ lookup => assigned.typed index type lookup)
      have secondTyped' := HasType.substituteBoundOnSupport secondTyped assignment
        (fun index type _ lookup => assigned.typed index type lookup)
      have firstObject' := isObject_substitute _ assigned.objects firstObject
      have secondObject' := isObject_substitute _ assigned.objects secondObject
      cases stepped with
      | @inContext stepContext redex contractum generator =>
          have shape : Shape (substitute (ContextSubstitution.atHole assignment stepContext) redex)
                (substitute (ContextSubstitution.atHole assignment stepContext) contractum) ∨
              Shape (substitute (ContextSubstitution.atHole assignment stepContext) contractum)
                (substitute (ContextSubstitution.atHole assignment stepContext) redex) := by
            rcases shapes.generator generator with shape | shape
            · exact .inl (substituted (plain.atHole stepContext) shape)
            · exact .inr (substituted (plain.atHole stepContext) shape)
          rw [ContextSubstitution.substitute_fill] at firstTyped' secondTyped' firstObject' secondObject' ⊢
          rw [ContextSubstitution.substitute_fill]
          have chain := shapes.shape_fill_objectChain targetContext _ shape firstTyped' secondTyped'
            (substFree_of_object firstObject')
          rwa [closeTails_of_object _ firstObject', closeTails_of_object _ secondObject'] at chain
  | refl => exact .refl _
  | symm _ _ _ recurse => exact .symm _ _ recurse
  | trans _ _ _ _ _ left right => exact .trans _ _ _ left right

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
