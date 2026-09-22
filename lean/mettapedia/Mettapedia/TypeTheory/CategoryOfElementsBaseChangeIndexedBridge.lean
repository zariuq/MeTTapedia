import Mettapedia.TypeTheory.CategoryOfElementsBaseChange
import Mettapedia.TypeTheory.CategoryIndexedFamilyTypeFormers

/-!
# Agreement with category-indexed CwF substitution

The universe-polymorphic category-of-elements change of base is the
existing chosen substitution lift of the indexed-family CwF on their
shared small-universe fragment. This prevents two different notions of
dependent substitution from becoming independent authorities.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.CategoryOfElementsBaseChangeIndexedBridge

open CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.CategoryOfElementsBaseChange
open Mettapedia.TypeTheory.CategoryIndexedFamilyCwf
open Mettapedia.TypeTheory.CategoryIndexedFamilyTypeFormers

universe u

/-- The generic lift and the CwF's concrete lift are the same functor
on the shared category-indexed fragment. -/
theorem mapPrecompElements_eq_liftIndexedSubstitution
    {source target : Context.{u}}
    (substitution : ContextHom source target)
    (family : IndexedFamily target) :
    mapPrecompElements substitution family =
      liftIndexedSubstitution substitution family := by
  apply CategoryTheory.Functor.ext (fun _ => rfl)

/-- Thus the generic change of base also agrees with the CwF's
specified comprehension-substitution operation. -/
theorem mapPrecompElements_eq_extensionSubstitution
    {source target : Context.{u}}
    (substitution : ContextHom source target)
    (family : IndexedFamily target) :
    mapPrecompElements substitution family =
      TypeOver.extensionSubstitution (C := categoryIndexedCwf)
        substitution family := by
  exact (mapPrecompElements_eq_liftIndexedSubstitution substitution family).trans
    (liftIndexedSubstitution_eq_extensionSubstitution substitution family)

#print axioms mapPrecompElements_eq_liftIndexedSubstitution
#print axioms mapPrecompElements_eq_extensionSubstitution

end Mettapedia.TypeTheory.CategoryOfElementsBaseChangeIndexedBridge
