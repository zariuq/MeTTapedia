import Mettapedia.TypeTheory.CategoryIndexedFamilyCwf
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Limits.Types.Limits

/-!
# General semantic dependent products for indexed families

For a family `A` over a category of contexts, context extension is its
category of elements and weakening is the projection. Reindexing along that
projection has a right adjoint: the right Kan extension into types. This
provides dependent products without assuming that substitution in `A` is
invertible. This adjunction alone is not a CwF dependent-product former:
the separate directed-edge control proves that its indexed family fails
arbitrary substitution stability. The construction is semantic and
noncomputable; it does not provide authored Prime syntax or executable
conversion.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.CategoryIndexedFamilyGeneralPi

open CategoryTheory
open Mettapedia.TypeTheory.CategoryIndexedFamilyCwf

universe u

/-- The right-adjoint candidate for a semantic dependent product of a family
on the comprehension of `domain`. General substitution stability is false. -/
noncomputable def generalPiFamily {context : Context.{u}}
    (domain : IndexedFamily context)
    (codomain : IndexedFamily (extend context domain)) :
    IndexedFamily context :=
  (weaken domain).rightKanExtension codomain

/-- The application map evaluates a dependent product after substitution
into the extended context. -/
noncomputable def generalPiEvaluation {context : Context.{u}}
    (domain : IndexedFamily context)
    (codomain : IndexedFamily (extend context domain)) :
    reindexFamily (generalPiFamily domain codomain) (weaken domain) ⟶
      codomain :=
  (weaken domain).rightKanExtensionCounit codomain

/-- Reindexing along comprehension weakening is left adjoint to the
general semantic dependent-product operation. -/
noncomputable def generalPiAdjunction {context : Context.{u}}
    (domain : IndexedFamily context) :
    (Functor.whiskeringLeft _ _ (Type u)).obj (weaken domain) ⊣
      (weaken domain).ran :=
  (weaken domain).ranAdjunction (Type u)

/-- Dependent lambda abstraction is the adjoint transpose of a natural
family map over the extended context. -/
noncomputable def generalPiTranspose {context : Context.{u}}
    (domain : IndexedFamily context)
    {source : IndexedFamily context}
    {codomain : IndexedFamily (extend context domain)}
    (body : reindexFamily source (weaken domain) ⟶ codomain) :
    source ⟶ generalPiFamily domain codomain :=
  (generalPiAdjunction domain).homEquiv source codomain body

/-- Transposing a dependent body and then evaluating it returns that body
as a natural transformation, not only at an individual context. -/
theorem generalPi_beta {context : Context.{u}}
    (domain : IndexedFamily context)
    {source : IndexedFamily context}
    {codomain : IndexedFamily (extend context domain)}
    (body : reindexFamily source (weaken domain) ⟶ codomain) :
    Functor.whiskerLeft (weaken domain)
        (generalPiTranspose domain body) ≫
      generalPiEvaluation domain codomain = body := by
  change
    ((generalPiAdjunction domain).homEquiv source codomain).symm
      ((generalPiAdjunction domain).homEquiv source codomain body) = body
  exact Equiv.symm_apply_apply _ body

/-- Every semantic dependent function is uniquely recovered from its
evaluation body. This is the natural-transformation η law. -/
theorem generalPi_eta {context : Context.{u}}
    (domain : IndexedFamily context)
    {source : IndexedFamily context}
    {codomain : IndexedFamily (extend context domain)}
    (function : source ⟶ generalPiFamily domain codomain) :
    generalPiTranspose domain
      (Functor.whiskerLeft (weaken domain) function ≫
        generalPiEvaluation domain codomain) = function := by
  change
    (generalPiAdjunction domain).homEquiv source codomain
      (((generalPiAdjunction domain).homEquiv source codomain).symm
        function) = function
  exact Equiv.apply_symm_apply _ function

/-- The terminal family supplies the semantic empty parameter context for
the identity dependent function. -/
def unitFamily (context : Context.{u}) : IndexedFamily context :=
  (Functor.const (context : Type u)).obj PUnit

/-- The dependent identity body reads the actual last variable of context
comprehension. Its naturality uses the arrow's retained fibre transport. -/
def identityPiBody {context : Context.{u}}
    (domain : IndexedFamily context) :
    reindexFamily (unitFamily context) (weaken domain) ⟶
      reindexFamily domain (weaken domain) where
  app point := TypeCat.ofHom fun _ => point.2
  naturality := by
    intro first second arrow
    apply ConcreteCategory.hom_ext
    intro _
    exact arrow.property.symm

/-- A dependent identity function exists even when transport in its domain
is noninvertible; its body is the retained variable, not chosen evidence. -/
noncomputable def identityPiTranspose {context : Context.{u}}
    (domain : IndexedFamily context) :
    unitFamily context ⟶
      generalPiFamily domain
        (reindexFamily domain (weaken domain)) :=
  generalPiTranspose domain (identityPiBody domain)

/-- β for the identity dependent function holds as an equality of natural
transformations, hence simultaneously at every context and every arrow. -/
theorem identityPi_beta {context : Context.{u}}
    (domain : IndexedFamily context) :
    Functor.whiskerLeft (weaken domain) (identityPiTranspose domain) ≫
        generalPiEvaluation domain
          (reindexFamily domain (weaken domain)) =
      identityPiBody domain :=
  generalPi_beta domain (identityPiBody domain)

#print axioms generalPiFamily
#print axioms generalPiEvaluation
#print axioms generalPiAdjunction
#print axioms generalPiTranspose
#print axioms generalPi_beta
#print axioms generalPi_eta
#print axioms identityPiBody
#print axioms identityPiTranspose
#print axioms identityPi_beta

end Mettapedia.TypeTheory.CategoryIndexedFamilyGeneralPi
