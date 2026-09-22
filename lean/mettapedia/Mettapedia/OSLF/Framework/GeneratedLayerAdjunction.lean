import Mettapedia.OSLF.Framework.GeneratedHypercube
import Mettapedia.OSLF.Framework.GeneratedModalFamily
import Mettapedia.GSLT.LanguageDef.StructuralCategory

/-!
# Object-level layer data and declaration extension

The source states, without proving it, that there is a forgetful functor from
theories equipped with the modal, structural and propositional layers to
theories in classifying form, a left adjoint freely adjoining those layers, and
that the induced endofunctor is a monad whose value at a theory is "the
underlying theory of its free extension by generated type formers".

This module distinguishes two object-level constructions. Neither establishes
the categories, functors or universal property needed for that proposition.

**Reading one: the layers are extra structure over an unchanged theory.**  An
object is a theory together with an admissibility assignment at each redex site;
the forgetful map drops the assignment and `generatedLayers` supplies one. Their
composite is the identity on objects by field projection. Distinct layerings
exist over one theory. Neither fact constructs an adjunction, an endofunctor
on morphisms or an identity monad.

**Reading two: the generated formers enter the underlying theory.**  This is the
reading the source's own words require, since it calls the value "the underlying
theory of its free *extension*".  For the composite to be an extension, the
forgetful functor must return a theory carrying the adjoined vocabulary rather
than the theory one began with.

Under reading two the construction is a
transformation of language definitions that retains the authored sorts, grammar,
equations and rewrites and adjoins vocabulary generated from them -- which is
the shape the observer extension already has for the instrument vocabulary of a
later chapter.  So the generated-type-former monad is the type-former analogue
of a construction this development already performs, and that is where the proof
obligation lies.

Only the object-level comparison is proved here. The free structured extension,
its adjunction and induced monad remain obligations.
-/

namespace Mettapedia.OSLF.Framework.GeneratedLayerAdjunction

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework
open Mettapedia.GSLT.LanguageDef

set_option autoImplicit false

/-! ## Reading one, stated exactly -/

/-- A theory together with layer data: an admissibility assignment at each of
its redex sites, filling that site's sort slots.  The assignment is arbitrary --
these are objects equipped with layer data, not a category or only the image
of the generator. -/
structure LayeredLanguage where
  /-- The theory underneath. -/
  base : ValidatedLanguageDef
  /-- Its layer data, at each redex site of the theory. -/
  admissible :
    (site : GeneratedModalFamily.Site) → site ∈ GeneratedModalFamily.redexSites base.language →
      (Fin (GeneratedModalFamily.siteSlotCount site) → ModalHypercube.HSort) → Bool

/-- The forgetful map: drop the layer data. -/
def forgetLayers (layered : LayeredLanguage) : ValidatedLanguageDef :=
  layered.base

/-- Equip a theory with the candidate layers computed by the analyzer.
This object map is not asserted to be a left adjoint. -/
def generatedLayers (alg : GeneratedHypercube.SortAlgebra)
    (theory : ValidatedLanguageDef) : LayeredLanguage where
  base := theory
  admissible := fun site _ =>
    GeneratedHypercube.derivedAdmissible alg theory.language site.1 site.2

/-- **The composite is the identity on objects.**  Equipping a theory with its
generated layers and then forgetting them returns the theory unchanged, for
every theory and every sort algebra -- by `rfl`, since forgetting is projection
of a field the equipping just supplied. -/
theorem forget_generated (alg : GeneratedHypercube.SortAlgebra)
    (theory : ValidatedLanguageDef) :
    forgetLayers (generatedLayers alg theory) = theory := rfl

/-- Equipping and forgetting is the identity as a function on objects.
No functor or monad laws are established by this equality. -/
theorem composite_is_identity (alg : GeneratedHypercube.SortAlgebra) :
    (fun theory => forgetLayers (generatedLayers alg theory)) = id :=
  rfl

/-! ## The layers really are extra structure

The emptiness above is not because the category of layered theories collapses.
One theory carries many layerings. These are distinct objects, without a
category or adjunction being supplied here. -/

/-- Everything admissible. -/
def allAdmissible (theory : ValidatedLanguageDef) : LayeredLanguage where
  base := theory
  admissible := fun _ _ _ => true

/-- Nothing admissible. -/
def noneAdmissible (theory : ValidatedLanguageDef) : LayeredLanguage where
  base := theory
  admissible := fun _ _ _ => false

/-- **The forgetful map is not injective.**  A theory with a redex site carries at
least two distinct layerings, which forgetting identifies. -/
theorem forget_is_not_injective (theory : ValidatedLanguageDef)
    (site : GeneratedModalFamily.Site)
    (member : site ∈ GeneratedModalFamily.redexSites theory.language)
    (assignment : Fin (GeneratedModalFamily.siteSlotCount site) → ModalHypercube.HSort) :
    ¬ Function.Injective forgetLayers := by
  intro injective
  have equalLayerings : allAdmissible theory = noneAdmissible theory := injective rfl
  simp only [allAdmissible, noneAdmissible, LayeredLanguage.mk.injEq, true_and] at equalLayerings
  have applied := congrFun (congrFun (congrFun (eq_of_heq equalLayerings) site) member) assignment
  simp at applied

/-- And both forget to the same theory, so the failure of injectivity is
exactly at the layer data. -/
theorem both_forget_alike (theory : ValidatedLanguageDef) :
    forgetLayers (allAdmissible theory) = forgetLayers (noneAdmissible theory) :=
  rfl

/-! ## What reading two would have to supply

An object-level declaration extension changes some theory. That separates it
from merely supplying and projecting a field, but does not establish freeness. -/

/-- Whether an object map changes some language definition. This property
alone does not characterize a free extension, functor or monad. -/
def ExtendsSomeTheory (extend : ValidatedLanguageDef → ValidatedLanguageDef) : Prop :=
  ∃ theory : ValidatedLanguageDef, extend theory ≠ theory

/-- **Reading one fails it, for every sort algebra.**  So no choice of generator
rescues the extra-structure reading: the obligation is on the shape of the
forgetful functor, not on what the generator computes. -/
theorem reading_one_extends_nothing (alg : GeneratedHypercube.SortAlgebra) :
    ¬ ExtendsSomeTheory (fun theory => forgetLayers (generatedLayers alg theory)) := by
  rintro ⟨theory, differs⟩
  exact differs (forget_generated alg theory)

end Mettapedia.OSLF.Framework.GeneratedLayerAdjunction
