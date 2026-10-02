import Mathlib.CategoryTheory.Iso
import Mettapedia.GSLT.LanguageDef.SymbolMapCode
import Mettapedia.GSLT.LanguageDef.EffectiveSection
import Mettapedia.GSLT.LanguageDef.Contexts.Interacting
import Mettapedia.GSLT.LanguageDef.Contexts.Invertible

/-!
# Effective sections and isomorphic theories

Having an effective section is a property of a presentation.  This module
shows it is a property of the isomorphism class.

* The term map of a morphism of interactive theories is tracked on codes by a
  primitive recursive function: a term of the source uses only the finitely
  many declared constructors.
* A morphism whose relation map keeps the name of the built-in equality and
  whose constructor map keeps the declared units respects the static
  equivalence.
* So along an isomorphism the two static equivalences are decided together:
  if one theory has an effective section, the static equivalence of the other
  is decidable along every computable family of its terms.

A theory whose static equivalence is undecidable along a computable family is
therefore isomorphic to no theory with an effective section.
-/

set_option autoImplicit false

open CategoryTheory

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.PatternCode
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.Contexts
open Mettapedia.GSLT.LanguageDef.EquationSimulation

namespace IGSLT

variable {source target : IGSLT}

/-- **The term map of a morphism is tracked on codes by a computable
function.** -/
theorem exists_computable_mapTermCode (morphism : source ⟶ target) :
    ∃ track : ℕ → ℕ, Computable track ∧
      ∀ term : source.toGSLT.Term,
        target.termCode (Morphism.mapTerm morphism term) = track (source.termCode term) := by
  obtain ⟨track, primitive, tracks⟩ :=
    exists_primrec_mapPatternCode morphism.structural.structural.symbols
      source.presentation.presentation.language
  refine ⟨track, primitive.to_comp, fun term => ?_⟩
  have typed := (show source.presentation.Term from term).2.1
  exact (tracks typed).symm

/-- The image of the interacting interface is the interacting interface. -/
theorem interactingInterface_map (morphism : source ⟶ target) :
    (interactingInterface source.presentation).map morphism.structural.structural.symbols =
      interactingInterface target.presentation := by
  have sorts : morphism.structural.structural.symbols.sort
      source.presentation.interactingSort.1.name = target.presentation.interactingSort.1.name :=
    congrArg (fun sort => sort.1.name) morphism.structural.mapsInteractingSort
  simp only [interactingInterface, closedInterface, Interface.map, List.map_nil]
  congr 1
  simpa [mapTypeExpr, InteractivePresentation.interactingLangSort] using sorts

/-- **A morphism that keeps the built-in equality and the declared units
respects the static equivalence.** -/
theorem mapTerm_resp (morphism : source ⟶ target)
    (relationFixesEq : morphism.structural.structural.symbols.relation "eq" = "eq")
    (units : FixesDeclaredUnits morphism.structural.structural.symbols
      source.presentation.presentation.language)
    {left right : source.toGSLT.Term} (equivalent : source.toGSLT.equations.r left right) :
    target.toGSLT.equations.r (Morphism.mapTerm morphism left)
      (Morphism.mapTerm morphism right) := by
  have atInterface := (termSetoid_ofInteracting_iff defaultBasePremises
    (presentation := source.presentation) left right).mpr equivalent
  have mapped := preservesEquations_default morphism.structural.structural relationFixesEq
    units atInterface
  have moved := termSetoid_of_interface_eq (engineBasePremises RelationEnv.empty)
    (interactingInterface_map morphism)
    (left' := ofInteracting (Morphism.mapTerm morphism left))
    (right' := ofInteracting (Morphism.mapTerm morphism right)) rfl rfl mapped
  exact (termSetoid_ofInteracting_iff defaultBasePremises
    (presentation := target.presentation) _ _).mp moved

/-- The relation maps of an isomorphism are inverse to each other, so if one
keeps the built-in equality the other does. -/
theorem inv_relation_eq (iso : source ≅ target)
    (relationFixesEq : iso.hom.structural.structural.symbols.relation "eq" = "eq") :
    iso.inv.structural.structural.symbols.relation "eq" = "eq" := by
  have composite := congrArg
    (fun morphism : source ⟶ source => morphism.structural.structural.symbols.relation "eq")
    iso.hom_inv_id
  change iso.inv.structural.structural.symbols.relation
    (iso.hom.structural.structural.symbols.relation "eq") = "eq" at composite
  rwa [relationFixesEq] at composite

/-- Going back and forth along an isomorphism returns every term. -/
theorem mapTerm_hom_inv (iso : source ≅ target) (term : target.presentation.Term) :
    Morphism.mapTerm iso.hom (Morphism.mapTerm iso.inv term) = term := by
  have composite : Morphism.mapTerm (Morphism.comp iso.inv iso.hom) term =
      Morphism.mapTerm (Morphism.id target) term :=
    congrArg (fun morphism : target ⟶ target => Morphism.mapTerm morphism term) iso.inv_hom_id
  exact ((Morphism.mapTerm_comp iso.inv iso.hom term).symm.trans composite).trans
    (Morphism.mapTerm_id target term)

/-- **Along an isomorphism the two static equivalences agree.** -/
theorem equations_iff_of_iso (iso : source ≅ target)
    (relationFixesEq : iso.hom.structural.structural.symbols.relation "eq" = "eq")
    (homUnits : FixesDeclaredUnits iso.hom.structural.structural.symbols
      source.presentation.presentation.language)
    (invUnits : FixesDeclaredUnits iso.inv.structural.structural.symbols
      target.presentation.presentation.language)
    {left right : target.toGSLT.Term} :
    source.toGSLT.equations.r (Morphism.mapTerm iso.inv left) (Morphism.mapTerm iso.inv right) ↔
      target.toGSLT.equations.r left right := by
  constructor
  · intro equivalent
    have mapped := mapTerm_resp iso.hom relationFixesEq homUnits equivalent
    have leftBack := mapTerm_hom_inv iso left
    have rightBack := mapTerm_hom_inv iso right
    exact leftBack ▸ rightBack ▸ mapped
  · exact mapTerm_resp iso.inv (inv_relation_eq iso relationFixesEq) invUnits

/-- **An effective section of one theory decides the static equivalence of
every isomorphic theory**, along every family of its terms whose codes are
computable. -/
theorem computablePred_of_iso (iso : source ≅ target)
    (relationFixesEq : iso.hom.structural.structural.symbols.relation "eq" = "eq")
    (homUnits : FixesDeclaredUnits iso.hom.structural.structural.symbols
      source.presentation.presentation.language)
    (invUnits : FixesDeclaredUnits iso.inv.structural.structural.symbols
      target.presentation.presentation.language)
    {canonical : ComputableCanonicalSection source} (effective : canonical.Effective)
    {left right : ℕ → target.toGSLT.Term}
    (leftComputable : Computable fun index => target.termCode (left index))
    (rightComputable : Computable fun index => target.termCode (right index)) :
    ComputablePred fun index => target.toGSLT.equations.r (left index) (right index) := by
  obtain ⟨track, trackComputable, tracks⟩ := exists_computable_mapTermCode iso.inv
  have leftBack : Computable fun index =>
      source.termCode (Morphism.mapTerm iso.inv (left index)) :=
    (trackComputable.comp leftComputable).of_eq fun index => (tracks (left index)).symm
  have rightBack : Computable fun index =>
      source.termCode (Morphism.mapTerm iso.inv (right index)) :=
    (trackComputable.comp rightComputable).of_eq fun index => (tracks (right index)).symm
  exact (effective.computablePred leftBack rightBack).of_eq fun index =>
    equations_iff_of_iso iso relationFixesEq homUnits invUnits

end IGSLT

end Mettapedia.GSLT.LanguageDef
