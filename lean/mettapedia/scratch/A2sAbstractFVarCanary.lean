import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryDescent
import Mettapedia.GSLT.LanguageDef.ReflectiveCanonicalFreeRenaming
import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalOrderAgnosticDepths

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.A2sAbstractFVarCanary

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- A source-name canonical leaf in the authored skeleton gives the exact
occurrence, slot, and selected-colour canonical frame required by the direct
free-variable exposure constructor. -/
theorem sourceVariableFrame_of_abstractCanonical
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (children : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      node.finiteBoundaryTable)
    (name : String)
    (abstractCanonical :
      canonicalize rhoReflectivePresentation node.skeleton.1 =
        .fvar (costRegionSourceVariableName name)) :
    ∃ occurrence : CostStaticFVarOccurrence node.skeleton.1,
      ∃ slot : Fin (node.normalizationEnvironment
        rhoHereditaryStaticNormalizer children).atomCount,
      occurrence.name = costRegionSourceVariableName name ∧
        (node.normalizationEnvironment rhoHereditaryStaticNormalizer
          children).slotOfName? occurrence.name = some slot ∧
        node.canonicalizeReifiedTargetFrame
            (node.normalizationEnvironment rhoHereditaryStaticNormalizer
              children)
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation) =
          .fvar ((node.normalizationEnvironment
            rhoHereditaryStaticNormalizer children).atomName slot) := by
  let environment := node.normalizationEnvironment
    rhoHereditaryStaticNormalizer children
  have nameMembership : costRegionSourceVariableName name ∈
      node.skeleton.1.freeFvarNames := by
    rw [← mem_freeFvarNames_canonicalize_iff rhoReflectivePresentation]
    rw [abstractCanonical]
    simp [Pattern.freeFvarNames]
  obtain ⟨occurrence, occurrenceName⟩ :=
    CostStaticFVarOccurrence.exists_of_mem_freeFvarNames_of_object
      nameMembership node.skeleton.2.1.2.2.1
  have slotExists := environment.slotOfName?_isSome_of_occurrence occurrence
  let slot := (environment.slotOfName? occurrence.name).get slotExists
  have selected : environment.slotOfName? occurrence.name = some slot :=
    (Option.some_get slotExists).symm
  have selectedSourceName : environment.slotOfName?
      (costRegionSourceVariableName name) = some slot := by
    simpa [occurrenceName] using selected
  have reifiedOrdinary : canonicalize rhoReflectivePresentation
      (node.reifiedSourceFrame environment).1 =
      .fvar (environment.atomName slot) := by
    rw [node.reifiedSourceFrame_pattern]
    have canonicalEquality : canonicalize rhoReflectivePresentation
        node.skeleton.1 =
        canonicalize rhoReflectivePresentation
          (.fvar (costRegionSourceVariableName name)) := by
      simpa [canonicalize] using abstractCanonical
    have renamed := canonicalize_renameFVars_eq_of_eq
      rhoReflectivePresentation (by decide) environment.reifyName
      canonicalEquality
    calc
      canonicalize rhoReflectivePresentation
          (environment.reify node.skeleton.1) =
        canonicalize rhoReflectivePresentation
          (Pattern.renameFVars environment.reifyName
            (.fvar (costRegionSourceVariableName name))) := by
          simpa [CostStaticAtomEnvironment.reify] using renamed
      _ = .fvar (environment.atomName slot) := by
        simp [Pattern.renameFVars, CostStaticAtomEnvironment.reifyName,
          selectedSourceName, canonicalize]
  have keyed := canonicalizeByDepths_eq_fvar_of_canonicalize_eq
    (CostStaticRegionNode.sourceSemanticPatternKeyAt node environment)
    rhoReflectivePresentation node.targetBound.length 0 reifiedOrdinary
  refine ⟨occurrence, slot, occurrenceName, by simpa [environment] using selected, ?_⟩
  change node.canonicalizeReifiedTargetFrame environment
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation) = .fvar (environment.atomName slot)
  rw [CostStaticRegionNode.canonicalizeReifiedTargetFrame_eq_map_sourceCanonicalize
    node environment, keyed]
  simp [mapPattern, CostStaticBinderThinning.thickenAmbientBVars]

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.A2sAbstractFVarCanary
