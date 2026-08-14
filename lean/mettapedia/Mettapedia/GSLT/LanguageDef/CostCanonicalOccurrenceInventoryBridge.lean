import Mettapedia.GSLT.LanguageDef.CostCanonicalOccurrenceTraceDepths
import Mettapedia.GSLT.LanguageDef.CostStructuralSelection
import Mettapedia.GSLT.LanguageDef.CostHereditaryFrameNormalization

/-!
# Canonical occurrence ancestry into finite atom inventories

Canonical occurrence reflection stops at the atomized source frame.  This
module inverts the structural atom renaming once more, recovering the exact
authored occurrence and hence its finite inventory position.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

namespace CostStaticAtomEnvironment

/-- Every exact occurrence in an atom-reified frame is the structural image
of an exact authored occurrence.  The equality includes the complete zipper,
not only the selected name. -/
theorem exists_occurrence_preimage_reify
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (occurrence : CostStaticFVarOccurrence (environment.reify root)) :
    ∃ sourceOccurrence : CostStaticFVarOccurrence root,
      environment.reifyOccurrence sourceOccurrence = occurrence := by
  obtain ⟨sourcePayload, sourceContext, sourceSelected, contextEquality,
      payloadEquality⟩ :=
    Selects.exists_preimage_environmentReify environment occurrence.selected
  rw [environment.reify_eq_renameFVars] at payloadEquality
  cases sourcePayload with
  | bvar index =>
      simp only [Pattern.renameFVars] at payloadEquality
      cases payloadEquality
  | fvar name =>
      simp only [Pattern.renameFVars, Pattern.fvar.injEq] at payloadEquality
      have nameEquality : environment.reifyName name = occurrence.name :=
        payloadEquality
      let sourceOccurrence : CostStaticFVarOccurrence root :=
        { name := name
          context := sourceContext
          selected := sourceSelected }
      refine ⟨sourceOccurrence, CostStaticFVarOccurrence.ext ?_ ?_⟩
      · exact nameEquality
      · exact contextEquality
  | apply constructor arguments =>
      simp only [Pattern.renameFVars] at payloadEquality
      cases payloadEquality
  | lambda binder body =>
      simp only [Pattern.renameFVars] at payloadEquality
      cases payloadEquality
  | multiLambda arity binders body =>
      simp only [Pattern.renameFVars] at payloadEquality
      cases payloadEquality
  | subst body replacement =>
      simp only [Pattern.renameFVars] at payloadEquality
      cases payloadEquality
  | collection collectionType elements rest =>
      simp only [Pattern.renameFVars] at payloadEquality
      cases payloadEquality

/-- Constructive preimage chosen from `exists_occurrence_preimage_reify`.
It is intentionally non-unique when semantic quotienting coalesces names. -/
noncomputable def occurrencePreimageReify
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (occurrence : CostStaticFVarOccurrence (environment.reify root)) :
    CostStaticFVarOccurrence root :=
  Classical.choose (environment.exists_occurrence_preimage_reify occurrence)

@[simp]
theorem reifyOccurrence_occurrencePreimageReify
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (occurrence : CostStaticFVarOccurrence (environment.reify root)) :
    environment.reifyOccurrence
        (environment.occurrencePreimageReify occurrence) = occurrence :=
  Classical.choose_spec
    (environment.exists_occurrence_preimage_reify occurrence)

/-- Name lookup and exact positional lookup select the same semantic class.
They may choose different duplicate occurrences, but quotient extensionality
identifies their complete typed atom values. -/
theorem slotOfName?_eq_occurrenceSlot_positionOf
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (occurrence : CostStaticFVarOccurrence root) :
    environment.slotOfName? occurrence.name =
      some (environment.occurrenceSlot (inventory.positionOf occurrence)) := by
  unfold slotOfName?
  cases selected : inventory.positionOfName? occurrence.name with
  | none =>
      have represented :=
        inventory.positionOfName?_isSome_of_occurrence occurrence
      simp [selected] at represented
  | some position =>
      simp only [Option.map_some, Option.some.injEq]
      exact (environment.extensional position
        (inventory.positionOf occurrence)).mpr
        (inventory.occurrenceAtom_eq_of_positionOfName?_eq_some occurrence
          position selected)

/-- Reifying one exact occurrence names precisely the semantic class of that
position, even when name-based lookup chooses another duplicate occurrence. -/
theorem reifyOccurrence_name_eq_atomName_occurrenceSlot
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (occurrence : CostStaticFVarOccurrence root) :
    (environment.reifyOccurrence occurrence).name =
      environment.atomName
        (environment.occurrenceSlot (inventory.positionOf occurrence)) :=
  environment.reifyOccurrence_name_eq_atomName_of_slotOfName?_eq_some
    occurrence _
      (environment.slotOfName?_eq_occurrenceSlot_positionOf occurrence)

end CostStaticAtomEnvironment

/-- Exact ancestry package from one final two-depth canonical occurrence to
the authored finite parameter inventory. -/
structure CostCanonicalInventoryOccurrenceCertificate
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    {Key : Type} [LinearOrder Key] (key : Nat → Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl)
    (availableDepth scopeDepth : Nat)
    (targetOccurrence : CostStaticFVarOccurrence
      (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths key
        declaration availableDepth scopeDepth (environment.reify root))) where
  reifiedOccurrence : CostStaticFVarOccurrence (environment.reify root)
  sourceOccurrence : CostStaticFVarOccurrence root
  sourcePosition : inventory.Occurrence
  canonical_source_eq : reifiedOccurrence =
    canonicalizeByDepthsOccurrenceSource key declaration availableDepth
      scopeDepth (environment.reify root) targetOccurrence
  reified_eq : environment.reifyOccurrence sourceOccurrence = reifiedOccurrence
  position_eq :
    (inventory.occurrenceAt sourcePosition).fvarOccurrence = sourceOccurrence
  canonical_name_eq : reifiedOccurrence.name = targetOccurrence.name
  target_name_eq_atomName : targetOccurrence.name =
    environment.atomName (environment.occurrenceSlot sourcePosition)

/-- Compose two-depth canonical ancestry with atom-reification inversion and
the complete finite occurrence inventory. -/
noncomputable def costCanonicalInventoryOccurrenceCertificate
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    {Key : Type} [LinearOrder Key] (key : Nat → Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl)
    (availableDepth scopeDepth : Nat)
    (targetOccurrence : CostStaticFVarOccurrence
      (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths key
        declaration availableDepth scopeDepth (environment.reify root))) :
    CostCanonicalInventoryOccurrenceCertificate environment key declaration
      availableDepth scopeDepth targetOccurrence := by
  let canonicalCertificate := keyedCanonicalDepthsFVarCertificate key
    declaration availableDepth scopeDepth (environment.reify root)
      targetOccurrence
  let reifiedOccurrence := canonicalCertificate.sourceOccurrence
  let sourceOccurrence :=
    environment.occurrencePreimageReify reifiedOccurrence
  let sourcePosition := inventory.positionOf sourceOccurrence
  have reifiedName : reifiedOccurrence.name =
      environment.atomName (environment.occurrenceSlot sourcePosition) := by
    rw [← environment.reifyOccurrence_occurrencePreimageReify
      reifiedOccurrence]
    exact environment.reifyOccurrence_name_eq_atomName_occurrenceSlot
      sourceOccurrence
  exact
    { reifiedOccurrence := reifiedOccurrence
      sourceOccurrence := sourceOccurrence
      sourcePosition := sourcePosition
      canonical_source_eq := rfl
      reified_eq := environment.reifyOccurrence_occurrencePreimageReify
        reifiedOccurrence
      position_eq := inventory.fvarOccurrence_occurrenceAt_positionOf
        sourceOccurrence
      canonical_name_eq := canonicalCertificate.name_eq
      target_name_eq_atomName := canonicalCertificate.name_eq.symm.trans
        reifiedName }

end Mettapedia.GSLT.LanguageDef
