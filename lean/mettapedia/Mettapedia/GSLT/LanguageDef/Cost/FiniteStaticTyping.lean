import Mettapedia.GSLT.LanguageDef.Cost.FiniteStaticTypingCore
import Mettapedia.GSLT.LanguageDef.LambdaContinuedInteraction
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.SynchronousDecoration

/-!
# Static typing controls for finite continuation decoration

The lambda and synchronous rho profiles discharge the nonprincipal inventory
condition of the generic transport theorem. These static-frame results do
not embed arbitrary source programs or establish Cost iteration closure.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax StructuralMorphism WellSorted

namespace FiniteStaticTypingControls
open ContinuationDecorationProfile LambdaContinuedInteraction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous

/-- The actual lambda inventory discharges the prerequisite; it is not an
assumed closure law for a future continued object. -/
theorem lambda_nonprincipal :
    ∀ constructor ∈ (ofRetypingPlan lambdaContinuationRetyping).constructorClosure,
      constructor ≠ lambdaInteractionCut.program.constructor ∧
        constructor ≠ lambdaInteractionCut.environment.constructor :=
  ofRetypingPlan_nonprincipal lambdaContinuationRetyping

/-- The three-continuation synchronous profile has the same authored
nonprincipal inventory, even though its additional output slot is essential. -/
theorem synchronous_nonprincipal :
    ∀ constructor ∈ communicationDecoration.constructorClosure,
      constructor ≠ rhoSyncInteractionCut.program.constructor ∧
        constructor ≠ rhoSyncInteractionCut.environment.constructor :=
  fun constructor included =>
    (rhoSyncContinuationRetyping.mem_wrappedConstructors_iff constructor).mp included

/-- Static transport is class-wide on the synchronous declaration fragment,
with arbitrary free and bound type contexts. -/
theorem synchronous_mapStatic_hasType (color : CostStaticColor)
    {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (typed : HasTypeWithConstructors rhoSyncCalc
      (· ∈ communicationDecoration.wrappedLabels) free bound pattern type) :
    HasType communicationDecoration.costWholeLanguage
      (free.map (color.symbolsOf rhoSyncIGSLT))
      (bound.map (mapTypeExpr (color.symbolsOf rhoSyncIGSLT)))
      (mapPattern (color.symbolsOf rhoSyncIGSLT) pattern)
      (mapTypeExpr (color.symbolsOf rhoSyncIGSLT) type) :=
  communicationDecoration.mapStatic_hasType synchronous_nonprincipal color typed

/-- An open quotation containing both a drop and a bare parallel bag. This
is an ordinary sorting witness, not a claim that the quotation is sealed. -/
def openStaticName : Pattern :=
  .apply "NQuote" [.collection .hashBag
    [.apply "PDrop" [.bvar 0], .apply "PZero" []] none]

theorem openStaticName_typed (free : FreeTypeContext) (ambient : List TypeExpr) :
    HasTypeWithConstructors rhoSyncCalc (· ∈ communicationDecoration.wrappedLabels)
      free (.base "Name" :: ambient) openStaticName (.base "Name") := by
  apply HasTypeWithConstructors.constructor (rule := rhoSyncCalc.terms[2])
  · decide +kernel
  · exact List.getElem_mem _
  · simp [UsesBareCollection, rhoSyncCalc, rhoCalc, TypeExpr.proc, TypeExpr.name, TypeExpr.baseType]
  · apply ArgumentsHaveTypesWithConstructors.cons (expected := .base "Proc")
    · trivial
    · rfl
    · apply HasTypeWithConstructors.collectionConstructor (rule := rhoSyncCalc.terms[3])
      · decide +kernel
      · exact List.getElem_mem _
      · rfl
      · apply ElementsHaveTypeWithConstructors.cons
        · apply HasTypeWithConstructors.constructor (rule := rhoSyncCalc.terms[1])
          · decide +kernel
          · exact List.getElem_mem _
          · simp [UsesBareCollection, rhoSyncCalc, rhoCalc, TypeExpr.proc, TypeExpr.name, TypeExpr.baseType]
          · exact .cons trivial rfl (.bvar rfl) .nil
        · apply ElementsHaveTypeWithConstructors.cons
          · apply HasTypeWithConstructors.constructor (rule := rhoSyncCalc.terms[0])
            · decide +kernel
            · exact List.getElem_mem _
            · simp [UsesBareCollection, rhoSyncCalc, rhoCalc, TypeExpr.proc, TypeExpr.name, TypeExpr.baseType]
            · exact .nil
          · exact .nil _ _
    · exact .nil

/-- Both actual generated static colours type the open nested witness. -/
theorem openStaticName_transported (color : CostStaticColor)
    (free : FreeTypeContext) (ambient : List TypeExpr) :
    HasType communicationDecoration.costWholeLanguage
      (free.map (color.symbolsOf rhoSyncIGSLT))
      ((.base "Name" :: ambient).map (mapTypeExpr (color.symbolsOf rhoSyncIGSLT)))
      (mapPattern (color.symbolsOf rhoSyncIGSLT) openStaticName)
      (mapTypeExpr (color.symbolsOf rhoSyncIGSLT) (.base "Name")) :=
  synchronous_mapStatic_hasType color (openStaticName_typed free ambient)

/-- The two authored synchronous principals remain outside this theorem's
static fragment, despite all three continuation slots being decorated. -/
theorem synchronous_principals_excluded :
    "PInput" ∉ communicationDecoration.wrappedLabels ∧
      "POutputK" ∉ communicationDecoration.wrappedLabels :=
  communicationDecoration.principal_labels_excluded synchronous_nonprincipal

/-- The exclusion is enforced by the typing derivation itself. -/
theorem synchronous_output_not_static (free : FreeTypeContext) (bound : List TypeExpr)
    (arguments : List Pattern) (type : TypeExpr) :
    ¬ HasTypeWithConstructors rhoSyncCalc (· ∈ communicationDecoration.wrappedLabels)
      free bound (.apply "POutputK" arguments) type := by
  intro typed
  have supported := typed.constructorsWithin
  exact synchronous_principals_excluded.2 supported.1

end FiniteStaticTypingControls
end Mettapedia.GSLT.LanguageDef
