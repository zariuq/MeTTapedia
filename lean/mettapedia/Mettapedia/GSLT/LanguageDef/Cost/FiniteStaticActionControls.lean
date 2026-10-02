import Mettapedia.GSLT.LanguageDef.Cost.FiniteStaticAction
import Mettapedia.GSLT.LanguageDef.Cost.FiniteStaticScopeControls

/-!
# Actual synchronous boundary restoration

An open normalized static frame receives an independently supplied target
value containing synchronous POutputK, both continuation payload positions,
and both static colors. No old asynchronous target language is used to admit
that value.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.FiniteStaticActionControls
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Reflection
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open WellSorted StructuralMorphism ContinuationDecorationProfile
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Synchronous.StaticSource.Controls

/-- Actual synchronous output in the generated base grammar, with its two
wrapped continuation payloads and a wrapped quotation in its Name slot. -/
def outputK : Pattern := .apply (costBaseConstructorName "POutputK")
  [.apply (costWrappedConstructorName "NQuote") [.apply (costWrappedConstructorName "PZero") []],
    .apply (costWrappedConstructorName "PZero") [],
    .apply (costWrappedConstructorName "PZero") []]

def boundaryValue : CostStaticColor → Pattern
  | .base => outputK
  | .wrapped => .apply costSignedConstructorName
      [outputK, .apply costSignatureUnitConstructorName []]

theorem boundaryValue_typed (color : CostStaticColor) :
    HasType Synchronous.communicationDecoration.costWholeLanguage (fun _ => none)
      (targetBinders color) (boundaryValue color)
      (mapTypeExpr (color.symbolsOf Synchronous.rhoSyncIGSLT) (.base "Proc")) := by
  apply checkHasType_sound
  cases color <;> decide +kernel

theorem boundaryValue_sealed (color : CostStaticColor) :
    ReflectiveWellSorted.ReflectiveScopeSafeAt
      (Synchronous.communicationDecoration.costWholeReflectionProfile
        Synchronous.FiniteWhole.sourceReflection.1) (targetBinders color).length
      (boundaryValue color) := by
  intro declaration member
  cases color <;>
    simp only [Synchronous.FiniteWhole.sourceReflection,
      costWholeReflectionProfile, costStaticReflectivePresentations,
      ReflectionExtension.rhoReflectionProfile, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
      at member
  all_goals rcases member with rfl | rfl <;> decide +kernel

/-- The assignment is certified in the actual finite target grammar. Its
values are independent of the source frame and may use generated principals. -/
def outputAssignment (color : CostStaticColor) :
    SupportedOpenAssignment
      (Synchronous.communicationDecoration.costWholeReflectionProfile
        Synchronous.FiniteWhole.sourceReflection.1)
      Synchronous.communicationDecoration.costWholeLanguage
      (frameFree.map (color.symbolsOf Synchronous.rhoSyncIGSLT)) (fun _ => none)
      (frameSupport color) where
  assignment := fun _ => boundaryValue color
  typed := by
    intro name type lookup
    have named : name = "hole" := by
      by_contra other
      simp [FreeTypeContext.map, frameFree, other] at lookup
    subst name
    have typed : type = mapTypeExpr (color.symbolsOf Synchronous.rhoSyncIGSLT) (.base "Proc") := by
      simpa [FreeTypeContext.map, frameFree] using lookup.symm
    subst type
    simpa [frameSupport] using boundaryValue_typed color
  canonicalBinderMetadata := by
    intro name type lookup
    cases color <;> decide +kernel
  objectPattern := by
    intro name type lookup
    cases color <;> decide +kernel
  reflectiveScopeSafe := by
    intro name type lookup
    have named : name = "hole" := by
      by_contra other
      simp [FreeTypeContext.map, frameFree, other] at lookup
    subst name
    simpa [frameSupport] using boundaryValue_sealed color

def restoredFrame (color : CostStaticColor) :=
  (Synchronous.StaticSource.normalize (openFrameTerm color)).actAvailable
    FiniteStaticTypingControls.synchronous_nonprincipal
    CanonicalInventory.synchronous_bareConstructorsAllowed
    (.mapped (.base "Name") .nil) (outputAssignment color)

theorem restoredFrame_pattern (color : CostStaticColor) :
    (restoredFrame color).pattern = .collection .hashBag
      [boundaryValue color,
        .apply ((color.symbolsOf Synchronous.rhoSyncIGSLT).constructor "PDrop") [.bvar 0]] none := by
  change ReflectiveContextSupport.substituteAt
    (Synchronous.communicationDecoration.costWholeReflectionProfile
      Synchronous.FiniteWhole.sourceReflection.1)
    (frameSupport color) (outputAssignment color).assignment (targetBinders color).length
    (ContextSubstitution.renameAmbientBVarsAt
      (CostStaticTypeThinning.mapped (.base "Name") .nil).toTargetIndex 0
      (mapPattern (color.symbolsOf Synchronous.rhoSyncIGSLT)
        (Synchronous.StaticSource.normalize (openFrameTerm color)).term.1)) = _
  rw [openFrame_normalizes]
  cases color <;> decide +kernel

/-- The Signature sort cannot supply the frame's process-valued boundary. -/
theorem signature_rejected_as_boundary (color : CostStaticColor) :
    checkHasType Synchronous.communicationDecoration.costWholeLanguage (fun _ => none)
      (targetBinders color) (.apply costSignatureUnitConstructorName [])
      (mapTypeExpr (color.symbolsOf Synchronous.rhoSyncIGSLT) (.base "Proc")) = false := by
  cases color <;> decide +kernel

/-- Actual target validation discharges the generic typed pointwise action
law for arbitrary supported values, including POutputK-valued assignments. -/
theorem synchronous_assignment_equivalence (color : CostStaticColor)
    (first second : SupportedOpenAssignment
      (Synchronous.communicationDecoration.costWholeReflectionProfile
        Synchronous.FiniteWhole.sourceReflection.1)
      Synchronous.communicationDecoration.costWholeLanguage
      (frameFree.map (color.symbolsOf Synchronous.rhoSyncIGSLT)) (fun _ => none)
      (frameSupport color))
    (equivalent : first.FiberEquivalent second) :
    (AvailableOpenPattern.equationSetoid
      Synchronous.communicationDecoration.costWholeLanguage (fun _ => none)
      (targetBinders color) []
      (mapTypeExpr (color.symbolsOf Synchronous.rhoSyncIGSLT) (.base "Proc"))).r
      ((Synchronous.StaticSource.normalize (openFrameTerm color)).actAvailable
        FiniteStaticTypingControls.synchronous_nonprincipal
        CanonicalInventory.synchronous_bareConstructorsAllowed
        (.mapped (.base "Name") .nil) first)
      ((Synchronous.StaticSource.normalize (openFrameTerm color)).actAvailable
        FiniteStaticTypingControls.synchronous_nonprincipal
        CanonicalInventory.synchronous_bareConstructorsAllowed
        (.mapped (.base "Name") .nil) second) :=
  (Synchronous.StaticSource.normalize (openFrameTerm color)).actAvailable_equationSetoid_pointwise
    Synchronous.FiniteWhole.language_valid Synchronous.FiniteWhole.reflection_valid
    FiniteStaticTypingControls.synchronous_nonprincipal
    CanonicalInventory.synchronous_bareConstructorsAllowed
    (.mapped (.base "Name") .nil) first second equivalent

end Mettapedia.GSLT.LanguageDef.FiniteStaticActionControls
