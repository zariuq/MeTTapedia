import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.FiniteStaticCanonicalActionConsumer
import Mettapedia.GSLT.LanguageDef.Cost.FiniteStaticActionControls

/-!
# Canonical finite action with genuine synchronous boundary values

The open frame has nonempty dependency support and receives POutputK in
both static colors. Normalizing that source changes the literal target but
preserves its admitted equation class. A separate Quote/Drop control restores
a sealed quotation of the same synchronous value. Signature syntax is rejected
as a Name value; lambda's actual empty reflection supplies no rho declaration.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous.FiniteStaticCanonicalActionControls
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Reflection
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open ContinuationDecorationProfile ReflectionExtension
open StaticSource.Controls FiniteStaticActionControls

/-- The actual POutputK-valued restoration absorbs source normalization in
one typed generated equation edge, with one visible Name dependency. -/
theorem outputK_frame_generator (color : CostStaticColor) :
    AvailableOpenPattern.equationGenerator (restoredFrame color)
      ((openFrameTerm color).actAvailable FiniteStaticTypingControls.synchronous_nonprincipal
        CanonicalInventory.synchronous_bareConstructorsAllowed
        (.mapped (.base "Name") .nil) (outputAssignment color)) :=
  StaticSource.action_normalize_generator (openFrameTerm color)
    (.mapped (.base "Name") .nil) (outputAssignment color)

/-- Equation preservation does not assert literal equality of restored frames. -/
theorem outputK_frame_literal_distinct (color : CostStaticColor) :
    (restoredFrame color).pattern ≠
      ((openFrameTerm color).actAvailable FiniteStaticTypingControls.synchronous_nonprincipal
        CanonicalInventory.synchronous_bareConstructorsAllowed
        (.mapped (.base "Name") .nil) (outputAssignment color)).pattern := by
  rw [restoredFrame_pattern]
  cases color <;> decide +kernel

def nameFree : FreeTypeContext := fun name => if name = "n" then some (.base "Name") else none

def quotedOutput (color : CostStaticColor) : Pattern :=
  .apply ((color.symbolsOf rhoSyncIGSLT).constructor "NQuote") [boundaryValue color]

theorem quotedOutput_typed (color : CostStaticColor) :
    HasType communicationDecoration.costWholeLanguage (fun _ => none) [] (quotedOutput color)
      (mapTypeExpr (color.symbolsOf rhoSyncIGSLT) (.base "Name")) := by
  apply checkHasType_sound
  cases color <;> decide +kernel

theorem quotedOutput_sealed (color : CostStaticColor) :
    ReflectiveWellSorted.ReflectiveScopeSafeAt
      (communicationDecoration.costWholeReflectionProfile rhoReflectionProfile) 0
      (quotedOutput color) := by
  intro declaration member
  simp only [costWholeReflectionProfile, costStaticReflectivePresentations,
    rhoReflectionProfile, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> cases color <;> decide +kernel

def quotedOutputAssignment (color : CostStaticColor) :
    SupportedOpenAssignment
      (communicationDecoration.costWholeReflectionProfile rhoReflectionProfile)
      communicationDecoration.costWholeLanguage (nameFree.map (color.symbolsOf rhoSyncIGSLT))
      (fun _ => none) (fun _ => []) where
  assignment := fun _ => quotedOutput color
  typed := by
    intro name type lookup
    have named : name = "n" := by
      by_contra other
      simp [FreeTypeContext.map, nameFree, other] at lookup
    subst name
    have same : type = mapTypeExpr (color.symbolsOf rhoSyncIGSLT) (.base "Name") := by
      simpa [FreeTypeContext.map, nameFree] using lookup.symm
    subst type
    exact quotedOutput_typed color
  canonicalBinderMetadata := by intro name type lookup; cases color <;> decide +kernel
  objectPattern := by intro name type lookup; cases color <;> decide +kernel
  reflectiveScopeSafe := by intro name type lookup; exact quotedOutput_sealed color

/-- The nonstructural quotation case accepts a full finite target value with
synchronous output, under either authored static-color reflection declaration. -/
theorem quoted_output_cancellation (color : CostStaticColor) :
    canonicalize (FiniteStaticCanonicalAction.declaration rhoSyncIGSLT color)
      (FiniteStaticCanonicalAction.actionAt communicationDecoration color .nil
        (quotedOutputAssignment color) [] [] (.apply "NQuote" [.apply "PDrop" [.fvar "n"]])) =
    canonicalize (FiniteStaticCanonicalAction.declaration rhoSyncIGSLT color)
      (FiniteStaticCanonicalAction.actionAt communicationDecoration color .nil
        (quotedOutputAssignment color) [] [] (.fvar "n")) := by
  have typed : HasType rhoSyncCalc nameFree [] (.fvar "n") (.base "Name") :=
    .fvar (by simp [nameFree])
  have safe : typed.ReflectiveSupportSafeAt rhoReflectionProfile (fun _ => []) []
      (mapTypeExpr (color.symbolsOf rhoSyncIGSLT)) :=
    .fvar (by simp [nameFree]) _ ⟨[], rfl⟩
  exact FiniteStaticCanonicalAction.quoteDrop communicationDecoration
    FiniteStaticTypingControls.synchronous_nonprincipal
    CanonicalInventory.synchronous_bareConstructorsAllowed
    FiniteReflectiveInventory.nameResultsQuoted (inner := []) .nil (quotedOutputAssignment color)
    typed safe trivial rfl []

theorem signature_rejected_as_name (color : CostStaticColor) :
    checkHasType communicationDecoration.costWholeLanguage (fun _ => none) []
      (.apply costSignatureUnitConstructorName [])
      (mapTypeExpr (color.symbolsOf rhoSyncIGSLT) (.base "Name")) = false := by
  cases color <;> decide +kernel

/-- The required lambda instance does not acquire a rho equation declaration. -/
theorem lambda_reflection_stays_empty :
    ((ofRetypingPlan LambdaContinuedInteraction.lambdaContinuationRetyping).costWholeReflectionProfile
      (emptyAdmitted Mettapedia.OSLF.Framework.LambdaInstance.lambdaCalc).1).presentations = [] := rfl

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous.FiniteStaticCanonicalActionControls
