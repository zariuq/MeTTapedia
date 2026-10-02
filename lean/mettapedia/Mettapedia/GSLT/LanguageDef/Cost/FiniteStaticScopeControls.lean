import Mettapedia.GSLT.LanguageDef.Cost.FiniteStaticScope
import Mettapedia.GSLT.LanguageDef.Cost.FiniteStaticThinningControls

/-!
# Actual finite reflective carrier controls

Lambda retains a selected open variable; synchronous rho retains the computed
open static frame. Nonempty nested quotation syntax remains sealed under
foreign-binder insertion. An unsealed quotation is still rejected after that
insertion, despite its ordinary typing.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.FiniteStaticScopeControls
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Reflection
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.Framework.ConstructorCategory
open WellSorted StructuralMorphism ContinuationDecorationProfile
open LambdaContinuedInteraction Mettapedia.OSLF.Framework.LambdaInstance
open Mettapedia.Languages.ProcessCalculi.RhoCalculus

private def lambdaSort : LangSort lambdaCalc := ⟨"Term", by decide⟩

def lambdaVariable (color : CostStaticColor) :
    (ofRetypingPlan lambdaContinuationRetyping).StaticSourceTerm
      (ReflectionExtension.emptyAdmitted lambdaCalc) color (fun _ => none) (fun _ => [])
      [.base "Term", .base "Term"]
      [.base costSignatureSortName, mapTypeExpr (color.symbolsOf lambdaIGSLT) (.base "Term"),
        .base costKeySortName, mapTypeExpr (color.symbolsOf lambdaIGSLT) (.base "Term")]
      lambdaSort where
  term := ⟨.bvar 1, ⟨.bvar rfl, rfl, rfl, by simp [ScopeSafeAt, Pattern.isWellScopedAt]⟩,
    ReflectiveWellSorted.reflectiveScopeSafeAt_empty _ _⟩
  supported := .bvar rfl
  safe := .bvar rfl _

theorem lambda_carrier_position (color : CostStaticColor) :
    ((lambdaVariable color).reinsert FiniteStaticTypingControls.lambda_nonprincipal
      (CostStaticTypeThinning.Controls.repeated lambdaIGSLT color (.base "Term"))).1 =
        .bvar 3 := by
  change ContextSubstitution.renameAmbientBVarsAt
    (CostStaticTypeThinning.Controls.repeated lambdaIGSLT color (.base "Term")).toTargetIndex
    0 (mapPattern (color.symbolsOf lambdaIGSLT) (.bvar 1)) = _
  simp [CostStaticTypeThinning.Controls.repeated, CostStaticTypeThinning.toTargetIndex,
    mapPattern, ContextSubstitution.renameAmbientBVarsAt]

/-- Every supported synchronous source term, not just a closed example,
constructs the complete generated reflective object carrier. -/
def synchronousCarrier
    {color : CostStaticColor} {free : FreeTypeContext} {support : ContextSupport.Support}
    {sourceBound targetBound : List TypeExpr} {sort : LangSort Synchronous.rhoSyncCalc}
    (term : Synchronous.communicationDecoration.StaticSourceTerm
      Synchronous.FiniteWhole.sourceReflection color free support sourceBound targetBound sort)
    (thinning : CostStaticTypeThinning Synchronous.rhoSyncIGSLT color sourceBound targetBound) :
    ReflectiveWellSorted.OpenPattern
      (Synchronous.communicationDecoration.costWholeReflectionProfile
        Synchronous.FiniteWhole.sourceReflection.1)
      Synchronous.communicationDecoration.costWholeLanguage
      (free.map (color.symbolsOf Synchronous.rhoSyncIGSLT)) targetBound
      (mapTypeExpr (color.symbolsOf Synchronous.rhoSyncIGSLT) (.base sort.1)) :=
  term.reinsert FiniteStaticTypingControls.synchronous_nonprincipal thinning

def synchronousNormalizedOpenFrame (color : CostStaticColor) :=
  synchronousCarrier
    (Synchronous.StaticSource.normalize (Synchronous.StaticSource.Controls.openFrameTerm color))
    (CostStaticTypeThinning.mapped (.base "Name") .nil)

theorem synchronous_normalized_open_frame_pattern (color : CostStaticColor) :
    (synchronousNormalizedOpenFrame color).1 = .collection .hashBag
      [.fvar "hole", .apply ((color.symbolsOf Synchronous.rhoSyncIGSLT).constructor "PDrop")
        [.bvar 0]] none := by
  change ContextSubstitution.renameAmbientBVarsAt
    (CostStaticTypeThinning.mapped (.base "Name") .nil).toTargetIndex 0
    (mapPattern (color.symbolsOf Synchronous.rhoSyncIGSLT)
      (Synchronous.StaticSource.normalize (Synchronous.StaticSource.Controls.openFrameTerm color)).term.1) = _
  rw [Synchronous.StaticSource.Controls.openFrame_normalizes]
  simp [mapPattern, mapPatternList, ContextSubstitution.renameAmbientBVarsAt,
    CostStaticTypeThinning.toTargetIndex]

/-- The payload is nonempty and contains a nested quotation. Its sealed
locally nameless scope makes ambient renaming inert. -/
def nestedQuote : Pattern := .apply "NQuote"
  [.apply "PDrop" [.apply "NQuote" [.apply "PZero" []]]]

theorem nestedQuote_fixed (rename : Nat → Nat) (depth : Nat) :
    ContextSubstitution.renameAmbientBVarsAt rename depth nestedQuote = nestedQuote :=
  ContextSubstitution.renameAmbientBVarsAt_eq_self_of_isWellScopedAt rename (by
    simp [nestedQuote, Pattern.isWellScopedAt, Pattern.isWellScopedListAt])

theorem nestedQuote_typed : HasTypeWithConstructors Synchronous.rhoSyncCalc
    (· ∈ Synchronous.communicationDecoration.wrappedLabels) (fun _ => none)
    [.base "Name", .base "Name"] nestedQuote (.base "Name") := by
  apply HasType.withConstructors (checkHasType_sound (by decide +kernel))
  · simp only [nestedQuote, ConstructorsWithin, ConstructorListWithin, and_true]
    decide +kernel
  · exact CanonicalInventory.synchronous_bareConstructorsAllowed

theorem nestedQuote_reinsert_sealed (color : CostStaticColor) :
    ReflectiveWellSorted.ReflectiveScopeSafeAt
      (Synchronous.communicationDecoration.costWholeReflectionProfile
        Synchronous.FiniteWhole.sourceReflection.1) 4
      (ContextSubstitution.renameAmbientBVarsAt
        (CostStaticTypeThinning.Controls.repeated Synchronous.rhoSyncIGSLT color (.base "Name")).toTargetIndex 0
        (mapPattern (color.symbolsOf Synchronous.rhoSyncIGSLT) nestedQuote)) := by
  have sourceSafe : ReflectiveWellSorted.ReflectiveScopeSafeAt
      Synchronous.FiniteWhole.sourceReflection.1 2 nestedQuote := by
    intro declaration member
    have same : declaration = rhoReflectivePresentation := by
      change declaration ∈ ReflectionExtension.rhoReflectionProfile.presentations at member
      simpa [ReflectionExtension.rhoReflectionProfile] using member
    subst declaration
    decide +kernel
  have typed := Synchronous.communicationDecoration.mapStatic_hasType
    FiniteStaticTypingControls.synchronous_nonprincipal color nestedQuote_typed
  have mapped := Synchronous.communicationDecoration.reflectiveScopeSafeAt_mapStatic
    Synchronous.FiniteWhole.sourceReflection.1 color sourceSafe typed.isWellScopedAt
  intro presentation member
  exact ContextSubstitution.binderSafeAt_renameAmbientBVarsAt
    (CostStaticTypeThinning.Controls.repeated Synchronous.rhoSyncIGSLT color (.base "Name")).toTargetIndex
    (fun _ h => PreservesBoundTypes.index_lt
      (CostStaticTypeThinning.Controls.repeated Synchronous.rhoSyncIGSLT color
        (.base "Name")).preservesBoundTypes h)
    presentation.quoteConstructor 0 _ (mapped presentation member)

/-- Increasing ordinary ambient space cannot open a quotation seal. -/
theorem unsealed_quote_still_rejected (color : CostStaticColor) :
    ¬ ReflectiveWellSorted.ReflectiveScopeSafeAt
      (Synchronous.communicationDecoration.costWholeReflectionProfile
        Synchronous.FiniteWhole.sourceReflection.1) 4
      (ContextSubstitution.renameAmbientBVarsAt
        (CostStaticTypeThinning.Controls.repeated Synchronous.rhoSyncIGSLT color (.base "Name")).toTargetIndex 0
        (mapPattern (color.symbolsOf Synchronous.rhoSyncIGSLT)
          FiniteStaticTypingControls.openStaticName)) := by
  intro safe
  cases color with
  | base =>
      have impossible := safe
        (costBaseReflectivePresentationDecl rhoReflectivePresentation)
        (by decide +kernel)
      revert impossible
      decide +kernel
  | wrapped =>
      have impossible := safe
        (costWrappedReflectivePresentationDecl Synchronous.rhoSyncIGSLT
          rhoReflectivePresentation) (by decide +kernel)
      revert impossible
      decide +kernel

end Mettapedia.GSLT.LanguageDef.FiniteStaticScopeControls
