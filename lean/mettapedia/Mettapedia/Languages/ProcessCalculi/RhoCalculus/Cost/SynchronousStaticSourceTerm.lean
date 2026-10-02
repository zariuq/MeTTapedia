import Mettapedia.GSLT.LanguageDef.Cost.FiniteStaticSourceTerm
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalInventorySection

/-!
# The synchronous supported static source fibre

The actual finite three-payload profile has an executable source normalizer,
preserves its declaration-aware static fragment, and retains the target
support index. This instantiates the generic fibre without a continued
two-slot object or a supplied Cost-closure provider. It does not assert
operational subject reduction or retained-layer iteration closure.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Reflection
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open CanonicalInventory
open ContinuationDecorationProfile
open ReflectionExtension

namespace StaticSource
variable {color : CostStaticColor} {free : FreeTypeContext} {support : ContextSupport.Support}
  {sourceBound targetBound : List TypeExpr} {sort : LangSort rhoSyncCalc}

/-- The normalization algorithm is the established rho canonicalizer. -/
def normalize
    (term : communicationDecoration.StaticSourceTerm FiniteWhole.sourceReflection
      color free support sourceBound targetBound sort) :
    communicationDecoration.StaticSourceTerm FiniteWhole.sourceReflection
      color free support sourceBound targetBound sort :=
  term.normalize synchronousContextualSection synchronous_preservesTypedConstructors

@[simp] theorem normalize_pattern
    (term : communicationDecoration.StaticSourceTerm FiniteWhole.sourceReflection
      color free support sourceBound targetBound sort) :
    (normalize term).term.1 = Canonical.canonicalize term.term.1 := rfl

theorem normalize_idempotent
    (term : communicationDecoration.StaticSourceTerm FiniteWhole.sourceReflection
      color free support sourceBound targetBound sort) :
    normalize (normalize term) = normalize term :=
  term.normalize_idempotent synchronousContextualSection synchronous_preservesTypedConstructors

/-- Here the actual declared reflection supplies a direct edge. Thus no
unsupported intermediate source representatives are required. -/
theorem normalize_generator
    (term : communicationDecoration.StaticSourceTerm FiniteWhole.sourceReflection
      color free support sourceBound targetBound sort) :
    StaticSourceTerm.generator (normalize term) term := by
  apply ReflectiveEquationSemantics.ReflectiveEquationContextStep.reflectiveInContext .hole
    (show rhoReflectivePresentation.toReflectivePresentationDecl ∈
      rhoReflectionProfile.presentations from by simp [rhoReflectionProfile])
  change canonicalize rhoReflectivePresentation (Canonical.canonicalize term.term.1) =
    canonicalize rhoReflectivePresentation term.term.1
  simpa only [CanonicalMatch.derivedCanonicalize_eq] using
    Canonical.canonicalize_idempotent term.term.1

/-- Normalization lies in the supported equation fibre, not merely in the
larger unrestricted source equation quotient. -/
theorem normalize_equivalent
    (term : communicationDecoration.StaticSourceTerm FiniteWhole.sourceReflection
      color free support sourceBound targetBound sort) :
    StaticSourceTerm.equationSetoid.r (normalize term) term :=
  Relation.EqvGen.rel _ _ (normalize_generator term)

/-- The computed representative characterizes the actual supported source
equations on this finite profile. -/
theorem equivalent_iff_normalize_eq
    (left right : communicationDecoration.StaticSourceTerm FiniteWhole.sourceReflection
      color free support sourceBound targetBound sort) :
    StaticSourceTerm.equationSetoid.r left right ↔ normalize left = normalize right := by
  constructor
  · exact StaticSourceTerm.normalize_eq_of_equationSetoid synchronousContextualSection
      synchronous_preservesTypedConstructors
  · intro same
    exact Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.symm _ _ (normalize_equivalent left))
      (same ▸ normalize_equivalent right)

/-- Both finite Cost colours receive the normalized static representative. -/
theorem normalized_mapped_hasType
    (term : communicationDecoration.StaticSourceTerm FiniteWhole.sourceReflection
      color free support sourceBound targetBound sort) :
    HasType communicationDecoration.costWholeLanguage
      (free.map (color.symbolsOf rhoSyncIGSLT))
      (sourceBound.map (mapTypeExpr (color.symbolsOf rhoSyncIGSLT)))
      (mapPattern (color.symbolsOf rhoSyncIGSLT) (normalize term).term.1)
      (mapTypeExpr (color.symbolsOf rhoSyncIGSLT) (.base sort.1)) :=
  (normalize term).mapped_hasType FiniteStaticTypingControls.synchronous_nonprincipal

namespace Controls

def frameFree : FreeTypeContext := fun name => if name = "hole" then some (.base "Proc") else none

/-- The free boundary parameter and the open name survive unit removal. -/
def openFrame : Pattern := .collection .hashBag
  [.apply "PZero" [], .apply "PDrop" [.bvar 0], .fvar "hole"] none

theorem openFrame_typed : HasType rhoSyncCalc frameFree [.base "Name"] openFrame (.base "Proc") :=
  checkHasType_sound (by decide +kernel)

theorem openFrame_supported : HasTypeWithConstructors rhoSyncCalc
    (· ∈ communicationDecoration.wrappedLabels) frameFree [.base "Name"] openFrame (.base "Proc") := by
  apply HasType.withConstructors openFrame_typed
  · simp only [openFrame, ConstructorsWithin, ConstructorListWithin, and_true]
    exact ⟨by decide +kernel, by decide +kernel⟩
  · exact synchronous_bareConstructorsAllowed

def targetBinders (color : CostStaticColor) : List TypeExpr :=
  [mapTypeExpr (color.symbolsOf rhoSyncIGSLT) (.base "Name")]

def frameSupport (color : CostStaticColor) : ContextSupport.Support :=
  fun name => if name = "hole" then targetBinders color else []

/-- The boundary parameter depends on one actual target binder. This is
not the empty-support specialization. -/
theorem openFrame_safe (color : CostStaticColor) :
    openFrame_typed.ReflectiveSupportSafeAt rhoReflectionProfile (frameSupport color)
      (targetBinders color) (mapTypeExpr (color.symbolsOf rhoSyncIGSLT)) := by
  let zeroTyped : HasType rhoSyncCalc frameFree [.base "Name"] (.apply "PZero" []) (.base "Proc") :=
    .constructor (rule := rhoSyncCalc.terms[0]) (List.getElem_mem _)
      (by simp [UsesBareCollection, rhoSyncCalc, rhoCalc]) .nil
  have zeroSafe : zeroTyped.ReflectiveSupportSafeAt rhoReflectionProfile (frameSupport color)
      (targetBinders color) (mapTypeExpr (color.symbolsOf rhoSyncIGSLT)) := by
    apply HasType.ReflectiveSupportSafeAt.constructorOrdinary (rule := rhoSyncCalc.terms[0])
      (membership := List.getElem_mem _)
      (notBare := by simp [UsesBareCollection, rhoSyncCalc, rhoCalc])
    · decide +kernel
    · exact .nil _ _
  let dropTyped : HasType rhoSyncCalc frameFree [.base "Name"] (.apply "PDrop" [.bvar 0]) (.base "Proc") :=
    .constructor (rule := rhoSyncCalc.terms[1]) (List.getElem_mem _)
      (by simp [UsesBareCollection, rhoSyncCalc, rhoCalc, TypeExpr.name, TypeExpr.baseType])
      (.cons trivial rfl (.bvar rfl) .nil)
  have dropSafe : dropTyped.ReflectiveSupportSafeAt rhoReflectionProfile (frameSupport color)
      (targetBinders color) (mapTypeExpr (color.symbolsOf rhoSyncIGSLT)) := by
    apply HasType.ReflectiveSupportSafeAt.constructorOrdinary (rule := rhoSyncCalc.terms[1])
      (membership := List.getElem_mem _)
      (notBare := by simp [UsesBareCollection, rhoSyncCalc, rhoCalc, TypeExpr.name, TypeExpr.baseType])
      (argumentsTyped := .cons trivial rfl (.bvar rfl) .nil)
    · decide +kernel
    · exact .cons (parameter := .simple "n" (.base "Name")) (argument := .bvar 0)
        (expected := .base "Name") (representation := trivial) (parameterType := rfl)
        (.bvar rfl _) (.nil _ _)
  let holeTyped : HasType rhoSyncCalc frameFree [.base "Name"] (.fvar "hole") (.base "Proc") :=
    .fvar (by simp [frameFree])
  have holeSafe : holeTyped.ReflectiveSupportSafeAt rhoReflectionProfile (frameSupport color)
      (targetBinders color) (mapTypeExpr (color.symbolsOf rhoSyncIGSLT)) :=
    .fvar (by simp [frameFree]) _ ⟨[], by simp [frameSupport]⟩
  let frameTyped : HasType rhoSyncCalc frameFree [.base "Name"] openFrame (.base "Proc") :=
    .collectionConstructor (rule := rhoSyncCalc.terms[3]) (List.getElem_mem _) rfl
      (.cons zeroTyped (.cons dropTyped (.cons holeTyped (.nil _ _))))
  have frameSafe : frameTyped.ReflectiveSupportSafeAt rhoReflectionProfile (frameSupport color)
      (targetBinders color) (mapTypeExpr (color.symbolsOf rhoSyncIGSLT)) :=
    .collectionConstructor (rule := rhoSyncCalc.terms[3])
      (membership := List.getElem_mem _) (parameterShape := rfl)
      (.cons zeroSafe (.cons dropSafe (.cons holeSafe (.nil _ _ _))))
  exact frameSafe.castTyping

/-- Actual supported and reflectively sealed source term, with an open name
and a boundary variable carrying nonempty target support. -/
def openFrameTerm (color : CostStaticColor) :
    communicationDecoration.StaticSourceTerm FiniteWhole.sourceReflection color
      frameFree (frameSupport color) [.base "Name"] (targetBinders color)
      CanonicalInventory.Controls.processSort where
  term := ⟨openFrame, ⟨openFrame_typed, rfl, rfl, openFrame_typed.isWellScopedAt⟩, by
    intro declaration member
    have same : declaration = rhoReflectivePresentation := by
      change declaration ∈ rhoReflectionProfile.presentations at member
      simpa [rhoReflectionProfile] using member
    subst declaration
    decide +kernel⟩
  supported := openFrame_supported
  safe := openFrame_safe color

theorem openFrame_normalizes (color : CostStaticColor) :
    (normalize (openFrameTerm color)).term.1 =
      .collection .hashBag [.fvar "hole", .apply "PDrop" [.bvar 0]] none := by
  rw [normalize_pattern]
  change Canonical.canonicalize openFrame = _
  have sorted : Canonical.sortPatterns [.apply "PDrop" [.bvar 0], .fvar "hole"] =
      [.fvar "hole", .apply "PDrop" [.bvar 0]] := by
    rw [Canonical.sortPatterns_eq_of_perm (List.Perm.swap _ _ [])]
    apply List.mergeSort_of_pairwise
    exact List.pairwise_pair.mpr (by decide +kernel)
  simp [openFrame, Canonical.canonicalize, Canonical.canonicalizeList,
    Canonical.normalizeBagElements, Canonical.bagSplice, sorted, Canonical.collapseBag]

theorem openFrame_changes (color : CostStaticColor) :
    (openFrameTerm color).term.1 ≠ (normalize (openFrameTerm color)).term.1 := by
  rw [openFrame_normalizes]
  change openFrame ≠ _
  decide

theorem openFrame_support_nonempty (color : CostStaticColor) :
    frameSupport color "hole" ≠ [] := by simp [frameSupport, targetBinders]

/-- Ordinary static typing alone does not admit a quotation that reaches
through its sealing boundary to an outer name. -/
theorem unsealed_quote_rejected :
    ¬ ReflectiveWellSorted.ReflectiveScopeSafeAt rhoReflectionProfile 1
      FiniteStaticTypingControls.openStaticName := by
  intro safe
  have impossible := safe rhoReflectivePresentation (by simp [rhoReflectionProfile])
  contradiction

end Controls
end StaticSource
end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous
