import Mettapedia.GSLT.LanguageDef.CostHereditaryCanonical
import Mettapedia.GSLT.LanguageDef.CostHereditaryAlignment
import Mettapedia.GSLT.LanguageDef.CostHereditaryContextRoute
import Mettapedia.GSLT.LanguageDef.CostHereditaryTreeNormalization
import Mettapedia.GSLT.LanguageDef.CostElaborationTransportSound
import Mettapedia.GSLT.LanguageDef.CostSemanticAtomReifyCongruence
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalSupport
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostCanonicalLaws
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-!
# Hereditary Cost canonicalization for rho

The generic semantic-atom carrier exposes an authored rho frame and its exact
image in one generated Cost colour.  This module proves that rho's keyed
reflective canonicalizer remains in the declaration-derived constructor
fragment, then transports its typing and quote-safe support through the Cost
symbol map and the certified ambient-binder thinning.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ReflectionExtension
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.CostStaticRegionNode
open Mettapedia.GSLT.LanguageDef.CostHereditaryCanonical
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.PatternCode
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalSupport
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostCanonicalLaws
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefCanonicalSection
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- Keyed canonicalization of an authored rho name is independent of the
ambient quote-visible depth.  Variables are immediate; the sole
object-forming `Name` constructor is `NQuote`, whose child depth is reset to
zero. -/
theorem rhoName_canonicalizeByDepths_availableDepth_independent
    {Key : Type} [LinearOrder Key]
    (key : Nat -> Nat -> Pattern -> Key)
    {free : FreeTypeContext} {bound : List TypeExpr} {name : Pattern}
    (typed : HasType rhoCalc free bound name TypeExpr.name)
    (object : isObjectPattern name = true)
    (firstDepth secondDepth scopeDepth : Nat) :
    canonicalizeByDepths key rhoReflectivePresentation firstDepth scopeDepth
        name =
      canonicalizeByDepths key rhoReflectivePresentation secondDepth scopeDepth
        name := by
  have aux : ∀ {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr},
      HasType rhoCalc free bound pattern type ->
      type = TypeExpr.name ->
      isObjectPattern pattern = true ->
      ∀ firstDepth secondDepth scopeDepth,
        canonicalizeByDepths key rhoReflectivePresentation firstDepth
            scopeDepth pattern =
          canonicalizeByDepths key rhoReflectivePresentation secondDepth
            scopeDepth pattern := by
    intro bound pattern type typing type_eq object firstDepth secondDepth
      scopeDepth
    cases typing with
    | bvar lookup => rfl
    | fvar lookup => rfl
    | constructor ruleMembership notBare argumentsTyped =>
        simp [rhoCalc] at ruleMembership
        rcases ruleMembership with rfl | rfl | rfl | rfl | rfl | rfl
        all_goals simp [TypeExpr.name, TypeExpr.baseType] at type_eq
        rfl
    | lambda bodyTyped => simp [TypeExpr.name, TypeExpr.baseType] at type_eq
    | multiLambda bodyTyped =>
        simp [TypeExpr.name, TypeExpr.baseType] at type_eq
    | subst bodyTyped replacementTyped => simp [isObjectPattern] at object
    | collection elementsTyped =>
        simp [TypeExpr.name, TypeExpr.baseType] at type_eq
    | collectionConstructor ruleMembership parameterShape elementsTyped =>
        simp [rhoCalc] at ruleMembership
        rcases ruleMembership with rfl | rfl | rfl | rfl | rfl | rfl
        all_goals
          simp [TypeExpr.name, TypeExpr.proc, TypeExpr.baseType] at type_eq parameterShape
  exact aux typed rfl object firstDepth secondDepth scopeDepth

/-- The rho Quote/Drop generator is absorbed exactly by every two-depth keyed
canonicalizer on the authored name carrier.  The left branch resets to depth
zero; the preceding theorem identifies that result with the ambient-depth
right branch. -/
theorem rhoQuoteDrop_canonicalizeByDepths_eq
    {Key : Type} [LinearOrder Key]
    (key : Nat -> Nat -> Pattern -> Key)
    {free : FreeTypeContext} {bound : List TypeExpr} {name : Pattern}
    (typed : HasType rhoCalc free bound name TypeExpr.name)
    (object : isObjectPattern name = true)
    (availableDepth scopeDepth : Nat) :
    canonicalizeByDepths key rhoReflectivePresentation availableDepth scopeDepth
        (.apply rhoReflectivePresentation.quoteConstructor
          [.apply rhoReflectivePresentation.dropConstructor [name]]) =
      canonicalizeByDepths key rhoReflectivePresentation availableDepth scopeDepth
        name := by
  rw [canonicalizeByDepths_quote_drop]
  · exact rhoName_canonicalizeByDepths_availableDepth_independent key typed
      object 0 availableDepth scopeDepth
  · simp [rhoReflectivePresentation]

/-- Exact keyed Quote/Drop absorption remains valid at every structural
one-hole position.  The context computes the quote-visible and structural
depths at its hole before the local rho theorem is applied. -/
theorem rhoQuoteDrop_canonicalizeByDepths_fill_eq
    {Key : Type} [LinearOrder Key]
    (key : Nat -> Nat -> Pattern -> Key)
    {free : FreeTypeContext} {bound : List TypeExpr} {name : Pattern}
    (typed : HasType rhoCalc free bound name TypeExpr.name)
    (object : isObjectPattern name = true)
    (availableDepth scopeDepth : Nat) (context : OneHoleContext) :
    canonicalizeByDepths key rhoReflectivePresentation availableDepth scopeDepth
        (context.fill
          (.apply rhoReflectivePresentation.quoteConstructor
            [.apply rhoReflectivePresentation.dropConstructor [name]])) =
      canonicalizeByDepths key rhoReflectivePresentation availableDepth
        scopeDepth (context.fill name) := by
  apply Mettapedia.GSLT.LanguageDef.OneHoleContext.canonicalizeByDepths_fill_congr key
    rhoReflectivePresentation availableDepth scopeDepth context
  exact rhoQuoteDrop_canonicalizeByDepths_eq key typed object
    (Mettapedia.GSLT.LanguageDef.OneHoleContext.canonicalizeHoleDepths
      rhoReflectivePresentation availableDepth scopeDepth context).1
    (Mettapedia.GSLT.LanguageDef.OneHoleContext.canonicalizeHoleDepths
      rhoReflectivePresentation availableDepth scopeDepth context).2

/-- A generated rho Quote/Drop shell around one semantic atom is absorbed by
the selected Cost declaration at every structural position.  The atom is a
free variable in the common semantic namespace, so quotation's depth reset
cannot change its representative. -/
theorem rhoCostStaticQuoteDrop_canonicalizeByAt_fill_fvar_eq
    {Key : Type} [LinearOrder Key]
    (key : Nat -> Pattern -> Key) (color : CostStaticColor)
    (availableDepth : Nat) (context : OneHoleContext) (name : String) :
    let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
      rhoReflectivePresentation
    canonicalizeByAt key declaration availableDepth
        (context.fill
          (.apply declaration.quoteConstructor
            [.apply declaration.dropConstructor [.fvar name]])) =
      canonicalizeByAt key declaration availableDepth
        (context.fill (.fvar name)) := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation
  dsimp only
  have quoteNeDrop : declaration.quoteConstructor ≠
      declaration.dropConstructor := by
    cases color <;>
      simp [declaration, mapReflectivePresentation, rhoReflectivePresentation]
  rw [<- canonicalizeByDepths_ignoreScope key declaration availableDepth 0,
    <- canonicalizeByDepths_ignoreScope key declaration availableDepth 0]
  apply Mettapedia.GSLT.LanguageDef.OneHoleContext.canonicalizeByDepths_fill_congr
    (fun available _ pattern => key available pattern) declaration
      availableDepth 0 context
  rw [canonicalizeByDepths_quote_drop _ declaration quoteNeDrop]
  rfl

/-- Rho's two-depth keyed canonicalizer preserves the proof-relevant
constructor fragment as well as typing and reflective support. -/
theorem rhoCanonicalizeByDepths_hasTypeWithConstructors
    {Key : Type} [LinearOrder Key]
    (key : Nat → Nat → Pattern → Key) (scopeDepth : Nat)
    {free : FreeTypeContext} {support : ContextSupport.Support}
    {bound available : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    {binderImage : TypeExpr → TypeExpr}
    (typed : HasTypeWithConstructors rhoCalc
      (· ∈ rhoContinuationRetyping.wrappedLabels)
      free bound pattern type)
    (safe : typed.toHasType.ReflectiveSupportSafeAt rhoReflectionProfile
      support available
      binderImage)
    (canonicalizable : CanonicalizableRhoType type)
    (object : isObjectPattern pattern = true) :
    ∃ normalizedTyped : HasTypeWithConstructors rhoCalc
        (· ∈ rhoContinuationRetyping.wrappedLabels)
        free bound
        (canonicalizeByDepths key rhoReflectivePresentation available.length
          scopeDepth pattern) type,
      normalizedTyped.toHasType.ReflectiveSupportSafeAt rhoReflectionProfile
        support available
        binderImage := by
  obtain ⟨normalizedTyped, normalizedSafe⟩ :=
    canonicalizeByDepths_supportSafe key scopeDepth typed.toHasType safe
      canonicalizable object
  have normalizedSupported :
      ConstructorsWithin (· ∈ rhoContinuationRetyping.wrappedLabels)
        (canonicalizeByDepths key rhoReflectivePresentation available.length
          scopeDepth pattern) :=
    (constructorsWithin_canonicalizeByDepths_iff key
      rhoReflectivePresentation rhoReflectiveConstructorsAllowed
      available.length scopeDepth pattern).mpr typed.constructorsWithin
  let normalizedWithConstructors := normalizedTyped.withConstructors
    normalizedSupported rhoBareCollectionConstructorsWrapped
  refine ⟨normalizedWithConstructors, ?_⟩
  exact normalizedSafe.castTyping

namespace CostStaticRegionNode

/-- Pull the target semantic ordering key back through the exact Cost map and
ambient-binder thinning square. -/
def sourceSemanticPatternKeyAt
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    (availableDepth scopeDepth : Nat) (pattern : Pattern) : Nat :=
  Mettapedia.GSLT.LanguageDef.CostStaticRegionNode.semanticPatternKeyAt
    environment availableDepth
    (node.thinning.thickenAmbientBVars scopeDepth
      (mapPattern (color.symbols rhoCIGSLT) pattern))

/-- Canonicalizing the authored semantic-atom frame and then applying the
Cost map plus binder thinning is exactly target-frame keyed canonicalization.
This is an equality of compact patterns, not merely contextual equivalence. -/
theorem canonicalizeReifiedTargetFrame_eq_map_sourceCanonicalize
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory) :
    node.canonicalizeReifiedTargetFrame environment
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) =
      node.thinning.thickenAmbientBVars 0
        (mapPattern (color.symbols rhoCIGSLT)
          (canonicalizeByDepths (sourceSemanticPatternKeyAt node environment)
            rhoReflectivePresentation node.targetBound.length 0
            (node.reifiedSourceFrame environment).1)) := by
  symm
  let targetKey : Nat → Nat → Pattern → Nat :=
    fun availableDepth _ pattern =>
      Mettapedia.GSLT.LanguageDef.CostStaticRegionNode.semanticPatternKeyAt
        environment availableDepth pattern
  calc
    node.thinning.thickenAmbientBVars 0
          (mapPattern (color.symbols rhoCIGSLT)
            (canonicalizeByDepths
              (sourceSemanticPatternKeyAt node environment)
              rhoReflectivePresentation node.targetBound.length 0
              (node.reifiedSourceFrame environment).1)) =
        canonicalizeByDepths targetKey
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation)
          node.targetBound.length 0
          (node.thinning.thickenAmbientBVars 0
            (mapPattern (color.symbols rhoCIGSLT)
              (node.reifiedSourceFrame environment).1)) := by
      unfold sourceSemanticPatternKeyAt
      exact mapThicken_canonicalizeByDepths node.thinning targetKey
        rhoReflectivePresentation node.targetBound.length 0
        (node.reifiedSourceFrame environment).1
    _ = canonicalizeByDepths targetKey
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation)
          node.targetBound.length 0 (node.reifyTargetFrame environment) := by
      rw [node.reifyTargetFrame_eq_map_reifiedSourceFrame environment]
    _ = node.canonicalizeReifiedTargetFrame environment
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation) := by
      simpa [targetKey,
        Mettapedia.GSLT.LanguageDef.CostStaticRegionNode.canonicalizeReifiedTargetFrame]
        using
          (canonicalizeByDepths_ignoreScope
            (Mettapedia.GSLT.LanguageDef.CostStaticRegionNode.semanticPatternKeyAt
              environment)
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation)
            node.targetBound.length 0 (node.reifyTargetFrame environment))

/-- Rho's semantic-key canonical target frame is a genuine typed,
reflectively support-safe object of the generated Cost language.  The proof
comes entirely from the authored rho derivation, exact static transport, and
the node's certified binder thinning. -/
theorem canonicalizeReifiedTargetFrame_supportSafe
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    (typeMap : ∀ slot,
      mapTypeExpr (color.symbols rhoCIGSLT)
          (environment.atomValue slot).key.sourceType =
        (environment.atomValue slot).key.targetType) :
    ∃ targetTyped : HasType rhoCIGSLT.costWholeLanguage
        environment.atomFreeContext node.targetBound
        (node.canonicalizeReifiedTargetFrame environment
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation))
        (.base (color.mapLangSort rhoCIGSLT node.sourceSort).1),
      targetTyped.ReflectiveSupportSafeAt
        rhoCIGSLT.costWholeReflectionProfile environment.restorationSupport
        node.targetBound := by
  let sourceSupported := node.reifiedSourceFrame_supported environment
  have sourceSafe : sourceSupported.toHasType.ReflectiveSupportSafeAt
      rhoReflectionProfile environment.sourceAtomSupport node.targetBound
      (mapTypeExpr (color.symbols rhoCIGSLT)) :=
    (node.reifiedSourceFrame_supportSafe environment).castTyping
  obtain ⟨sourceNormalized, sourceNormalizedSafe⟩ :=
    rhoCanonicalizeByDepths_hasTypeWithConstructors
      (sourceSemanticPatternKeyAt node environment) 0 sourceSupported
      sourceSafe (by trivial)
        (node.reifiedSourceFrame environment).2.1.2.2.1
  obtain ⟨mappedTypedRaw, mappedSafeRaw⟩ :=
    sourceNormalizedSafe.mapCostStatic rhoCIGSLT color
      sourceNormalized.constructorsWithin
  have contextEquality :
      environment.sourceAtomFreeContext.map (color.symbols rhoCIGSLT) =
        environment.atomFreeContext :=
    environment.sourceAtomFreeContext_map_eq_atomFreeContext
      typeMap
  rw [← contextEquality]
  have mappedSafe : mappedTypedRaw.ReflectiveSupportSafeAt
      rhoCIGSLT.costWholeReflectionProfile environment.restorationSupport
      node.targetBound := by
    rw [← environment.sourceAtomSupport_eq_restorationSupport]
    exact mappedSafeRaw
  have thickenedTypedRaw := mappedTypedRaw.thickenAmbientBVars
    (inner := []) node.thinning
  have thickenedSafeRaw := mappedSafe.thickenAmbientBVars
    (inner := []) node.thinning
  have thickenedTyped : HasType rhoCIGSLT.costWholeLanguage
      (environment.sourceAtomFreeContext.map (color.symbols rhoCIGSLT))
      node.targetBound
      (node.thinning.thickenAmbientBVars 0
        (mapPattern (color.symbols rhoCIGSLT)
          (canonicalizeByDepths (sourceSemanticPatternKeyAt node environment)
            rhoReflectivePresentation node.targetBound.length 0
            (node.reifiedSourceFrame environment).1)))
      (.base (color.mapLangSort rhoCIGSLT node.sourceSort).1) := by
    simpa only [List.nil_append, List.length_nil, mapTypeExpr,
      CostStaticColor.mapLangSort_name] using thickenedTypedRaw
  have thickenedSafe : thickenedTyped.ReflectiveSupportSafeAt
      rhoCIGSLT.costWholeReflectionProfile environment.restorationSupport
      node.targetBound :=
    thickenedSafeRaw.castTyping
  rw [canonicalizeReifiedTargetFrame_eq_map_sourceCanonicalize node
    environment]
  exact ⟨thickenedTyped, thickenedSafe⟩

/-- The executable semantic quotient produced from an inventory satisfies the
type-map premise automatically, so its keyed target canonicalization is
support-safe without any external hypothesis. -/
theorem canonicalizeReifiedTargetFrame_ofInventory_supportSafe
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable)
    (inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1) :
    ∃ targetTyped : HasType rhoCIGSLT.costWholeLanguage
        (CostStaticAtomEnvironment.ofInventory inventory).atomFreeContext
        node.targetBound
        (node.canonicalizeReifiedTargetFrame
          (CostStaticAtomEnvironment.ofInventory inventory)
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation))
        (.base (color.mapLangSort rhoCIGSLT node.sourceSort).1),
      targetTyped.ReflectiveSupportSafeAt
        rhoCIGSLT.costWholeReflectionProfile
        (CostStaticAtomEnvironment.ofInventory inventory).restorationSupport
        node.targetBound :=
  canonicalizeReifiedTargetFrame_supportSafe node
    (CostStaticAtomEnvironment.ofInventory inventory)
    (node.semanticAtom_typeMap values inventory)

/-- The semantic-key target frame is a full open object, not merely a raw
typed pattern.  Key ordering preserves binder metadata, object syntax, and
the quote-aware scope invariant of every generated reflective presentation. -/
def canonicalizeReifiedTargetFrame_openTerm
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable)
    (inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1) :
    ReflectiveWellSorted.OpenTerm rhoCIGSLT.costWholeReflectionProfile
      rhoCIGSLT.costWholeLanguage
      (CostStaticAtomEnvironment.ofInventory inventory).atomFreeContext
      node.targetBound (color.mapLangSort rhoCIGSLT node.sourceSort) := by
  let environment := CostStaticAtomEnvironment.ofInventory inventory
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation
  refine ⟨node.canonicalizeReifiedTargetFrame environment declaration, ?_⟩
  obtain ⟨targetTyped, targetSafe⟩ :=
    canonicalizeReifiedTargetFrame_ofInventory_supportSafe node values
      inventory
  refine ⟨⟨targetTyped, ?_, ?_, targetTyped.isWellScopedAt⟩, ?_⟩
  · exact canonicalizeByAt_hasCanonicalBinderMetadata
      (CostStaticRegionNode.semanticPatternKeyAt environment) declaration
      node.targetBound.length (node.reifyTargetFrame environment)
      (by simpa only [CostStaticRegionNode.reifiedTargetFrame_pattern] using
        (node.reifiedTargetFrame environment).2.1.2.1)
  · exact canonicalizeByAt_isObjectPattern
      (CostStaticRegionNode.semanticPatternKeyAt environment) declaration
      node.targetBound.length (node.reifyTargetFrame environment)
      (by simpa only [CostStaticRegionNode.reifiedTargetFrame_pattern] using
        (node.reifiedTargetFrame environment).2.1.2.2.1)
  · intro presentation membership
    exact canonicalizeByAt_binderSafeAt
      (CostStaticRegionNode.semanticPatternKeyAt environment) declaration
      presentation.quoteConstructor node.targetBound.length
      node.targetBound.length (node.reifyTargetFrame environment)
      (by simpa only [CostStaticRegionNode.reifiedTargetFrame_pattern] using
        (node.reifiedTargetFrame environment).2.2 presentation membership)

/-- The full open target frame retains the restoration-support certificate
proved by the rho source action. -/
theorem canonicalizeReifiedTargetFrame_openTerm_supportSafe
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable)
    (inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1) :
    (canonicalizeReifiedTargetFrame_openTerm node values inventory
      ).2.1.1.ReflectiveSupportSafeAt
        rhoCIGSLT.costWholeReflectionProfile
        (CostStaticAtomEnvironment.ofInventory inventory).restorationSupport
        node.targetBound := by
  obtain ⟨targetTyped, targetSafe⟩ :=
    canonicalizeReifiedTargetFrame_ofInventory_supportSafe node values
      inventory
  exact targetSafe.castTyping

/-- Rename one typed hereditary target frame into a common semantic-key
namespace.  Both the generated result type and the exact reflective support
travel through the cospan leg; the common frame is not reconstructed by a
second syntax checker. -/
theorem canonicalizeReifiedTargetFrame_toCommon_supportSafe
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable)
    (inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leg : Fin (CostStaticAtomEnvironment.ofInventory inventory).atomCount →
      Fin cospan.commonKeys.length)
    (commutes : ∀ slot,
      cospan.commonKeys.get (leg slot) =
        ((CostStaticAtomEnvironment.ofInventory inventory).atomValue slot).key) :
    ∃ targetTyped : HasType rhoCIGSLT.costWholeLanguage
        cospan.commonTargetFreeContext node.targetBound
        (cospan.reifyWith
          (CostStaticAtomEnvironment.ofInventory inventory).lookupAtom? leg
          (node.canonicalizeReifiedTargetFrame
            (CostStaticAtomEnvironment.ofInventory inventory)
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation)))
        (.base (color.mapLangSort rhoCIGSLT node.sourceSort).1),
      targetTyped.ReflectiveSupportSafeAt
        rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
        node.targetBound := by
  let environment := CostStaticAtomEnvironment.ofInventory inventory
  obtain ⟨targetTyped, targetSafe⟩ :=
    canonicalizeReifiedTargetFrame_ofInventory_supportSafe node values
      inventory
  have renamed := environment.reifyWith_targetReflectiveSupportSafeAt
    cospan leg commutes targetSafe
  simpa only [environment] using renamed

/-- Every free name in the selected canonical target frame resolves to one
slot of the finite semantic-atom environment.  This follows from the frame's
typed open carrier; no independent syntactic occurrence scan is needed. -/
theorem canonicalizeReifiedTargetFrame_atomCovered
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable)
    (inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1)
    (name : String)
    (membership : name ∈
      (node.canonicalizeReifiedTargetFrame
        (CostStaticAtomEnvironment.ofInventory inventory)
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation)).freeFvarNames) :
    ∃ slot, (CostStaticAtomEnvironment.ofInventory inventory).lookupAtom?
      name = some slot := by
  let term := canonicalizeReifiedTargetFrame_openTerm node values inventory
  have termMembership : name ∈ term.1.freeFvarNames := by
    exact membership
  obtain ⟨type, lookup⟩ :=
    term.toCore.freeType_of_mem_freeFvarNames termMembership
  let environment := CostStaticAtomEnvironment.ofInventory inventory
  change environment.atomFreeContext name = some type at lookup
  simp only [CostStaticAtomEnvironment.atomFreeContext] at lookup
  cases selected : environment.lookupAtom? name with
  | none => simp [selected] at lookup
  | some slot => exact ⟨slot, rfl⟩

/-- Build the complete canonical atom-frame alignment from its sole semantic
content: equality after both endpoint frames are renamed into the common
semantic namespace.  Coverage is discharged by the typed finite carriers. -/
def canonicalAtomFrameAlignmentOfCommonEquality
    {leftColor rightColor : CostStaticColor}
    {targetFree : FreeTypeContext}
    (leftNode : CostStaticRegionNode rhoCIGSLT leftColor targetFree)
    (rightNode : CostStaticRegionNode rhoCIGSLT rightColor targetFree)
    (leftValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT leftColor
      targetFree leftNode.boundaryTable)
    (rightValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT rightColor
      targetFree rightNode.boundaryTable)
    (leftInventory : CostStaticParameterInventory rhoCIGSLT leftColor
      targetFree leftNode.boundaryTable leftValues leftNode.skeleton.1)
    (rightInventory : CostStaticParameterInventory rhoCIGSLT rightColor
      targetFree rightNode.boundaryTable rightValues rightNode.skeleton.1)
    (commonFramesEq :
      let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
      let rightEnvironment :=
        CostStaticAtomEnvironment.ofInventory rightInventory
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
          (leftNode.canonicalizeReifiedTargetFrame leftEnvironment
            (costStaticReflectivePresentationDecl rhoCIGSLT leftColor
              rhoReflectivePresentation)) =
        cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
          (rightNode.canonicalizeReifiedTargetFrame rightEnvironment
            (costStaticReflectivePresentationDecl rhoCIGSLT rightColor
              rhoReflectivePresentation))) :
    CostStaticCanonicalAtomFrameAlignment
      (CostStaticAtomEnvironment.ofInventory leftInventory)
      (CostStaticAtomEnvironment.ofInventory rightInventory)
      (leftNode.canonicalizeReifiedTargetFrame
        (CostStaticAtomEnvironment.ofInventory leftInventory)
        (costStaticReflectivePresentationDecl rhoCIGSLT leftColor
          rhoReflectivePresentation))
      (rightNode.canonicalizeReifiedTargetFrame
        (CostStaticAtomEnvironment.ofInventory rightInventory)
        (costStaticReflectivePresentationDecl rhoCIGSLT rightColor
          rhoReflectivePresentation)) where
  cospan :=
    (CostStaticAtomEnvironment.ofInventory leftInventory).semanticKeyCospan
      (CostStaticAtomEnvironment.ofInventory rightInventory)
  leftCovered := by
    intro name membership
    exact canonicalizeReifiedTargetFrame_atomCovered leftNode leftValues
      leftInventory name membership
  rightCovered := by
    intro name membership
    exact canonicalizeReifiedTargetFrame_atomCovered rightNode rightValues
      rightInventory name membership
  reifiedFrames_eq := commonFramesEq

/-- Build a canonical atom-frame alignment whose common semantic apex agrees
after restoration.  This is the appropriate boundary when distinct typed atom
identities have the same compact value: the complete cospan remains in the
certificate, while exact equality is required only of the restored meaning. -/
def canonicalAtomRestorationAlignmentOfCommonEquality
    {leftColor rightColor : CostStaticColor}
    {targetFree : FreeTypeContext}
    (leftNode : CostStaticRegionNode rhoCIGSLT leftColor targetFree)
    (rightNode : CostStaticRegionNode rhoCIGSLT rightColor targetFree)
    (leftValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT leftColor
      targetFree leftNode.boundaryTable)
    (rightValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT rightColor
      targetFree rightNode.boundaryTable)
    (leftInventory : CostStaticParameterInventory rhoCIGSLT leftColor
      targetFree leftNode.boundaryTable leftValues leftNode.skeleton.1)
    (rightInventory : CostStaticParameterInventory rhoCIGSLT rightColor
      targetFree rightNode.boundaryTable rightValues rightNode.skeleton.1)
    (availableDepth : Nat)
    (commonRestorationsEq :
      let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
      let rightEnvironment :=
        CostStaticAtomEnvironment.ofInventory rightInventory
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      ReflectiveContextSupport.substituteAt
          rhoCIGSLT.costWholeReflectionProfile
          cospan.commonSupport cospan.commonAssignment availableDepth
          (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
            (leftNode.canonicalizeReifiedTargetFrame leftEnvironment
              (costStaticReflectivePresentationDecl rhoCIGSLT leftColor
                rhoReflectivePresentation))) =
        ReflectiveContextSupport.substituteAt
          rhoCIGSLT.costWholeReflectionProfile
          cospan.commonSupport cospan.commonAssignment availableDepth
          (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
            (rightNode.canonicalizeReifiedTargetFrame rightEnvironment
              (costStaticReflectivePresentationDecl rhoCIGSLT rightColor
                rhoReflectivePresentation)))) :
    CostStaticCanonicalAtomRestorationAlignment
      (CostStaticAtomEnvironment.ofInventory leftInventory)
      (CostStaticAtomEnvironment.ofInventory rightInventory)
      availableDepth
      (leftNode.canonicalizeReifiedTargetFrame
        (CostStaticAtomEnvironment.ofInventory leftInventory)
        (costStaticReflectivePresentationDecl rhoCIGSLT leftColor
          rhoReflectivePresentation))
      (rightNode.canonicalizeReifiedTargetFrame
        (CostStaticAtomEnvironment.ofInventory rightInventory)
        (costStaticReflectivePresentationDecl rhoCIGSLT rightColor
          rhoReflectivePresentation)) where
  cospan :=
    (CostStaticAtomEnvironment.ofInventory leftInventory).semanticKeyCospan
      (CostStaticAtomEnvironment.ofInventory rightInventory)
  leftCovered := by
    intro name membership
    exact canonicalizeReifiedTargetFrame_atomCovered leftNode leftValues
      leftInventory name membership
  rightCovered := by
    intro name membership
    exact canonicalizeReifiedTargetFrame_atomCovered rightNode rightValues
      rightInventory name membership
  commonRestorations_eq := commonRestorationsEq

/-- Typed hereditary normalization of one rho static frame for one explicit
finite semantic inventory.  Restoration is the established supported-open
substitution, so all open-term invariants are transported by one operation. -/
def normalizeHereditaryWithInventory
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable)
    (inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1) :
    ReflectiveWellSorted.OpenTerm rhoCIGSLT.costWholeReflectionProfile
      rhoCIGSLT.costWholeLanguage targetFree node.targetBound
      (color.mapLangSort rhoCIGSLT node.sourceSort) :=
  let environment := CostStaticAtomEnvironment.ofInventory inventory
  ReflectiveWellSorted.OpenTerm.substituteReflectiveSupported
    (canonicalizeReifiedTargetFrame_openTerm node values inventory)
      environment.restorationSupportedOpenAssignment
      (canonicalizeReifiedTargetFrame_openTerm_supportSafe node values
        inventory)

@[simp]
theorem normalizeHereditaryWithInventory_pattern
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable)
    (inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1) :
    (normalizeHereditaryWithInventory node values inventory).1 =
      node.normalizeHereditaryRawWithInventory values inventory
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) := by
  rfl

/-- Canonical atom-frame alignment is exactly the local proof obligation for
equality of two rho hereditary static evaluations.  Both evaluators already
factor definitionally through their selected canonical frame; this theorem
records that factorization without exposing either boundary-table index. -/
def normalizeHereditaryWithInventoryEvaluationBridge
    {leftColor rightColor : CostStaticColor}
    {targetFree : FreeTypeContext}
    (leftNode : CostStaticRegionNode rhoCIGSLT leftColor targetFree)
    (rightNode : CostStaticRegionNode rhoCIGSLT rightColor targetFree)
    (leftValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT leftColor
      targetFree leftNode.boundaryTable)
    (rightValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT rightColor
      targetFree rightNode.boundaryTable)
    (leftInventory : CostStaticParameterInventory rhoCIGSLT leftColor
      targetFree leftNode.boundaryTable leftValues leftNode.skeleton.1)
    (rightInventory : CostStaticParameterInventory rhoCIGSLT rightColor
      targetFree rightNode.boundaryTable rightValues rightNode.skeleton.1)
    (sameDepth : leftNode.targetBound.length = rightNode.targetBound.length)
    (alignment : CostStaticCanonicalAtomFrameAlignment
      (CostStaticAtomEnvironment.ofInventory leftInventory)
      (CostStaticAtomEnvironment.ofInventory rightInventory)
      (leftNode.canonicalizeReifiedTargetFrame
        (CostStaticAtomEnvironment.ofInventory leftInventory)
        (costStaticReflectivePresentationDecl rhoCIGSLT leftColor
          rhoReflectivePresentation))
      (rightNode.canonicalizeReifiedTargetFrame
        (CostStaticAtomEnvironment.ofInventory rightInventory)
        (costStaticReflectivePresentationDecl rhoCIGSLT rightColor
          rhoReflectivePresentation))) :
    CostStaticCanonicalAtomEvaluationBridge alignment
      leftNode.targetBound.length
      (normalizeHereditaryWithInventory leftNode leftValues leftInventory).1
      (normalizeHereditaryWithInventory rightNode rightValues
        rightInventory).1 where
  leftFactors := by
    rfl
  rightFactors := by
    rw [sameDepth]
    rfl

/-- Hide only the dependent endpoint indices of the canonical-frame bridge,
retaining both finite inventories for the enclosing root classifier. -/
def normalizeHereditaryWithInventoryPackedEvaluationBridge
    {leftColor rightColor : CostStaticColor}
    {targetFree : FreeTypeContext}
    (leftNode : CostStaticRegionNode rhoCIGSLT leftColor targetFree)
    (rightNode : CostStaticRegionNode rhoCIGSLT rightColor targetFree)
    (leftValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT leftColor
      targetFree leftNode.boundaryTable)
    (rightValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT rightColor
      targetFree rightNode.boundaryTable)
    (leftInventory : CostStaticParameterInventory rhoCIGSLT leftColor
      targetFree leftNode.boundaryTable leftValues leftNode.skeleton.1)
    (rightInventory : CostStaticParameterInventory rhoCIGSLT rightColor
      targetFree rightNode.boundaryTable rightValues rightNode.skeleton.1)
    (sameDepth : leftNode.targetBound.length = rightNode.targetBound.length)
    (alignment : CostStaticCanonicalAtomFrameAlignment
      (CostStaticAtomEnvironment.ofInventory leftInventory)
      (CostStaticAtomEnvironment.ofInventory rightInventory)
      (leftNode.canonicalizeReifiedTargetFrame
        (CostStaticAtomEnvironment.ofInventory leftInventory)
        (costStaticReflectivePresentationDecl rhoCIGSLT leftColor
          rhoReflectivePresentation))
      (rightNode.canonicalizeReifiedTargetFrame
        (CostStaticAtomEnvironment.ofInventory rightInventory)
        (costStaticReflectivePresentationDecl rhoCIGSLT rightColor
          rhoReflectivePresentation))) :
    PackedCostStaticCanonicalAtomEvaluationBridge rhoCIGSLT
      (normalizeHereditaryWithInventory leftNode leftValues leftInventory).1
      (normalizeHereditaryWithInventory rightNode rightValues
        rightInventory).1 :=
  PackedCostStaticCanonicalAtomEvaluationBridge.ofBridge
    (normalizeHereditaryWithInventoryEvaluationBridge leftNode rightNode
      leftValues rightValues leftInventory rightInventory sameDepth alignment)

/-- The complete local bridge reduces to one common-namespace equality of
the selected canonical atom frames.  All typing, finite coverage, endpoint
restoration, and dependent packaging are supplied by the established
carriers. -/
def normalizeHereditaryWithInventoryPackedBridgeOfCommonEquality
    {leftColor rightColor : CostStaticColor}
    {targetFree : FreeTypeContext}
    (leftNode : CostStaticRegionNode rhoCIGSLT leftColor targetFree)
    (rightNode : CostStaticRegionNode rhoCIGSLT rightColor targetFree)
    (leftValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT leftColor
      targetFree leftNode.boundaryTable)
    (rightValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT rightColor
      targetFree rightNode.boundaryTable)
    (leftInventory : CostStaticParameterInventory rhoCIGSLT leftColor
      targetFree leftNode.boundaryTable leftValues leftNode.skeleton.1)
    (rightInventory : CostStaticParameterInventory rhoCIGSLT rightColor
      targetFree rightNode.boundaryTable rightValues rightNode.skeleton.1)
    (sameDepth : leftNode.targetBound.length = rightNode.targetBound.length)
    (commonFramesEq :
      let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
      let rightEnvironment :=
        CostStaticAtomEnvironment.ofInventory rightInventory
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
          (leftNode.canonicalizeReifiedTargetFrame leftEnvironment
            (costStaticReflectivePresentationDecl rhoCIGSLT leftColor
              rhoReflectivePresentation)) =
        cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
          (rightNode.canonicalizeReifiedTargetFrame rightEnvironment
            (costStaticReflectivePresentationDecl rhoCIGSLT rightColor
              rhoReflectivePresentation))) :
    PackedCostStaticCanonicalAtomEvaluationBridge rhoCIGSLT
      (normalizeHereditaryWithInventory leftNode leftValues leftInventory).1
      (normalizeHereditaryWithInventory rightNode rightValues
        rightInventory).1 :=
  normalizeHereditaryWithInventoryPackedEvaluationBridge leftNode rightNode
    leftValues rightValues leftInventory rightInventory sameDepth
    (canonicalAtomFrameAlignmentOfCommonEquality leftNode rightNode leftValues
      rightValues leftInventory rightInventory commonFramesEq)

/-- The local rho evaluator factors through a common-restoration atom cospan.
Unlike the stronger frame bridge, this permits distinct proof-relevant atoms
whose restored compact values coincide. -/
def normalizeHereditaryWithInventoryRestorationEvaluationBridge
    {leftColor rightColor : CostStaticColor}
    {targetFree : FreeTypeContext}
    (leftNode : CostStaticRegionNode rhoCIGSLT leftColor targetFree)
    (rightNode : CostStaticRegionNode rhoCIGSLT rightColor targetFree)
    (leftValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT leftColor
      targetFree leftNode.boundaryTable)
    (rightValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT rightColor
      targetFree rightNode.boundaryTable)
    (leftInventory : CostStaticParameterInventory rhoCIGSLT leftColor
      targetFree leftNode.boundaryTable leftValues leftNode.skeleton.1)
    (rightInventory : CostStaticParameterInventory rhoCIGSLT rightColor
      targetFree rightNode.boundaryTable rightValues rightNode.skeleton.1)
    (sameDepth : leftNode.targetBound.length = rightNode.targetBound.length)
    (alignment : CostStaticCanonicalAtomRestorationAlignment
      (CostStaticAtomEnvironment.ofInventory leftInventory)
      (CostStaticAtomEnvironment.ofInventory rightInventory)
      leftNode.targetBound.length
      (leftNode.canonicalizeReifiedTargetFrame
        (CostStaticAtomEnvironment.ofInventory leftInventory)
        (costStaticReflectivePresentationDecl rhoCIGSLT leftColor
          rhoReflectivePresentation))
      (rightNode.canonicalizeReifiedTargetFrame
        (CostStaticAtomEnvironment.ofInventory rightInventory)
        (costStaticReflectivePresentationDecl rhoCIGSLT rightColor
          rhoReflectivePresentation))) :
    CostStaticCanonicalAtomRestorationEvaluationBridge alignment
      (normalizeHereditaryWithInventory leftNode leftValues leftInventory).1
      (normalizeHereditaryWithInventory rightNode rightValues
        rightInventory).1 where
  leftFactors := by
    rfl
  rightFactors := by
    rw [sameDepth]
    rfl

/-- Hide only the dependent endpoint indices of the common-restoration
bridge, retaining both finite inventories for the enclosing root classifier. -/
def normalizeHereditaryWithInventoryPackedRestorationEvaluationBridge
    {leftColor rightColor : CostStaticColor}
    {targetFree : FreeTypeContext}
    (leftNode : CostStaticRegionNode rhoCIGSLT leftColor targetFree)
    (rightNode : CostStaticRegionNode rhoCIGSLT rightColor targetFree)
    (leftValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT leftColor
      targetFree leftNode.boundaryTable)
    (rightValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT rightColor
      targetFree rightNode.boundaryTable)
    (leftInventory : CostStaticParameterInventory rhoCIGSLT leftColor
      targetFree leftNode.boundaryTable leftValues leftNode.skeleton.1)
    (rightInventory : CostStaticParameterInventory rhoCIGSLT rightColor
      targetFree rightNode.boundaryTable rightValues rightNode.skeleton.1)
    (sameDepth : leftNode.targetBound.length = rightNode.targetBound.length)
    (alignment : CostStaticCanonicalAtomRestorationAlignment
      (CostStaticAtomEnvironment.ofInventory leftInventory)
      (CostStaticAtomEnvironment.ofInventory rightInventory)
      leftNode.targetBound.length
      (leftNode.canonicalizeReifiedTargetFrame
        (CostStaticAtomEnvironment.ofInventory leftInventory)
        (costStaticReflectivePresentationDecl rhoCIGSLT leftColor
          rhoReflectivePresentation))
      (rightNode.canonicalizeReifiedTargetFrame
        (CostStaticAtomEnvironment.ofInventory rightInventory)
        (costStaticReflectivePresentationDecl rhoCIGSLT rightColor
          rhoReflectivePresentation))) :
    PackedCostStaticCanonicalAtomRestorationEvaluationBridge rhoCIGSLT
      (normalizeHereditaryWithInventory leftNode leftValues leftInventory).1
      (normalizeHereditaryWithInventory rightNode rightValues
        rightInventory).1 :=
  PackedCostStaticCanonicalAtomRestorationEvaluationBridge.ofBridge
    (normalizeHereditaryWithInventoryRestorationEvaluationBridge leftNode
      rightNode leftValues rightValues leftInventory rightInventory sameDepth
      alignment)

/-- The complete restoration-level bridge reduces to one exact equality at
the independently constructed common semantic apex. -/
def normalizeHereditaryWithInventoryPackedRestorationBridgeOfCommonEquality
    {leftColor rightColor : CostStaticColor}
    {targetFree : FreeTypeContext}
    (leftNode : CostStaticRegionNode rhoCIGSLT leftColor targetFree)
    (rightNode : CostStaticRegionNode rhoCIGSLT rightColor targetFree)
    (leftValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT leftColor
      targetFree leftNode.boundaryTable)
    (rightValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT rightColor
      targetFree rightNode.boundaryTable)
    (leftInventory : CostStaticParameterInventory rhoCIGSLT leftColor
      targetFree leftNode.boundaryTable leftValues leftNode.skeleton.1)
    (rightInventory : CostStaticParameterInventory rhoCIGSLT rightColor
      targetFree rightNode.boundaryTable rightValues rightNode.skeleton.1)
    (sameDepth : leftNode.targetBound.length = rightNode.targetBound.length)
    (commonRestorationsEq :
      let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
      let rightEnvironment :=
        CostStaticAtomEnvironment.ofInventory rightInventory
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      ReflectiveContextSupport.substituteAt
          rhoCIGSLT.costWholeReflectionProfile
          cospan.commonSupport cospan.commonAssignment
          leftNode.targetBound.length
          (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
            (leftNode.canonicalizeReifiedTargetFrame leftEnvironment
              (costStaticReflectivePresentationDecl rhoCIGSLT leftColor
                rhoReflectivePresentation))) =
        ReflectiveContextSupport.substituteAt
          rhoCIGSLT.costWholeReflectionProfile
          cospan.commonSupport cospan.commonAssignment
          leftNode.targetBound.length
          (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
            (rightNode.canonicalizeReifiedTargetFrame rightEnvironment
              (costStaticReflectivePresentationDecl rhoCIGSLT rightColor
                rhoReflectivePresentation)))) :
    PackedCostStaticCanonicalAtomRestorationEvaluationBridge rhoCIGSLT
      (normalizeHereditaryWithInventory leftNode leftValues leftInventory).1
      (normalizeHereditaryWithInventory rightNode rightValues
        rightInventory).1 :=
  normalizeHereditaryWithInventoryPackedRestorationEvaluationBridge leftNode
    rightNode leftValues rightValues leftInventory rightInventory sameDepth
    (canonicalAtomRestorationAlignmentOfCommonEquality leftNode rightNode
      leftValues rightValues leftInventory rightInventory
      leftNode.targetBound.length commonRestorationsEq)

/-- Total typed hereditary normalization of one admitted rho static node.
The finite environment builder is executed once and cannot fail on the
node's proof-relevant authored skeleton. -/
def normalizeHereditary
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable) :
    ReflectiveWellSorted.OpenTerm rhoCIGSLT.costWholeReflectionProfile
      rhoCIGSLT.costWholeLanguage targetFree node.targetBound
      (color.mapLangSort rhoCIGSLT node.sourceSort) :=
  let packed := node.semanticAtomEnvironment values
  normalizeHereditaryWithInventory node values packed.1

/-- The semantic-key representative of one atomized rho frame, retained in
the exact constructor and reflective-support fibre consumed by the generic
same-colour Cost action. -/
def semanticCanonicalizedSourceTerm
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory) :
    CostStaticSourceTerm rhoCIGSLT color environment.sourceAtomFreeContext
      environment.sourceAtomSupport node.sourceBound node.targetBound
      node.sourceSort := by
  let sourceKey := sourceSemanticPatternKeyAt node environment
  let sourceFrame := node.reifiedSourceFrame environment
  let sourceSupported := node.reifiedSourceFrame_supported environment
  have sourceSafe : sourceSupported.toHasType.ReflectiveSupportSafeAt
      rhoReflectionProfile environment.sourceAtomSupport node.targetBound
      (mapTypeExpr (color.symbols rhoCIGSLT)) :=
    (node.reifiedSourceFrame_supportSafe environment).castTyping
  let normalizedEvidence :=
    rhoCanonicalizeByDepths_hasTypeWithConstructors sourceKey 0
      sourceSupported sourceSafe (by trivial) sourceFrame.2.1.2.2.1
  let normalizedSupported := Classical.choose normalizedEvidence
  let normalizedSafe := Classical.choose_spec normalizedEvidence
  let normalizedPattern := canonicalizeByDepths sourceKey
    rhoReflectivePresentation node.targetBound.length 0 sourceFrame.1
  have normalizedCanonical : normalizedPattern.hasCanonicalBinderMetadata =
      true := by
    exact canonicalizeByDepths_hasCanonicalBinderMetadata sourceKey
      rhoReflectivePresentation node.targetBound.length 0 sourceFrame.1
        sourceFrame.2.1.2.1
  have normalizedObject : isObjectPattern normalizedPattern = true := by
    exact canonicalizeByDepths_isObjectPattern sourceKey
      rhoReflectivePresentation node.targetBound.length 0 sourceFrame.1
        sourceFrame.2.1.2.2.1
  have normalizedScope : ReflectiveWellSorted.ReflectiveScopeSafeAt
      rhoCIGSLT.reflection.1 node.sourceBound.length normalizedPattern := by
    intro declaration membership
    exact canonicalizeByDepths_binderSafeAt sourceKey
      rhoReflectivePresentation declaration.quoteConstructor
      node.targetBound.length 0 node.sourceBound.length sourceFrame.1
        (sourceFrame.2.2 declaration membership)
  let normalizedTerm : ReflectiveWellSorted.OpenTerm rhoCIGSLT.reflection.1
      rhoCalc environment.sourceAtomFreeContext node.sourceBound
      node.sourceSort :=
    ⟨normalizedPattern,
      ⟨normalizedSupported.toHasType, normalizedCanonical,
        normalizedObject, normalizedSupported.toHasType.isWellScopedAt⟩,
      normalizedScope⟩
  exact
    { term := normalizedTerm
      supported := normalizedSupported
      safe := normalizedSafe }

@[simp]
theorem semanticCanonicalizedSourceTerm_pattern
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory) :
    (semanticCanonicalizedSourceTerm node environment).term.1 =
      canonicalizeByDepths (sourceSemanticPatternKeyAt node environment)
        rhoReflectivePresentation node.targetBound.length 0
        (node.reifiedSourceFrame environment).1 := by
  rfl

/-- Keyed rho canonicalization is one source-authored reflective edge in the
exact atomized static fibre.  The ordinary rho canonical form absorbs the
semantic ordering key, so no generated target equation is postulated. -/
theorem semanticCanonicalizedSourceTerm_equationSetoid
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory) :
    (CostStaticSourceTerm.equationSetoid rhoCIGSLT color
      environment.sourceAtomFreeContext environment.sourceAtomSupport
      node.sourceBound node.targetBound node.sourceSort).r
        (semanticCanonicalizedSourceTerm node environment)
        (node.reifiedSourceTerm environment) := by
  apply Relation.EqvGen.rel _ _
  unfold CostStaticSourceTerm.generator
  apply
    ReflectiveEquationSemantics.ReflectiveEquationContextStep.reflectiveInContext
      .hole (declaration := rhoReflectivePresentation.toReflectivePresentationDecl)
  · change List.Mem rhoReflectivePresentation.toReflectivePresentationDecl
      [rhoReflectivePresentation.toReflectivePresentationDecl]
    exact .head _
  · change canonicalize rhoReflectivePresentation
        (canonicalizeByDepths
          (sourceSemanticPatternKeyAt node environment)
          rhoReflectivePresentation node.targetBound.length 0
          (node.reifiedSourceFrame environment).1) =
      canonicalize rhoReflectivePresentation
        (node.reifiedSourceFrame environment).1
    exact canonicalize_canonicalizeByDepths
      (sourceSemanticPatternKeyAt node environment) rhoReflectivePresentation
      (by decide) node.targetBound.length 0
        (node.reifiedSourceFrame environment).1

/-- The source-rho action of the semantic-key representative remains in the
same generated authored-equation class as the unnormalized semantic-atom
frame.  This deliberately uses rho's source-typed action theorem rather than
assuming substitution stability for arbitrary generated Cost languages. -/
theorem sourceSemanticCanonicalize_action_equationEquiv
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    (typeMap : ∀ slot,
      mapTypeExpr (color.symbols rhoCIGSLT)
          (environment.atomValue slot).key.sourceType =
        (environment.atomValue slot).key.targetType) :
    ReflectiveEquationSemantics.ReflectiveEquationEquiv
      rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
      rhoCIGSLT.costWholeLanguage
      (rhoCostStaticActionAt node.thinning
        environment.restorationSupportedOpenAssignment [] node.targetBound
        (canonicalizeByDepths (sourceSemanticPatternKeyAt node environment)
          rhoReflectivePresentation node.targetBound.length 0
          (node.reifiedSourceFrame environment).1))
      (rhoCostStaticActionAt node.thinning
        environment.restorationSupportedOpenAssignment [] node.targetBound
        (node.reifiedSourceFrame environment).1) := by
  let sourceKey := sourceSemanticPatternKeyAt node environment
  let sourceFrame := node.reifiedSourceFrame environment
  have sourceSupported := node.reifiedSourceFrame_supported environment
  have sourceSafe : sourceSupported.toHasType.ReflectiveSupportSafeAt
      rhoReflectionProfile environment.sourceAtomSupport node.targetBound
      (mapTypeExpr (color.symbols rhoCIGSLT)) :=
    (node.reifiedSourceFrame_supportSafe environment).castTyping
  obtain ⟨normalizedSupported, normalizedSafe⟩ :=
    rhoCanonicalizeByDepths_hasTypeWithConstructors sourceKey 0
      sourceSupported sourceSafe (by trivial) sourceFrame.2.1.2.2.1
  have normalizedObject :
      isObjectPattern
          (canonicalizeByDepths sourceKey rhoReflectivePresentation
            node.targetBound.length 0 sourceFrame.1) = true :=
    canonicalizeByDepths_isObjectPattern sourceKey rhoReflectivePresentation
      node.targetBound.length 0 sourceFrame.1 sourceFrame.2.1.2.2.1
  have contextEquality :
      environment.sourceAtomFreeContext.map (color.symbols rhoCIGSLT) =
        environment.atomFreeContext :=
    environment.sourceAtomFreeContext_map_eq_atomFreeContext typeMap
  have normalizedStep :=
    rhoCostStaticActionAt_canonicalize_equationEquiv
      (inner := []) (available := node.targetBound) node.thinning
      environment.restorationSupportedOpenAssignment contextEquality
      environment.sourceAtomSupport_eq_restorationSupport
      normalizedSupported.toHasType normalizedSafe
      normalizedSupported.constructorsWithin normalizedObject
  have sourceStep :=
    rhoCostStaticActionAt_canonicalize_equationEquiv
      (inner := []) (available := node.targetBound) node.thinning
      environment.restorationSupportedOpenAssignment contextEquality
      environment.sourceAtomSupport_eq_restorationSupport
      sourceSupported.toHasType sourceSafe sourceSupported.constructorsWithin
      sourceFrame.2.1.2.2.1
  have absorption :
      canonicalize rhoReflectivePresentation
          (canonicalizeByDepths sourceKey rhoReflectivePresentation
            node.targetBound.length 0 sourceFrame.1) =
        canonicalize rhoReflectivePresentation sourceFrame.1 :=
    canonicalize_canonicalizeByDepths sourceKey rhoReflectivePresentation
      (by decide) node.targetBound.length 0 sourceFrame.1
  rw [absorption] at normalizedStep
  exact Relation.EqvGen.trans _ _ _ normalizedStep
    (Relation.EqvGen.symm _ _ sourceStep)

/-- The executable hereditary target frame is definitionally the restored
rho static action of the semantic-key source representative. -/
theorem normalizeHereditaryRawWithInventory_eq_sourceAction
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable)
    (inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1) :
    node.normalizeHereditaryRawWithInventory values inventory
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) =
      rhoCostStaticActionAt node.thinning
        (CostStaticAtomEnvironment.ofInventory inventory
          ).restorationSupportedOpenAssignment [] node.targetBound
        (canonicalizeByDepths
          (sourceSemanticPatternKeyAt node
            (CostStaticAtomEnvironment.ofInventory inventory))
          rhoReflectivePresentation node.targetBound.length 0
          (node.reifiedSourceFrame
            (CostStaticAtomEnvironment.ofInventory inventory)).1) := by
  let environment := CostStaticAtomEnvironment.ofInventory inventory
  change environment.restore node.targetBound
      (node.canonicalizeReifiedTargetFrame environment
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation)) = _
  rw [canonicalizeReifiedTargetFrame_eq_map_sourceCanonicalize node
    environment]
  rfl

/-- A selected rho frame consisting of one `NQuote (PDrop atom)` shell
evaluates to restoration of that atom at the frame's exact target binder
depth.  This is the open form of the hereditary Quote/Drop root bridge. -/
theorem normalizeHereditaryRawWithInventory_quoteDrop_restore
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable)
    (inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1)
    (slot : Fin (CostStaticAtomEnvironment.ofInventory inventory).atomCount)
    (reifiedFrame : (node.reifiedSourceFrame
        (CostStaticAtomEnvironment.ofInventory inventory)).1 =
      .apply rhoReflectivePresentation.quoteConstructor
        [.apply rhoReflectivePresentation.dropConstructor
          [.fvar ((CostStaticAtomEnvironment.ofInventory inventory
            ).atomName slot)]]) :
    node.normalizeHereditaryRawWithInventory values inventory
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) =
      (CostStaticAtomEnvironment.ofInventory inventory).restore
        node.targetBound
        (.fvar ((CostStaticAtomEnvironment.ofInventory inventory
          ).atomName slot)) := by
  let environment := CostStaticAtomEnvironment.ofInventory inventory
  rw [normalizeHereditaryRawWithInventory_eq_sourceAction node values
    inventory, reifiedFrame]
  unfold rhoCostStaticActionAt
  rw [canonicalizeByDepths_quote_drop _ rhoReflectivePresentation (by decide)]
  simp only [canonicalizeByDepths, mapPattern,
    CostStaticBinderThinning.thickenAmbientBVars]
  rfl

/-- Total-inventory form of the open hereditary Quote/Drop root bridge.  The
semantic inventory is the one constructed from the node's certified finite
boundary table, so callers need not choose a second occurrence authority. -/
theorem normalizeHereditary_quoteDrop_restore
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable)
    (slot : Fin (CostStaticAtomEnvironment.ofInventory
      (node.semanticAtomEnvironment values).1).atomCount)
    (reifiedFrame : (node.reifiedSourceFrame
        (CostStaticAtomEnvironment.ofInventory
          (node.semanticAtomEnvironment values).1)).1 =
      .apply rhoReflectivePresentation.quoteConstructor
        [.apply rhoReflectivePresentation.dropConstructor
          [.fvar ((CostStaticAtomEnvironment.ofInventory
            (node.semanticAtomEnvironment values).1).atomName slot)]]) :
    (normalizeHereditary node values).1 =
      (CostStaticAtomEnvironment.ofInventory
        (node.semanticAtomEnvironment values).1).restore node.targetBound
          (.fvar ((CostStaticAtomEnvironment.ofInventory
            (node.semanticAtomEnvironment values).1).atomName slot)) := by
  unfold normalizeHereditary
  rw [normalizeHereditaryWithInventory_pattern]
  exact normalizeHereditaryRawWithInventory_quoteDrop_restore node values
    (node.semanticAtomEnvironment values).1 slot reifiedFrame

/-- A selected rho Quote/Drop frame and any classified positional parameter
meet at one retained semantic atom.  The parameter may be either an authored
source variable or a recursively normalized opposite-colour boundary; its
proof-relevant classification remains in the finite inventory while the
selected canonicalizer observes only the complete typed semantic value. -/
def quoteDropParameterSemanticAtomJoinWithInventory
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable)
    (inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1)
    (parameter : CostStaticParameterOccurrence rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1)
    (slot : Fin (CostStaticAtomEnvironment.ofInventory inventory).atomCount)
    (selected : (CostStaticAtomEnvironment.ofInventory inventory).slotOfName?
      parameter.fvarOccurrence.name = some slot)
    (reifiedFrame : (node.reifiedSourceFrame
        (CostStaticAtomEnvironment.ofInventory inventory)).1 =
      .apply rhoReflectivePresentation.quoteConstructor
        [.apply rhoReflectivePresentation.dropConstructor
          [.fvar ((CostStaticAtomEnvironment.ofInventory inventory
            ).atomName slot)]]) :
    PackedCostSemanticAtomJoin rhoCIGSLT
      (normalizeHereditaryWithInventory node values inventory).1
      (ReflectiveContextSupport.substituteAt
        rhoCIGSLT.costWholeReflectionProfile
        node.boundaryTable.restorationSupport (values.assignment
          node.boundaryTable) node.targetBound.length
        (.fvar parameter.fvarOccurrence.name)) where
  color := color
  targetFree := targetFree
  occurrences := node.plan.occurrences
  table := node.boundaryTable
  values := values
  root := node.skeleton.1
  inventory := inventory
  environment := CostStaticAtomEnvironment.ofInventory inventory
  bound := node.targetBound
  slot := slot
  leftFactors := by
    rw [normalizeHereditaryWithInventory_pattern]
    exact normalizeHereditaryRawWithInventory_quoteDrop_restore node values
      inventory slot reifiedFrame
  rightFactors := by
    exact ((CostStaticAtomEnvironment.ofInventory inventory
      ).substituteAt_atomName_eq_substituteAt_occurrence
        parameter.fvarOccurrence slot selected node.targetBound.length).symm

/-- A selected rho Quote/Drop frame and the structural source variable it
reveals meet at one retained semantic atom.  This is the one-sided
static-to-structural root cell: a bare free variable is structural syntax,
not a static region root. -/
def quoteDropSourceVariableSemanticAtomJoinWithInventory
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable)
    (inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1)
    (occurrence : CostStaticFVarOccurrence node.skeleton.1)
    (name : String)
    (occurrenceName : occurrence.name = costRegionSourceVariableName name)
    (slot : Fin (CostStaticAtomEnvironment.ofInventory inventory).atomCount)
    (selected : (CostStaticAtomEnvironment.ofInventory inventory).slotOfName?
      occurrence.name = some slot)
    (reifiedFrame : (node.reifiedSourceFrame
        (CostStaticAtomEnvironment.ofInventory inventory)).1 =
      .apply rhoReflectivePresentation.quoteConstructor
        [.apply rhoReflectivePresentation.dropConstructor
          [.fvar ((CostStaticAtomEnvironment.ofInventory inventory
            ).atomName slot)]]) :
    PackedCostSemanticAtomJoin rhoCIGSLT
      (normalizeHereditaryWithInventory node values inventory).1
      (.fvar name) where
  color := color
  targetFree := targetFree
  occurrences := node.plan.occurrences
  table := node.boundaryTable
  values := values
  root := node.skeleton.1
  inventory := inventory
  environment := CostStaticAtomEnvironment.ofInventory inventory
  bound := node.targetBound
  slot := slot
  leftFactors := by
    rw [normalizeHereditaryWithInventory_pattern]
    exact normalizeHereditaryRawWithInventory_quoteDrop_restore node values
      inventory slot reifiedFrame
  rightFactors := by
    unfold CostStaticAtomEnvironment.restore CostStaticAtomEnvironment.restoreAt
    rw [(CostStaticAtomEnvironment.ofInventory inventory
      ).substituteAt_atomName_eq_substituteAt_occurrence occurrence slot
        selected node.targetBound.length]
    simp [occurrenceName, ReflectiveContextSupport.substituteAt,
      TypedCostRegionBoundaryTable.Values.assignment,
      Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars]

/-- Total-inventory form of the static-to-structural rho Quote/Drop cell. -/
def quoteDropSourceVariableSemanticAtomJoin
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable)
    (occurrence : CostStaticFVarOccurrence node.skeleton.1)
    (name : String)
    (occurrenceName : occurrence.name = costRegionSourceVariableName name)
    (slot : Fin (CostStaticAtomEnvironment.ofInventory
      (node.semanticAtomEnvironment values).1).atomCount)
    (selected : (CostStaticAtomEnvironment.ofInventory
      (node.semanticAtomEnvironment values).1).slotOfName? occurrence.name =
        some slot)
    (reifiedFrame : (node.reifiedSourceFrame
        (CostStaticAtomEnvironment.ofInventory
          (node.semanticAtomEnvironment values).1)).1 =
      .apply rhoReflectivePresentation.quoteConstructor
        [.apply rhoReflectivePresentation.dropConstructor
          [.fvar ((CostStaticAtomEnvironment.ofInventory
            (node.semanticAtomEnvironment values).1).atomName slot)]]) :
    PackedCostSemanticAtomJoin rhoCIGSLT
      (normalizeHereditary node values).1 (.fvar name) := by
  unfold normalizeHereditary
  exact quoteDropSourceVariableSemanticAtomJoinWithInventory node values
    (node.semanticAtomEnvironment values).1 occurrence name occurrenceName slot
      selected reifiedFrame

/-- A closed selected rho frame consisting of one `NQuote (PDrop atom)`
shell evaluates to that atom's semantic value.  The statement is independent
of how the value entered the frame: a source variable and a recursively
normalized foreign-colour boundary therefore share this exact reduction law
when their complete typed atom keys agree. -/
theorem normalizeHereditaryRawWithInventory_quoteDrop
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable)
    (inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1)
    (slot : Fin (CostStaticAtomEnvironment.ofInventory inventory).atomCount)
    (reifiedFrame : (node.reifiedSourceFrame
        (CostStaticAtomEnvironment.ofInventory inventory)).1 =
      .apply rhoReflectivePresentation.quoteConstructor
        [.apply rhoReflectivePresentation.dropConstructor
          [.fvar ((CostStaticAtomEnvironment.ofInventory inventory
            ).atomName slot)]])
    (closed : node.targetBound = []) :
    node.normalizeHereditaryRawWithInventory values inventory
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) =
      ((CostStaticAtomEnvironment.ofInventory inventory).atomValue slot
        ).key.normal := by
  let environment := CostStaticAtomEnvironment.ofInventory inventory
  rw [normalizeHereditaryRawWithInventory_quoteDrop_restore node values
    inventory slot reifiedFrame]
  unfold CostStaticAtomEnvironment.restore
  have targetDepth : node.targetBound.length = 0 := by simp [closed]
  rw [targetDepth]
  unfold CostStaticAtomEnvironment.restoreAt
  simp only [ReflectiveContextSupport.substituteAt]
  rw [(CostStaticAtomEnvironment.ofInventory inventory
    ).restorationAssignment_atomName]
  simpa using
    (Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero
      (environment.atomValue slot).key.normal 0)

/-- Before restoration, a closed wrapped frame containing two drops is
canonically ordered by the semantic values of its atoms.  The result retains
the endpoint atom names; a common semantic cospan may subsequently rename
them without consulting boundary origins. -/
theorem canonicalizeReifiedTargetFrame_wrappedParallelTwoDrops
    {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT .wrapped targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT .wrapped
      targetFree node.boundaryTable)
    (inventory : CostStaticParameterInventory rhoCIGSLT .wrapped targetFree
      node.boundaryTable values node.skeleton.1)
    (first second : Fin
      (CostStaticAtomEnvironment.ofInventory inventory).atomCount)
    (firstNormal secondNormal : Pattern)
    (reifiedFrame : (node.reifiedSourceFrame
        (CostStaticAtomEnvironment.ofInventory inventory)).1 =
      .collection .hashBag
        [.apply rhoReflectivePresentation.dropConstructor
            [.fvar ((CostStaticAtomEnvironment.ofInventory inventory
              ).atomName first)],
          .apply rhoReflectivePresentation.dropConstructor
            [.fvar ((CostStaticAtomEnvironment.ofInventory inventory
              ).atomName second)]] none)
    (firstValue : ((CostStaticAtomEnvironment.ofInventory inventory
        ).atomValue first).key.normal = firstNormal)
    (secondValue : ((CostStaticAtomEnvironment.ofInventory inventory
        ).atomValue second).key.normal = secondNormal)
    (ordered : patternCode
        (.apply (costWrappedConstructorName
          rhoReflectivePresentation.dropConstructor) [firstNormal]) ≤
      patternCode
        (.apply (costWrappedConstructorName
          rhoReflectivePresentation.dropConstructor) [secondNormal]))
    (closed : node.targetBound = []) :
    node.canonicalizeReifiedTargetFrame
        (CostStaticAtomEnvironment.ofInventory inventory)
        (costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
          rhoReflectivePresentation) =
      .collection .hashBag
        [.apply (costWrappedConstructorName
            rhoReflectivePresentation.dropConstructor)
            [.fvar ((CostStaticAtomEnvironment.ofInventory inventory
              ).atomName first)],
          .apply (costWrappedConstructorName
            rhoReflectivePresentation.dropConstructor)
            [.fvar ((CostStaticAtomEnvironment.ofInventory inventory
              ).atomName second)]] none := by
  let environment := CostStaticAtomEnvironment.ofInventory inventory
  have firstKey : sourceSemanticPatternKeyAt node environment 0 0
        (.apply rhoReflectivePresentation.dropConstructor
          [.fvar (environment.atomName first)]) =
      patternCode
        (.apply (costWrappedConstructorName
          rhoReflectivePresentation.dropConstructor) [firstNormal]) := by
    simp [sourceSemanticPatternKeyAt,
      Mettapedia.GSLT.LanguageDef.CostStaticRegionNode.semanticPatternKeyAt,
      CostStaticAtomEnvironment.restoreAt, mapPattern,
      CostStaticBinderThinning.thickenAmbientBVars_eq_self_of_targetBound_eq_nil
        node.thinning closed,
      ReflectiveContextSupport.substituteAt, costWrappedConstructorName,
      CostStaticColor.constructorTag]
    rw [Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero, firstValue]
  have secondKey : sourceSemanticPatternKeyAt node environment 0 0
        (.apply rhoReflectivePresentation.dropConstructor
          [.fvar (environment.atomName second)]) =
      patternCode
        (.apply (costWrappedConstructorName
          rhoReflectivePresentation.dropConstructor) [secondNormal]) := by
    simp [sourceSemanticPatternKeyAt,
      Mettapedia.GSLT.LanguageDef.CostStaticRegionNode.semanticPatternKeyAt,
      CostStaticAtomEnvironment.restoreAt, mapPattern,
      CostStaticBinderThinning.thickenAmbientBVars_eq_self_of_targetBound_eq_nil
        node.thinning closed,
      ReflectiveContextSupport.substituteAt, costWrappedConstructorName,
      CostStaticColor.constructorTag]
    rw [Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero, secondValue]
  have keyOrder : sourceSemanticPatternKeyAt node environment 0 0
        (.apply rhoReflectivePresentation.dropConstructor
          [.fvar (environment.atomName first)]) ≤
      sourceSemanticPatternKeyAt node environment 0 0
        (.apply rhoReflectivePresentation.dropConstructor
          [.fvar (environment.atomName second)]) := by
    simpa [firstKey, secondKey] using ordered
  have keyOrderLiteral : sourceSemanticPatternKeyAt node environment 0 0
        (.apply "PDrop" [.fvar (environment.atomName first)]) ≤
      sourceSemanticPatternKeyAt node environment 0 0
        (.apply "PDrop" [.fvar (environment.atomName second)]) := by
    simpa [rhoReflectivePresentation] using keyOrder
  have canonicalized :
      canonicalizeByDepths (sourceSemanticPatternKeyAt node environment)
          rhoReflectivePresentation 0 0
          (.collection .hashBag
            [.apply rhoReflectivePresentation.dropConstructor
                [.fvar (environment.atomName first)],
              .apply rhoReflectivePresentation.dropConstructor
                [.fvar (environment.atomName second)]] none) =
        .collection .hashBag
          [.apply rhoReflectivePresentation.dropConstructor
              [.fvar (environment.atomName first)],
            .apply rhoReflectivePresentation.dropConstructor
              [.fvar (environment.atomName second)]] none := by
    simp [canonicalizeByDepths, canonicalizeListByDepths,
      Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
      normalizeParallelElementsBy, parallelSplice, collapseParallel,
      rhoReflectivePresentation]
    rw [sortPatternsBy_pair_eq_of_le _ _ _ keyOrderLiteral]
  rw [canonicalizeReifiedTargetFrame_eq_map_sourceCanonicalize node
    environment]
  rw [CostStaticBinderThinning.thickenAmbientBVars_eq_self_of_targetBound_eq_nil
    node.thinning closed]
  have targetDepth : node.targetBound.length = 0 := by simp [closed]
  rw [targetDepth, reifiedFrame, canonicalized]
  simp [mapPattern, mapPatternList_eq_map,
    CostStaticColor.symbols_constructor, CostStaticColor.constructorTag,
    costWrappedConstructorName, rhoReflectivePresentation]
  exact ⟨rfl, rfl⟩

/-- A closed wrapped rho frame containing two drops is ordered by the
restored semantic values of its atoms, not by either atom spelling or the
serialized origin of an occurrence. -/
theorem normalizeHereditaryRawWithInventory_wrappedParallelTwoDrops
    {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT .wrapped targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT .wrapped
      targetFree node.boundaryTable)
    (inventory : CostStaticParameterInventory rhoCIGSLT .wrapped targetFree
      node.boundaryTable values node.skeleton.1)
    (first second : Fin
      (CostStaticAtomEnvironment.ofInventory inventory).atomCount)
    (firstNormal secondNormal : Pattern)
    (reifiedFrame : (node.reifiedSourceFrame
        (CostStaticAtomEnvironment.ofInventory inventory)).1 =
      .collection .hashBag
        [.apply rhoReflectivePresentation.dropConstructor
            [.fvar ((CostStaticAtomEnvironment.ofInventory inventory
              ).atomName first)],
          .apply rhoReflectivePresentation.dropConstructor
            [.fvar ((CostStaticAtomEnvironment.ofInventory inventory
              ).atomName second)]] none)
    (firstValue : ((CostStaticAtomEnvironment.ofInventory inventory
        ).atomValue first).key.normal = firstNormal)
    (secondValue : ((CostStaticAtomEnvironment.ofInventory inventory
        ).atomValue second).key.normal = secondNormal)
    (ordered : patternCode
        (.apply (costWrappedConstructorName
          rhoReflectivePresentation.dropConstructor) [firstNormal]) ≤
      patternCode
        (.apply (costWrappedConstructorName
          rhoReflectivePresentation.dropConstructor) [secondNormal]))
    (closed : node.targetBound = []) :
    node.normalizeHereditaryRawWithInventory values inventory
        (costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
          rhoReflectivePresentation) =
      .collection .hashBag
        [.apply (costWrappedConstructorName
            rhoReflectivePresentation.dropConstructor) [firstNormal],
          .apply (costWrappedConstructorName
            rhoReflectivePresentation.dropConstructor) [secondNormal]] none := by
  unfold Mettapedia.GSLT.LanguageDef.CostStaticRegionNode.normalizeHereditaryRawWithInventory
  change (CostStaticAtomEnvironment.ofInventory inventory).restore
      node.targetBound
      (node.canonicalizeReifiedTargetFrame
        (CostStaticAtomEnvironment.ofInventory inventory)
        (costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
          rhoReflectivePresentation)) = _
  rw [canonicalizeReifiedTargetFrame_wrappedParallelTwoDrops node values
    inventory first second firstNormal secondNormal reifiedFrame firstValue
    secondValue ordered closed]
  unfold CostStaticAtomEnvironment.restore
  have targetDepth : node.targetBound.length = 0 := by simp [closed]
  rw [targetDepth]
  simp [CostStaticAtomEnvironment.restoreAt,
    ReflectiveContextSupport.substituteAt,
    costWrappedConstructorName, rhoReflectivePresentation,
    (CostStaticAtomEnvironment.ofInventory inventory
      ).restorationAssignment_atomName,
    Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero]
  exact ⟨firstValue, secondValue⟩

/-- The unnormalized source action restores exactly the original mapped frame
with the selected finite child values. -/
theorem sourceAction_eq_restoreSupportedSkeleton
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable)
    (inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1) :
    rhoCostStaticActionAt node.thinning
        (CostStaticAtomEnvironment.ofInventory inventory
          ).restorationSupportedOpenAssignment [] node.targetBound
        (node.reifiedSourceFrame
          (CostStaticAtomEnvironment.ofInventory inventory)).1 =
      values.restoreSupportedSkeleton node.boundaryTable node.targetBound
        node.mappedThickenedSkeleton.1 := by
  let environment := CostStaticAtomEnvironment.ofInventory inventory
  calc
    rhoCostStaticActionAt node.thinning
          environment.restorationSupportedOpenAssignment [] node.targetBound
          (node.reifiedSourceFrame environment).1 =
        environment.restore node.targetBound
          (node.thinning.thickenAmbientBVars 0
            (mapPattern (color.symbols rhoCIGSLT)
              (node.reifiedSourceFrame environment).1)) := by
      rfl
    _ = environment.restore node.targetBound
          (node.reifyTargetFrame environment) := by
      rw [node.reifyTargetFrame_eq_map_reifiedSourceFrame environment]
    _ = values.restoreSupportedSkeleton node.boundaryTable node.targetBound
          node.mappedThickenedSkeleton.1 :=
      node.restore_reifyTargetFrame environment

/-- Hereditary semantic-key normalization of one rho static frame is an
authored generated-equation equivalence to the same frame with the same
finite child values. -/
theorem normalizeHereditaryRawWithInventory_equationEquiv
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable)
    (inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1) :
    ReflectiveEquationSemantics.ReflectiveEquationEquiv
      rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
      rhoCIGSLT.costWholeLanguage
      (node.normalizeHereditaryRawWithInventory values inventory
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation))
      (values.restoreSupportedSkeleton node.boundaryTable node.targetBound
        node.mappedThickenedSkeleton.1) := by
  let environment := CostStaticAtomEnvironment.ofInventory inventory
  have actionStep := sourceSemanticCanonicalize_action_equationEquiv node
    environment (node.semanticAtom_typeMap values inventory)
  rw [normalizeHereditaryRawWithInventory_eq_sourceAction node values
    inventory]
  rw [← sourceAction_eq_restoreSupportedSkeleton node values inventory]
  exact actionStep

/-- The total typed rho static kernel has the same unary authored-equation
law as its explicit-inventory form. -/
theorem normalizeHereditary_equationEquiv
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable) :
    ReflectiveEquationSemantics.ReflectiveEquationEquiv
      rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
      rhoCIGSLT.costWholeLanguage
      (normalizeHereditary node values).1
      (values.restoreSupportedSkeleton node.boundaryTable node.targetBound
        node.mappedThickenedSkeleton.1) := by
  unfold normalizeHereditary
  rw [normalizeHereditaryWithInventory_pattern]
  exact normalizeHereditaryRawWithInventory_equationEquiv node values
    (node.semanticAtomEnvironment values).1

/-- The hereditary rho static normalizer remains in the exact split typing
fibre of its input.  The proof first maps the source-authored semantic-key
edge, then changes only the finite boundary assignment.  It never invokes
the false mixed-colour substitution-closure principle. -/
theorem normalizeHereditary_available_equationSetoid
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable)
    (valuesEquivalent :
      (values.supportedOpenAssignment node.boundaryTable).FiberEquivalent
        ((TypedCostRegionBoundaryTable.Values.original node.boundaryTable
          ).supportedOpenAssignment node.boundaryTable)) :
    (WellSorted.AvailableOpenPattern.equationSetoid
      (profile := rhoCIGSLT.costWholeReflectionProfile)
      rhoCIGSLT.costWholeLanguage targetFree node.targetBound []
        (.base (color.mapLangSort rhoCIGSLT node.sourceSort).1)).r
      (WellSorted.AvailableOpenPattern.ofOpenPattern
        (normalizeHereditary node values))
      node.termAvailable := by
  let inventory := (node.semanticAtomEnvironment values).1
  let environment := CostStaticAtomEnvironment.ofInventory inventory
  have typeMap : ∀ slot,
      mapTypeExpr (color.symbols rhoCIGSLT)
          (environment.atomValue slot).key.sourceType =
        (environment.atomValue slot).key.targetType :=
    node.semanticAtom_typeMap values inventory
  have contextEquality :
      environment.sourceAtomFreeContext.map (color.symbols rhoCIGSLT) =
        environment.atomFreeContext :=
    environment.sourceAtomFreeContext_map_eq_atomFreeContext typeMap
  have sourceStep := CostStaticSourceTerm.equationSetoid_actAvailable
    rho_costStaticMappedGeneratorFiberAction node.thinning
      environment.restorationSupportedOpenAssignment contextEquality
      environment.sourceAtomSupport_eq_restorationSupport
      (semanticCanonicalizedSourceTerm_equationSetoid node environment)
  let valuesAssignment := values.supportedOpenAssignment node.boundaryTable
  let originalAssignment :=
    (TypedCostRegionBoundaryTable.Values.original node.boundaryTable
      ).supportedOpenAssignment node.boundaryTable
  let mappedAvailableRaw :=
    node.sourceActionTerm.mappedThickenedAvailable node.thinning
  let mappedAvailable := mappedAvailableRaw.castFree
    node.transport.freeContext
  have mappedAvailableSafe :
      mappedAvailable.typed.ReflectiveSupportSafeAt
        rhoCIGSLT.costWholeReflectionProfile
        node.boundaryTable.restorationSupport node.targetBound :=
    mappedAvailableRaw.castFree_supportSafe node.transport.freeContext
      (node.sourceActionTerm.mappedThickenedAvailable_supportSafe
        node.thinning)
  have assignmentStep := mappedAvailable.equationSetoid_substitute_pointwise
    rhoCIGSLT.costWholeLanguage_validate
      rhoCIGSLT.costWholeReflectionProfile_validate mappedAvailableSafe
      valuesAssignment originalAssignment valuesEquivalent
  have leftEndpoint :
      (semanticCanonicalizedSourceTerm node environment).actAvailable
          node.thinning environment.restorationSupportedOpenAssignment
            contextEquality environment.sourceAtomSupport_eq_restorationSupport =
        WellSorted.AvailableOpenPattern.ofOpenPattern
          (normalizeHereditary node values) := by
    apply WellSorted.AvailableOpenPattern.ext
    rw [CostStaticSourceTerm.actAvailable_pattern,
      WellSorted.AvailableOpenPattern.ofOpenPattern_pattern]
    have hereditaryPattern : (normalizeHereditary node values).1 =
        rhoCostStaticActionAt node.thinning
          environment.restorationSupportedOpenAssignment [] node.targetBound
          (canonicalizeByDepths
            (sourceSemanticPatternKeyAt node environment)
            rhoReflectivePresentation node.targetBound.length 0
            (node.reifiedSourceFrame environment).1) := by
      unfold normalizeHereditary
      rw [normalizeHereditaryWithInventory_pattern]
      exact normalizeHereditaryRawWithInventory_eq_sourceAction node values
        inventory
    rw [hereditaryPattern]
    unfold CostStaticSourceTerm.act rhoCostStaticActionAt
      ReflectiveContextSupport.substitute
    rw [semanticCanonicalizedSourceTerm_pattern]
    simp only [List.length_nil]
  have middleEndpoint :
      (node.reifiedSourceTerm environment).actAvailable node.thinning
          environment.restorationSupportedOpenAssignment contextEquality
            environment.sourceAtomSupport_eq_restorationSupport =
        mappedAvailable.substitute valuesAssignment mappedAvailableSafe := by
    apply WellSorted.AvailableOpenPattern.ext
    rw [CostStaticSourceTerm.actAvailable_pattern,
      WellSorted.AvailableOpenPattern.substitute_pattern,
      WellSorted.AvailableOpenPattern.castFree_pattern,
      CostStaticSourceTerm.mappedThickenedAvailable_pattern]
    change rhoCostStaticActionAt node.thinning
        environment.restorationSupportedOpenAssignment [] node.targetBound
        (node.reifiedSourceFrame environment).1 =
      values.restoreSupportedSkeleton node.boundaryTable node.targetBound
        node.mappedThickenedSkeleton.1
    exact sourceAction_eq_restoreSupportedSkeleton node values inventory
  have rightEndpoint :
      mappedAvailable.substitute originalAssignment mappedAvailableSafe =
        node.termAvailable := by
    apply WellSorted.AvailableOpenPattern.ext
    rw [WellSorted.AvailableOpenPattern.substitute_pattern,
      WellSorted.AvailableOpenPattern.castFree_pattern,
      CostStaticSourceTerm.mappedThickenedAvailable_pattern]
    change
      (TypedCostRegionBoundaryTable.Values.original node.boundaryTable
        ).restoreSupportedSkeleton node.boundaryTable node.targetBound
          node.mappedThickenedSkeleton.1 = node.term.1
    rw [TypedCostRegionBoundaryTable.Values.restoreSupportedSkeleton_original]
    exact node.restore_mappedThickenedSkeleton_eq_term
  rw [leftEndpoint, middleEndpoint] at sourceStep
  rw [rightEndpoint] at assignmentStep
  exact Relation.EqvGen.trans _ _ _ sourceStep assignmentStep

end CostStaticRegionNode

/-- The rho static kernel used by the generic child-first alternating-tree
traversal. -/
def rhoHereditaryStaticNormalizer : CostStaticRegionNormalizer rhoCIGSLT :=
  fun node values => CostStaticRegionNode.normalizeHereditary node values

/-- Proof-relevant alignment kernel for rho's hereditary static normalizer. -/
def rhoHereditaryNormalizationKernel :
    CostStaticNormalizationKernel rhoCIGSLT where
  normalize := rhoHereditaryStaticNormalizer

/-- Two same-colour rho source frames may be compared at the typed common
semantic-atom apex.  Canonical equality in that one authored source context
survives the shared Cost action exactly, including ambient thinning and
restoration of the common normalized atom values.

This theorem intentionally stops at the generated reflective canonical
representative.  Hereditary root equality additionally needs the existing
restoration/permutation terminal, because restoring values can change the
deterministic order of a parallel frame. -/
theorem rhoCommonSourceAction_canonicalize_eq
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (leftNode rightNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    {leftValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree leftNode.boundaryTable}
    {rightValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree rightNode.boundaryTable}
    (leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftNode.boundaryTable leftValues leftNode.skeleton.1)
    (rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightNode.boundaryTable rightValues rightNode.skeleton.1)
    (sameTargetBound : leftNode.targetBound = rightNode.targetBound)
    (commonSourceCanonical :
      let leftEnvironment := CostStaticAtomEnvironment.ofInventory
        leftInventory
      let rightEnvironment := CostStaticAtomEnvironment.ofInventory
        rightInventory
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      canonicalize rhoReflectivePresentation
          (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
            (leftNode.reifiedSourceFrame leftEnvironment).1) =
        canonicalize rhoReflectivePresentation
          (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
            (rightNode.reifiedSourceFrame rightEnvironment).1)) :
    let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
    let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    let assignment :=
      leftEnvironment.semanticKeyCospanSupportedOpenAssignment rightEnvironment
    canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation)
        (rhoCostStaticActionAt leftNode.thinning assignment []
          leftNode.targetBound
          (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
            (leftNode.reifiedSourceFrame leftEnvironment).1)) =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation)
        (rhoCostStaticActionAt rightNode.thinning assignment []
          rightNode.targetBound
          (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
            (rightNode.reifiedSourceFrame rightEnvironment).1)) := by
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let assignment :=
    leftEnvironment.semanticKeyCospanSupportedOpenAssignment rightEnvironment
  have typeMap : ∀ slot,
      mapTypeExpr (color.symbols rhoCIGSLT)
          (cospan.commonKeys.get slot).sourceType =
        (cospan.commonKeys.get slot).targetType :=
    leftEnvironment.semanticKeyCospan_typeMap_of_sameColor rightEnvironment
      (leftNode.semanticAtom_typeMap leftValues leftInventory)
      (rightNode.semanticAtom_typeMap rightValues rightInventory)
  have freeContext :
      cospan.commonSourceFreeContext.map (color.symbols rhoCIGSLT) =
        cospan.commonTargetFreeContext :=
    cospan.commonSourceFreeContext_map_eq_commonTargetFreeContext rhoCIGSLT
      color typeMap
  let leftCommon := leftEnvironment.reifySourceTermToCommon cospan
    cospan.leftSlot cospan.leftCommutes
    (leftNode.reifiedSourceTerm leftEnvironment)
  let rightCommonRaw := rightEnvironment.reifySourceTermToCommon cospan
    cospan.rightSlot cospan.rightCommutes
    (rightNode.reifiedSourceTerm rightEnvironment)
  let sourceBoundEq : leftNode.sourceBound = rightNode.sourceBound :=
    congrArg
      (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT color)
      sameTargetBound
  let rightCommon := rightCommonRaw.reindex sourceBoundEq sameTargetBound rfl
  have actionEquality :=
    rhoCostStaticActionAt_canonicalize_eq_of_canonicalize_eq
      (inner := []) (available := leftNode.targetBound) leftNode.thinning
      assignment freeContext rfl leftCommon.term.2.1.1 rightCommon.term.2.1.1
      leftCommon.safe rightCommon.safe leftCommon.supported.constructorsWithin
      rightCommon.supported.constructorsWithin leftCommon.term.2.1.2.2.1
      rightCommon.term.2.1.2.2.1 (by
        simpa [leftCommon, rightCommon,
          CostStaticRegionNode.CostStaticSourceTerm.reindex_pattern,
          CostStaticRegionNode.reifiedSourceTerm,
          CostStaticRegionNode.reifiedSourceFrame_pattern,
          rightCommonRaw, leftEnvironment, rightEnvironment, cospan] using
            commonSourceCanonical)
  have rightAction :
      rhoCostStaticActionAt leftNode.thinning assignment []
          leftNode.targetBound rightCommon.term.1 =
        rhoCostStaticActionAt rightNode.thinning assignment []
          rightNode.targetBound rightCommonRaw.term.1 := by
    simpa [CostStaticRegionNode.CostStaticSourceTerm.act,
      rhoCostStaticActionAt, ReflectiveContextSupport.substitute,
      rightCommon] using
        (CostStaticRegionNode.CostStaticSourceTerm.reindex_act_ofTarget
          rightCommonRaw sameTargetBound rfl assignment)
  rw [rightAction] at actionEquality
  simpa [leftCommon, rightCommonRaw,
    CostStaticRegionNode.reifiedSourceTerm,
    CostStaticRegionNode.reifiedSourceFrame_pattern, leftEnvironment,
    rightEnvironment, cospan, assignment] using actionEquality

/-- Structural alignment of the two already-canonical authored frames is a
sufficient, occurrence-sensitive interface to the common-source Cost action.
Related free-variable names must resolve to the same semantic atom at the
common cospan apex; no equality of endpoint spellings or boundary names is
assumed.

The conclusion still concerns the generated reflective canonical
representative.  A hereditary root bridge additionally consumes the existing
restoration/permutation terminal, where equal semantic atoms may be restored
to values whose deterministic parallel order differs from their boundary
order. -/
theorem rhoCommonSourceAction_canonicalize_eq_of_aligned
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (leftNode rightNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    {leftValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree leftNode.boundaryTable}
    {rightValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree rightNode.boundaryTable}
    (leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftNode.boundaryTable leftValues leftNode.skeleton.1)
    (rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightNode.boundaryTable rightValues rightNode.skeleton.1)
    (sameTargetBound : leftNode.targetBound = rightNode.targetBound)
    {relation : String → String → Prop}
    (matched :
      let leftEnvironment := CostStaticAtomEnvironment.ofInventory
        leftInventory
      let rightEnvironment := CostStaticAtomEnvironment.ofInventory
        rightInventory
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      ∀ {leftName rightName : String}, relation leftName rightName →
        ∃ leftSlot rightSlot,
          leftEnvironment.lookupAtom? leftName = some leftSlot ∧
            rightEnvironment.lookupAtom? rightName = some rightSlot ∧
            cospan.leftSlot leftSlot = cospan.rightSlot rightSlot)
    (aligned :
      let leftEnvironment := CostStaticAtomEnvironment.ofInventory
        leftInventory
      let rightEnvironment := CostStaticAtomEnvironment.ofInventory
        rightInventory
      FvarAligned relation
        (canonicalize rhoReflectivePresentation
          (leftNode.reifiedSourceFrame leftEnvironment).1)
        (canonicalize rhoReflectivePresentation
          (rightNode.reifiedSourceFrame rightEnvironment).1)) :
    let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
    let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    let assignment :=
      leftEnvironment.semanticKeyCospanSupportedOpenAssignment rightEnvironment
    canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation)
        (rhoCostStaticActionAt leftNode.thinning assignment []
          leftNode.targetBound
          (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
            (leftNode.reifiedSourceFrame leftEnvironment).1)) =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation)
        (rhoCostStaticActionAt rightNode.thinning assignment []
          rightNode.targetBound
          (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
            (rightNode.reifiedSourceFrame rightEnvironment).1)) := by
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  apply rhoCommonSourceAction_canonicalize_eq leftNode rightNode leftInventory
    rightInventory sameTargetBound
  exact leftEnvironment.canonicalize_commonReification_eq_of_aligned
    rightEnvironment cospan cospan.leftSlot cospan.rightSlot
    rhoReflectivePresentation (by decide) matched aligned

/-- Close two selected rho static roots when their independently atomized
canonical frames agree after restoration at the common semantic apex.  This
retains declaration, colour, support, and boundary identity in the cospan but
does not confuse those internal identities with the compact value they
restore. -/
noncomputable def rhoStaticRootBridgeOfCommonRestoredCanonicalFrame
    {leftColor rightColor : CostStaticColor}
    {targetFree : FreeTypeContext} {leftOuter rightOuter : List TypeExpr}
    (leftNode : CostStaticRegionNode rhoCIGSLT leftColor targetFree)
    (rightNode : CostStaticRegionNode rhoCIGSLT rightColor targetFree)
    (leftChildren : CostRegionBoundaryTrees rhoCIGSLT targetFree leftColor
      leftNode.finiteBoundaryTable)
    (rightChildren : CostRegionBoundaryTrees rhoCIGSLT targetFree rightColor
      rightNode.finiteBoundaryTable)
    (sameDepth : leftNode.targetBound.length = rightNode.targetBound.length)
    (commonRestorationsEq :
      let leftValues := leftChildren.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let rightValues := rightChildren.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let leftInventory := (leftNode.semanticAtomEnvironment leftValues).1
      let rightInventory := (rightNode.semanticAtomEnvironment rightValues).1
      let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
      let rightEnvironment :=
        CostStaticAtomEnvironment.ofInventory rightInventory
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      ReflectiveContextSupport.substituteAt
        rhoCIGSLT.costWholeReflectionProfile
          cospan.commonSupport cospan.commonAssignment
          leftNode.targetBound.length
          (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
            (leftNode.canonicalizeReifiedTargetFrame leftEnvironment
              (costStaticReflectivePresentationDecl rhoCIGSLT leftColor
                rhoReflectivePresentation))) =
        ReflectiveContextSupport.substituteAt
          rhoCIGSLT.costWholeReflectionProfile
          cospan.commonSupport cospan.commonAssignment
          leftNode.targetBound.length
          (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
            (rightNode.canonicalizeReifiedTargetFrame rightEnvironment
              (costStaticReflectivePresentationDecl rhoCIGSLT rightColor
                rhoReflectivePresentation)))) :
    CostRegionRootNormalizationBridge rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree
      (CostRegionTree.static (outer := leftOuter) leftNode leftChildren)
      (CostRegionTree.static (outer := rightOuter) rightNode rightChildren) := by
  refine .canonicalAtomRestorationRoot _ _ ?_
  rw [CostRegionTree.normalize_static_pattern,
    CostRegionTree.normalize_static_pattern]
  exact CostStaticRegionNode.normalizeHereditaryWithInventoryPackedRestorationBridgeOfCommonEquality
    leftNode rightNode
    (leftChildren.normalizeValues
      (normalizeStatic := rhoHereditaryStaticNormalizer))
    (rightChildren.normalizeValues
      (normalizeStatic := rhoHereditaryStaticNormalizer))
    (leftNode.semanticAtomEnvironment
      (leftChildren.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))).1
    (rightNode.semanticAtomEnvironment
      (rightChildren.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))).1
    sameDepth commonRestorationsEq

/-- Close two selected rho static roots once their canonical atom frames
agree in the common semantic namespace.  This is the reusable terminal cell
for the single-occurrence context route; all recursive foreign-boundary
values have already been supplied by `normalizeValues`. -/
noncomputable def rhoStaticRootBridgeOfCommonCanonicalFrame
    {leftColor rightColor : CostStaticColor}
    {targetFree : FreeTypeContext} {leftOuter rightOuter : List TypeExpr}
    (leftNode : CostStaticRegionNode rhoCIGSLT leftColor targetFree)
    (rightNode : CostStaticRegionNode rhoCIGSLT rightColor targetFree)
    (leftChildren : CostRegionBoundaryTrees rhoCIGSLT targetFree leftColor
      leftNode.finiteBoundaryTable)
    (rightChildren : CostRegionBoundaryTrees rhoCIGSLT targetFree rightColor
      rightNode.finiteBoundaryTable)
    (sameDepth : leftNode.targetBound.length = rightNode.targetBound.length)
    (commonFramesEq :
      let leftValues := leftChildren.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let rightValues := rightChildren.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let leftInventory := (leftNode.semanticAtomEnvironment leftValues).1
      let rightInventory := (rightNode.semanticAtomEnvironment rightValues).1
      let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
      let rightEnvironment :=
        CostStaticAtomEnvironment.ofInventory rightInventory
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
          (leftNode.canonicalizeReifiedTargetFrame leftEnvironment
            (costStaticReflectivePresentationDecl rhoCIGSLT leftColor
              rhoReflectivePresentation)) =
        cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
          (rightNode.canonicalizeReifiedTargetFrame rightEnvironment
            (costStaticReflectivePresentationDecl rhoCIGSLT rightColor
              rhoReflectivePresentation))) :
    CostRegionRootNormalizationBridge rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree
      (CostRegionTree.static (outer := leftOuter) leftNode leftChildren)
      (CostRegionTree.static (outer := rightOuter) rightNode rightChildren) := by
  refine .canonicalAtomRoot _ _ ?_
  rw [CostRegionTree.normalize_static_pattern,
    CostRegionTree.normalize_static_pattern]
  exact CostStaticRegionNode.normalizeHereditaryWithInventoryPackedBridgeOfCommonEquality
    leftNode rightNode
    (leftChildren.normalizeValues
      (normalizeStatic := rhoHereditaryStaticNormalizer))
    (rightChildren.normalizeValues
      (normalizeStatic := rhoHereditaryStaticNormalizer))
    (leftNode.semanticAtomEnvironment
      (leftChildren.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))).1
    (rightNode.semanticAtomEnvironment
      (rightChildren.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))).1
    sameDepth commonFramesEq

/-- Close two selected rho roots of one static colour when their atomized
frames have the same semantic-key representative in the common namespace.
This is the root bridge used by a selected authored generator: the generator
may change the frame before canonicalization, while the finite atom cospan
retains normalized boundary meanings. -/
noncomputable def rhoStaticRootBridgeOfCommonKeyedFrame
    {color : CostStaticColor}
    {targetFree : FreeTypeContext} {leftOuter rightOuter : List TypeExpr}
    (leftNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (rightNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (leftChildren : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      leftNode.finiteBoundaryTable)
    (rightChildren : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      rightNode.finiteBoundaryTable)
    (sameDepth : leftNode.targetBound.length = rightNode.targetBound.length)
    (commonKeyedFramesEq :
      let leftValues := leftChildren.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let rightValues := rightChildren.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let leftInventory := (leftNode.semanticAtomEnvironment leftValues).1
      let rightInventory := (rightNode.semanticAtomEnvironment rightValues).1
      let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
      let rightEnvironment :=
        CostStaticAtomEnvironment.ofInventory rightInventory
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt
          (cospan.commonSemanticPatternKeyAt rhoCIGSLT) declaration
          leftNode.targetBound.length
          (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
            (leftNode.reifyTargetFrame leftEnvironment)) =
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt
          (cospan.commonSemanticPatternKeyAt rhoCIGSLT) declaration
          leftNode.targetBound.length
          (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
            (rightNode.reifyTargetFrame rightEnvironment))) :
    CostRegionRootNormalizationBridge rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree
      (CostRegionTree.static (outer := leftOuter) leftNode leftChildren)
      (CostRegionTree.static (outer := rightOuter) rightNode rightChildren) := by
  apply rhoStaticRootBridgeOfCommonCanonicalFrame leftNode rightNode
    leftChildren rightChildren sameDepth
  let leftValues := leftChildren.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let rightValues := rightChildren.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let leftInventory := (leftNode.semanticAtomEnvironment leftValues).1
  let rightInventory := (rightNode.semanticAtomEnvironment rightValues).1
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  have leftCovered : leftEnvironment.Covers
      (leftNode.reifyTargetFrame leftEnvironment) := by
    intro name membership
    exact leftNode.reifyTargetFrame_atomCovered leftEnvironment name membership
  have rightCovered : rightEnvironment.Covers
      (rightNode.reifyTargetFrame rightEnvironment) := by
    intro name membership
    exact rightNode.reifyTargetFrame_atomCovered rightEnvironment name
      membership
  change cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
      (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt
        (CostStaticRegionNode.semanticPatternKeyAt leftEnvironment)
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation)
        leftNode.targetBound.length
        (leftNode.reifyTargetFrame leftEnvironment)) =
    cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
      (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt
        (CostStaticRegionNode.semanticPatternKeyAt rightEnvironment)
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation)
        rightNode.targetBound.length
        (rightNode.reifyTargetFrame rightEnvironment))
  rw [← sameDepth]
  exact leftEnvironment.commonCanonicalFrames_eq_of_commonCanonicalFrames_eq
    rightEnvironment cospan
    (costStaticReflectivePresentationDecl rhoCIGSLT color
      rhoReflectivePresentation)
    leftNode.targetBound.length (leftNode.reifyTargetFrame leftEnvironment)
    (rightNode.reifyTargetFrame rightEnvironment) leftCovered rightCovered
    commonKeyedFramesEq

/-- Construct the selected-colour terminal cell directly from a localized
generated Quote/Drop occurrence in the common semantic namespace.  Both
endpoint environments retain their own positional inventories; only the
complete semantic keys are renamed into the common apex. -/
noncomputable def rhoStaticRootBridgeOfSelectedQuoteDrop
    {color : CostStaticColor}
    {targetFree : FreeTypeContext} {leftOuter rightOuter : List TypeExpr}
    (leftNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (rightNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (leftChildren : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      leftNode.finiteBoundaryTable)
    (rightChildren : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      rightNode.finiteBoundaryTable)
    (sameDepth : leftNode.targetBound.length = rightNode.targetBound.length)
    (context : OneHoleContext) (atomName : String)
    (leftCommonFrameEq :
      let leftValues := leftChildren.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let rightValues := rightChildren.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let leftInventory := (leftNode.semanticAtomEnvironment leftValues).1
      let rightInventory := (rightNode.semanticAtomEnvironment rightValues).1
      let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
      let rightEnvironment :=
        CostStaticAtomEnvironment.ofInventory rightInventory
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation
      cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
          (leftNode.reifyTargetFrame leftEnvironment) =
        context.fill
          (.apply declaration.quoteConstructor
            [.apply declaration.dropConstructor [.fvar atomName]]))
    (rightCommonFrameEq :
      let leftValues := leftChildren.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let rightValues := rightChildren.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let leftInventory := (leftNode.semanticAtomEnvironment leftValues).1
      let rightInventory := (rightNode.semanticAtomEnvironment rightValues).1
      let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
      let rightEnvironment :=
        CostStaticAtomEnvironment.ofInventory rightInventory
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
          (rightNode.reifyTargetFrame rightEnvironment) =
        context.fill (.fvar atomName)) :
    CostRegionRootNormalizationBridge rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree
      (CostRegionTree.static (outer := leftOuter) leftNode leftChildren)
      (CostRegionTree.static (outer := rightOuter) rightNode rightChildren) := by
  apply rhoStaticRootBridgeOfCommonKeyedFrame leftNode rightNode leftChildren
    rightChildren sameDepth
  let leftValues := leftChildren.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let rightValues := rightChildren.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let leftInventory := (leftNode.semanticAtomEnvironment leftValues).1
  let rightInventory := (rightNode.semanticAtomEnvironment rightValues).1
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation
  change Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt
      (cospan.commonSemanticPatternKeyAt rhoCIGSLT) declaration
      leftNode.targetBound.length
      (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
        (leftNode.reifyTargetFrame leftEnvironment)) =
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt
      (cospan.commonSemanticPatternKeyAt rhoCIGSLT) declaration
      leftNode.targetBound.length
      (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
        (rightNode.reifyTargetFrame rightEnvironment))
  rw [leftCommonFrameEq, rightCommonFrameEq]
  exact rhoCostStaticQuoteDrop_canonicalizeByAt_fill_fvar_eq
    (cospan.commonSemanticPatternKeyAt rhoCIGSLT) color
      leftNode.targetBound.length context atomName

/-- Close two selected rho roots of one static colour from equality of their
pre-canonical mapped frames in the common semantic namespace.  Atomization,
semantic-key canonicalization, and restoration are derived by the generic
covered-cospan naturality square. -/
noncomputable def rhoStaticRootBridgeOfCommonMappedFrame
    {color : CostStaticColor}
    {targetFree : FreeTypeContext} {leftOuter rightOuter : List TypeExpr}
    (leftNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (rightNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (leftChildren : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      leftNode.finiteBoundaryTable)
    (rightChildren : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      rightNode.finiteBoundaryTable)
    (sameDepth : leftNode.targetBound.length = rightNode.targetBound.length)
    (commonMappedFramesEq :
      let leftValues := leftChildren.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let rightValues := rightChildren.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let leftInventory := (leftNode.semanticAtomEnvironment leftValues).1
      let rightInventory := (rightNode.semanticAtomEnvironment rightValues).1
      let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
      let rightEnvironment :=
        CostStaticAtomEnvironment.ofInventory rightInventory
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      cospan.reifyWith leftEnvironment.slotOfName? cospan.leftSlot
          leftNode.mappedThickenedSkeleton.1 =
        cospan.reifyWith rightEnvironment.slotOfName? cospan.rightSlot
          rightNode.mappedThickenedSkeleton.1) :
    CostRegionRootNormalizationBridge rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree
      (CostRegionTree.static (outer := leftOuter) leftNode leftChildren)
      (CostRegionTree.static (outer := rightOuter) rightNode rightChildren) := by
  apply rhoStaticRootBridgeOfCommonCanonicalFrame leftNode rightNode
    leftChildren rightChildren sameDepth
  let leftValues := leftChildren.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let rightValues := rightChildren.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let leftInventory := (leftNode.semanticAtomEnvironment leftValues).1
  let rightInventory := (rightNode.semanticAtomEnvironment rightValues).1
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  have leftFrameFactor :=
    leftEnvironment.reifyWith_reifyTargetFrame_eq_mappedThickenedSkeleton
      leftNode cospan cospan.leftSlot
  have rightFrameFactor :=
    rightEnvironment.reifyWith_reifyTargetFrame_eq_mappedThickenedSkeleton
      rightNode cospan cospan.rightSlot
  have commonFrames :
      cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
          (leftNode.reifyTargetFrame leftEnvironment) =
        cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
          (rightNode.reifyTargetFrame rightEnvironment) :=
    leftFrameFactor.trans (commonMappedFramesEq.trans rightFrameFactor.symm)
  have leftCovered : leftEnvironment.Covers
      (leftNode.reifyTargetFrame leftEnvironment) := by
    intro name membership
    exact leftNode.reifyTargetFrame_atomCovered leftEnvironment name membership
  have rightCovered : rightEnvironment.Covers
      (rightNode.reifyTargetFrame rightEnvironment) := by
    intro name membership
    exact rightNode.reifyTargetFrame_atomCovered rightEnvironment name
      membership
  change cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
      (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt
        (CostStaticRegionNode.semanticPatternKeyAt leftEnvironment)
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation)
        leftNode.targetBound.length
        (leftNode.reifyTargetFrame leftEnvironment)) =
    cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
      (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt
        (CostStaticRegionNode.semanticPatternKeyAt rightEnvironment)
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation)
        rightNode.targetBound.length
        (rightNode.reifyTargetFrame rightEnvironment))
  rw [← sameDepth]
  exact leftEnvironment.commonCanonicalFrames_eq_of_commonFrames_eq
    rightEnvironment cospan
    (costStaticReflectivePresentationDecl rhoCIGSLT color
      rhoReflectivePresentation)
    leftNode.targetBound.length (leftNode.reifyTargetFrame leftEnvironment)
    (rightNode.reifyTargetFrame rightEnvironment) leftCovered rightCovered
    commonFrames

/-- Close two selected rho roots of one static colour when their reified
target frames expose parallel outer contents whose recursively normalized,
restored meanings agree up to permutation at the common semantic apex.

This is the reusable foreign-root terminal: the selected parent orders its
frame by the restored meanings of its opaque children, so any two frames
carrying the same restored outer multiset evaluate to the same canonical
parallel process.  Neither endpoint atom order nor literal canonical-frame
equality is required, and no foreign atom value is canonicalized again under
the parent's declaration. -/
noncomputable def rhoStaticRootBridgeOfCommonRestoredParallelContentsPerm
    {color : CostStaticColor}
    {targetFree : FreeTypeContext} {leftOuter rightOuter : List TypeExpr}
    (leftNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (rightNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (leftChildren : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      leftNode.finiteBoundaryTable)
    (rightChildren : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      rightNode.finiteBoundaryTable)
    (sameDepth : leftNode.targetBound.length = rightNode.targetBound.length)
    {leftContents rightContents : List Pattern}
    (leftParallel :
      let leftValues := leftChildren.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let rightValues := rightChildren.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let leftInventory := (leftNode.semanticAtomEnvironment leftValues).1
      let rightInventory := (rightNode.semanticAtomEnvironment rightValues).1
      let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
      let rightEnvironment :=
        CostStaticAtomEnvironment.ofInventory rightInventory
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation
      cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
          (leftNode.reifyTargetFrame leftEnvironment) =
        .collection declaration.parallelCollection leftContents none)
    (rightParallel :
      let leftValues := leftChildren.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let rightValues := rightChildren.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let leftInventory := (leftNode.semanticAtomEnvironment leftValues).1
      let rightInventory := (rightNode.semanticAtomEnvironment rightValues).1
      let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
      let rightEnvironment :=
        CostStaticAtomEnvironment.ofInventory rightInventory
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation
      cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
          (rightNode.reifyTargetFrame rightEnvironment) =
        .collection declaration.parallelCollection rightContents none)
    (permutation :
      let leftValues := leftChildren.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let rightValues := rightChildren.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let leftInventory := (leftNode.semanticAtomEnvironment leftValues).1
      let rightInventory := (rightNode.semanticAtomEnvironment rightValues).1
      let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
      let rightEnvironment :=
        CostStaticAtomEnvironment.ofInventory rightInventory
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation
      List.Perm
        ((Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelContents
          declaration
          (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeListByAt
            (cospan.commonSemanticPatternKeyAt rhoCIGSLT) declaration
            leftNode.targetBound.length leftContents)).map
              (ReflectiveContextSupport.substituteAt
                rhoCIGSLT.costWholeReflectionProfile
                cospan.commonSupport cospan.commonAssignment
                leftNode.targetBound.length))
        ((Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelContents
          declaration
          (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeListByAt
            (cospan.commonSemanticPatternKeyAt rhoCIGSLT) declaration
            leftNode.targetBound.length rightContents)).map
              (ReflectiveContextSupport.substituteAt
                rhoCIGSLT.costWholeReflectionProfile
                cospan.commonSupport cospan.commonAssignment
                leftNode.targetBound.length))) :
    CostRegionRootNormalizationBridge rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree
      (CostRegionTree.static (outer := leftOuter) leftNode leftChildren)
      (CostRegionTree.static (outer := rightOuter) rightNode rightChildren) := by
  apply rhoStaticRootBridgeOfCommonRestoredCanonicalFrame leftNode rightNode
    leftChildren rightChildren sameDepth
  let leftValues := leftChildren.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let rightValues := rightChildren.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let leftInventory := (leftNode.semanticAtomEnvironment leftValues).1
  let rightInventory := (rightNode.semanticAtomEnvironment rightValues).1
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation
  have leftCovered : leftEnvironment.Covers
      (leftNode.reifyTargetFrame leftEnvironment) := by
    intro name membership
    exact leftNode.reifyTargetFrame_atomCovered leftEnvironment name membership
  have rightCovered : rightEnvironment.Covers
      (rightNode.reifyTargetFrame rightEnvironment) := by
    intro name membership
    exact rightNode.reifyTargetFrame_atomCovered rightEnvironment name
      membership
  change ReflectiveContextSupport.substituteAt
      rhoCIGSLT.costWholeReflectionProfile
      cospan.commonSupport cospan.commonAssignment
      leftNode.targetBound.length
      (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt
          (CostStaticRegionNode.semanticPatternKeyAt leftEnvironment)
          declaration leftNode.targetBound.length
          (leftNode.reifyTargetFrame leftEnvironment))) =
    ReflectiveContextSupport.substituteAt
      rhoCIGSLT.costWholeReflectionProfile
      cospan.commonSupport cospan.commonAssignment
      leftNode.targetBound.length
      (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt
          (CostStaticRegionNode.semanticPatternKeyAt rightEnvironment)
          declaration rightNode.targetBound.length
          (rightNode.reifyTargetFrame rightEnvironment)))
  rw [← sameDepth]
  exact leftEnvironment.commonRestoredCanonicalFrames_eq_of_parallelFrames_of_perm
    rightEnvironment cospan declaration leftNode.targetBound.length
    (leftNode.reifyTargetFrame leftEnvironment)
    (rightNode.reifyTargetFrame rightEnvironment) leftCovered rightCovered
    leftParallel rightParallel permutation

/-- Rho discharges both local obligations of hereditary tree normalization:
semantic-atom canonicalization normalizes the current frame, and generated
rho equations are natural under ambient binder insertion. -/
theorem rhoHereditaryStaticNormalizerLaws :
    CostStaticRegionNormalizerLaws rhoCIGSLT
      rhoHereditaryStaticNormalizer where
  ambientRenamingStable := rho_costSupportedEquationAmbientRenamingStable
  normalizesCurrentFrame := by
    intro color targetFree node values
    simpa only [rhoHereditaryStaticNormalizer] using
      CostStaticRegionNode.normalizeHereditary_equationEquiv node values

/-- Rho also discharges the stronger split-fibre interface consumed by the
generic typed Cost executor.  The hereditary normalizer is therefore a
literal instance of the language-independent theorem rather than a parallel
rho-only semantics. -/
theorem rhoHereditaryTypedStaticNormalizerLaws :
    CostTypedStaticRegionNormalizerLaws rhoCIGSLT
      rhoHereditaryStaticNormalizer where
  weakeningStable := rho_costOpenPatternEquationWeakeningStable
  normalizesCurrentFrame := by
    intro color targetFree node values valuesEquivalent
    simpa only [rhoHereditaryStaticNormalizer] using
      CostStaticRegionNode.normalizeHereditary_available_equationSetoid
        node values valuesEquivalent

/-- Every proof-relevant rho decomposition of one compact Cost term erases to
the same hereditary normalized pattern.  This exact chooser-independence is
strictly stronger than the unary authored-equation theorem. -/
theorem rhoHereditaryCompactCoherent :
    CostStaticRegionNormalizerCompactCoherent rhoCIGSLT
      rhoHereditaryStaticNormalizer :=
  CostCanonicalLaws.rho_unambiguousStaticDecomposition.normalizerCompactCoherent
    rhoHereditaryStaticNormalizer

namespace CostRegionTree

/-- Total child-first hereditary normalization of a complete rho Cost region
tree.  Every static frame receives the already-normalized values of its
opposite-colour children. -/
def normalizeHereditary
    {targetFree : FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (tree : CostRegionTree rhoCIGSLT targetFree available outer pattern type) :
    NormalizedCostRegionPattern rhoCIGSLT targetFree available outer pattern
      type :=
  tree.normalize (normalizeStatic := rhoHereditaryStaticNormalizer)

/-- The hereditary rho normal form of every proof-relevant region tree lies
in the authored generated-rho equation class of its exact compact input. -/
theorem normalizeHereditary_equationEquiv
    {targetFree : FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (tree : CostRegionTree rhoCIGSLT targetFree available outer pattern type) :
    ReflectiveEquationSemantics.ReflectiveEquationEquiv
      rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
      rhoCIGSLT.costWholeLanguage (normalizeHereditary tree).pattern pattern := by
  simpa only [normalizeHereditary] using
    tree.normalizeWithStatic_equationEquiv rhoHereditaryStaticNormalizer
      rhoHereditaryStaticNormalizerLaws

/-- Any two rho decompositions of the same typed compact term have hereditary
normal forms in the same sole authored equation class. -/
theorem normalizeHereditary_overlap_equivalent
    {targetFree : FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (first second : CostRegionTree rhoCIGSLT targetFree available outer pattern
      type) :
    ReflectiveEquationSemantics.ReflectiveEquationEquiv
      rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
      rhoCIGSLT.costWholeLanguage (normalizeHereditary first).pattern
        (normalizeHereditary second).pattern := by
  simpa only [normalizeHereditary] using
    CostRegionTree.normalizeWithStatic_overlap_equivalent
      rhoHereditaryStaticNormalizer rhoHereditaryStaticNormalizerLaws
        first second

/-- Rho's structural unambiguity makes hereditary normalization independent
of the proof-relevant decomposition chosen before execution.  This is exact
`Pattern` equality, not merely contextual equivalence, and holds for every
admitted open term because both trees replay through the same generated
compiler. -/
theorem normalizeHereditary_eq_buildOpenTerm
    {targetFree : FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort rhoCIGSLT.costWholeLanguage}
    (term : ReflectiveWellSorted.OpenTerm
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree targetBound targetSort)
    (tree : CostRegionTree rhoCIGSLT targetFree targetBound [] term.1
      (.base targetSort.1)) :
    (normalizeHereditary tree).pattern =
      (normalizeHereditary
        (CostRegionTree.buildOpenTerm (source := rhoCIGSLT) term)).pattern := by
  let compiled := CostRegionTree.buildOpenTerm (source := rhoCIGSLT) term
  have compiledEq : CostRegionTree.buildFuel? (source := rhoCIGSLT)
      (targetFree := targetFree) (costRegionPatternWeight term.1 + 1)
        targetBound [] term.1 (.base targetSort.1) = some compiled := by
    simpa only [CostRegionTree.build?] using
      (CostRegionTree.build?_eq_some_buildOpenTerm (source := rhoCIGSLT) term)
  simpa only [normalizeHereditary] using
    (CostRegionTree.normalize_pattern_eq_of_buildFuel
      CostCanonicalLaws.rho_unambiguousStaticDecomposition
      (normalizeStatic := rhoHereditaryStaticNormalizer)
      (costRegionPatternWeight term.1 + 1) tree compiledEq)

/-- Repackage hereditary normalization in the established checked open
carrier, erasing only the proof-relevant decomposition evidence. -/
def normalizeHereditaryOpen
    {targetFree : FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (tree : CostRegionTree rhoCIGSLT targetFree available outer pattern type)
    (canonical : pattern.hasCanonicalBinderMetadata = true)
    (object : isObjectPattern pattern = true)
    (scope : ReflectiveWellSorted.ReflectiveScopeSafeAt
      rhoCIGSLT.costWholeReflectionProfile available.length pattern) :
    ReflectiveWellSorted.OpenPattern rhoCIGSLT.costWholeReflectionProfile
      rhoCIGSLT.costWholeLanguage targetFree (available ++ outer) type :=
  (normalizeHereditary tree).toOpenPattern canonical object scope

@[simp]
theorem normalizeHereditaryOpen_pattern
    {targetFree : FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (tree : CostRegionTree rhoCIGSLT targetFree available outer pattern type)
    (canonical : pattern.hasCanonicalBinderMetadata = true)
    (object : isObjectPattern pattern = true)
    (scope : ReflectiveWellSorted.ReflectiveScopeSafeAt
      rhoCIGSLT.costWholeReflectionProfile available.length pattern) :
    (normalizeHereditaryOpen tree canonical object scope).1 =
      (normalizeHereditary tree).pattern :=
  rfl

end CostRegionTree

/-- The repaired compact rho Cost executor: elaborate once into the complete
proof-relevant alternating tree, normalize children before their parent
frames, then erase the final typed normal form.  This is the rho instance of
the generic hereditary GSLT executor, not a second implementation. -/
def rhoCostNormalizeOpenHereditary
    {targetFree : FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort rhoCIGSLT.costWholeLanguage}
    (term : ReflectiveWellSorted.OpenTerm
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree targetBound targetSort) :
    ReflectiveWellSorted.OpenTerm rhoCIGSLT.costWholeReflectionProfile
      rhoCIGSLT.costWholeLanguage targetFree targetBound targetSort :=
  rhoCIGSLT.costNormalizeOpenWithStatic rhoHereditaryStaticNormalizer term

@[simp]
theorem rhoCostNormalizeOpenHereditary_pattern
    {targetFree : FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort rhoCIGSLT.costWholeLanguage}
    (term : ReflectiveWellSorted.OpenTerm
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree targetBound targetSort) :
    (rhoCostNormalizeOpenHereditary term).1 =
      (CostRegionTree.normalizeHereditary
        (CostRegionTree.buildOpenTerm (source := rhoCIGSLT) term)).pattern :=
  rfl

/-- The repaired compact executor erases exactly the deterministic
elaboration normalized by the hereditary static kernel.  Both sides reduce to
the same `buildOpenTerm` computation, so no second parser or normalizer
participates. -/
theorem rhoCostNormalizeOpenHereditary_agreesWithStatic :
    CostOpenNormalizerAgreesWithStatic rhoCIGSLT
      rhoHereditaryStaticNormalizer
      (fun term => rhoCostNormalizeOpenHereditary term) :=
  rhoCIGSLT.costNormalizeOpenWithStatic_agreesWithStatic
    rhoHereditaryStaticNormalizer

/-- The repaired compact executor is unary-sound for every admitted rho Cost
term, independently of the compiler's internal decomposition choices. -/
theorem rhoCostNormalizeOpenHereditary_equationEquiv
    {targetFree : FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort rhoCIGSLT.costWholeLanguage}
    (term : ReflectiveWellSorted.OpenTerm
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree targetBound targetSort) :
    ReflectiveEquationSemantics.ReflectiveEquationEquiv
      rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
      rhoCIGSLT.costWholeLanguage (rhoCostNormalizeOpenHereditary term).1
        term.1 :=
  rhoCIGSLT.costNormalizeOpenWithStatic_equationEquiv
    rhoHereditaryStaticNormalizer rhoHereditaryStaticNormalizerLaws term

/-- The same executor is sound in the exact typed open-equation fibre.  This
is the generic hereditary theorem instantiated by rho's local static law. -/
theorem rhoCostNormalizeOpenHereditary_typed_openEquationSetoid
    {targetFree : FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort rhoCIGSLT.costWholeLanguage}
    (term : ReflectiveWellSorted.OpenTerm
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree targetBound targetSort) :
    (ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid
      rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
        rhoCIGSLT.costWholeLanguage targetFree targetBound
          (.base targetSort.1)).r
      (rhoCostNormalizeOpenHereditary term) term :=
  rhoCIGSLT.costNormalizeOpenWithStatic_typed_openEquationSetoid
    rhoHereditaryStaticNormalizer rhoHereditaryTypedStaticNormalizerLaws term

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
