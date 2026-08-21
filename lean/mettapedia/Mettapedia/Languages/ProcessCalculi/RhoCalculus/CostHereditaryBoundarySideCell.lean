import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryNonBoundaryPlanStop
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryMatchedFramesMixedLeaf
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryVariableLeafRoutes
import Mettapedia.GSLT.LanguageDef.CostRestorationLeafDichotomy

/-!
# The certified-boundary side of the non-boundary plan-stop residual

Family 1 of `RhoStaticNonBoundaryPlanStopSourceAlignedOn` is the cell
`RhoPlanStopBoundarySideCell`: exactly one reached root class is a certified
boundary.  Everything here is stated for an arbitrary `rawStop` together with
the two properties both instantiated measures supply — a delegated stop
carries canonical equality of its endpoints, and the recursion callback is
available below the endpoint pair size — so a single proof serves A1 and A2.

## What is established here

* `CostStaticRegionPlan.rigid_cases` — the reached root class `.rigid` has
  *four* inhabitants: the bound-variable plan, the authored source-variable
  plan, and both binder plans.  Only the source-variable plan abstracts to a
  free variable.

* `rho_planStop_boundarySide_rigid_rawStop` — a certified boundary facing a
  rigid root is never a structurally eligible stop, so the delegated raw stop
  is forced and the recursion callback is always available in this slice.

* `rhoPlanStopBoundaryRigid_sourceAligned` — **the entire rigid-partner
  sub-family of family 1 is discharged**, in the residual's own per-stop
  shape.  The bound-variable case is impossible by reflective scope, both
  binder cases are impossible by the common source type, and the surviving
  source-variable case uses the hereditary normal form of the strictly
  smaller payload pair.

* `not_boundarySide_bvarPartner_sourcePatternLeafAligned` and its mirror show
  that a certified-boundary/bound-variable pair cannot satisfy the requested
  restoration relation.  The exact plan-stop configuration is then ruled out
  in both orientations by `rho_planStop_boundarySide_bvarPartner_absurd` and
  `rho_planStop_bvarPartner_boundarySide_absurd`: the boundary route supplies
  a typed reflective-scope certificate, while a bound-variable partner would
  force that boundary payload to canonicalize to a bare bound variable.

## What is *not* established here

The remaining sub-families of family 1 — a certified boundary facing an
ordinary application or a source collection — are open.  Each needs a
pair-level bridge relating `(commonKeys.get slot).normal`, a hereditary normal
form, to a restored `canonicalizeByDepths` frame.  The bridge must use the
reached-plan provenance; the unrestricted pointwise commutation statement is
false.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax

namespace CostStaticAtomKeyCospan

/-! ## A reified free variable never meets a reified bound variable -/

/-- Cospan reification sends a free variable to a free variable, whichever
leg resolves it. -/
theorem exists_reifyWith_fvar
    {leftCount rightCount endpointCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (resolve : String → Option (Fin endpointCount))
    (leg : Fin endpointCount → Fin cospan.commonKeys.length)
    (name : String) :
    ∃ reified, cospan.reifyWith resolve leg (.fvar name) = .fvar reified := by
  cases resolved : resolve name with
  | none =>
      exact ⟨name, by
        simp only [CostStaticAtomKeyCospan.reifyWith, resolved]⟩
  | some slot =>
      exact ⟨cospan.commonAtomName (leg slot), by
        simp only [CostStaticAtomKeyCospan.reifyWith, resolved]⟩

/-- Cospan reification leaves a bound variable alone. -/
@[simp]
theorem reifyWith_bvar
    {leftCount rightCount endpointCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (resolve : String → Option (Fin endpointCount))
    (leg : Fin endpointCount → Fin cospan.commonKeys.length)
    (index : Nat) :
    cospan.reifyWith resolve leg (.bvar index) = .bvar index := by
  simp only [CostStaticAtomKeyCospan.reifyWith]

/-- **The depth-uniform restoration relation of a semantic cospan cannot hold
between a reified free variable and a reified bound variable.**

This is `not_restoresTogether_fvar_bvar` transported across cospan
reification: reification changes only free names, so both endpoints keep
their leaf kinds and the shift law still applies. -/
theorem not_restoresTogether_reifyWith_fvar_bvar
    {leftCount rightCount leftEndpoint rightEndpoint : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile)
    (leftResolve : String → Option (Fin leftEndpoint))
    (leftLeg : Fin leftEndpoint → Fin cospan.commonKeys.length)
    (rightResolve : String → Option (Fin rightEndpoint))
    (rightLeg : Fin rightEndpoint → Fin cospan.commonKeys.length)
    (name : String) (index : Nat) :
    ¬ ReflectiveContextSupport.RestoresTogether profile cospan.commonSupport
      cospan.commonAssignment
      (cospan.reifyWith leftResolve leftLeg (.fvar name))
      (cospan.reifyWith rightResolve rightLeg (.bvar index)) := by
  obtain ⟨reified, reifiedEq⟩ :=
    cospan.exists_reifyWith_fvar leftResolve leftLeg name
  rw [reifiedEq, cospan.reifyWith_bvar]
  exact ReflectiveContextSupport.not_restoresTogether_fvar_bvar reified index

/-- Mirror of `not_restoresTogether_reifyWith_fvar_bvar`. -/
theorem not_restoresTogether_reifyWith_bvar_fvar
    {leftCount rightCount leftEndpoint rightEndpoint : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile)
    (leftResolve : String → Option (Fin leftEndpoint))
    (leftLeg : Fin leftEndpoint → Fin cospan.commonKeys.length)
    (rightResolve : String → Option (Fin rightEndpoint))
    (rightLeg : Fin rightEndpoint → Fin cospan.commonKeys.length)
    (index : Nat) (name : String) :
    ¬ ReflectiveContextSupport.RestoresTogether profile cospan.commonSupport
      cospan.commonAssignment
      (cospan.reifyWith leftResolve leftLeg (.bvar index))
      (cospan.reifyWith rightResolve rightLeg (.fvar name)) := by
  obtain ⟨reified, reifiedEq⟩ :=
    cospan.exists_reifyWith_fvar rightResolve rightLeg name
  rw [reifiedEq, cospan.reifyWith_bvar]
  exact ReflectiveContextSupport.not_restoresTogether_bvar_fvar index reified

/-- The form the plan-stop residual actually presents: both leaves pass
through the colour symbol map and the endpoint binder thinning before
reification.  Neither stage changes a leaf's kind, so the exclusion
survives. -/
theorem not_restoresTogether_transported_fvar_bvar
    {leftCount rightCount leftEndpoint rightEndpoint : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile)
    (leftResolve : String → Option (Fin leftEndpoint))
    (leftLeg : Fin leftEndpoint → Fin cospan.commonKeys.length)
    (rightResolve : String → Option (Fin rightEndpoint))
    (rightLeg : Fin rightEndpoint → Fin cospan.commonKeys.length)
    {source : CIGSLT} {color : CostStaticColor}
    {leftSourceBound leftTargetBound rightSourceBound rightTargetBound :
      List TypeExpr}
    (leftThinning : CostStaticBinderThinning source color leftSourceBound
      leftTargetBound)
    (rightThinning : CostStaticBinderThinning source color rightSourceBound
      rightTargetBound)
    (sourceDepth : Nat) (name : String) (index : Nat) :
    ¬ ReflectiveContextSupport.RestoresTogether profile cospan.commonSupport
      cospan.commonAssignment
      (cospan.reifyWith leftResolve leftLeg
        (leftThinning.thickenAmbientBVars sourceDepth
          (mapPattern (color.symbols source) (.fvar name))))
      (cospan.reifyWith rightResolve rightLeg
        (rightThinning.thickenAmbientBVars sourceDepth
          (mapPattern (color.symbols source) (.bvar index)))) := by
  simp only [mapPattern, CostStaticBinderThinning.thickenAmbientBVars]
  exact cospan.not_restoresTogether_reifyWith_fvar_bvar profile leftResolve
    leftLeg rightResolve rightLeg name _

/-- Mirror of `not_restoresTogether_transported_fvar_bvar`. -/
theorem not_restoresTogether_transported_bvar_fvar
    {leftCount rightCount leftEndpoint rightEndpoint : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile)
    (leftResolve : String → Option (Fin leftEndpoint))
    (leftLeg : Fin leftEndpoint → Fin cospan.commonKeys.length)
    (rightResolve : String → Option (Fin rightEndpoint))
    (rightLeg : Fin rightEndpoint → Fin cospan.commonKeys.length)
    {source : CIGSLT} {color : CostStaticColor}
    {leftSourceBound leftTargetBound rightSourceBound rightTargetBound :
      List TypeExpr}
    (leftThinning : CostStaticBinderThinning source color leftSourceBound
      leftTargetBound)
    (rightThinning : CostStaticBinderThinning source color rightSourceBound
      rightTargetBound)
    (sourceDepth : Nat) (index : Nat) (name : String) :
    ¬ ReflectiveContextSupport.RestoresTogether profile cospan.commonSupport
      cospan.commonAssignment
      (cospan.reifyWith leftResolve leftLeg
        (leftThinning.thickenAmbientBVars sourceDepth
          (mapPattern (color.symbols source) (.bvar index))))
      (cospan.reifyWith rightResolve rightLeg
        (rightThinning.thickenAmbientBVars sourceDepth
          (mapPattern (color.symbols source) (.fvar name)))) := by
  simp only [mapPattern, CostStaticBinderThinning.thickenAmbientBVars]
  exact cospan.not_restoresTogether_reifyWith_bvar_fvar profile leftResolve
    leftLeg rightResolve rightLeg _ name

end CostStaticAtomKeyCospan

end Mettapedia.GSLT.LanguageDef

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryLeafDichotomyProbe
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryExposureClosure
open CostStaticRegionNode

/-! ## Positional support regime of an embedded reached boundary -/

/-- Every boundary retained by a rho static root sees either the complete
ambient target context or no ambient binders at all. -/
theorem CostStaticRegionNode.boundaryTargetSupport_eq_targetBound_or_nil
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (boundary : TypedCostRegionBoundary rhoCIGSLT color targetFree)
    (membership : boundary ∈ node.plan.boundaryTable.entries) :
    boundary.boundary.targetSupport = node.targetBound ∨
      boundary.boundary.targetSupport = [] := by
  have frameFree : WellSorted.ReflectiveSubstitutionBinderFree
      node.plan.abstractPattern = true :=
    CostStaticRegionPlan.rhoAbstractPattern_binderFree_of_base node.plan
      ⟨node.sourceSort.1, rfl⟩
  exact
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionNode.CostStaticRegionPlan.boundaryTargetSupport_eq_sourceAvailable_or_nil
      node.plan frameFree boundary membership

/-- Every certified boundary selected below an authored Quote is sealed: the
Quote resets the child plan's reflective availability to the empty context. -/
theorem CostStaticRegionPlan.boundaryTargetSupport_eq_nil_of_quoteRoot
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound sourceAvailable : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {outer : OneHoleContext} {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    (frameFree : WellSorted.ReflectiveSubstitutionBinderFree
      plan.abstractPattern = true)
    (boundary : TypedCostRegionBoundary rhoCIGSLT color targetFree)
    (membership : boundary ∈ plan.boundaryTable.entries)
    (quoteRoot : plan.rootClass =
      CostStaticPlanRootClass.application
        rhoReflectivePresentation.quoteConstructor) :
    boundary.boundary.targetSupport = [] := by
  cases plan with
  | application constructor rendered current preimage notBare children =>
      have childrenFree :
          WellSorted.ReflectiveSubstitutionBinderFreeList
            children.abstractPatterns = true := by
        simpa [CostStaticRegionPlan.abstractPattern,
          WellSorted.ReflectiveSubstitutionBinderFree] using frameFree
      have childResult :=
        CostStaticArgumentPlan.boundaryTargetSupport_eq_sourceAvailable_or_nil
          children childrenFree boundary membership
      have sourceQuote : preimage.sourceConstructor.1.label =
          rhoReflectivePresentation.quoteConstructor := by
        simpa [CostStaticRegionPlan.rootClass] using quoteRoot
      have quote : ReflectiveContextSupport.isQuoteConstructor
          rhoCIGSLT.reflection.1 preimage.sourceConstructor.1.label = true := by
        rw [sourceQuote]
        exact rho_isQuoteConstructor_quote
      rcases childResult with exposed | sealed
      · simpa [quote] using exposed
      · exact sealed
  | bvar | fvar | boundaryApplication | lambda | multiLambda | collection |
      boundaryCollection =>
      simp [CostStaticRegionPlan.rootClass] at quoteRoot

/-- Every semantic atom of an authored Quote-root plan is sealed.  Boundary
atoms inherit the empty support established above, while authored source
variables are intrinsically independent of the local target binder suffix. -/
theorem CostStaticRegionPlan.ofInventory_atomValue_targetSupport_eq_nil_of_quoteRoot
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound sourceAvailable : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {outer : OneHoleContext} {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    (frameFree : WellSorted.ReflectiveSubstitutionBinderFree
      plan.abstractPattern = true)
    (quoteRoot : plan.rootClass =
      CostStaticPlanRootClass.application
        rhoReflectivePresentation.quoteConstructor)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      plan.boundaryTable}
    (inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      plan.boundaryTable values plan.abstractPattern)
    (slot : Fin (CostStaticAtomEnvironment.ofInventory inventory).atomCount) :
    ((CostStaticAtomEnvironment.ofInventory inventory).atomValue slot).key.targetSupport =
      [] := by
  apply
    CostStaticAtomEnvironment.ofInventory_atomValue_targetSupport_eq_nil_of_boundaryEntries
      inventory
  intro boundary membership
  exact
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionPlan.boundaryTargetSupport_eq_nil_of_quoteRoot
      plan frameFree boundary membership quoteRoot

/-- A Quote-root static plan is reflectively safe at the reset depth.  The
authored rho quotation is unary, so its singleton child is checked at depth
zero independently of the ambient source context. -/
theorem CostStaticRegionPlan.abstractPattern_binderSafeAt_zero_of_quoteRoot
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound sourceAvailable : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {outer : OneHoleContext} {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    (quoteRoot : plan.rootClass =
      CostStaticPlanRootClass.application
        rhoReflectivePresentation.quoteConstructor) :
    binderSafeAt rhoReflectivePresentation.quoteConstructor 0
      plan.abstractPattern = true := by
  have safe := plan.abstractPattern_reflectiveScopeSafeAt
    rhoReflectivePresentation.toReflectivePresentationDecl (by
      change rhoReflectivePresentation.toReflectivePresentationDecl ∈
        ReflectionExtension.rhoReflectionProfile.presentations
      simp [ReflectionExtension.rhoReflectionProfile])
  cases plan with
  | application constructor rendered current preimage notBare children =>
      have sourceQuote : preimage.sourceConstructor.1.label =
          rhoReflectivePresentation.quoteConstructor := by
        simpa [CostStaticRegionPlan.rootClass] using quoteRoot
      have paramsLength : preimage.sourceConstructor.1.params.length = 1 :=
        CostHereditaryCrossColorLeafHinge.rhoCalc_params_length_eq_one_of_label_eq_quote
          preimage.sourceConstructor.2 (by
            simpa [rhoReflectivePresentation] using sourceQuote)
      obtain ⟨abstractLength, argumentsLength⟩ :=
        CostHereditaryCrossColorLeafHinge.CostStaticArgumentPlan.abstractPatterns_length
          children
      obtain ⟨child, childShape⟩ := List.length_eq_one_iff.mp
        (abstractLength.trans (argumentsLength.trans paramsLength))
      simp only [CostStaticRegionPlan.abstractPattern] at safe ⊢
      rw [childShape] at safe ⊢
      simpa [binderSafeAt, sourceQuote] using safe
  | bvar | fvar | boundaryApplication | lambda | multiLambda | collection |
      boundaryCollection =>
      simp [CostStaticRegionPlan.rootClass] at quoteRoot

/-- Every semantic atom used by an embedded reached Quote frame is sealed in
the parent environment.  The proof transports the original occurrence through
the reached skeleton context and replays the exact finite-table embedding; no
claim is made about unrelated atoms elsewhere in the parent frame. -/
theorem CostStaticPlanReached.parentAtomTargetSupport_eq_nil_of_quoteRoot
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {payload : Pattern}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (reached : CostStaticPlanReached rhoCIGSLT color targetFree payload
      node.plan.abstractPattern)
    (admission : reached.plan.RawAdmission)
    (frameFree : WellSorted.ReflectiveSubstitutionBinderFree
      reached.plan.abstractPattern = true)
    (quoteRoot : reached.plan.rootClass =
      CostStaticPlanRootClass.application
        rhoReflectivePresentation.quoteConstructor)
    (embedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      reached.plan.boundaryTable.entries node.plan.boundaryTable.entries)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    {name : String}
    (membership : name ∈
      (environment.reify reached.plan.abstractPattern).freeFvarNames)
    (slot : Fin environment.atomCount)
    (selected : environment.lookupAtom? name = some slot) :
    (environment.atomValue slot).key.targetSupport = [] := by
  have abstractObject :
      WellSorted.isObjectPattern reached.plan.abstractPattern = true :=
    reached.plan.abstractPattern_object admission.object
  obtain ⟨originalName, originalMembership, reifiedName⟩ :=
    environment.exists_originalName_of_mem_freeFvarNames_reify_of_object
      reached.plan.abstractPattern abstractObject membership
  obtain ⟨localOccurrence, localName⟩ :=
    CostStaticFVarOccurrence.exists_of_mem_freeFvarNames_of_object
      originalMembership abstractObject
  let parentOccurrence : CostStaticFVarOccurrence node.skeleton.1 :=
    CostStaticFVarOccurrence.castRoot
      (reached.abstract_eq.symm.trans node.skeleton_pattern.symm)
      (localOccurrence.inContext reached.skeletonContext)
  have parentName : parentOccurrence.name = originalName := by
    simp [parentOccurrence, localName]
  obtain ⟨parentSlot, parentSelected⟩ := Option.isSome_iff_exists.mp
    (environment.slotOfName?_isSome_of_occurrence parentOccurrence)
  have originalSelected : environment.slotOfName? originalName =
      some parentSlot := by
    simpa [parentName] using parentSelected
  have reifiedNameAtSlot : environment.reifyName originalName =
      environment.atomName parentSlot := by
    simp [CostStaticAtomEnvironment.reifyName, originalSelected]
  have selectedAtSlot : environment.lookupAtom?
      (environment.atomName parentSlot) = some slot := by
    rw [← reifiedNameAtSlot, reifiedName]
    exact selected
  have slotEq : parentSlot = slot := by
    rw [environment.lookupAtom?_atomName] at selectedAtSlot
    exact Option.some.inj selectedAtSlot
  subst slot
  have localSubset : reached.plan.boundaryTable.entries ⊆
      reached.plan.boundaryTable.entries := fun _ membership => membership
  obtain ⟨typed, _safe⟩ :=
    reached.plan.abstractPattern_supportedSafe reached.plan.boundaryTable
      localSubset
  obtain ⟨freeType, typedName⟩ :=
    typed.toHasType.freeType_of_mem_freeFvarNames_of_isObjectPattern
      abstractObject originalMembership
  have parentSupport : node.plan.boundaryTable.restorationSupport
      originalName = [] := by
    apply reached.plan.boundaryTable.restorationSupport_eq_nil_of_entries_subset
      node.plan.boundaryTable embedding.subset
    · intro boundary boundaryMembership
      exact
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionPlan.boundaryTargetSupport_eq_nil_of_quoteRoot
          reached.plan frameFree boundary boundaryMembership quoteRoot
    · exact typedName
  rw [environment.atomValue_targetSupport_eq_of_slotOfName?_eq_some
    parentOccurrence parentSlot parentSelected]
  simpa only [CostStaticRegionNode.boundaryTable, parentName] using
    parentSupport

/-- On a scope-safe source subframe, the pulled-back key is independent of
both keyed-canonicalizer depths when every semantic atom used by that
subframe is sealed. -/
theorem CostStaticRegionNode.sourceSemanticPatternKeyAt_eq_of_freeAtomTargetSupport_eq_nil
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    {safetyDepth : Nat} (availableDepth scopeDepth : Nat) (pattern : Pattern)
    (supportNil : ∀ name, name ∈ pattern.freeFvarNames →
      ∀ slot, environment.lookupAtom? name = some slot →
        (environment.atomValue slot).key.targetSupport = [])
    (safe : binderSafeAt rhoReflectivePresentation.quoteConstructor
      safetyDepth pattern = true)
    (depthOrder : safetyDepth ≤ scopeDepth) :
    sourceSemanticPatternKeyAt node environment availableDepth scopeDepth
        pattern =
      Mettapedia.GSLT.LanguageDef.CostStaticRegionNode.semanticPatternKeyAt
        environment 0 (mapPattern (color.symbols rhoCIGSLT) pattern) := by
  have mappedSafe : binderSafeAt
      ((color.symbols rhoCIGSLT).constructor
        rhoReflectivePresentation.quoteConstructor)
      safetyDepth (mapPattern (color.symbols rhoCIGSLT) pattern) = true := by
    rw [CostStaticColor.binderSafeAt_mapPattern_symbols]
    exact safe
  unfold sourceSemanticPatternKeyAt
  rw [node.thinning.thickenAmbientBVars_eq_self_of_binderSafeAt_le
    ((color.symbols rhoCIGSLT).constructor
      rhoReflectivePresentation.quoteConstructor) mappedSafe depthOrder]
  apply Mettapedia.GSLT.LanguageDef.CostStaticRegionNode.semanticPatternKeyAt_eq_of_freeAtomTargetSupport_eq_nil
    environment _ _ availableDepth 0
  intro name membership slot selected
  apply supportNil name
  · simpa using membership
  · exact selected

/-- Global sealed-environment specialization of the local pulled-back key
invariance theorem. -/
theorem CostStaticRegionNode.sourceSemanticPatternKeyAt_eq_of_atomTargetSupport_eq_nil
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    (supportNil : ∀ slot,
      (environment.atomValue slot).key.targetSupport = [])
    {safetyDepth : Nat} (availableDepth scopeDepth : Nat) (pattern : Pattern)
    (safe : binderSafeAt rhoReflectivePresentation.quoteConstructor
      safetyDepth pattern = true)
    (depthOrder : safetyDepth ≤ scopeDepth) :
    sourceSemanticPatternKeyAt node environment availableDepth scopeDepth
        pattern =
      Mettapedia.GSLT.LanguageDef.CostStaticRegionNode.semanticPatternKeyAt
        environment 0 (mapPattern (color.symbols rhoCIGSLT) pattern) := by
  apply
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionNode.sourceSemanticPatternKeyAt_eq_of_freeAtomTargetSupport_eq_nil
      node environment availableDepth scopeDepth pattern
  · intro name membership slot selected
    exact supportNil slot
  · exact safe
  · exact depthOrder

/-- A scope-safe frame canonicalizes identically with its pulled-back key and
the corresponding depth-free target key when every semantic atom used by the
frame is sealed. -/
theorem CostStaticRegionNode.canonicalizeByDepths_sourceSemanticPatternKeyAt_eq_of_freeAtomTargetSupport_eq_nil
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory) :
    ∀ (availableDepth scopeDepth safetyDepth : Nat) (pattern : Pattern),
      (∀ name, name ∈ pattern.freeFvarNames →
        ∀ slot, environment.lookupAtom? name = some slot →
          (environment.atomValue slot).key.targetSupport = []) →
      binderSafeAt rhoReflectivePresentation.quoteConstructor safetyDepth
          pattern = true →
      safetyDepth ≤ scopeDepth →
      canonicalizeByDepths (sourceSemanticPatternKeyAt node environment)
          rhoReflectivePresentation availableDepth scopeDepth pattern =
        canonicalizeByDepths
          (fun _ _ pattern =>
            Mettapedia.GSLT.LanguageDef.CostStaticRegionNode.semanticPatternKeyAt
              environment 0 (mapPattern (color.symbols rhoCIGSLT) pattern))
          rhoReflectivePresentation availableDepth scopeDepth pattern := by
  intro availableDepth scopeDepth safetyDepth pattern supportNil safe depthOrder
  induction pattern using Pattern.inductionOn generalizing availableDepth
      scopeDepth safetyDepth with
  | hbvar index => rfl
  | hfvar name => rfl
  | happly constructor arguments inductionHypothesis =>
      let childSafetyDepth := match arguments with
        | [_] =>
            if constructor == rhoReflectivePresentation.quoteConstructor
              then 0 else safetyDepth
        | _ => safetyDepth
      have argumentsSafe : binderSafeListAt
          rhoReflectivePresentation.quoteConstructor childSafetyDepth
          arguments = true := by
        cases arguments with
        | nil => simp [binderSafeListAt]
        | cons argument arguments =>
            cases arguments with
            | nil =>
                by_cases quoted :
                    constructor = rhoReflectivePresentation.quoteConstructor
                · have quotedDecision :
                      (constructor ==
                        rhoReflectivePresentation.quoteConstructor) = true :=
                    beq_iff_eq.mpr quoted
                  simpa [childSafetyDepth, binderSafeAt, quotedDecision,
                    binderSafeListAt] using safe
                · have quotedDecision :
                      (constructor ==
                        rhoReflectivePresentation.quoteConstructor) = false :=
                    beq_eq_false_iff_ne.mpr quoted
                  simpa [childSafetyDepth, binderSafeAt, quotedDecision,
                    binderSafeListAt] using safe
            | cons second remainder =>
                simpa [childSafetyDepth, binderSafeAt] using safe
      have childDepthOrder : childSafetyDepth ≤ scopeDepth := by
        cases arguments with
        | nil => simpa [childSafetyDepth] using depthOrder
        | cons argument arguments =>
            cases arguments with
            | nil =>
                by_cases quoted :
                    constructor = rhoReflectivePresentation.quoteConstructor
                · simp [childSafetyDepth, quoted]
                · simpa [childSafetyDepth, quoted] using depthOrder
            | cons second remainder =>
                simpa [childSafetyDepth] using depthOrder
      simp only [canonicalizeByDepths]
      apply congrArg
      rw [canonicalizeListByDepths_eq_map,
        canonicalizeListByDepths_eq_map]
      apply List.map_congr_left
      intro argument membership
      exact inductionHypothesis argument membership _ _ _
        (by
          intro name nameMembership slot selected
          apply supportNil name
          · simp only [Pattern.freeFvarNames, List.mem_flatMap]
            exact ⟨argument, membership, nameMembership⟩
          · exact selected)
        ((binderSafeListAt_eq_true_iff _ _ _).mp argumentsSafe argument
          membership) childDepthOrder
  | hlambda binder body inductionHypothesis =>
      have bodySafe : binderSafeAt rhoReflectivePresentation.quoteConstructor
          (safetyDepth + 1) body = true := by
        simpa [binderSafeAt] using safe
      simp only [canonicalizeByDepths, Pattern.lambda.injEq, true_and]
      exact inductionHypothesis _ _ _
        (by
          intro name nameMembership slot selected
          exact supportNil name (by
            simpa only [Pattern.freeFvarNames] using nameMembership) slot
              selected)
        bodySafe
        (Nat.add_le_add_right depthOrder 1)
  | hmultiLambda arity binders body inductionHypothesis =>
      have bodySafe : binderSafeAt rhoReflectivePresentation.quoteConstructor
          (safetyDepth + arity) body = true := by
        simpa [binderSafeAt] using safe
      simp only [canonicalizeByDepths, Pattern.multiLambda.injEq, true_and]
      exact inductionHypothesis _ _ _
        (by
          intro name nameMembership slot selected
          exact supportNil name (by
            simpa only [Pattern.freeFvarNames] using nameMembership) slot
              selected)
        bodySafe
        (Nat.add_le_add_right depthOrder arity)
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      simp only [binderSafeAt, Bool.and_eq_true] at safe
      simp only [canonicalizeByDepths, Pattern.subst.injEq]
      exact ⟨
        bodyHypothesis _ _ _ (by
          intro name nameMembership slot selected
          apply supportNil name
          · simp [Pattern.freeFvarNames, nameMembership]
          · exact selected) safe.1
          (Nat.add_le_add_right depthOrder 1),
        replacementHypothesis _ _ _ (by
          intro name nameMembership slot selected
          apply supportNil name
          · simp [Pattern.freeFvarNames, nameMembership]
          · exact selected) safe.2 depthOrder⟩
  | hcollection collectionType elements rest inductionHypothesis =>
      have elementsSafe : binderSafeListAt
          rhoReflectivePresentation.quoteConstructor safetyDepth elements =
            true := by
        simpa [binderSafeAt] using safe
      have normalizedElementsEq :
          canonicalizeListByDepths
              (sourceSemanticPatternKeyAt node environment)
              rhoReflectivePresentation availableDepth scopeDepth elements =
            canonicalizeListByDepths
              (fun _ _ pattern =>
                Mettapedia.GSLT.LanguageDef.CostStaticRegionNode.semanticPatternKeyAt
                  environment 0
                    (mapPattern (color.symbols rhoCIGSLT) pattern))
              rhoReflectivePresentation availableDepth scopeDepth elements := by
        rw [canonicalizeListByDepths_eq_map,
          canonicalizeListByDepths_eq_map]
        apply List.map_congr_left
        intro element membership
        exact inductionHypothesis element membership _ _ _
          (by
            intro name nameMembership slot selected
            apply supportNil name
            · simp only [Pattern.freeFvarNames, List.mem_append,
                List.mem_flatMap]
              exact Or.inl ⟨element, membership, nameMembership⟩
            · exact selected)
          ((binderSafeListAt_eq_true_iff _ _ _).mp elementsSafe element
            membership) depthOrder
      have normalizedElementsSafe : binderSafeListAt
          rhoReflectivePresentation.quoteConstructor safetyDepth
          (canonicalizeListByDepths
            (sourceSemanticPatternKeyAt node environment)
            rhoReflectivePresentation availableDepth scopeDepth elements) =
            true := by
        rw [canonicalizeListByDepths_eq_map,
          binderSafeListAt_eq_true_iff]
        intro normalizedElement normalizedMembership
        rw [List.mem_map] at normalizedMembership
        obtain ⟨element, membership, rfl⟩ := normalizedMembership
        exact canonicalizeByDepths_binderSafeAt
          (sourceSemanticPatternKeyAt node environment)
          rhoReflectivePresentation rhoReflectivePresentation.quoteConstructor
          availableDepth scopeDepth safetyDepth element
          ((binderSafeListAt_eq_true_iff _ _ _).mp elementsSafe element
            membership)
      have stableNormalizedElementsSafe : binderSafeListAt
          rhoReflectivePresentation.quoteConstructor safetyDepth
          (canonicalizeListByDepths
            (fun _ _ pattern =>
              Mettapedia.GSLT.LanguageDef.CostStaticRegionNode.semanticPatternKeyAt
                environment 0 (mapPattern (color.symbols rhoCIGSLT) pattern))
            rhoReflectivePresentation availableDepth scopeDepth elements) =
              true := by
        rw [← normalizedElementsEq]
        exact normalizedElementsSafe
      cases rest with
      | some restName =>
          simpa [canonicalizeByDepths] using normalizedElementsEq
      | none =>
          by_cases parallel :
              collectionType = rhoReflectivePresentation.parallelCollection
          · subst collectionType
            simp only [canonicalizeByDepths, beq_self_eq_true, if_true]
            rw [normalizedElementsEq]
            apply congrArg (collapseParallel rhoReflectivePresentation)
            unfold normalizeParallelElementsBy
            apply CostStaticAtomKeyCospan.sortPatternsBy_eq_of_keys_eq_on
            intro member memberMembership
            have retainedMembership := List.mem_of_mem_filter memberMembership
            rw [List.mem_flatMap] at retainedMembership
            obtain ⟨sourcePattern, sourceMembership, memberSource⟩ :=
              retainedMembership
            have sourceSafe :=
              (binderSafeListAt_eq_true_iff _ _ _).mp
                stableNormalizedElementsSafe sourcePattern sourceMembership
            have memberSafe : binderSafeAt
                rhoReflectivePresentation.quoteConstructor safetyDepth
                member = true := by
              exact (binderSafeListAt_eq_true_iff _ _ _).mp
                (parallelSplice_binderSafeListAt rhoReflectivePresentation
                  rhoReflectivePresentation.quoteConstructor safetyDepth
                    sourceSafe) member memberSource
            have memberSupport : ∀ name,
                name ∈ member.freeFvarNames →
                ∀ slot, environment.lookupAtom? name = some slot →
                  (environment.atomValue slot).key.targetSupport = [] := by
              intro name nameMembership slot selected
              apply supportNil name
              · simp only [Pattern.freeFvarNames, Option.toList_none,
                  List.append_nil, List.mem_flatMap]
                have spliceMembership : name ∈
                    (parallelSplice rhoReflectivePresentation sourcePattern
                      ).flatMap Pattern.freeFvarNames :=
                  List.mem_flatMap.mpr
                    ⟨member, memberSource, nameMembership⟩
                have sourceNameMembership :
                    name ∈ sourcePattern.freeFvarNames :=
                  (mem_flatMap_freeFvarNames_parallelSplice_iff
                    rhoReflectivePresentation name sourcePattern).mp
                      spliceMembership
                rw [canonicalizeListByDepths_eq_map] at sourceMembership
                obtain ⟨element, elementMembership, sourcePatternEq⟩ :=
                  List.mem_map.mp sourceMembership
                subst sourcePattern
                have elementNameMembership :=
                  (CostStaticAtomKeyCospan.mem_freeFvarNames_canonicalizeByDepths_iff
                    (fun _ _ pattern =>
                      Mettapedia.GSLT.LanguageDef.CostStaticRegionNode.semanticPatternKeyAt
                        environment 0
                          (mapPattern (color.symbols rhoCIGSLT) pattern))
                    rhoReflectivePresentation name availableDepth scopeDepth
                    element).mp sourceNameMembership
                exact ⟨element, elementMembership, elementNameMembership⟩
              · exact selected
            exact
              Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionNode.sourceSemanticPatternKeyAt_eq_of_freeAtomTargetSupport_eq_nil
                node environment availableDepth scopeDepth member memberSupport
                  memberSafe depthOrder
          · have notParallel :
                (collectionType ==
                  rhoReflectivePresentation.parallelCollection) = false :=
              beq_eq_false_iff_ne.mpr parallel
            simpa [canonicalizeByDepths, notParallel] using
              congrArg
                (fun normalized =>
                  Pattern.collection collectionType normalized none)
                normalizedElementsEq

/-- Global sealed-environment specialization of local-support keyed
canonicalization invariance. -/
theorem CostStaticRegionNode.canonicalizeByDepths_sourceSemanticPatternKeyAt_eq_of_atomTargetSupport_eq_nil
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    (supportNil : ∀ slot,
      (environment.atomValue slot).key.targetSupport = []) :
    ∀ (availableDepth scopeDepth safetyDepth : Nat) (pattern : Pattern),
      binderSafeAt rhoReflectivePresentation.quoteConstructor safetyDepth
          pattern = true →
      safetyDepth ≤ scopeDepth →
      canonicalizeByDepths (sourceSemanticPatternKeyAt node environment)
          rhoReflectivePresentation availableDepth scopeDepth pattern =
        canonicalizeByDepths
          (fun _ _ pattern =>
            Mettapedia.GSLT.LanguageDef.CostStaticRegionNode.semanticPatternKeyAt
              environment 0 (mapPattern (color.symbols rhoCIGSLT) pattern))
          rhoReflectivePresentation availableDepth scopeDepth pattern := by
  intro availableDepth scopeDepth safetyDepth pattern safe depthOrder
  apply
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionNode.canonicalizeByDepths_sourceSemanticPatternKeyAt_eq_of_freeAtomTargetSupport_eq_nil
      node environment availableDepth scopeDepth safetyDepth pattern
  · intro name membership slot selected
    exact supportNil slot
  · exact safe
  · exact depthOrder

/-- Embedding a singleton reached boundary into its parent plan rules out
intermediate availability prefixes: the reached plan is either fully exposed
to the parent's ambient target context or sealed below Quote. -/
theorem CostStaticPlanReached.BoundaryView.sourceAvailable_eq_parentTargetBound_or_nil
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {payload rootAbstract : Pattern}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (reached : CostStaticPlanReached rhoCIGSLT color targetFree payload
      rootAbstract)
    (view : reached.BoundaryView)
    (embedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      reached.plan.boundaryTable.entries node.plan.boundaryTable.entries) :
    reached.sourceAvailable = node.targetBound ∨
      reached.sourceAvailable = [] := by
  have member : view.stopped.certified.typed ∈
      node.plan.boundaryTable.entries :=
    embedding.subset (by
      rw [view.entries_eq]
      simp)
  have support :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionNode.boundaryTargetSupport_eq_targetBound_or_nil
      node view.stopped.certified.typed member
  simpa only [view.targetSupport_eq] using support

/-! ## Shape of a rigid partner -/

/-- **The rigid reached root class has four inhabitants, not two.**

`CostStaticRegionPlan.rootClass` sends the bound-variable plan, the authored
source-variable plan *and both binder plans* to `.rigid`.  A rigid partner is
therefore a bound variable, a source variable, a lambda or a multi-lambda,
and only the second of these abstracts to a free variable. -/
theorem CostStaticRegionPlan.rigid_cases
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    (rigid : plan.rootClass = .rigid) :
    (∃ index sourceIndex, pattern = .bvar index ∧
        plan.abstractPattern = .bvar sourceIndex) ∨
      (∃ name, pattern = .fvar name ∧
        plan.abstractPattern = .fvar (costRegionSourceVariableName name) ∧
        targetFree name =
          some (mapTypeExpr (color.symbols source) sourceType)) ∨
      (∃ binder body abstractBody, pattern = .lambda binder body ∧
        plan.abstractPattern = .lambda binder abstractBody) ∨
      (∃ arity binders body abstractBody,
        pattern = .multiLambda arity binders body ∧
        plan.abstractPattern = .multiLambda arity binders abstractBody) := by
  cases plan
  case bvar sourceIndex lookup correspondence availableScope =>
      exact Or.inl ⟨_, sourceIndex, rfl, rfl⟩
  case fvar lookup => exact Or.inr (Or.inl ⟨_, rfl, rfl, lookup⟩)
  case lambda bodyPlan => exact Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl, rfl⟩))
  case multiLambda bodyPlan =>
      exact Or.inr (Or.inr (Or.inr ⟨_, _, _, _, rfl, rfl⟩))
  all_goals simp [CostStaticRegionPlan.rootClass] at rigid

/-- The rigid-root classification with the source type retained in the two
binder cases.  This is the form needed when a partner's certified-boundary
type rules out arrows. -/
theorem CostStaticRegionPlan.rigid_cases_typed
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    (rigid : plan.rootClass = .rigid) :
    (∃ index sourceIndex, pattern = .bvar index ∧
        plan.abstractPattern = .bvar sourceIndex) ∨
      (∃ name, pattern = .fvar name ∧
        plan.abstractPattern = .fvar (costRegionSourceVariableName name) ∧
        targetFree name =
          some (mapTypeExpr (color.symbols source) sourceType)) ∨
      (∃ binder body abstractBody domain codomain,
        pattern = .lambda binder body ∧
        plan.abstractPattern = .lambda binder abstractBody ∧
        sourceType = .arrow domain codomain) ∨
      (∃ arity binders body abstractBody domain codomain,
        pattern = .multiLambda arity binders body ∧
        plan.abstractPattern = .multiLambda arity binders abstractBody ∧
        sourceType = .arrow (.multiBinder domain) codomain) := by
  cases plan
  case bvar sourceIndex lookup correspondence availableScope =>
      exact Or.inl ⟨_, sourceIndex, rfl, rfl⟩
  case fvar lookup => exact Or.inr (Or.inl ⟨_, rfl, rfl, lookup⟩)
  case lambda bodyPlan =>
      exact Or.inr (Or.inr (Or.inl ⟨_, _, _, _, _, rfl, rfl, rfl⟩))
  case multiLambda bodyPlan =>
      exact Or.inr (Or.inr (Or.inr
        ⟨_, _, _, _, _, _, rfl, rfl, rfl⟩))
  all_goals simp [CostStaticRegionPlan.rootClass] at rigid

/-- A certified boundary plan cannot inhabit an authored arrow fibre.

Application boundaries are certified at a base target type.  Collection
boundaries are certified at either a collection or a base target type.  Since
the Cost colour map preserves the outer constructor of a type expression,
neither case can be the image of an arrow.  This excludes both binder-plan
partners from the boundary-side residual by typing, before any semantic
restoration argument is needed. -/
theorem CostStaticRegionPlan.sourceType_ne_arrow_of_isCertifiedBoundary
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr}
    {outer : OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    (boundary : plan.rootClass.IsCertifiedBoundary) :
    ∀ domain codomain, sourceType ≠ .arrow domain codomain := by
  intro domain codomain sourceTypeEq
  cases plan with
  | boundaryApplication constructor rendered outsideCurrent certified certifies =>
      obtain ⟨category, targetTypeEq⟩ :=
        certified.exists_targetType_eq_base_of_application
      have mappedEq : mapTypeExpr (color.symbols source)
            (.arrow domain codomain) = .base category := by
        rw [← sourceTypeEq]
        exact certified.targetType_eq.symm.trans targetTypeEq
      exact TypeExpr.noConfusion mappedEq
  | boundaryCollection currentRejected oppositeChoice oppositeSelected
      certified certifies =>
      rename_i collectionType elements rest
      rcases certified.targetType_collection_or_base_of_collection with
        ⟨elementType, targetTypeEq⟩ | ⟨category, targetTypeEq⟩
      · have mappedEq : mapTypeExpr (color.symbols source)
              (.arrow domain codomain) =
            .collection collectionType elementType := by
          rw [← sourceTypeEq]
          exact certified.targetType_eq.symm.trans targetTypeEq
        exact TypeExpr.noConfusion mappedEq
      · have mappedEq : mapTypeExpr (color.symbols source)
              (.arrow domain codomain) = .base category := by
          rw [← sourceTypeEq]
          exact certified.targetType_eq.symm.trans targetTypeEq
        exact TypeExpr.noConfusion mappedEq
  | bvar | fvar | application | lambda | multiLambda | collection =>
      simp [CostStaticRegionPlan.rootClass,
        CostStaticPlanRootClass.IsCertifiedBoundary] at boundary

/-- **A certified boundary facing a rigid root is always a delegated stop.**

`CostStaticPlanStopEligible` has no shape pairing a certified boundary with a
rigid root, so the residual's stop reason must be the raw stop.  The recursive
closure callback is therefore available throughout the rigid slice of family
1, at either measure. -/
theorem rho_planStop_boundarySide_rigid_rawStop
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {leftPayload rightPayload leftRootAbstract rightRootAbstract : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftRootAbstract)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightRootAbstract)
    {rawStop : Pattern → Pattern → Prop}
    (leftBoundary : leftReached.plan.rootClass.IsCertifiedBoundary)
    (rightRigid : rightReached.plan.rootClass = .rigid)
    (stopReason : rawStop leftPayload rightPayload ∨
      CostStaticPlanStopEligible rhoReflectivePresentation leftReached.plan
        rightReached.plan) :
    rawStop leftPayload rightPayload := by
  rcases stopReason with stopped | eligible
  · exact stopped
  · rcases leftBoundary with boundaryClass | boundaryClass <;>
      simp [CostStaticPlanStopEligible, boundaryClass, rightRigid] at eligible

/-- Mirror of `rho_planStop_boundarySide_rigid_rawStop`. -/
theorem rho_planStop_rigid_boundarySide_rawStop
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {leftPayload rightPayload leftRootAbstract rightRootAbstract : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftRootAbstract)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightRootAbstract)
    {rawStop : Pattern → Pattern → Prop}
    (leftRigid : leftReached.plan.rootClass = .rigid)
    (rightBoundary : rightReached.plan.rootClass.IsCertifiedBoundary)
    (stopReason : rawStop leftPayload rightPayload ∨
      CostStaticPlanStopEligible rhoReflectivePresentation leftReached.plan
        rightReached.plan) :
    rawStop leftPayload rightPayload := by
  rcases stopReason with stopped | eligible
  · exact stopped
  · rcases rightBoundary with boundaryClass | boundaryClass <;>
      simp [CostStaticPlanStopEligible, boundaryClass, leftRigid] at eligible

/-! ## The bound-variable partner is refuted, not merely open -/

/-- **The certified-boundary/bound-variable sub-cell of family 1 is refuted at
its own conclusion.**

A certified-boundary endpoint abstracts to a single free variable, and both
reification and keyed canonicalization leave it free; a bound-variable plan
abstracts to a bound index that every stage of the same pipeline leaves
bound.  `PatternLeafAligned` therefore has only its `leaf` constructor here,
and the depth-uniform restoration relation excludes exactly that pair.

The later full-telescope contradiction theorems show that this false
conclusion is never demanded by an actual plan stop. -/
theorem not_boundarySide_bvarPartner_sourcePatternLeafAligned
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (leftNode rightNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      rightOccurrences}
    {leftValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree leftTable}
    {rightValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree rightTable}
    {leftRoot rightRoot : Pattern}
    {leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftTable leftValues leftRoot}
    {rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightTable rightValues rightRoot}
    (leftEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      rightInventory)
    {Key : Type} [LinearOrder Key]
    (leftKey rightKey : Nat → Nat → Pattern → Key)
    (availableDepth scopeDepth : Nat)
    (boundaryName : String) (index : Nat) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    let relation : Pattern → Pattern → Prop := fun leftLeaf rightLeaf =>
      ∀ sourceDepth,
        ReflectiveContextSupport.RestoresTogether
          rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
            cospan.commonAssignment
            (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
              (leftNode.thinning.thickenAmbientBVars sourceDepth
                (mapPattern (color.symbols rhoCIGSLT) leftLeaf)))
            (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
              (rightNode.thinning.thickenAmbientBVars sourceDepth
                (mapPattern (color.symbols rhoCIGSLT) rightLeaf)))
    ¬ PatternLeafAligned relation
      (canonicalizeByDepths leftKey rhoReflectivePresentation availableDepth
        scopeDepth (leftEnvironment.reify (.fvar boundaryName)))
      (canonicalizeByDepths rightKey rhoReflectivePresentation availableDepth
        scopeDepth (rightEnvironment.reify (.bvar index))) := by
  intro cospan relation aligned
  simp only [CostStaticAtomEnvironment.reify, canonicalizeByDepths] at aligned
  cases aligned with
  | leaf related =>
      exact CostStaticAtomKeyCospan.not_restoresTogether_transported_fvar_bvar
        cospan rhoCIGSLT.costWholeReflectionProfile
        leftEnvironment.lookupAtom? cospan.leftSlot
        rightEnvironment.lookupAtom? cospan.rightSlot leftNode.thinning
        rightNode.thinning 0 _ index (related 0)

/-- Mirror of `not_boundarySide_bvarPartner_sourcePatternLeafAligned`. -/
theorem not_bvarPartner_boundarySide_sourcePatternLeafAligned
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (leftNode rightNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      rightOccurrences}
    {leftValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree leftTable}
    {rightValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree rightTable}
    {leftRoot rightRoot : Pattern}
    {leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftTable leftValues leftRoot}
    {rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightTable rightValues rightRoot}
    (leftEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      rightInventory)
    {Key : Type} [LinearOrder Key]
    (leftKey rightKey : Nat → Nat → Pattern → Key)
    (availableDepth scopeDepth : Nat)
    (index : Nat) (boundaryName : String) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    let relation : Pattern → Pattern → Prop := fun leftLeaf rightLeaf =>
      ∀ sourceDepth,
        ReflectiveContextSupport.RestoresTogether
          rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
            cospan.commonAssignment
            (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
              (leftNode.thinning.thickenAmbientBVars sourceDepth
                (mapPattern (color.symbols rhoCIGSLT) leftLeaf)))
            (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
              (rightNode.thinning.thickenAmbientBVars sourceDepth
                (mapPattern (color.symbols rhoCIGSLT) rightLeaf)))
    ¬ PatternLeafAligned relation
      (canonicalizeByDepths leftKey rhoReflectivePresentation availableDepth
        scopeDepth (leftEnvironment.reify (.bvar index)))
      (canonicalizeByDepths rightKey rhoReflectivePresentation availableDepth
        scopeDepth (rightEnvironment.reify (.fvar boundaryName))) := by
  intro cospan relation aligned
  simp only [CostStaticAtomEnvironment.reify, canonicalizeByDepths] at aligned
  cases aligned with
  | leaf related =>
      exact CostStaticAtomKeyCospan.not_restoresTogether_transported_bvar_fvar
        cospan rhoCIGSLT.costWholeReflectionProfile
        leftEnvironment.lookupAtom? cospan.leftSlot
        rightEnvironment.lookupAtom? cospan.rightSlot leftNode.thinning
        rightNode.thinning 0 index _ (related 0)

/-- **Exactly what the refuted sub-cell reduces to.**

A certified boundary facing a bound-variable plan forces the delegated raw
stop, and that stop carries canonical equality of the two payloads.  So the
configuration occurs only when a *certified boundary payload canonicalizes to
a bare bound variable*.

This is the emptiness obligation family 1 now owes: discharge it and family 1
is re-cut legitimately; leave it and family 1 is false.  It is not discharged
by any syntactic argument about `canonicalize` alone, because both of rho's
root-changing rules — quote/drop contraction and parallel collapse — can
produce a bare bound variable from a compound root. -/
theorem rho_planStop_boundarySide_bvarPartner_canonicalize_eq_bvar
    {declarationColor color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftPayload rightPayload leftRootAbstract rightRootAbstract : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftRootAbstract)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightRootAbstract)
    {parentMeasure : Nat}
    (leftBoundaryClass : leftReached.plan.rootClass.IsCertifiedBoundary)
    (rightRigid : rightReached.plan.rootClass = .rigid)
    (rightAbstractBVar : ∃ index,
      rightReached.plan.abstractPattern = .bvar index)
    (stopReason :
      RhoCanonicalRawStop declarationColor parentMeasure leftPayload
          rightPayload ∨
        CostStaticPlanStopEligible rhoReflectivePresentation leftReached.plan
          rightReached.plan) :
    ∃ index, canonicalize
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation) leftPayload = .bvar index := by
  have stopped := rho_planStop_boundarySide_rigid_rawStop leftReached
    rightReached leftBoundaryClass rightRigid stopReason
  obtain ⟨abstractIndex, abstractEq⟩ := rightAbstractBVar
  rcases CostStaticRegionPlan.rigid_cases rightReached.plan rightRigid with
    ⟨index, sourceIndex, payloadEq, _⟩ | ⟨name, _, absEq, _⟩ |
    ⟨binder, body, abstractBody, _, absEq⟩ |
    ⟨arity, binders, body, abstractBody, _, absEq⟩
  · exact ⟨index, by rw [stopped.1.2, payloadEq, canonicalize]⟩
  · rw [absEq] at abstractEq; exact absurd abstractEq (by simp)
  · rw [absEq] at abstractEq; exact absurd abstractEq (by simp)
  · rw [absEq] at abstractEq; exact absurd abstractEq (by simp)

/-- Mirror of
`rho_planStop_boundarySide_bvarPartner_canonicalize_eq_bvar`. -/
theorem rho_planStop_bvarPartner_boundarySide_canonicalize_eq_bvar
    {declarationColor color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftPayload rightPayload leftRootAbstract rightRootAbstract : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftRootAbstract)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightRootAbstract)
    {parentMeasure : Nat}
    (leftRigid : leftReached.plan.rootClass = .rigid)
    (leftAbstractBVar : ∃ index,
      leftReached.plan.abstractPattern = .bvar index)
    (rightBoundaryClass : rightReached.plan.rootClass.IsCertifiedBoundary)
    (stopReason :
      RhoCanonicalRawStop declarationColor parentMeasure leftPayload
          rightPayload ∨
        CostStaticPlanStopEligible rhoReflectivePresentation leftReached.plan
          rightReached.plan) :
    ∃ index, canonicalize
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation) rightPayload = .bvar index := by
  have stopped := rho_planStop_rigid_boundarySide_rawStop leftReached
    rightReached leftRigid rightBoundaryClass stopReason
  obtain ⟨abstractIndex, abstractEq⟩ := leftAbstractBVar
  rcases CostStaticRegionPlan.rigid_cases leftReached.plan leftRigid with
    ⟨index, sourceIndex, payloadEq, _⟩ | ⟨name, _, absEq, _⟩ |
    ⟨binder, body, abstractBody, _, absEq⟩ |
    ⟨arity, binders, body, abstractBody, _, absEq⟩
  · exact ⟨index, by rw [← stopped.1.2, payloadEq, canonicalize]⟩
  · rw [absEq] at abstractEq; exact absurd abstractEq (by simp)
  · rw [absEq] at abstractEq; exact absurd abstractEq (by simp)
  · rw [absEq] at abstractEq; exact absurd abstractEq (by simp)

/-- A certified boundary cannot face a reached bound-variable plan in the
rho residual.  The raw stop would force the certified boundary payload to
canonicalize to a bound variable, contradicting its quote-aware scope
certificate (and the impossible foreign-collection branch). -/
theorem rho_planStop_boundarySide_bvarPartner_absurd
    {declarationColor color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftPayload rightPayload leftRootAbstract rightRootAbstract : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftRootAbstract)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightRootAbstract)
    {parentMeasure : Nat}
    (leftBoundaryClass : leftReached.plan.rootClass.IsCertifiedBoundary)
    (rightRigid : rightReached.plan.rootClass = .rigid)
    (rightAbstractBVar : ∃ index,
      rightReached.plan.abstractPattern = .bvar index)
    (stopReason :
      RhoCanonicalRawStop declarationColor parentMeasure leftPayload
          rightPayload ∨
        CostStaticPlanStopEligible rhoReflectivePresentation leftReached.plan
          rightReached.plan) : False := by
  obtain ⟨index, canonical⟩ :=
    rho_planStop_boundarySide_bvarPartner_canonicalize_eq_bvar leftReached
      rightReached leftBoundaryClass rightRigid rightAbstractBVar stopReason
  exact rho_boundaryPlan_canonicalize_ne_bvar leftReached.plan
    leftBoundaryClass index canonical

/-- Mirror of `rho_planStop_boundarySide_bvarPartner_absurd`. -/
theorem rho_planStop_bvarPartner_boundarySide_absurd
    {declarationColor color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftPayload rightPayload leftRootAbstract rightRootAbstract : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftRootAbstract)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightRootAbstract)
    {parentMeasure : Nat}
    (leftRigid : leftReached.plan.rootClass = .rigid)
    (leftAbstractBVar : ∃ index,
      leftReached.plan.abstractPattern = .bvar index)
    (rightBoundaryClass : rightReached.plan.rootClass.IsCertifiedBoundary)
    (stopReason :
      RhoCanonicalRawStop declarationColor parentMeasure leftPayload
          rightPayload ∨
        CostStaticPlanStopEligible rhoReflectivePresentation leftReached.plan
          rightReached.plan) : False := by
  obtain ⟨index, canonical⟩ :=
    rho_planStop_bvarPartner_boundarySide_canonicalize_eq_bvar leftReached
      rightReached leftRigid leftAbstractBVar rightBoundaryClass stopReason
  exact rho_boundaryPlan_canonicalize_ne_bvar rightReached.plan
    rightBoundaryClass index canonical

/-- A rigid plan opposite a certified boundary is necessarily an authored
source variable.  Bound variables are excluded by reflective scope, while
both binder forms are excluded by the common source type. -/
theorem boundarySide_rigidPartner_is_sourceVariable
    {declarationColor color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {leftPayload rightPayload leftRootAbstract rightRootAbstract : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftRootAbstract)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree rightPayload
      rightRootAbstract)
    {parentMeasure : Nat}
    (sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
    (leftBoundary : leftReached.plan.rootClass.IsCertifiedBoundary)
    (rightRigid : rightReached.plan.rootClass = .rigid)
    (stopReason :
      RhoCanonicalRawStop declarationColor parentMeasure leftPayload
          rightPayload ∨
        CostStaticPlanStopEligible rhoReflectivePresentation leftReached.plan
          rightReached.plan) :
    ∃ name,
      rightPayload = .fvar name ∧
      rightReached.plan.abstractPattern =
        .fvar (costRegionSourceVariableName name) ∧
      targetFree name = some
        (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType) := by
  rcases CostStaticRegionPlan.rigid_cases_typed rightReached.plan rightRigid with
    ⟨index, sourceIndex, payloadEq, abstractEq⟩ |
    ⟨name, payloadEq, abstractEq, lookup⟩ |
    ⟨binder, body, abstractBody, domain, codomain, payloadEq, abstractEq,
      rightTypeEq⟩ |
    ⟨arity, binders, body, abstractBody, domain, codomain, payloadEq,
      abstractEq, rightTypeEq⟩
  · exact (rho_planStop_boundarySide_bvarPartner_absurd leftReached
      rightReached leftBoundary rightRigid ⟨sourceIndex, abstractEq⟩
      stopReason).elim
  · exact ⟨name, payloadEq, abstractEq, lookup⟩
  · exact (CostStaticRegionPlan.sourceType_ne_arrow_of_isCertifiedBoundary
      leftReached.plan leftBoundary domain codomain
        (sourceTypeEq.trans rightTypeEq)).elim
  · exact (CostStaticRegionPlan.sourceType_ne_arrow_of_isCertifiedBoundary
      leftReached.plan leftBoundary (.multiBinder domain) codomain
        (sourceTypeEq.trans rightTypeEq)).elim

/-- Mirror of `boundarySide_rigidPartner_is_sourceVariable`. -/
theorem rigidPartner_boundarySide_is_sourceVariable
    {declarationColor color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {leftPayload rightPayload leftRootAbstract rightRootAbstract : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftRootAbstract)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree rightPayload
      rightRootAbstract)
    {parentMeasure : Nat}
    (sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
    (leftRigid : leftReached.plan.rootClass = .rigid)
    (rightBoundary : rightReached.plan.rootClass.IsCertifiedBoundary)
    (stopReason :
      RhoCanonicalRawStop declarationColor parentMeasure leftPayload
          rightPayload ∨
        CostStaticPlanStopEligible rhoReflectivePresentation leftReached.plan
          rightReached.plan) :
    ∃ name,
      leftPayload = .fvar name ∧
      leftReached.plan.abstractPattern =
        .fvar (costRegionSourceVariableName name) ∧
      targetFree name = some
        (mapTypeExpr (color.symbols rhoCIGSLT) leftReached.sourceType) := by
  rcases CostStaticRegionPlan.rigid_cases_typed leftReached.plan leftRigid with
    ⟨index, sourceIndex, payloadEq, abstractEq⟩ |
    ⟨name, payloadEq, abstractEq, lookup⟩ |
    ⟨binder, body, abstractBody, domain, codomain, payloadEq, abstractEq,
      leftTypeEq⟩ |
    ⟨arity, binders, body, abstractBody, domain, codomain, payloadEq,
      abstractEq, leftTypeEq⟩
  · exact (rho_planStop_bvarPartner_boundarySide_absurd leftReached
      rightReached leftRigid ⟨sourceIndex, abstractEq⟩ rightBoundary
      stopReason).elim
  · exact ⟨name, payloadEq, abstractEq, lookup⟩
  · exact (CostStaticRegionPlan.sourceType_ne_arrow_of_isCertifiedBoundary
      rightReached.plan rightBoundary domain codomain
        (sourceTypeEq.symm.trans leftTypeEq)).elim
  · exact (CostStaticRegionPlan.sourceType_ne_arrow_of_isCertifiedBoundary
      rightReached.plan rightBoundary (.multiBinder domain) codomain
        (sourceTypeEq.symm.trans leftTypeEq)).elim

/-- Positive control for
`rho_planStop_boundarySide_bvarPartner_canonicalize_eq_bvar`: rho's parallel
collapse does send a compound root to a bare bound variable, at both
colours.  The emptiness obligation is therefore not discharged by any
syntactic argument about `canonicalize` alone. -/
theorem canonicalize_rhoParallel_singleton_bvar
    (declarationColor : CostStaticColor) (index : Nat) :
    canonicalize
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation)
      (.collection
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation).parallelCollection
        [.bvar index] none) = .bvar index := by
  rw [canonicalize_parallel_singleton, canonicalize]

/-- Second positive control: rho's quote/drop contraction is also available
at both colours, so an application root can collapse to a bare bound variable
too. -/
theorem canonicalize_rhoQuoteDrop_bvar
    (declarationColor : CostStaticColor) (index : Nat) :
    canonicalize
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation)
      (.apply
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation).quoteConstructor
        [.apply
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation).dropConstructor [.bvar index]]) =
      .bvar index := by
  rw [canonicalize_quote_drop _ (by cases declarationColor <;> decide),
    canonicalize]

/-! ## Depth-polymorphic collapse of a stopped plan context -/

/-- The environment used to reify a stopped abstract may belong to a larger
parent inventory.  Only the stopped factorization and the selected spelling
are needed to transfer an ordinary source collapse to arbitrary keyed depths. -/
theorem CostStaticPlanStopped.canonicalizeByDepths_environmentReify_abstract_eq_fvar
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      table}
    {environmentRoot : Pattern}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      table values environmentRoot}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    {payload rootAbstract : Pattern}
    (state : CostStaticPlanStopped rhoCIGSLT color targetFree payload
      rootAbstract)
    (slot : Fin environment.atomCount)
    (selected : environment.slotOfName? state.boundaryOccurrence.name =
      some slot)
    (collapse : canonicalize
        rhoReflectivePresentation.toReflectivePresentationDecl
        (state.skeletonContext.fill (.fvar state.boundaryOccurrence.name)) =
      .fvar state.boundaryOccurrence.name)
    {Key : Type} [LinearOrder Key]
    (key : Nat → Nat → Pattern → Key)
    (availableDepth scopeDepth : Nat) :
    canonicalizeByDepths key rhoReflectivePresentation availableDepth scopeDepth
        (environment.reify rootAbstract) =
      .fvar (environment.atomName slot) := by
  let declaration := rhoReflectivePresentation.toReflectivePresentationDecl
  have frameFree : contextFrameFreeFvarNames state.skeletonContext = [] :=
    contextFrameFreeFvarNames_eq_nil_of_collapse declaration collapse
  have reifiedContext :
      environment.reifyContext state.skeletonContext = state.skeletonContext :=
    CostStaticAtomEnvironment.reifyContext_eq_self_of_frameFreeFvarNames_eq_nil
      environment state.skeletonContext frameFree
  have reifiedFrame : environment.reify rootAbstract =
      state.skeletonContext.fill (.fvar (environment.atomName slot)) := by
    calc
      environment.reify rootAbstract =
          environment.reify
            (state.skeletonContext.fill
              (.fvar state.boundaryOccurrence.name)) :=
        congrArg environment.reify state.abstract_eq
      _ = (environment.reifyContext state.skeletonContext).fill
          (environment.reify (.fvar state.boundaryOccurrence.name)) :=
        (environment.reifyContext_fill state.skeletonContext _).symm
      _ = state.skeletonContext.fill
          (.fvar (environment.atomName slot)) := by
        rw [reifiedContext]
        simp only [CostStaticAtomEnvironment.reify]
        unfold CostStaticAtomEnvironment.reifyName
        rw [selected]
  have ordinaryCollapse : canonicalize declaration
        (state.skeletonContext.fill (.fvar (environment.atomName slot))) =
      .fvar (environment.atomName slot) := by
    simpa [declaration, canonicalize] using
      canonicalize_fill_eq_of_collapse declaration (by decide) collapse
        (.fvar (environment.atomName slot))
  rw [reifiedFrame]
  exact canonicalizeByDepths_eq_fvar_of_canonicalize_eq key declaration
    availableDepth scopeDepth ordinaryCollapse

/-- A stopped occurrence whose surrounding source context canonically
evaporates is its selected semantic atom for every pair of keyed
canonicalization depths.

This is the source-plan form of
`CostStaticRegionNode.stopped_collapse_canonicalFrame`.  Keeping the two depths
arbitrary is essential in the foreign-declaration residual: the plan-stop
callback chooses them independently, while the stopped occurrence and its
position in the parent environment remain fixed. -/
theorem CostStaticPlanStopped.canonicalizeByDepths_environmentReify_root_eq_fvar
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    {payload : Pattern}
    (state : CostStaticPlanStopped rhoCIGSLT color targetFree payload
      node.skeleton.1)
    (slot : Fin environment.atomCount)
    (selected : environment.slotOfName? state.boundaryOccurrence.name =
      some slot)
    (collapse : canonicalize
        rhoReflectivePresentation.toReflectivePresentationDecl
        (state.skeletonContext.fill (.fvar state.boundaryOccurrence.name)) =
      .fvar state.boundaryOccurrence.name)
    {Key : Type} [LinearOrder Key]
    (key : Nat → Nat → Pattern → Key)
    (availableDepth scopeDepth : Nat) :
    canonicalizeByDepths key rhoReflectivePresentation availableDepth scopeDepth
        (environment.reify node.skeleton.1) =
      .fvar (environment.atomName slot) := by
  exact
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanStopped.canonicalizeByDepths_environmentReify_abstract_eq_fvar
      environment state slot selected collapse key availableDepth scopeDepth

/-! ## Two stopped contributors under the positional support regimes -/

/-- Two stopped plan contexts which both canonically expose their selected
boundary occurrence form one source-aligned semantic leaf whenever their
supports are equal or either occurrence is quote-sealed.

The three support cases are exactly the interface of the existing recursive
leaf closure.  This adapter only transfers the two ordinary source-context
collapses through endpoint reification and keyed canonicalization. -/
noncomputable def stoppedPair_sourcePatternLeafAligned_of_closeSmaller
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (leftNode rightNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (leftTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      leftNode.finiteBoundaryTable)
    (rightTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      rightNode.finiteBoundaryTable)
    {leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftNode.boundaryTable
      (leftTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      leftNode.skeleton.1}
    {rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightNode.boundaryTable
      (rightTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      rightNode.skeleton.1}
    (leftEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      rightInventory)
    {leftPayload rightPayload leftRootAbstract rightRootAbstract : Pattern}
    (leftStopped : CostStaticPlanStopped rhoCIGSLT color targetFree leftPayload
      leftRootAbstract)
    (rightStopped : CostStaticPlanStopped rhoCIGSLT color targetFree
      rightPayload rightRootAbstract)
    (leftRootContext rightRootContext : OneHoleContext)
    (leftRootEq : leftNode.skeleton.1 =
      leftRootContext.fill leftRootAbstract)
    (rightRootEq : rightNode.skeleton.1 =
      rightRootContext.fill rightRootAbstract)
    (leftEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [leftStopped.certified.typed] leftNode.plan.boundaryTable.entries)
    (rightEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [rightStopped.certified.typed] rightNode.plan.boundaryTable.entries)
    (leftContextCollapse : canonicalize
      rhoReflectivePresentation.toReflectivePresentationDecl
        (leftStopped.skeletonContext.fill
          (.fvar leftStopped.boundaryOccurrence.name)) =
      .fvar leftStopped.boundaryOccurrence.name)
    (rightContextCollapse : canonicalize
      rhoReflectivePresentation.toReflectivePresentationDecl
        (rightStopped.skeletonContext.fill
          (.fvar rightStopped.boundaryOccurrence.name)) =
      .fvar rightStopped.boundaryOccurrence.name)
    (supportCase :
      leftStopped.certified.typed.boundary.targetSupport =
          rightStopped.certified.typed.boundary.targetSupport ∨
      leftStopped.certified.typed.boundary.targetSupport = [] ∨
      rightStopped.certified.typed.boundary.targetSupport = [])
    (typeEq : leftStopped.certified.typed.boundary.targetType =
      rightStopped.certified.typed.boundary.targetType)
    (childDeclaration : ReflectivePresentationDecl)
    (canonical : canonicalize childDeclaration
        leftStopped.certified.typed.boundary.content =
      canonicalize childDeclaration
        rightStopped.certified.typed.boundary.content)
    (parentMeasure : Nat)
    (smaller :
      sizeOf leftStopped.certified.typed.boundary.content +
          sizeOf rightStopped.certified.typed.boundary.content < parentMeasure)
    (rightAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      rightStopped.certified.typed.boundary.targetType)
    (closeSmaller :
      ∀ {childAvailable childOuter : List TypeExpr}
        {leftChild rightChild : Pattern} {childType : TypeExpr},
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType leftChild →
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType rightChild →
        canonicalize childDeclaration leftChild =
          canonicalize childDeclaration rightChild →
        sizeOf leftChild + sizeOf rightChild < parentMeasure →
        rhoCanonicalRecursiveTypeDomain.Admissible childType →
        Nonempty (CostCanonicalPairElaboration rhoCIGSLT
          rhoHereditaryNormalizationKernel targetFree childAvailable
          childOuter leftChild rightChild childType))
    {Key : Type} [LinearOrder Key]
    (leftKey rightKey : Nat → Nat → Pattern → Key)
    (availableDepth scopeDepth : Nat) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    let relation : Pattern → Pattern → Prop := fun leftLeaf rightLeaf =>
      ∀ sourceDepth,
        ReflectiveContextSupport.RestoresTogether
          rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
            cospan.commonAssignment
            (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
              (leftNode.thinning.thickenAmbientBVars sourceDepth
                (mapPattern (color.symbols rhoCIGSLT) leftLeaf)))
            (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
              (rightNode.thinning.thickenAmbientBVars sourceDepth
                (mapPattern (color.symbols rhoCIGSLT) rightLeaf)))
    PatternLeafAligned relation
      (canonicalizeByDepths leftKey rhoReflectivePresentation availableDepth
        scopeDepth
        (leftEnvironment.reify leftRootAbstract))
      (canonicalizeByDepths rightKey rhoReflectivePresentation availableDepth
        scopeDepth
        (rightEnvironment.reify rightRootAbstract)) := by
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let relation : Pattern → Pattern → Prop := fun leftLeaf rightLeaf =>
    ∀ sourceDepth,
      ReflectiveContextSupport.RestoresTogether
        rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
          cospan.commonAssignment
          (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
            (leftNode.thinning.thickenAmbientBVars sourceDepth
              (mapPattern (color.symbols rhoCIGSLT) leftLeaf)))
          (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
            (rightNode.thinning.thickenAmbientBVars sourceDepth
              (mapPattern (color.symbols rhoCIGSLT) rightLeaf)))
  let leftAtRoot : CostStaticPlanStopped rhoCIGSLT color targetFree leftPayload
      leftNode.skeleton.1 :=
    { leftStopped with
      skeletonContext := leftRootContext.comp leftStopped.skeletonContext
      abstract_eq := by
        rw [OneHoleContext.fill_comp, ← leftStopped.abstract_eq]
        exact leftRootEq }
  let rightAtRoot : CostStaticPlanStopped rhoCIGSLT color targetFree
      rightPayload rightNode.skeleton.1 :=
    { rightStopped with
      skeletonContext := rightRootContext.comp rightStopped.skeletonContext
      abstract_eq := by
        rw [OneHoleContext.fill_comp, ← rightStopped.abstract_eq]
        exact rightRootEq }
  obtain ⟨leftSlot, leftSelectedAtRoot⟩ := Option.isSome_iff_exists.mp
    (leftEnvironment.slotOfName?_isSome_of_occurrence
      leftAtRoot.boundaryOccurrence)
  obtain ⟨rightSlot, rightSelectedAtRoot⟩ := Option.isSome_iff_exists.mp
    (rightEnvironment.slotOfName?_isSome_of_occurrence
      rightAtRoot.boundaryOccurrence)
  have leftSelected : leftEnvironment.slotOfName?
      leftStopped.boundaryOccurrence.name = some leftSlot := by
    simpa [leftAtRoot] using leftSelectedAtRoot
  have rightSelected : rightEnvironment.slotOfName?
      rightStopped.boundaryOccurrence.name = some rightSlot := by
    simpa [rightAtRoot] using rightSelectedAtRoot
  have leftEmbeddingAtRoot : CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree [leftAtRoot.certified.typed]
        leftNode.plan.boundaryTable.entries := by
    simpa [leftAtRoot] using leftEmbedding
  have rightEmbeddingAtRoot : CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree [rightAtRoot.certified.typed]
        rightNode.plan.boundaryTable.entries := by
    simpa [rightAtRoot] using rightEmbedding
  have leftFrame :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanStopped.canonicalizeByDepths_environmentReify_abstract_eq_fvar
      leftEnvironment leftStopped leftSlot leftSelected leftContextCollapse
        leftKey availableDepth scopeDepth
  have rightFrame :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanStopped.canonicalizeByDepths_environmentReify_abstract_eq_fvar
      rightEnvironment rightStopped rightSlot rightSelected
        rightContextCollapse rightKey availableDepth scopeDepth
  rw [leftFrame, rightFrame]
  apply PatternLeafAligned.leaf
  intro sourceDepth
  have restores :
      ReflectiveContextSupport.RestoresTogether
        rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
          cospan.commonAssignment
          (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
            (.fvar (leftEnvironment.atomName leftSlot)))
          (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
            (.fvar (rightEnvironment.atomName rightSlot))) :=
    CostStaticAtomKeyCospan.CommonRestorationApex.restoresTogether_of_forall_apex
      (fun depth =>
        CostStaticPlanStopped.selectedAtoms_commonRestorationApex_of_closeSmaller
          leftAtRoot rightAtRoot leftEmbeddingAtRoot rightEmbeddingAtRoot
          leftTrees rightTrees leftEnvironment rightEnvironment leftSlot
          leftSelectedAtRoot rightSlot rightSelectedAtRoot (by
            simpa [leftAtRoot, rightAtRoot] using supportCase) (by
            simpa [leftAtRoot, rightAtRoot] using typeEq) childDeclaration
          rhoReflectivePresentation (by
            simpa [leftAtRoot, rightAtRoot] using canonical) parentMeasure (by
            simpa [leftAtRoot, rightAtRoot] using smaller) (by
            simpa [rightAtRoot] using rightAdmissible) closeSmaller depth)
  simpa [relation, cospan, mapPattern,
    CostStaticBinderThinning.thickenAmbientBVars] using restores

/-! ## A certified boundary facing an escaped process frame -/

/-- Every authored rho rule returns either `Name` or `Proc`. -/
theorem rho_rule_category_name_or_proc {rule : GrammarRule}
    (membership : rule ∈ rhoCalc.terms) :
    rule.category = "Name" ∨ rule.category = "Proc" := by
  simp only [rhoCalc, List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp

/-- The authored rho constructor named `NQuote` is in the `Name` result
fibre.  This is the converse direction needed when a plan exposes its root
label rather than its result type. -/
theorem rhoCalc_category_eq_name_of_label_eq_quote {rule : GrammarRule}
    (membership : rule ∈ rhoCalc.terms)
    (label : rule.label = rhoReflectivePresentation.quoteConstructor) :
    rule.category = "Name" := by
  simp only [rhoCalc, List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [rhoReflectivePresentation]

/-- An ordinary static application plan therefore lies in exactly one of
rho's two authored result fibres. -/
theorem rho_applicationPlan_sourceType_name_or_proc
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    (applicationClass : ∃ constructor,
      plan.rootClass = .application constructor) :
    sourceType = .base "Name" ∨ sourceType = .base "Proc" := by
  cases plan with
  | application constructor rendered current preimage notBare children =>
      rcases rho_rule_category_name_or_proc
          preimage.sourceConstructor.2 with category | category
      · exact Or.inl (congrArg TypeExpr.base category)
      · exact Or.inr (congrArg TypeExpr.base category)
  | bvar | fvar | boundaryApplication | lambda | multiLambda | collection |
      boundaryCollection =>
      simp [CostStaticRegionPlan.rootClass] at applicationClass

/-- A static application plan whose authored root is Quote lies in rho's
`Name` fibre. -/
theorem rho_applicationPlan_sourceType_eq_name_of_quoteRoot
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    (quoteRoot : plan.rootClass = .application
      rhoReflectivePresentation.quoteConstructor) :
    sourceType = .base "Name" := by
  cases plan with
  | application constructor rendered current preimage notBare children =>
      exact congrArg TypeExpr.base
        (rhoCalc_category_eq_name_of_label_eq_quote
          preimage.sourceConstructor.2 (by
            simpa [CostStaticRegionPlan.rootClass] using quoteRoot))
  | bvar | fvar | boundaryApplication | lambda | multiLambda | collection |
      boundaryCollection =>
      simp [CostStaticRegionPlan.rootClass] at quoteRoot

/-- A Quote-root plan exposes the exact generated static application data at
its payload index. -/
theorem CostStaticRegionPlan.staticApplicationData_of_quoteRoot
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    (quoteRoot : plan.rootClass = .application
      rhoReflectivePresentation.quoteConstructor) :
    ∃ wireName arguments constructor,
      pattern = .apply wireName arguments ∧
      rhoCIGSLT.decodeDeclaredCostConstructor wireName = some constructor ∧
      rhoCIGSLT.declaredCostConstructorRole constructor = .static color := by
  cases plan with
  | application constructor rendered current preimage notBare children =>
      refine ⟨_, _, constructor, rfl, ?_, current⟩
      rw [← rendered]
      exact rhoCIGSLT.decodeDeclaredCostConstructor_render constructor
  | bvar | fvar | boundaryApplication | lambda | multiLambda | collection |
      boundaryCollection =>
      simp [CostStaticRegionPlan.rootClass] at quoteRoot

/-- An admitted reached Quote has a visible-root static plan related to the
contextual reached plan by the exact sealed suffix. -/
theorem CostStaticPlanReached.exists_staticRootPlanSealedAlignment_of_quoteRoot
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {payload rootAbstract : Pattern}
    (reached : CostStaticPlanReached rhoCIGSLT color targetFree payload
      rootAbstract)
    (admission : reached.plan.RawAdmission)
    (quoteRoot : reached.plan.rootClass = .application
      rhoReflectivePresentation.quoteConstructor) :
    ∃ (sealed : List TypeExpr)
        (rootPlan : CostStaticRegionPlan rhoCIGSLT color targetFree
          (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT color
            reached.sourceAvailable)
          reached.sourceAvailable
          (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT color
            reached.sourceAvailable)
          reached.sourceAvailable .hole payload reached.sourceType),
      reached.targetBound = reached.sourceAvailable ++ sealed ∧
      rootPlan.CompilerReceipt ∧
      rootPlan.isStaticRoot = true ∧
      CostStaticRegionPlan.BoundaryFibersAvailabilitySuffix sealed .sealed
        rootPlan (reached.plan.recontextualize .hole) := by
  obtain ⟨sealed, rootPlan, split, rootBuilt, aligned⟩ :=
    reached.exists_rootPlanSealedAlignment
      CostCanonicalLaws.rho_unambiguousStaticDecomposition.collectionGloballyUnambiguous
      admission
  obtain ⟨wireName, arguments, constructor, payloadEq, decoded, role⟩ :=
    CostStaticRegionPlan.staticApplicationData_of_quoteRoot reached.plan
      quoteRoot
  let planFamily := fun pattern =>
    CostStaticRegionPlan rhoCIGSLT color targetFree
      (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT color
        reached.sourceAvailable)
      reached.sourceAvailable
      (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT color
        reached.sourceAvailable)
      reached.sourceAvailable .hole pattern reached.sourceType
  let applicationPlan : planFamily (.apply wireName arguments) :=
    Eq.mp (congrArg planFamily payloadEq) rootPlan
  have applicationPlanStatic : applicationPlan.isStaticRoot = true :=
    applicationPlan.isStaticRoot_of_current_application constructor decoded
      role
  have transportStatic : applicationPlan.isStaticRoot = rootPlan.isStaticRoot := by
    cases payloadEq
    rfl
  have rootStatic : rootPlan.isStaticRoot = true := by
    rw [← transportStatic]
    exact applicationPlanStatic
  exact ⟨sealed, rootPlan, split, rootBuilt, rootStatic, aligned⟩

/-- Parent-environment canonicalization of an embedded Quote frame is
independent of both semantic-key depths.  Only atoms actually occurring in
the reached frame need be sealed; their support is transported through the
proof-relevant entry embedding. -/
theorem CostStaticPlanReached.parentCanonicalizeByDepths_sourceSemanticPatternKeyAt_eq_of_quoteRoot
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {payload : Pattern}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (reached : CostStaticPlanReached rhoCIGSLT color targetFree payload
      node.plan.abstractPattern)
    (admission : reached.plan.RawAdmission)
    (quoteRoot : reached.plan.rootClass =
      CostStaticPlanRootClass.application
        rhoReflectivePresentation.quoteConstructor)
    (embedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      reached.plan.boundaryTable.entries node.plan.boundaryTable.entries)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    (availableDepth scopeDepth : Nat) :
    canonicalizeByDepths
        (CostStaticRegionNode.sourceSemanticPatternKeyAt node environment)
        rhoReflectivePresentation availableDepth scopeDepth
        (environment.reify reached.plan.abstractPattern) =
      canonicalizeByDepths
        (fun _ _ pattern =>
          Mettapedia.GSLT.LanguageDef.CostStaticRegionNode.semanticPatternKeyAt
            environment 0 (mapPattern (color.symbols rhoCIGSLT) pattern))
        rhoReflectivePresentation availableDepth scopeDepth
        (environment.reify reached.plan.abstractPattern) := by
  have sourceBase : ∃ category, reached.sourceType = .base category := by
    rcases rho_applicationPlan_sourceType_name_or_proc reached.plan
        ⟨rhoReflectivePresentation.quoteConstructor, quoteRoot⟩ with
      name | process
    · exact ⟨"Name", name⟩
    · exact ⟨"Proc", process⟩
  have frameFree : WellSorted.ReflectiveSubstitutionBinderFree
      reached.plan.abstractPattern = true :=
    CostStaticRegionNode.CostStaticRegionPlan.rhoAbstractPattern_binderFree_of_base
      reached.plan sourceBase
  apply
    CostStaticRegionNode.canonicalizeByDepths_sourceSemanticPatternKeyAt_eq_of_freeAtomTargetSupport_eq_nil
      node environment availableDepth scopeDepth 0
        (environment.reify reached.plan.abstractPattern)
  · intro name membership slot selected
    exact CostStaticPlanReached.parentAtomTargetSupport_eq_nil_of_quoteRoot
      node reached admission frameFree quoteRoot embedding environment
        membership slot selected
  · rw [CostStaticAtomEnvironment.binderSafeAt_reify]
    exact CostStaticRegionPlan.abstractPattern_binderSafeAt_zero_of_quoteRoot
      reached.plan quoteRoot
  · exact Nat.zero_le _

/-- Every reached plan root is rigid, an ordinary application, an ordinary
collection, or a certified boundary.  The disjunction follows the semantic
dispatcher order used by the boundary-side residual. -/
theorem CostStaticRegionPlan.rootClass_cases
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType) :
    plan.rootClass = .rigid ∨
      (∃ constructor, plan.rootClass = .application constructor) ∨
      (∃ collectionType, plan.rootClass = .collection collectionType) ∨
      plan.rootClass.IsCertifiedBoundary := by
  cases plan <;>
    simp [CostStaticRegionPlan.rootClass,
      CostStaticPlanRootClass.IsCertifiedBoundary]

/-- A rho application outside the authored Quote cell necessarily returns a
process.  The only authored constructor in the `Name` fibre is `NQuote`. -/
theorem rho_applicationPlan_sourceType_eq_proc_of_not_quote
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    {constructor : String}
    (applicationClass : plan.rootClass = .application constructor)
    (notQuote : constructor ≠ rhoReflectivePresentation.quoteConstructor) :
    sourceType = .base "Proc" := by
  rcases rho_applicationPlan_sourceType_name_or_proc plan
      ⟨constructor, applicationClass⟩ with name | process
  · cases plan with
    | application declared rendered current preimage notBare children =>
        have categoryEq : preimage.sourceConstructor.1.category = "Name" :=
          TypeExpr.base.inj name
        have labelEq : preimage.sourceConstructor.1.label = "NQuote" :=
          rhoCalc_label_eq_quote_of_category_name
            preimage.sourceConstructor.2 categoryEq
        have classEq : constructor = preimage.sourceConstructor.1.label := by
          simpa [CostStaticRegionPlan.rootClass] using
            (CostStaticPlanRootClass.application.inj applicationClass).symm
        exact (notQuote (classEq.trans labelEq)).elim
    | bvar | fvar | boundaryApplication | lambda | multiLambda | collection |
        boundaryCollection =>
        simp [CostStaticRegionPlan.rootClass] at applicationClass
  · exact process

/-- An admissible rho collection plan must be the bare parallel in the
`Proc` fibre.  A direct collection result is rejected by the recursive type
domain, and rho's only bare-collection rule is authored at `Proc`. -/
theorem rho_collectionPlan_sourceType_eq_proc
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    (collectionClass : ∃ collectionType,
      plan.rootClass = .collection collectionType)
    (admissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT) sourceType)) :
    sourceType = .base "Proc" := by
  cases plan with
  | collection choice selected children =>
      rename_i collectionType elements rest
      rcases mem_costStaticCollectionTypingChoices_sound rhoCIGSLT color
          targetFree targetBound collectionType elements
          (mapTypeExpr (color.symbols rhoCIGSLT) sourceType) choice selected with
        direct | bare
      · rcases direct with
          ⟨sourceElementType, choiceEq, expectedEq, _elementsChecked⟩
        have sourceEq : sourceType =
            .collection collectionType sourceElementType :=
          mapTypeExpr_costStatic_injective rhoCIGSLT color expectedEq
        subst sourceType
        exact (rhoCanonicalRecursiveTypeDomain.noCollection admissible).elim
      · rcases bare with
          ⟨rule, sourceElementType, choiceEq, membership, wrapped,
            expectedEq, parameterName, parameterShape, _elementsChecked⟩
        have sourceEq : sourceType = .base rule.category :=
          mapTypeExpr_costStatic_injective rhoCIGSLT color expectedEq
        rw [sourceEq, rho_bare_src_category rule membership
          ⟨parameterName, collectionType, sourceElementType, parameterShape⟩]
  | boundaryCollection currentRejected oppositeChoice oppositeSelected
      certified certifies =>
      exact absurd oppositeSelected (fun selected =>
        rho_boundaryCollection_choices_absurd color targetFree targetBound _ _ _
          selected currentRejected)
  | bvar | fvar | boundaryApplication | application | lambda | multiLambda =>
      simp [CostStaticRegionPlan.rootClass] at collectionClass

/-- A certified rho boundary in the `Proc` fibre canonicalizes to a
non-unit application whose head is outside the current static colour.  The
two apparent exceptions are impossible for typed reasons: the current-colour
Quote/unit contradicts the boundary role, while the opposite-colour
Quote/unit has the wrong generated `Proc` sort. -/
theorem rhoProc_boundaryPlan_canonical_escape
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern (.base "Proc"))
    (boundaryClass : plan.rootClass.IsCertifiedBoundary)
    (declarationColor : CostStaticColor) :
    let declaration := costStaticReflectivePresentationDecl rhoCIGSLT
      declarationColor rhoReflectivePresentation.toReflectivePresentationDecl
    RhoDescendEscape color (canonicalize declaration pattern) ∧
      canonicalize declaration pattern ≠
        .apply declaration.parallelUnitConstructor [] := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT
    declarationColor rhoReflectivePresentation.toReflectivePresentationDecl
  generalize sourceTypeEq : (TypeExpr.base "Proc") = sourceType at plan
  cases plan with
  | boundaryApplication declared rendered outsideCurrent certified certifies =>
      subst sourceType
      rename_i wireName arguments
      have typed : HasType rhoCIGSLT.costWholeLanguage targetFree
          sourceAvailable (.apply wireName arguments)
          (mapTypeExpr (color.symbols rhoCIGSLT) (.base "Proc")) := by
        simpa only [certified.content_eq, certified.targetSupport_eq,
          certified.targetType_eq] using certified.typed.contentTyped
      by_cases quoteHead : wireName = declaration.quoteConstructor
      · have quoteRole := rhoRole_static_of_render_eq_quote declared
          (rendered.trans quoteHead)
        by_cases sameColor : declarationColor = color
        · subst declarationColor
          exact (outsideCurrent quoteRole).elim
        · have declarationFlip : declarationColor = color.flip :=
            CostStaticColor.eq_flip_of_ne (Ne.symm sameColor)
          subst declarationColor
          obtain ⟨rule, ruleMembership, labelEquality, _notBare,
              typeEquality, _argumentsTyped⟩ :=
            WellSorted.hasType_apply_inversion typed
          have categoryForm := rho_costWhole_rule_category_of_quoteWire
            color.flip ruleMembership
            (labelEquality.symm.trans
              (quoteHead.trans (rhoDecl_quoteConstructor color.flip)))
          have cross : mapTypeExpr (color.symbols rhoCIGSLT) (.base "Proc") =
              mapTypeExpr (color.flip.symbols rhoCIGSLT) (.base "Name") :=
            typeEquality.trans categoryForm
          exact (mapTypeExpr_cross_proc_ne color "Name" (by decide) cross).elim
      · have canonicalShape : canonicalize declaration
            (.apply wireName arguments) =
          .apply wireName (arguments.map (canonicalize declaration)) :=
          canonicalize_apply_of_ne_quote declaration quoteHead arguments
        have decodedNone : decodeDeclaredCostStaticConstructor rhoCIGSLT color
            wireName = none := by
          have decoded := decodeDeclaredCostStaticConstructor_render_of_role_ne
            rhoCIGSLT declared color outsideCurrent
          simpa only [rendered] using decoded
        constructor
        · constructor
          · intro collectionType elements rest equality
            rw [canonicalShape] at equality
            cases equality
          · exact ⟨wireName, arguments.map (canonicalize declaration),
              canonicalShape, decodedNone⟩
        · rw [canonicalShape]
          intro unitEquality
          have wireEq : wireName = declaration.parallelUnitConstructor :=
            (Pattern.apply.inj unitEquality).1
          have unitRole := rhoRole_static_of_render_eq_parallelUnit declared
            (rendered.trans wireEq)
          by_cases sameColor : declarationColor = color
          · subst declarationColor
            exact outsideCurrent unitRole
          · have declarationFlip : declarationColor = color.flip :=
              CostStaticColor.eq_flip_of_ne (Ne.symm sameColor)
            subst declarationColor
            obtain ⟨rule, ruleMembership, labelEquality, _notBare,
                typeEquality, _argumentsTyped⟩ :=
              WellSorted.hasType_apply_inversion typed
            have categoryForm := rho_costWhole_rule_category_of_unitWire
              color.flip ruleMembership
              (labelEquality.symm.trans
                (wireEq.trans (rhoDecl_unitConstructor color.flip)))
            have cross : mapTypeExpr (color.symbols rhoCIGSLT) (.base "Proc") =
                mapTypeExpr (color.flip.symbols rhoCIGSLT) (.base "Proc") :=
              typeEquality.trans categoryForm
            exact mapTypeExpr_flipProc_ne color (.base "Proc") cross.symm
  | boundaryCollection currentRejected oppositeChoice oppositeSelected
      certified certifies =>
      exact absurd oppositeSelected (fun selected =>
        rho_boundaryCollection_choices_absurd color targetFree targetBound _ _ _
          selected currentRejected)
  | bvar | fvar | application | lambda | multiLambda | collection =>
      simp [CostStaticRegionPlan.rootClass,
        CostStaticPlanRootClass.IsCertifiedBoundary] at boundaryClass

/-- Index-tolerant form of `rhoProc_boundaryPlan_canonical_escape`. -/
theorem rho_boundaryPlan_canonical_escape_of_sourceType_eq_proc
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    (process : sourceType = .base "Proc")
    (boundaryClass : plan.rootClass.IsCertifiedBoundary)
    (declarationColor : CostStaticColor) :
    let declaration := costStaticReflectivePresentationDecl rhoCIGSLT
      declarationColor rhoReflectivePresentation.toReflectivePresentationDecl
    RhoDescendEscape color (canonicalize declaration pattern) ∧
      canonicalize declaration pattern ≠
        .apply declaration.parallelUnitConstructor [] := by
  subst sourceType
  exact rhoProc_boundaryPlan_canonical_escape plan boundaryClass
    declarationColor

/-- A certified boundary and a process plan with the same escaped canonical
target both expose stopped contributors in their reached subplans.  Their
supports and target types agree by the reached-pair telescope, so the
stopped-pair leaf closure applies after replaying both contributors into the
parent semantic forests. -/
noncomputable def boundaryProcEscapePlanStops_sourcePatternLeafAligned_of_closeSmaller
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (leftNode rightNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (leftTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      leftNode.finiteBoundaryTable)
    (rightTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      rightNode.finiteBoundaryTable)
    {leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftNode.boundaryTable
      (leftTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      leftNode.skeleton.1}
    {rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightNode.boundaryTable
      (rightTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      rightNode.skeleton.1}
    (leftEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      rightInventory)
    {leftPayload rightPayload : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftNode.plan.abstractPattern)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightNode.plan.abstractPattern)
    (leftBoundary : leftReached.BoundaryView)
    (rightProcess : rightReached.sourceType = .base "Proc")
    (sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
    (sourceAvailableEq : leftReached.sourceAvailable =
      rightReached.sourceAvailable)
    (leftEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      leftReached.plan.boundaryTable.entries
      leftNode.plan.boundaryTable.entries)
    (rightEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      rightReached.plan.boundaryTable.entries
      rightNode.plan.boundaryTable.entries)
    (rightRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT) (.base rightNode.sourceSort.1))
      (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType)))
    (rightRootAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightNode.sourceSort.1)))
    (declarationColor : CostStaticColor)
    {rawStop : Pattern → Pattern → Prop}
    (rawAligned : CanonicalStopAligned
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation)
      rawStop leftPayload rightPayload)
    (stopCanonical : ∀ {left right}, rawStop left right →
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation) left =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation) right)
    (escape : RhoDescendEscape color
      (canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation) rightPayload))
    (targetNeUnit : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation) rightPayload ≠
      .apply
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation).parallelUnitConstructor [])
    (closeSmaller :
      ∀ {childAvailable childOuter : List TypeExpr}
        {leftChild rightChild : Pattern} {childType : TypeExpr},
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType leftChild →
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType rightChild →
        canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation) leftChild =
          canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation) rightChild →
        sizeOf leftChild + sizeOf rightChild <
          sizeOf leftNode.term.1 + sizeOf rightNode.term.1 →
        rhoCanonicalRecursiveTypeDomain.Admissible childType →
        Nonempty (CostCanonicalPairElaboration rhoCIGSLT
          rhoHereditaryNormalizationKernel targetFree childAvailable
          childOuter leftChild rightChild childType))
    {Key : Type} [LinearOrder Key]
    (leftKey rightKey : Nat → Nat → Pattern → Key)
    (availableDepth scopeDepth : Nat) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    let relation : Pattern → Pattern → Prop := fun leftLeaf rightLeaf =>
      ∀ sourceDepth,
        ReflectiveContextSupport.RestoresTogether
          rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
            cospan.commonAssignment
            (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
              (leftNode.thinning.thickenAmbientBVars sourceDepth
                (mapPattern (color.symbols rhoCIGSLT) leftLeaf)))
            (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
              (rightNode.thinning.thickenAmbientBVars sourceDepth
                (mapPattern (color.symbols rhoCIGSLT) rightLeaf)))
    PatternLeafAligned relation
      (canonicalizeByDepths leftKey rhoReflectivePresentation availableDepth
        scopeDepth
        (leftEnvironment.reify leftReached.plan.abstractPattern))
      (canonicalizeByDepths rightKey rhoReflectivePresentation availableDepth
        scopeDepth
        (rightEnvironment.reify rightReached.plan.abstractPattern)) := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT
    declarationColor rhoReflectivePresentation
  let target := canonicalize declaration rightPayload
  let rightProcessPlan := castCostStaticRegionPlanSourceType rightProcess
    rightReached.plan
  obtain ⟨descent⟩ := rhoProc_applyBoundaryDescent
    (sizeOf rightPayload) rightProcessPlan target (by omega) rfl escape
      targetNeUnit
  have rightProcessAbstract : rightProcessPlan.abstractPattern =
      rightReached.plan.abstractPattern :=
    castCostStaticRegionPlanSourceType_abstractPattern rightProcess
      rightReached.plan
  let leftStopped : CostStaticPlanStopped rhoCIGSLT color targetFree
      leftPayload leftReached.plan.abstractPattern :=
    { leftBoundary.stopped with
      skeletonContext := .hole
      abstract_eq := by
        simpa [OneHoleContext.fill] using leftBoundary.abstract_eq }
  have leftEmbedding' : CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree [leftStopped.certified.typed]
        leftNode.plan.boundaryTable.entries := by
    have retained : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
        [leftBoundary.stopped.certified.typed]
          leftNode.plan.boundaryTable.entries := by
      simpa only [leftBoundary.entries_eq] using leftEmbedding
    simpa [leftStopped] using retained
  have rightInnerEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree [descent.state.certified.typed]
        rightReached.plan.boundaryTable.entries := by
    rw [← castCostStaticRegionPlanSourceType_boundaryTable_entries
      rightProcess rightReached.plan]
    exact descent.entryEmbedding
  have rightEmbedding' : CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree [descent.state.certified.typed]
        rightNode.plan.boundaryTable.entries := by
    exact rightInnerEmbedding.comp rightEmbedding
  have supportEq : leftStopped.certified.typed.boundary.targetSupport =
      descent.state.certified.typed.boundary.targetSupport := by
    calc
      leftStopped.certified.typed.boundary.targetSupport =
          leftReached.sourceAvailable := by
        simpa [leftStopped] using leftBoundary.targetSupport_eq
      _ = rightReached.sourceAvailable := sourceAvailableEq
      _ = descent.state.certified.typed.boundary.targetSupport := by
        exact descent.boundarySupport.symm
  have typeEq : leftStopped.certified.typed.boundary.targetType =
      descent.state.certified.typed.boundary.targetType := by
    calc
      leftStopped.certified.typed.boundary.targetType =
          mapTypeExpr (color.symbols rhoCIGSLT) leftReached.sourceType := by
        simpa [leftStopped] using leftBoundary.targetType_eq
      _ = mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType :=
        congrArg (mapTypeExpr (color.symbols rhoCIGSLT)) sourceTypeEq
      _ = descent.state.certified.typed.boundary.targetType := by
        rw [rightProcess]
        exact descent.boundaryType.symm
  have canonical : canonicalize declaration
        leftStopped.certified.typed.boundary.content =
      canonicalize declaration
        descent.state.certified.typed.boundary.content := by
    calc
      canonicalize declaration leftStopped.certified.typed.boundary.content =
          canonicalize declaration leftPayload := by
        rw [show leftStopped.certified.typed.boundary.content = leftPayload by
          simpa [leftStopped] using leftBoundary.content_eq]
      _ = canonicalize declaration rightPayload :=
        rawAligned.canonicalize_eq declaration stopCanonical
      _ = canonicalize declaration
          descent.state.certified.typed.boundary.content := by
        simpa [target, declaration] using
          descent.boundaryCanonical.symm
  have leftMember : leftStopped.certified.typed ∈
      leftNode.plan.boundaryTable.entries := leftEmbedding'.subset (by simp)
  have rightMember : descent.state.certified.typed ∈
      rightNode.plan.boundaryTable.entries := rightEmbedding'.subset (by simp)
  have leftSmaller := leftNode.plan.boundary_content_size_lt_of_isStaticRoot
    leftNode.rootStatic leftStopped.certified.typed leftMember
  have rightSmaller := rightNode.plan.boundary_content_size_lt_of_isStaticRoot
    rightNode.rootStatic descent.state.certified.typed rightMember
  have smaller :
      sizeOf leftStopped.certified.typed.boundary.content +
          sizeOf descent.state.certified.typed.boundary.content <
        sizeOf leftNode.term.1 + sizeOf rightNode.term.1 := by omega
  obtain ⟨rightRoute'⟩ := rightRoute
  have rightAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      descent.state.certified.typed.boundary.targetType := by
    rw [← typeEq, show leftStopped.certified.typed.boundary.targetType =
        mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType by
      exact (by
        simpa [leftStopped] using leftBoundary.targetType_eq.trans
          (congrArg (mapTypeExpr (color.symbols rhoCIGSLT)) sourceTypeEq))]
    exact CostCanonicalTypeRoute.rho_admissible rightRoute'
      rightRootAdmissible
  have rightRootEq : rightNode.skeleton.1 =
      rightReached.skeletonContext.fill rightProcessPlan.abstractPattern := by
    exact rightNode.skeleton_pattern.trans
      (rightReached.abstract_eq.trans
        (congrArg rightReached.skeletonContext.fill
          rightProcessAbstract.symm))
  have aligned := stoppedPair_sourcePatternLeafAligned_of_closeSmaller
    leftNode rightNode
    leftTrees rightTrees leftEnvironment rightEnvironment leftStopped
    descent.state leftReached.skeletonContext rightReached.skeletonContext
    (leftNode.skeleton_pattern.trans leftReached.abstract_eq)
    rightRootEq leftEmbedding'
    rightEmbedding' (by simp [leftStopped, canonicalize])
    descent.contextCollapse (Or.inl supportEq)
    typeEq declaration canonical _ smaller rightAdmissible closeSmaller
    leftKey rightKey availableDepth scopeDepth
  simpa only [rightProcessAbstract] using aligned

/-- Orientation-preserving mirror of
`boundaryProcEscapePlanStops_sourcePatternLeafAligned_of_closeSmaller`.
The process contributor is descended on the left while the endpoint cospan
retains its original left-to-right ordering. -/
noncomputable def procEscapeBoundaryPlanStops_sourcePatternLeafAligned_of_closeSmaller
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (leftNode rightNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (leftTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      leftNode.finiteBoundaryTable)
    (rightTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      rightNode.finiteBoundaryTable)
    {leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftNode.boundaryTable
      (leftTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      leftNode.skeleton.1}
    {rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightNode.boundaryTable
      (rightTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      rightNode.skeleton.1}
    (leftEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      rightInventory)
    {leftPayload rightPayload : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftNode.plan.abstractPattern)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightNode.plan.abstractPattern)
    (leftProcess : leftReached.sourceType = .base "Proc")
    (rightBoundary : rightReached.BoundaryView)
    (sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
    (sourceAvailableEq : leftReached.sourceAvailable =
      rightReached.sourceAvailable)
    (leftEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      leftReached.plan.boundaryTable.entries
      leftNode.plan.boundaryTable.entries)
    (rightEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      rightReached.plan.boundaryTable.entries
      rightNode.plan.boundaryTable.entries)
    (rightRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT) (.base rightNode.sourceSort.1))
      (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType)))
    (rightRootAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightNode.sourceSort.1)))
    (declarationColor : CostStaticColor)
    {rawStop : Pattern → Pattern → Prop}
    (rawAligned : CanonicalStopAligned
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation)
      rawStop leftPayload rightPayload)
    (stopCanonical : ∀ {left right}, rawStop left right →
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation) left =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation) right)
    (escape : RhoDescendEscape color
      (canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation) leftPayload))
    (targetNeUnit : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation) leftPayload ≠
      .apply
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation).parallelUnitConstructor [])
    (closeSmaller :
      ∀ {childAvailable childOuter : List TypeExpr}
        {leftChild rightChild : Pattern} {childType : TypeExpr},
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType leftChild →
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType rightChild →
        canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation) leftChild =
          canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation) rightChild →
        sizeOf leftChild + sizeOf rightChild <
          sizeOf leftNode.term.1 + sizeOf rightNode.term.1 →
        rhoCanonicalRecursiveTypeDomain.Admissible childType →
        Nonempty (CostCanonicalPairElaboration rhoCIGSLT
          rhoHereditaryNormalizationKernel targetFree childAvailable
          childOuter leftChild rightChild childType))
    {Key : Type} [LinearOrder Key]
    (leftKey rightKey : Nat → Nat → Pattern → Key)
    (availableDepth scopeDepth : Nat) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    let relation : Pattern → Pattern → Prop := fun leftLeaf rightLeaf =>
      ∀ sourceDepth,
        ReflectiveContextSupport.RestoresTogether
          rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
            cospan.commonAssignment
            (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
              (leftNode.thinning.thickenAmbientBVars sourceDepth
                (mapPattern (color.symbols rhoCIGSLT) leftLeaf)))
            (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
              (rightNode.thinning.thickenAmbientBVars sourceDepth
                (mapPattern (color.symbols rhoCIGSLT) rightLeaf)))
    PatternLeafAligned relation
      (canonicalizeByDepths leftKey rhoReflectivePresentation availableDepth
        scopeDepth
        (leftEnvironment.reify leftReached.plan.abstractPattern))
      (canonicalizeByDepths rightKey rhoReflectivePresentation availableDepth
        scopeDepth
        (rightEnvironment.reify rightReached.plan.abstractPattern)) := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT
    declarationColor rhoReflectivePresentation
  let target := canonicalize declaration leftPayload
  let leftProcessPlan := castCostStaticRegionPlanSourceType leftProcess
    leftReached.plan
  obtain ⟨descent⟩ := rhoProc_applyBoundaryDescent
    (sizeOf leftPayload) leftProcessPlan target (by omega) rfl escape
      targetNeUnit
  have leftProcessAbstract : leftProcessPlan.abstractPattern =
      leftReached.plan.abstractPattern :=
    castCostStaticRegionPlanSourceType_abstractPattern leftProcess
      leftReached.plan
  let rightStopped : CostStaticPlanStopped rhoCIGSLT color targetFree
      rightPayload rightReached.plan.abstractPattern :=
    { rightBoundary.stopped with
      skeletonContext := .hole
      abstract_eq := by
        simpa [OneHoleContext.fill] using rightBoundary.abstract_eq }
  have leftInnerEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree [descent.state.certified.typed]
        leftReached.plan.boundaryTable.entries := by
    rw [← castCostStaticRegionPlanSourceType_boundaryTable_entries
      leftProcess leftReached.plan]
    exact descent.entryEmbedding
  have leftEmbedding' : CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree [descent.state.certified.typed]
        leftNode.plan.boundaryTable.entries :=
    leftInnerEmbedding.comp leftEmbedding
  have rightEmbedding' : CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree [rightStopped.certified.typed]
        rightNode.plan.boundaryTable.entries := by
    have retained : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
        [rightBoundary.stopped.certified.typed]
          rightNode.plan.boundaryTable.entries := by
      simpa only [rightBoundary.entries_eq] using rightEmbedding
    simpa [rightStopped] using retained
  have supportEq : descent.state.certified.typed.boundary.targetSupport =
      rightStopped.certified.typed.boundary.targetSupport := by
    calc
      descent.state.certified.typed.boundary.targetSupport =
          leftReached.sourceAvailable := descent.boundarySupport
      _ = rightReached.sourceAvailable := sourceAvailableEq
      _ = rightStopped.certified.typed.boundary.targetSupport := by
        simpa [rightStopped] using rightBoundary.targetSupport_eq.symm
  have typeEq : descent.state.certified.typed.boundary.targetType =
      rightStopped.certified.typed.boundary.targetType := by
    calc
      descent.state.certified.typed.boundary.targetType =
          mapTypeExpr (color.symbols rhoCIGSLT) (.base "Proc") :=
        descent.boundaryType
      _ = mapTypeExpr (color.symbols rhoCIGSLT) leftReached.sourceType :=
        congrArg (mapTypeExpr (color.symbols rhoCIGSLT)) leftProcess.symm
      _ = mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType :=
        congrArg (mapTypeExpr (color.symbols rhoCIGSLT)) sourceTypeEq
      _ = rightStopped.certified.typed.boundary.targetType := by
        simpa [rightStopped] using rightBoundary.targetType_eq.symm
  have canonical : canonicalize declaration
        descent.state.certified.typed.boundary.content =
      canonicalize declaration
        rightStopped.certified.typed.boundary.content := by
    calc
      canonicalize declaration descent.state.certified.typed.boundary.content =
          canonicalize declaration leftPayload := by
        simpa [target, declaration] using descent.boundaryCanonical
      _ = canonicalize declaration rightPayload :=
        rawAligned.canonicalize_eq declaration stopCanonical
      _ = canonicalize declaration
          rightStopped.certified.typed.boundary.content := by
        rw [show rightStopped.certified.typed.boundary.content = rightPayload by
          simpa [rightStopped] using rightBoundary.content_eq]
  have leftMember : descent.state.certified.typed ∈
      leftNode.plan.boundaryTable.entries := leftEmbedding'.subset (by simp)
  have rightMember : rightStopped.certified.typed ∈
      rightNode.plan.boundaryTable.entries := rightEmbedding'.subset (by simp)
  have leftSmaller := leftNode.plan.boundary_content_size_lt_of_isStaticRoot
    leftNode.rootStatic descent.state.certified.typed leftMember
  have rightSmaller := rightNode.plan.boundary_content_size_lt_of_isStaticRoot
    rightNode.rootStatic rightStopped.certified.typed rightMember
  have smaller :
      sizeOf descent.state.certified.typed.boundary.content +
          sizeOf rightStopped.certified.typed.boundary.content <
        sizeOf leftNode.term.1 + sizeOf rightNode.term.1 := by omega
  obtain ⟨rightRoute'⟩ := rightRoute
  have rightAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      rightStopped.certified.typed.boundary.targetType := by
    rw [show rightStopped.certified.typed.boundary.targetType =
        mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType by
      simpa [rightStopped] using rightBoundary.targetType_eq]
    exact CostCanonicalTypeRoute.rho_admissible rightRoute'
      rightRootAdmissible
  have leftRootEq : leftNode.skeleton.1 =
      leftReached.skeletonContext.fill leftProcessPlan.abstractPattern := by
    exact leftNode.skeleton_pattern.trans
      (leftReached.abstract_eq.trans
        (congrArg leftReached.skeletonContext.fill
          leftProcessAbstract.symm))
  have aligned := stoppedPair_sourcePatternLeafAligned_of_closeSmaller
    leftNode rightNode leftTrees rightTrees leftEnvironment rightEnvironment
    descent.state rightStopped leftReached.skeletonContext
    rightReached.skeletonContext leftRootEq
    (rightNode.skeleton_pattern.trans rightReached.abstract_eq)
    leftEmbedding' rightEmbedding' descent.contextCollapse
    (by simp [rightStopped, canonicalize]) (Or.inl supportEq) typeEq
    declaration canonical _ smaller rightAdmissible closeSmaller leftKey
    rightKey availableDepth scopeDepth
  simpa only [leftProcessAbstract] using aligned

/-- Residual-telescope wrapper for the left-boundary/right-process escape
cell.  All semantic environments are the endpoint environments selected by
the terminal callback; no auxiliary atom carrier is introduced. -/
noncomputable def rhoPlanStopBoundarySide_procEscapePartner_sourceAligned
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (declarationColor : CostStaticColor)
    (rightRootAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1)))
    {rawStop : Pattern → Pattern → Prop}
    (stopCanonical : ∀ {left right}, rawStop left right →
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation) left =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation) right)
    (closeSmaller :
      ∀ {childAvailable childOuter : List TypeExpr}
        {leftChild rightChild : Pattern} {childType : TypeExpr},
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType leftChild →
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType rightChild →
        canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation) leftChild =
          canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation) rightChild →
        sizeOf leftChild + sizeOf rightChild <
          sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1 →
        rhoCanonicalRecursiveTypeDomain.Admissible childType →
        Nonempty (CostCanonicalPairElaboration rhoCIGSLT
          rhoHereditaryNormalizationKernel targetFree childAvailable
          childOuter leftChild rightChild childType))
    (callbackAvailable callbackScope : Nat)
    {leftPayload rightPayload : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftView.node.plan.abstractPattern)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightView.node.plan.abstractPattern)
    (sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
    (sourceAvailableEq : leftReached.sourceAvailable =
      rightReached.sourceAvailable)
    (leftEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree leftReached.plan.boundaryTable.entries
      leftView.node.plan.boundaryTable.entries))
    (rightEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree rightReached.plan.boundaryTable.entries
      rightView.node.plan.boundaryTable.entries))
    (rightRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1))
      (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType)))
    (rawAligned : CanonicalStopAligned
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation)
      rawStop leftPayload rightPayload)
    (leftBoundaryClass : leftReached.plan.rootClass.IsCertifiedBoundary)
    (rightProcess : rightReached.sourceType = .base "Proc")
    (escape : RhoDescendEscape color
      (canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation) rightPayload))
    (targetNeUnit : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation) rightPayload ≠
      .apply
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation).parallelUnitConstructor []) :
    let leftEnvironment := CostStaticAtomEnvironment.ofInventory
      (leftView.node.semanticAtomEnvironment
        (leftView.children.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer))).1
    let rightEnvironment := CostStaticAtomEnvironment.ofInventory
      (rightView.node.semanticAtomEnvironment
        (rightView.children.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer))).1
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    PatternLeafAligned
      (fun leftLeaf rightLeaf => ∀ sourceDepth,
        ReflectiveContextSupport.RestoresTogether
          rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
            cospan.commonAssignment
            (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
              (leftView.node.thinning.thickenAmbientBVars sourceDepth
                (mapPattern (color.symbols rhoCIGSLT) leftLeaf)))
            (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
              (rightView.node.thinning.thickenAmbientBVars sourceDepth
                (mapPattern (color.symbols rhoCIGSLT) rightLeaf))))
      (canonicalizeByDepths
        (sourceSemanticPatternKeyAt leftView.node leftEnvironment)
        rhoReflectivePresentation callbackAvailable callbackScope
        (leftEnvironment.reify leftReached.plan.abstractPattern))
      (canonicalizeByDepths
        (sourceSemanticPatternKeyAt rightView.node rightEnvironment)
        rhoReflectivePresentation callbackAvailable callbackScope
        (rightEnvironment.reify rightReached.plan.abstractPattern)) := by
  obtain ⟨leftBoundary⟩ :=
    leftReached.nonempty_boundaryView_of_boundaryClass leftBoundaryClass
  obtain ⟨leftEmbedding⟩ := leftEmbedding
  obtain ⟨rightEmbedding⟩ := rightEmbedding
  exact boundaryProcEscapePlanStops_sourcePatternLeafAligned_of_closeSmaller
    leftView.node rightView.node leftView.children rightView.children _ _
    leftReached rightReached leftBoundary rightProcess sourceTypeEq
    sourceAvailableEq leftEmbedding rightEmbedding rightRoute
    rightRootAdmissible declarationColor rawAligned stopCanonical escape
    targetNeUnit closeSmaller _ _ callbackAvailable callbackScope

/-- A certified boundary facing any `Proc`-typed reached plan closes.  The
boundary endpoint itself proves that the common raw-stop target is an escaped,
non-unit application; canonical equality transports those two facts to the
partner, where the production process descent exposes its stopped
contributor. -/
noncomputable def rhoPlanStopBoundarySide_processPartner_sourceAligned
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (declarationColor : CostStaticColor)
    (rightRootAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1)))
    {rawStop : Pattern → Pattern → Prop}
    (stopCanonical : ∀ {left right}, rawStop left right →
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation) left =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation) right)
    (closeSmaller :
      ∀ {childAvailable childOuter : List TypeExpr}
        {leftChild rightChild : Pattern} {childType : TypeExpr},
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType leftChild →
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType rightChild →
        canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation) leftChild =
          canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation) rightChild →
        sizeOf leftChild + sizeOf rightChild <
          sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1 →
        rhoCanonicalRecursiveTypeDomain.Admissible childType →
        Nonempty (CostCanonicalPairElaboration rhoCIGSLT
          rhoHereditaryNormalizationKernel targetFree childAvailable
          childOuter leftChild rightChild childType))
    (callbackAvailable callbackScope : Nat)
    {leftPayload rightPayload : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftView.node.plan.abstractPattern)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightView.node.plan.abstractPattern)
    (sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
    (sourceAvailableEq : leftReached.sourceAvailable =
      rightReached.sourceAvailable)
    (leftEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree leftReached.plan.boundaryTable.entries
      leftView.node.plan.boundaryTable.entries))
    (rightEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree rightReached.plan.boundaryTable.entries
      rightView.node.plan.boundaryTable.entries))
    (rightRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1))
      (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType)))
    (rawAligned : CanonicalStopAligned
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation)
      rawStop leftPayload rightPayload)
    (leftBoundaryClass : leftReached.plan.rootClass.IsCertifiedBoundary)
    (rightProcess : rightReached.sourceType = .base "Proc") :
    let leftEnvironment := CostStaticAtomEnvironment.ofInventory
      (leftView.node.semanticAtomEnvironment
        (leftView.children.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer))).1
    let rightEnvironment := CostStaticAtomEnvironment.ofInventory
      (rightView.node.semanticAtomEnvironment
        (rightView.children.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer))).1
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    PatternLeafAligned
      (fun leftLeaf rightLeaf => ∀ sourceDepth,
        ReflectiveContextSupport.RestoresTogether
          rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
            cospan.commonAssignment
            (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
              (leftView.node.thinning.thickenAmbientBVars sourceDepth
                (mapPattern (color.symbols rhoCIGSLT) leftLeaf)))
            (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
              (rightView.node.thinning.thickenAmbientBVars sourceDepth
                (mapPattern (color.symbols rhoCIGSLT) rightLeaf))))
      (canonicalizeByDepths
        (sourceSemanticPatternKeyAt leftView.node leftEnvironment)
        rhoReflectivePresentation callbackAvailable callbackScope
        (leftEnvironment.reify leftReached.plan.abstractPattern))
      (canonicalizeByDepths
        (sourceSemanticPatternKeyAt rightView.node rightEnvironment)
        rhoReflectivePresentation callbackAvailable callbackScope
        (rightEnvironment.reify rightReached.plan.abstractPattern)) := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT
    declarationColor rhoReflectivePresentation
  have gate := rho_boundaryPlan_canonical_escape_of_sourceType_eq_proc
    leftReached.plan (sourceTypeEq.trans rightProcess) leftBoundaryClass
      declarationColor
  have canonicalEq : canonicalize declaration leftPayload =
      canonicalize declaration rightPayload :=
    rawAligned.canonicalize_eq declaration stopCanonical
  have escape : RhoDescendEscape color
      (canonicalize declaration rightPayload) := by
    rw [← canonicalEq]
    exact gate.1
  have targetNeUnit : canonicalize declaration rightPayload ≠
      .apply declaration.parallelUnitConstructor [] := by
    rw [← canonicalEq]
    exact gate.2
  exact rhoPlanStopBoundarySide_procEscapePartner_sourceAligned leftView
    rightView declarationColor rightRootAdmissible stopCanonical closeSmaller
    callbackAvailable callbackScope leftReached rightReached sourceTypeEq
    sourceAvailableEq leftEmbedding rightEmbedding rightRoute rawAligned
    leftBoundaryClass rightProcess escape targetNeUnit

/-- Orientation-preserving residual closure for a `Proc`-typed reached plan
facing a certified boundary on the right.  The right boundary supplies the
escaped, non-unit raw target; canonical equality transports that gate to the
left process descent. -/
noncomputable def rhoPlanStopProcessPartner_boundarySide_sourceAligned
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (declarationColor : CostStaticColor)
    (rightRootAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1)))
    {rawStop : Pattern → Pattern → Prop}
    (stopCanonical : ∀ {left right}, rawStop left right →
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation) left =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation) right)
    (closeSmaller :
      ∀ {childAvailable childOuter : List TypeExpr}
        {leftChild rightChild : Pattern} {childType : TypeExpr},
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType leftChild →
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType rightChild →
        canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation) leftChild =
          canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation) rightChild →
        sizeOf leftChild + sizeOf rightChild <
          sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1 →
        rhoCanonicalRecursiveTypeDomain.Admissible childType →
        Nonempty (CostCanonicalPairElaboration rhoCIGSLT
          rhoHereditaryNormalizationKernel targetFree childAvailable
          childOuter leftChild rightChild childType))
    (callbackAvailable callbackScope : Nat)
    {leftPayload rightPayload : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftView.node.plan.abstractPattern)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightView.node.plan.abstractPattern)
    (sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
    (sourceAvailableEq : leftReached.sourceAvailable =
      rightReached.sourceAvailable)
    (leftEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree leftReached.plan.boundaryTable.entries
      leftView.node.plan.boundaryTable.entries))
    (rightEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree rightReached.plan.boundaryTable.entries
      rightView.node.plan.boundaryTable.entries))
    (rightRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1))
      (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType)))
    (rawAligned : CanonicalStopAligned
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation)
      rawStop leftPayload rightPayload)
    (leftProcess : leftReached.sourceType = .base "Proc")
    (rightBoundaryClass : rightReached.plan.rootClass.IsCertifiedBoundary) :
    let leftEnvironment := CostStaticAtomEnvironment.ofInventory
      (leftView.node.semanticAtomEnvironment
        (leftView.children.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer))).1
    let rightEnvironment := CostStaticAtomEnvironment.ofInventory
      (rightView.node.semanticAtomEnvironment
        (rightView.children.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer))).1
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    PatternLeafAligned
      (fun leftLeaf rightLeaf => ∀ sourceDepth,
        ReflectiveContextSupport.RestoresTogether
          rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
            cospan.commonAssignment
            (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
              (leftView.node.thinning.thickenAmbientBVars sourceDepth
                (mapPattern (color.symbols rhoCIGSLT) leftLeaf)))
            (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
              (rightView.node.thinning.thickenAmbientBVars sourceDepth
                (mapPattern (color.symbols rhoCIGSLT) rightLeaf))))
      (canonicalizeByDepths
        (sourceSemanticPatternKeyAt leftView.node leftEnvironment)
        rhoReflectivePresentation callbackAvailable callbackScope
        (leftEnvironment.reify leftReached.plan.abstractPattern))
      (canonicalizeByDepths
        (sourceSemanticPatternKeyAt rightView.node rightEnvironment)
        rhoReflectivePresentation callbackAvailable callbackScope
        (rightEnvironment.reify rightReached.plan.abstractPattern)) := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT
    declarationColor rhoReflectivePresentation
  have gate := rho_boundaryPlan_canonical_escape_of_sourceType_eq_proc
    rightReached.plan (sourceTypeEq.symm.trans leftProcess) rightBoundaryClass
      declarationColor
  have canonicalEq : canonicalize declaration leftPayload =
      canonicalize declaration rightPayload :=
    rawAligned.canonicalize_eq declaration stopCanonical
  have escape : RhoDescendEscape color
      (canonicalize declaration leftPayload) := by
    rw [canonicalEq]
    exact gate.1
  have targetNeUnit : canonicalize declaration leftPayload ≠
      .apply declaration.parallelUnitConstructor [] := by
    rw [canonicalEq]
    exact gate.2
  obtain ⟨rightBoundary⟩ :=
    rightReached.nonempty_boundaryView_of_boundaryClass rightBoundaryClass
  obtain ⟨leftEmbedding⟩ := leftEmbedding
  obtain ⟨rightEmbedding⟩ := rightEmbedding
  exact procEscapeBoundaryPlanStops_sourcePatternLeafAligned_of_closeSmaller
    leftView.node rightView.node leftView.children rightView.children _ _
    leftReached rightReached leftProcess rightBoundary sourceTypeEq
    sourceAvailableEq leftEmbedding rightEmbedding rightRoute
    rightRootAdmissible declarationColor rawAligned stopCanonical escape
    targetNeUnit closeSmaller _ _ callbackAvailable callbackScope

/-! ## The source-variable partner closes -/

/-- Every proof-relevant elaboration of a free variable has that same free
variable as its hereditary normal form. -/
private theorem normalize_fvar_tree'
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {name : String} {type : TypeExpr}
    (tree : CostRegionTree rhoCIGSLT targetFree available outer (.fvar name)
      type) :
    (tree.normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        .fvar name := by
  let view := tree.structuralRootView tree.rootIsStatic_eq_false_of_fvar
  cases view with
  | fvar lookup => simp [CostRegionTree.normalize]

/-- **Family 1 closes whenever the non-boundary endpoint is an authored source
variable.**

The certified boundary contributes one semantic atom whose value is the
hereditary normal form of its content; the source variable contributes one
semantic atom whose value is that variable.  Recursive closure of the strictly
smaller payload pair identifies the two, and the resulting value is closed, so
the unequal target-support stamps are inert. -/
noncomputable def boundarySourceVariablePlanStops_sourcePatternLeafAligned_of_closeSmaller
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (leftNode rightNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (leftTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      leftNode.finiteBoundaryTable)
    {leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftNode.boundaryTable
      (leftTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      leftNode.skeleton.1}
    {rightValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree rightNode.boundaryTable}
    {rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightNode.boundaryTable rightValues rightNode.skeleton.1}
    (leftEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      rightInventory)
    {leftPayload rightPayload : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftNode.plan.abstractPattern)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightNode.plan.abstractPattern)
    (leftBoundary : leftReached.BoundaryView)
    (rightName : String)
    (rightPayloadEq : rightPayload = .fvar rightName)
    (rightAbstractEq : rightReached.plan.abstractPattern =
      .fvar (costRegionSourceVariableName rightName))
    (rightLookup : targetFree rightName =
      some (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType))
    (sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
    (leftEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      leftReached.plan.boundaryTable.entries
      leftNode.plan.boundaryTable.entries)
    (rightRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT) (.base rightNode.sourceSort.1))
      (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType)))
    (rightRootAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT) (.base rightNode.sourceSort.1)))
    (childDeclaration : ReflectivePresentationDecl)
    {rawStop : Pattern → Pattern → Prop}
    (rawAligned : CanonicalStopAligned childDeclaration rawStop leftPayload
      rightPayload)
    (stopCanonical : ∀ {left right}, rawStop left right →
      canonicalize childDeclaration left = canonicalize childDeclaration right)
    (rightPayloadSizeLe : sizeOf rightPayload ≤ sizeOf rightNode.term.1)
    (closeSmaller :
      ∀ {childAvailable childOuter : List TypeExpr}
        {leftChild rightChild : Pattern} {childType : TypeExpr},
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType leftChild →
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType rightChild →
        canonicalize childDeclaration leftChild =
          canonicalize childDeclaration rightChild →
        sizeOf leftChild + sizeOf rightChild <
          sizeOf leftNode.term.1 + sizeOf rightNode.term.1 →
        rhoCanonicalRecursiveTypeDomain.Admissible childType →
        Nonempty (CostCanonicalPairElaboration rhoCIGSLT
          rhoHereditaryNormalizationKernel targetFree childAvailable
          childOuter leftChild rightChild childType))
    {Key : Type} [LinearOrder Key]
    (leftKey rightKey : Nat → Nat → Pattern → Key)
    (availableDepth scopeDepth : Nat) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    let relation : Pattern → Pattern → Prop := fun leftLeaf rightLeaf =>
      ∀ sourceDepth,
        ReflectiveContextSupport.RestoresTogether
          rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
            cospan.commonAssignment
            (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
              (leftNode.thinning.thickenAmbientBVars sourceDepth
                (mapPattern (color.symbols rhoCIGSLT) leftLeaf)))
            (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
              (rightNode.thinning.thickenAmbientBVars sourceDepth
                (mapPattern (color.symbols rhoCIGSLT) rightLeaf)))
    PatternLeafAligned relation
      (canonicalizeByDepths leftKey rhoReflectivePresentation availableDepth
        scopeDepth
        (leftEnvironment.reify leftReached.plan.abstractPattern))
      (canonicalizeByDepths rightKey rhoReflectivePresentation availableDepth
        scopeDepth
        (rightEnvironment.reify rightReached.plan.abstractPattern)) := by
  intro cospan relation
  -- the left semantic atom
  have leftEmbedding' : CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree [leftBoundary.stopped.certified.typed]
        leftNode.plan.boundaryTable.entries := by
    simpa only [leftBoundary.entries_eq] using leftEmbedding
  let leftAtRoot := leftBoundary.stopped.castRoot leftNode.skeleton_pattern.symm
  have castTyped : leftAtRoot.certified.typed =
      leftBoundary.stopped.certified.typed :=
    CostStaticPlanStopped.castRoot_certified_typed
      leftNode.skeleton_pattern.symm leftBoundary.stopped
  have leftEmbeddingAtRoot : CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree [leftAtRoot.certified.typed]
        leftNode.plan.boundaryTable.entries := by
    rw [castTyped]; exact leftEmbedding'
  obtain ⟨leftSlot, leftSelectedAtRoot⟩ := Option.isSome_iff_exists.mp
    (leftEnvironment.slotOfName?_isSome_of_occurrence
      leftAtRoot.boundaryOccurrence)
  have leftSelectedBoundary : leftEnvironment.slotOfName?
      (costRegionBoundaryVariableName
        leftBoundary.stopped.certified.typed.boundary) = some leftSlot := by
    rw [← castTyped]; exact leftSelectedAtRoot
  -- the right semantic atom
  have rightRootEq : rightNode.skeleton.1 =
      rightReached.skeletonContext.fill
        (.fvar (costRegionSourceVariableName rightName)) :=
    rightNode.skeleton_pattern.trans
      (rightReached.abstract_eq.trans
        (congrArg rightReached.skeletonContext.fill rightAbstractEq))
  let rightOccurrence : CostStaticFVarOccurrence rightNode.skeleton.1 :=
    { name := costRegionSourceVariableName rightName
      context := rightReached.skeletonContext
      selected :=
        Eq.mpr
          (congrArg
            (Selects (.fvar (costRegionSourceVariableName rightName))
              rightReached.skeletonContext) rightRootEq)
          (Selects.of_fill _ _) }
  obtain ⟨rightSlot, rightSelected⟩ := Option.isSome_iff_exists.mp
    (rightEnvironment.slotOfName?_isSome_of_occurrence rightOccurrence)
  have rightSelectedSource : rightEnvironment.slotOfName?
      (costRegionSourceVariableName rightName) = some rightSlot := rightSelected
  have rightNormal : (rightEnvironment.atomValue rightSlot).key.normal =
      .fvar rightName := by
    rw [rightEnvironment.atomValue_normal_eq_of_slotOfName?_eq_some
      rightOccurrence rightSlot rightSelected]
    exact rightValues.assignment_sourceVariable rightName
  -- recursive closure of the strictly smaller payload pair
  have contentEq : leftAtRoot.certified.typed.boundary.content =
      leftPayload := by
    rw [castTyped]; exact leftBoundary.content_eq
  have targetTypeEq : leftAtRoot.certified.typed.boundary.targetType =
      mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType := by
    rw [castTyped, leftBoundary.targetType_eq, sourceTypeEq]
  have canonical : canonicalize childDeclaration
        leftAtRoot.certified.typed.boundary.content =
      canonicalize childDeclaration (.fvar rightName) := by
    rw [contentEq, ← rightPayloadEq]
    exact rawAligned.canonicalize_eq childDeclaration stopCanonical
  have leftMember : leftBoundary.stopped.certified.typed ∈
      leftNode.plan.boundaryTable.entries := leftEmbedding'.subset (by simp)
  have leftSmaller :=
    leftNode.plan.boundary_content_size_lt_of_isStaticRoot leftNode.rootStatic
      leftBoundary.stopped.certified.typed leftMember
  have smaller :
      sizeOf leftAtRoot.certified.typed.boundary.content +
          sizeOf (Pattern.fvar rightName) <
        sizeOf leftNode.term.1 + sizeOf rightNode.term.1 := by
    have rightSize : sizeOf (Pattern.fvar rightName) ≤
        sizeOf rightNode.term.1 := by
      simpa [rightPayloadEq] using rightPayloadSizeLe
    have leftSize : sizeOf leftPayload < sizeOf leftNode.term.1 := by
      simpa only [leftBoundary.content_eq] using leftSmaller
    rw [contentEq]
    omega
  obtain ⟨rightRoute'⟩ := rightRoute
  have rightEndpointAdmissible :=
    CostCanonicalTypeRoute.rho_admissible rightRoute' rightRootAdmissible
  have admissible : rhoCanonicalRecursiveTypeDomain.Admissible
      leftAtRoot.certified.typed.boundary.targetType := by
    rw [targetTypeEq]
    exact rightEndpointAdmissible
  have leftWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree leftAtRoot.certified.typed.boundary.targetSupport
      leftAtRoot.certified.typed.boundary.targetType
      leftAtRoot.certified.typed.boundary.content :=
    ⟨⟨leftAtRoot.certified.typed.contentTyped,
        leftAtRoot.certified.typed.contentCanonicalBinderMetadata,
        leftAtRoot.certified.typed.contentObjectPattern,
        leftAtRoot.certified.typed.contentTyped.isWellScopedAt⟩,
      leftAtRoot.certified.typed.contentReflectiveScopeSafe⟩
  have rightWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree leftAtRoot.certified.typed.boundary.targetSupport
      leftAtRoot.certified.typed.boundary.targetType (.fvar rightName) :=
    ⟨⟨WellSorted.HasType.fvar (by rw [targetTypeEq]; exact rightLookup),
        rfl, rfl, rfl⟩,
      by intro presentation membership; rfl⟩
  let pair := Classical.choice
    (closeSmaller (childOuter := []) leftWellSorted rightWellSorted canonical
      smaller admissible)
  let selectedTree := leftAtRoot.selectedTreeFromForest leftEmbeddingAtRoot
    leftTrees
  have selectedToPair :
      (selectedTree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        (pair.leftTree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern :=
    CostRegionTree.normalize_pattern_eq_of_unambiguous
      CostCanonicalLaws.rho_unambiguousStaticDecomposition
      rhoHereditaryNormalizationKernel selectedTree pair.leftTree
      (by simpa [selectedTree, leftAtRoot] using
        leftAtRoot.certified.typed.contentObjectPattern)
  have pairNormal :
      (pair.leftTree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        (pair.rightTree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
    simpa only [rhoHereditaryNormalizationKernel] using
      pair.alignment.normalize_pattern_eq
  have childNormal :
      (selectedTree.normalizedBoundaryValue
          rhoHereditaryNormalizationKernel).1 = .fvar rightName := by
    rw [CostRegionTree.normalizedBoundaryValue_pattern]
    exact selectedToPair.trans
      (pairNormal.trans (normalize_fvar_tree' pair.rightTree))
  have leftAtom := leftAtRoot.environmentAtom_eq_selectedTree
    (kernel := rhoHereditaryNormalizationKernel)
    CostCanonicalLaws.rho_unambiguousStaticDecomposition leftEmbeddingAtRoot
      leftTrees leftEnvironment leftSlot leftSelectedAtRoot
  have leftNormal : (leftEnvironment.atomValue leftSlot).key.normal =
      .fvar rightName := by
    have normalEq := congrArg (fun atom => atom.key.normal) leftAtom
    have atomToChild : (leftEnvironment.atomValue leftSlot).key.normal =
        ((leftAtRoot.selectedTreeFromForest leftEmbeddingAtRoot leftTrees
          ).normalizedBoundaryValue rhoHereditaryNormalizationKernel).1 := by
      simpa only [TypedCostStaticAtom.ofBoundaryValue] using normalEq
    exact atomToChild.trans (by simpa only [selectedTree] using childNormal)
  -- assemble the semantic leaf
  rw [leftBoundary.abstract_eq, rightAbstractEq]
  simp only [CostStaticAtomEnvironment.reify, canonicalizeByDepths]
  apply PatternLeafAligned.leaf
  intro sourceDepth
  have restores :
      ReflectiveContextSupport.RestoresTogether
        rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
          cospan.commonAssignment
          (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
            (.fvar (leftEnvironment.atomName leftSlot)))
          (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
            (.fvar (rightEnvironment.atomName rightSlot))) := fun depth =>
    leftEnvironment.substituteAt_commonReifiedAtom_eq_of_scoped_normal
      rightEnvironment leftSlot rightSlot (leftNormal.trans rightNormal.symm)
      (by rw [leftNormal]; rfl) depth
  simpa [relation, cospan, mapPattern,
    CostStaticBinderThinning.thickenAmbientBVars,
    CostStaticAtomEnvironment.reifyName, leftSelectedBoundary,
    rightSelectedSource] using restores


/-- **Mirror of
`boundarySourceVariablePlanStops_sourcePatternLeafAligned_of_closeSmaller`**:
the authored source variable on the left, the certified boundary on the
right. -/
noncomputable def sourceVariableBoundaryPlanStops_sourcePatternLeafAligned_of_closeSmaller
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (leftNode rightNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (rightTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      rightNode.finiteBoundaryTable)
    {leftValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree leftNode.boundaryTable}
    {leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftNode.boundaryTable leftValues leftNode.skeleton.1}
    {rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightNode.boundaryTable
      (rightTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      rightNode.skeleton.1}
    (leftEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      rightInventory)
    {leftPayload rightPayload : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftNode.plan.abstractPattern)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightNode.plan.abstractPattern)
    (rightBoundary : rightReached.BoundaryView)
    (leftName : String)
    (leftPayloadEq : leftPayload = .fvar leftName)
    (leftAbstractEq : leftReached.plan.abstractPattern =
      .fvar (costRegionSourceVariableName leftName))
    (leftLookup : targetFree leftName =
      some (mapTypeExpr (color.symbols rhoCIGSLT) leftReached.sourceType))
    (sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
    (rightEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      rightReached.plan.boundaryTable.entries
      rightNode.plan.boundaryTable.entries)
    (rightRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT) (.base rightNode.sourceSort.1))
      (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType)))
    (rightRootAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT) (.base rightNode.sourceSort.1)))
    (childDeclaration : ReflectivePresentationDecl)
    {rawStop : Pattern → Pattern → Prop}
    (rawAligned : CanonicalStopAligned childDeclaration rawStop leftPayload
      rightPayload)
    (stopCanonical : ∀ {left right}, rawStop left right →
      canonicalize childDeclaration left = canonicalize childDeclaration right)
    (leftPayloadSizeLe : sizeOf leftPayload ≤ sizeOf leftNode.term.1)
    (closeSmaller :
      ∀ {childAvailable childOuter : List TypeExpr}
        {leftChild rightChild : Pattern} {childType : TypeExpr},
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType leftChild →
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType rightChild →
        canonicalize childDeclaration leftChild =
          canonicalize childDeclaration rightChild →
        sizeOf leftChild + sizeOf rightChild <
          sizeOf leftNode.term.1 + sizeOf rightNode.term.1 →
        rhoCanonicalRecursiveTypeDomain.Admissible childType →
        Nonempty (CostCanonicalPairElaboration rhoCIGSLT
          rhoHereditaryNormalizationKernel targetFree childAvailable
          childOuter leftChild rightChild childType))
    {Key : Type} [LinearOrder Key]
    (leftKey rightKey : Nat → Nat → Pattern → Key)
    (availableDepth scopeDepth : Nat) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    let relation : Pattern → Pattern → Prop := fun leftLeaf rightLeaf =>
      ∀ sourceDepth,
        ReflectiveContextSupport.RestoresTogether
          rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
            cospan.commonAssignment
            (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
              (leftNode.thinning.thickenAmbientBVars sourceDepth
                (mapPattern (color.symbols rhoCIGSLT) leftLeaf)))
            (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
              (rightNode.thinning.thickenAmbientBVars sourceDepth
                (mapPattern (color.symbols rhoCIGSLT) rightLeaf)))
    PatternLeafAligned relation
      (canonicalizeByDepths leftKey rhoReflectivePresentation availableDepth
        scopeDepth
        (leftEnvironment.reify leftReached.plan.abstractPattern))
      (canonicalizeByDepths rightKey rhoReflectivePresentation availableDepth
        scopeDepth
        (rightEnvironment.reify rightReached.plan.abstractPattern)) := by
  intro cospan relation
  -- the right semantic atom
  have rightEmbedding' : CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree [rightBoundary.stopped.certified.typed]
        rightNode.plan.boundaryTable.entries := by
    simpa only [rightBoundary.entries_eq] using rightEmbedding
  let rightAtRoot :=
    rightBoundary.stopped.castRoot rightNode.skeleton_pattern.symm
  have castTyped : rightAtRoot.certified.typed =
      rightBoundary.stopped.certified.typed :=
    CostStaticPlanStopped.castRoot_certified_typed
      rightNode.skeleton_pattern.symm rightBoundary.stopped
  have rightEmbeddingAtRoot : CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree [rightAtRoot.certified.typed]
        rightNode.plan.boundaryTable.entries := by
    rw [castTyped]; exact rightEmbedding'
  obtain ⟨rightSlot, rightSelectedAtRoot⟩ := Option.isSome_iff_exists.mp
    (rightEnvironment.slotOfName?_isSome_of_occurrence
      rightAtRoot.boundaryOccurrence)
  have rightSelectedBoundary : rightEnvironment.slotOfName?
      (costRegionBoundaryVariableName
        rightBoundary.stopped.certified.typed.boundary) = some rightSlot := by
    rw [← castTyped]; exact rightSelectedAtRoot
  -- the left semantic atom
  have leftRootEq : leftNode.skeleton.1 =
      leftReached.skeletonContext.fill
        (.fvar (costRegionSourceVariableName leftName)) :=
    leftNode.skeleton_pattern.trans
      (leftReached.abstract_eq.trans
        (congrArg leftReached.skeletonContext.fill leftAbstractEq))
  let leftOccurrence : CostStaticFVarOccurrence leftNode.skeleton.1 :=
    { name := costRegionSourceVariableName leftName
      context := leftReached.skeletonContext
      selected :=
        Eq.mpr
          (congrArg
            (Selects (.fvar (costRegionSourceVariableName leftName))
              leftReached.skeletonContext) leftRootEq)
          (Selects.of_fill _ _) }
  obtain ⟨leftSlot, leftSelected⟩ := Option.isSome_iff_exists.mp
    (leftEnvironment.slotOfName?_isSome_of_occurrence leftOccurrence)
  have leftSelectedSource : leftEnvironment.slotOfName?
      (costRegionSourceVariableName leftName) = some leftSlot := leftSelected
  have leftNormal : (leftEnvironment.atomValue leftSlot).key.normal =
      .fvar leftName := by
    rw [leftEnvironment.atomValue_normal_eq_of_slotOfName?_eq_some
      leftOccurrence leftSlot leftSelected]
    exact leftValues.assignment_sourceVariable leftName
  -- recursive closure of the strictly smaller payload pair
  have contentEq : rightAtRoot.certified.typed.boundary.content =
      rightPayload := by
    rw [castTyped]; exact rightBoundary.content_eq
  have targetTypeEq : rightAtRoot.certified.typed.boundary.targetType =
      mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType := by
    rw [castTyped, rightBoundary.targetType_eq]
  have canonical : canonicalize childDeclaration (.fvar leftName) =
      canonicalize childDeclaration
        rightAtRoot.certified.typed.boundary.content := by
    rw [contentEq, ← leftPayloadEq]
    exact rawAligned.canonicalize_eq childDeclaration stopCanonical
  have rightMember : rightBoundary.stopped.certified.typed ∈
      rightNode.plan.boundaryTable.entries := rightEmbedding'.subset (by simp)
  have rightSmaller :=
    rightNode.plan.boundary_content_size_lt_of_isStaticRoot
      rightNode.rootStatic rightBoundary.stopped.certified.typed rightMember
  have smaller :
      sizeOf (Pattern.fvar leftName) +
          sizeOf rightAtRoot.certified.typed.boundary.content <
        sizeOf leftNode.term.1 + sizeOf rightNode.term.1 := by
    have leftSize : sizeOf (Pattern.fvar leftName) ≤
        sizeOf leftNode.term.1 := by
      simpa [leftPayloadEq] using leftPayloadSizeLe
    have rightSize : sizeOf rightPayload < sizeOf rightNode.term.1 := by
      simpa only [rightBoundary.content_eq] using rightSmaller
    rw [contentEq]
    omega
  obtain ⟨rightRoute'⟩ := rightRoute
  have rightEndpointAdmissible :=
    CostCanonicalTypeRoute.rho_admissible rightRoute' rightRootAdmissible
  have admissible : rhoCanonicalRecursiveTypeDomain.Admissible
      rightAtRoot.certified.typed.boundary.targetType := by
    rw [targetTypeEq]
    exact rightEndpointAdmissible
  have rightWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree rightAtRoot.certified.typed.boundary.targetSupport
      rightAtRoot.certified.typed.boundary.targetType
      rightAtRoot.certified.typed.boundary.content :=
    ⟨⟨rightAtRoot.certified.typed.contentTyped,
        rightAtRoot.certified.typed.contentCanonicalBinderMetadata,
        rightAtRoot.certified.typed.contentObjectPattern,
        rightAtRoot.certified.typed.contentTyped.isWellScopedAt⟩,
      rightAtRoot.certified.typed.contentReflectiveScopeSafe⟩
  have leftWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree rightAtRoot.certified.typed.boundary.targetSupport
      rightAtRoot.certified.typed.boundary.targetType (.fvar leftName) :=
    ⟨⟨WellSorted.HasType.fvar
        (by rw [targetTypeEq, ← sourceTypeEq]; exact leftLookup),
        rfl, rfl, rfl⟩,
      by intro presentation membership; rfl⟩
  let pair := Classical.choice
    (closeSmaller (childOuter := []) leftWellSorted rightWellSorted canonical
      smaller admissible)
  let selectedTree := rightAtRoot.selectedTreeFromForest rightEmbeddingAtRoot
    rightTrees
  have selectedToPair :
      (selectedTree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        (pair.rightTree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern :=
    CostRegionTree.normalize_pattern_eq_of_unambiguous
      CostCanonicalLaws.rho_unambiguousStaticDecomposition
      rhoHereditaryNormalizationKernel selectedTree pair.rightTree
      (by simpa [selectedTree, rightAtRoot] using
        rightAtRoot.certified.typed.contentObjectPattern)
  have pairNormal :
      (pair.leftTree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        (pair.rightTree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
    simpa only [rhoHereditaryNormalizationKernel] using
      pair.alignment.normalize_pattern_eq
  have childNormal :
      (selectedTree.normalizedBoundaryValue
          rhoHereditaryNormalizationKernel).1 = .fvar leftName := by
    rw [CostRegionTree.normalizedBoundaryValue_pattern]
    exact selectedToPair.trans
      (pairNormal.symm.trans (normalize_fvar_tree' pair.leftTree))
  have rightAtom := rightAtRoot.environmentAtom_eq_selectedTree
    (kernel := rhoHereditaryNormalizationKernel)
    CostCanonicalLaws.rho_unambiguousStaticDecomposition rightEmbeddingAtRoot
      rightTrees rightEnvironment rightSlot rightSelectedAtRoot
  have rightNormal : (rightEnvironment.atomValue rightSlot).key.normal =
      .fvar leftName := by
    have normalEq := congrArg (fun atom => atom.key.normal) rightAtom
    have atomToChild : (rightEnvironment.atomValue rightSlot).key.normal =
        ((rightAtRoot.selectedTreeFromForest rightEmbeddingAtRoot rightTrees
          ).normalizedBoundaryValue rhoHereditaryNormalizationKernel).1 := by
      simpa only [TypedCostStaticAtom.ofBoundaryValue] using normalEq
    exact atomToChild.trans (by simpa only [selectedTree] using childNormal)
  -- assemble the semantic leaf
  rw [leftAbstractEq, rightBoundary.abstract_eq]
  simp only [CostStaticAtomEnvironment.reify, canonicalizeByDepths]
  apply PatternLeafAligned.leaf
  intro sourceDepth
  have restores :
      ReflectiveContextSupport.RestoresTogether
        rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
          cospan.commonAssignment
          (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
            (.fvar (leftEnvironment.atomName leftSlot)))
          (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
            (.fvar (rightEnvironment.atomName rightSlot))) := fun depth =>
    leftEnvironment.substituteAt_commonReifiedAtom_eq_of_scoped_normal
      rightEnvironment leftSlot rightSlot (leftNormal.trans rightNormal.symm)
      (by rw [leftNormal]; rfl) depth
  simpa [relation, cospan, mapPattern,
    CostStaticBinderThinning.thickenAmbientBVars,
    CostStaticAtomEnvironment.reifyName, leftSelectedSource,
    rightSelectedBoundary] using restores


/-! ## The closed slice, in the residual's own telescope -/

/-- **The rigid slice of family 1 closes on the source-variable partner**, at
either measure, in the shape `RhoStaticNonBoundaryPlanStopSourceAlignedOn`
demands.

Only the sub-family hypotheses `leftBoundaryClass`, `rightRigid` and
`rightAbstractFVar` are added to the residual's own per-stop telescope; the
recursion callback is the provider's, taken at the endpoint pair size, which
is exactly the budget `rho_planStop_boundarySide_size_lt` certifies for this
family at both measures. -/
noncomputable def rhoPlanStopBoundarySide_sourceVariablePartner_sourceAligned
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (declarationColor : CostStaticColor)
    (rightRootAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1)))
    {rawStop : Pattern → Pattern → Prop}
    (stopCanonical : ∀ {left right}, rawStop left right →
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation) left =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation) right)
    (closeSmaller :
      ∀ {childAvailable childOuter : List TypeExpr}
        {leftChild rightChild : Pattern} {childType : TypeExpr},
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType leftChild →
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType rightChild →
        canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation) leftChild =
          canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation) rightChild →
        sizeOf leftChild + sizeOf rightChild <
          sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1 →
        rhoCanonicalRecursiveTypeDomain.Admissible childType →
        Nonempty (CostCanonicalPairElaboration rhoCIGSLT
          rhoHereditaryNormalizationKernel targetFree childAvailable
          childOuter leftChild rightChild childType))
    (callbackAvailable callbackScope : Nat)
    {leftPayload rightPayload : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftView.node.plan.abstractPattern)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightView.node.plan.abstractPattern)
    (sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
    (leftEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree leftReached.plan.boundaryTable.entries
      leftView.node.plan.boundaryTable.entries))
    (rightRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1))
      (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType)))
    (rightPayloadSizeLe : sizeOf rightPayload ≤ sizeOf rightView.node.term.1)
    (rawAligned : CanonicalStopAligned
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation)
      rawStop leftPayload rightPayload)
    (leftBoundaryClass : leftReached.plan.rootClass.IsCertifiedBoundary)
    (rightRigid : rightReached.plan.rootClass = .rigid)
    (rightAbstractFVar : ∃ name,
      rightReached.plan.abstractPattern = .fvar name) :
    let leftEnvironment := CostStaticAtomEnvironment.ofInventory
      (leftView.node.semanticAtomEnvironment
        (leftView.children.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer))).1
    let rightEnvironment := CostStaticAtomEnvironment.ofInventory
      (rightView.node.semanticAtomEnvironment
        (rightView.children.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer))).1
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    PatternLeafAligned
      (fun leftLeaf rightLeaf => ∀ sourceDepth,
        ReflectiveContextSupport.RestoresTogether
          rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
            cospan.commonAssignment
            (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
              (leftView.node.thinning.thickenAmbientBVars sourceDepth
                (mapPattern (color.symbols rhoCIGSLT) leftLeaf)))
            (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
              (rightView.node.thinning.thickenAmbientBVars sourceDepth
                (mapPattern (color.symbols rhoCIGSLT) rightLeaf))))
      (canonicalizeByDepths
        (sourceSemanticPatternKeyAt leftView.node leftEnvironment)
        rhoReflectivePresentation callbackAvailable callbackScope
        (leftEnvironment.reify leftReached.plan.abstractPattern))
      (canonicalizeByDepths
        (sourceSemanticPatternKeyAt rightView.node rightEnvironment)
        rhoReflectivePresentation callbackAvailable callbackScope
        (rightEnvironment.reify rightReached.plan.abstractPattern)) := by
  obtain ⟨rightAbstractName, rightAbstractNameEq⟩ := rightAbstractFVar
  obtain ⟨leftBoundaryView⟩ :=
    leftReached.nonempty_boundaryView_of_boundaryClass leftBoundaryClass
  obtain ⟨leftEmbedding⟩ := leftEmbedding
  rcases CostStaticRegionPlan.rigid_cases rightReached.plan rightRigid with
    ⟨index, sourceIndex, _, absEq⟩ | ⟨name, payloadEq, absEq, lookup⟩ |
    ⟨binder, body, abstractBody, _, absEq⟩ |
    ⟨arity, binders, body, abstractBody, _, absEq⟩
  · rw [absEq] at rightAbstractNameEq
    exact absurd rightAbstractNameEq (by simp)
  · exact boundarySourceVariablePlanStops_sourcePatternLeafAligned_of_closeSmaller
      leftView.node rightView.node leftView.children _ _ leftReached
      rightReached leftBoundaryView name payloadEq absEq lookup sourceTypeEq
      leftEmbedding rightRoute rightRootAdmissible _ rawAligned stopCanonical
      rightPayloadSizeLe closeSmaller _ _ callbackAvailable callbackScope
  · rw [absEq] at rightAbstractNameEq
    exact absurd rightAbstractNameEq (by simp)
  · rw [absEq] at rightAbstractNameEq
    exact absurd rightAbstractNameEq (by simp)

/-- Mirror of `rhoPlanStopBoundarySide_sourceVariablePartner_sourceAligned`. -/
noncomputable def rhoPlanStopSourceVariablePartner_boundarySide_sourceAligned
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (declarationColor : CostStaticColor)
    (rightRootAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1)))
    {rawStop : Pattern → Pattern → Prop}
    (stopCanonical : ∀ {left right}, rawStop left right →
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation) left =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation) right)
    (closeSmaller :
      ∀ {childAvailable childOuter : List TypeExpr}
        {leftChild rightChild : Pattern} {childType : TypeExpr},
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType leftChild →
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType rightChild →
        canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation) leftChild =
          canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation) rightChild →
        sizeOf leftChild + sizeOf rightChild <
          sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1 →
        rhoCanonicalRecursiveTypeDomain.Admissible childType →
        Nonempty (CostCanonicalPairElaboration rhoCIGSLT
          rhoHereditaryNormalizationKernel targetFree childAvailable
          childOuter leftChild rightChild childType))
    (callbackAvailable callbackScope : Nat)
    {leftPayload rightPayload : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftView.node.plan.abstractPattern)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightView.node.plan.abstractPattern)
    (sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
    (rightEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree rightReached.plan.boundaryTable.entries
      rightView.node.plan.boundaryTable.entries))
    (rightRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1))
      (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType)))
    (leftPayloadSizeLe : sizeOf leftPayload ≤ sizeOf leftView.node.term.1)
    (rawAligned : CanonicalStopAligned
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation)
      rawStop leftPayload rightPayload)
    (leftRigid : leftReached.plan.rootClass = .rigid)
    (leftAbstractFVar : ∃ name,
      leftReached.plan.abstractPattern = .fvar name)
    (rightBoundaryClass : rightReached.plan.rootClass.IsCertifiedBoundary) :
    let leftEnvironment := CostStaticAtomEnvironment.ofInventory
      (leftView.node.semanticAtomEnvironment
        (leftView.children.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer))).1
    let rightEnvironment := CostStaticAtomEnvironment.ofInventory
      (rightView.node.semanticAtomEnvironment
        (rightView.children.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer))).1
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    PatternLeafAligned
      (fun leftLeaf rightLeaf => ∀ sourceDepth,
        ReflectiveContextSupport.RestoresTogether
          rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
            cospan.commonAssignment
            (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
              (leftView.node.thinning.thickenAmbientBVars sourceDepth
                (mapPattern (color.symbols rhoCIGSLT) leftLeaf)))
            (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
              (rightView.node.thinning.thickenAmbientBVars sourceDepth
                (mapPattern (color.symbols rhoCIGSLT) rightLeaf))))
      (canonicalizeByDepths
        (sourceSemanticPatternKeyAt leftView.node leftEnvironment)
        rhoReflectivePresentation callbackAvailable callbackScope
        (leftEnvironment.reify leftReached.plan.abstractPattern))
      (canonicalizeByDepths
        (sourceSemanticPatternKeyAt rightView.node rightEnvironment)
        rhoReflectivePresentation callbackAvailable callbackScope
        (rightEnvironment.reify rightReached.plan.abstractPattern)) := by
  obtain ⟨leftAbstractName, leftAbstractNameEq⟩ := leftAbstractFVar
  obtain ⟨rightBoundaryView⟩ :=
    rightReached.nonempty_boundaryView_of_boundaryClass rightBoundaryClass
  obtain ⟨rightEmbedding⟩ := rightEmbedding
  rcases CostStaticRegionPlan.rigid_cases leftReached.plan leftRigid with
    ⟨index, sourceIndex, _, absEq⟩ | ⟨name, payloadEq, absEq, lookup⟩ |
    ⟨binder, body, abstractBody, _, absEq⟩ |
    ⟨arity, binders, body, abstractBody, _, absEq⟩
  · rw [absEq] at leftAbstractNameEq
    exact absurd leftAbstractNameEq (by simp)
  · exact sourceVariableBoundaryPlanStops_sourcePatternLeafAligned_of_closeSmaller
      leftView.node rightView.node rightView.children _ _ leftReached
      rightReached rightBoundaryView name payloadEq absEq lookup sourceTypeEq
      rightEmbedding rightRoute rightRootAdmissible _ rawAligned stopCanonical
      leftPayloadSizeLe closeSmaller _ _ callbackAvailable callbackScope
  · rw [absEq] at leftAbstractNameEq
    exact absurd leftAbstractNameEq (by simp)
  · rw [absEq] at leftAbstractNameEq
    exact absurd leftAbstractNameEq (by simp)

/-- The certified-boundary family restricted to a rigid partner, in either
orientation. -/
def RhoPlanStopBoundaryRigidCell (leftClass rightClass :
    CostStaticPlanRootClass) : Prop :=
  (leftClass.IsCertifiedBoundary ∧ rightClass = .rigid) ∨
    (leftClass = .rigid ∧ rightClass.IsCertifiedBoundary)

/-- The whole rigid-partner slice of the certified-boundary residual is
closed.  The raw stop excludes bound variables, common typing excludes both
binder plans, and the remaining source-variable case is the semantic atom
alignment proved above. -/
noncomputable def rhoPlanStopBoundaryRigid_sourceAligned
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (declarationColor : CostStaticColor)
    (parentMeasure : Nat)
    (rightRootAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1)))
    (closeSmaller :
      ∀ {childAvailable childOuter : List TypeExpr}
        {leftChild rightChild : Pattern} {childType : TypeExpr},
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType leftChild →
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType rightChild →
        canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation) leftChild =
          canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation) rightChild →
        sizeOf leftChild + sizeOf rightChild <
          sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1 →
        rhoCanonicalRecursiveTypeDomain.Admissible childType →
        Nonempty (CostCanonicalPairElaboration rhoCIGSLT
          rhoHereditaryNormalizationKernel targetFree childAvailable
          childOuter leftChild rightChild childType)) :
    RhoStaticNonBoundaryPlanStopSourceAlignedOn leftView rightView
      declarationColor (RhoCanonicalRawStop declarationColor parentMeasure)
      RhoPlanStopBoundaryRigidCell := by
  intro callbackAvailable callbackScope leftAbstract rightAbstract leftPayload
    rightPayload leftReached rightReached leftAdmission rightAdmission
    leftAbstractEq rightAbstractEq sourceTypeEq sourceAvailableEq sourceBoundEq
    targetBoundEq thinningEq leftEmbedding rightEmbedding leftRoute rightRoute
    stopReason leftPayloadSizeLe rightPayloadSizeLe rawAligned notBothBoundary
    cell
  rcases cell with ⟨leftBoundary, rightRigid⟩ |
      ⟨leftRigid, rightBoundary⟩
  · obtain ⟨name, payloadEq, abstractEq, lookup⟩ :=
      boundarySide_rigidPartner_is_sourceVariable leftReached rightReached
        sourceTypeEq leftBoundary rightRigid stopReason
    have aligned :=
      rhoPlanStopBoundarySide_sourceVariablePartner_sourceAligned
        leftView rightView declarationColor rightRootAdmissible
        (fun stopped => stopped.1.2) closeSmaller callbackAvailable
        callbackScope leftReached rightReached sourceTypeEq leftEmbedding
        rightRoute rightPayloadSizeLe rawAligned leftBoundary rightRigid
        ⟨costRegionSourceVariableName name, abstractEq⟩
    simpa only [← leftAbstractEq, ← rightAbstractEq] using aligned
  · obtain ⟨name, payloadEq, abstractEq, lookup⟩ :=
      rigidPartner_boundarySide_is_sourceVariable leftReached rightReached
        sourceTypeEq leftRigid rightBoundary stopReason
    have aligned :=
      rhoPlanStopSourceVariablePartner_boundarySide_sourceAligned
        leftView rightView declarationColor rightRootAdmissible
        (fun stopped => stopped.1.2) closeSmaller callbackAvailable
        callbackScope leftReached rightReached sourceTypeEq rightEmbedding
        rightRoute leftPayloadSizeLe rawAligned leftRigid
        ⟨costRegionSourceVariableName name, abstractEq⟩ rightBoundary
    simpa only [← leftAbstractEq, ← rightAbstractEq] using aligned

/-- The certified-boundary residual away from the authored `NQuote` root, in
either endpoint orientation. -/
def RhoPlanStopBoundaryNonQuoteCell (leftClass rightClass :
    CostStaticPlanRootClass) : Prop :=
  (leftClass.IsCertifiedBoundary ∧
      rightClass ≠ .application rhoReflectivePresentation.quoteConstructor) ∨
    (leftClass ≠ .application rhoReflectivePresentation.quoteConstructor ∧
      rightClass.IsCertifiedBoundary)

/-- Every certified-boundary residual whose partner is not an authored quote
is source aligned.  Rigid partners reduce to source variables, while ordinary
applications and admissible collections lie in rho's process fibre. -/
noncomputable def rhoPlanStopBoundaryNonQuote_sourceAligned
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (declarationColor : CostStaticColor)
    (parentMeasure : Nat)
    (rightRootAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1)))
    (closeSmaller :
      ∀ {childAvailable childOuter : List TypeExpr}
        {leftChild rightChild : Pattern} {childType : TypeExpr},
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType leftChild →
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType rightChild →
        canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation) leftChild =
          canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation) rightChild →
        sizeOf leftChild + sizeOf rightChild <
          sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1 →
        rhoCanonicalRecursiveTypeDomain.Admissible childType →
        Nonempty (CostCanonicalPairElaboration rhoCIGSLT
          rhoHereditaryNormalizationKernel targetFree childAvailable
          childOuter leftChild rightChild childType)) :
    RhoStaticNonBoundaryPlanStopSourceAlignedOn leftView rightView
      declarationColor (RhoCanonicalRawStop declarationColor parentMeasure)
      RhoPlanStopBoundaryNonQuoteCell := by
  intro callbackAvailable callbackScope leftAbstract rightAbstract leftPayload
    rightPayload leftReached rightReached leftAdmission rightAdmission
    leftAbstractEq rightAbstractEq sourceTypeEq sourceAvailableEq sourceBoundEq
    targetBoundEq thinningEq leftEmbedding rightEmbedding leftRoute rightRoute
    stopReason leftPayloadSizeLe rightPayloadSizeLe rawAligned notBothBoundary
    cell
  obtain ⟨rightRoute'⟩ := rightRoute
  have rightEndpointAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType) :=
    CostCanonicalTypeRoute.rho_admissible rightRoute' rightRootAdmissible
  rcases cell with ⟨leftBoundary, rightNotQuote⟩ |
      ⟨leftNotQuote, rightBoundary⟩
  · rcases
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionPlan.rootClass_cases
        rightReached.plan with rightRigid |
        ⟨constructor, rightApplication⟩ |
        ⟨collectionType, rightCollection⟩ | rightBoundary'
    · obtain ⟨name, payloadEq, abstractEq, lookup⟩ :=
        boundarySide_rigidPartner_is_sourceVariable leftReached rightReached
          sourceTypeEq leftBoundary rightRigid stopReason
      have aligned :=
        rhoPlanStopBoundarySide_sourceVariablePartner_sourceAligned
          leftView rightView declarationColor rightRootAdmissible
          (fun stopped => stopped.1.2) closeSmaller callbackAvailable
          callbackScope leftReached rightReached sourceTypeEq leftEmbedding
          ⟨rightRoute'⟩ rightPayloadSizeLe rawAligned leftBoundary rightRigid
          ⟨costRegionSourceVariableName name, abstractEq⟩
      simpa only [← leftAbstractEq, ← rightAbstractEq] using aligned
    · have rightProcess :=
        rho_applicationPlan_sourceType_eq_proc_of_not_quote rightReached.plan
          rightApplication (fun equality => rightNotQuote
            (rightApplication.trans (congrArg _ equality)))
      have aligned := rhoPlanStopBoundarySide_processPartner_sourceAligned
        leftView rightView declarationColor rightRootAdmissible
        (fun stopped => stopped.1.2) closeSmaller callbackAvailable
        callbackScope leftReached rightReached sourceTypeEq sourceAvailableEq
        leftEmbedding rightEmbedding ⟨rightRoute'⟩ rawAligned leftBoundary
        rightProcess
      simpa only [← leftAbstractEq, ← rightAbstractEq] using aligned
    · have rightProcess := rho_collectionPlan_sourceType_eq_proc
        rightReached.plan ⟨collectionType, rightCollection⟩
          rightEndpointAdmissible
      have aligned := rhoPlanStopBoundarySide_processPartner_sourceAligned
        leftView rightView declarationColor rightRootAdmissible
        (fun stopped => stopped.1.2) closeSmaller callbackAvailable
        callbackScope leftReached rightReached sourceTypeEq sourceAvailableEq
        leftEmbedding rightEmbedding ⟨rightRoute'⟩ rawAligned leftBoundary
        rightProcess
      simpa only [← leftAbstractEq, ← rightAbstractEq] using aligned
    · exact (notBothBoundary ⟨leftBoundary, rightBoundary'⟩).elim
  · rcases
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionPlan.rootClass_cases
        leftReached.plan with leftRigid |
        ⟨constructor, leftApplication⟩ |
        ⟨collectionType, leftCollection⟩ | leftBoundary'
    · obtain ⟨name, payloadEq, abstractEq, lookup⟩ :=
        rigidPartner_boundarySide_is_sourceVariable leftReached rightReached
          sourceTypeEq leftRigid rightBoundary stopReason
      have aligned :=
        rhoPlanStopSourceVariablePartner_boundarySide_sourceAligned
          leftView rightView declarationColor rightRootAdmissible
          (fun stopped => stopped.1.2) closeSmaller callbackAvailable
          callbackScope leftReached rightReached sourceTypeEq rightEmbedding
          ⟨rightRoute'⟩ leftPayloadSizeLe rawAligned leftRigid
          ⟨costRegionSourceVariableName name, abstractEq⟩ rightBoundary
      simpa only [← leftAbstractEq, ← rightAbstractEq] using aligned
    · have leftProcess :=
        rho_applicationPlan_sourceType_eq_proc_of_not_quote leftReached.plan
          leftApplication (fun equality => leftNotQuote
            (leftApplication.trans (congrArg _ equality)))
      have aligned := rhoPlanStopProcessPartner_boundarySide_sourceAligned
        leftView rightView declarationColor rightRootAdmissible
        (fun stopped => stopped.1.2) closeSmaller callbackAvailable
        callbackScope leftReached rightReached sourceTypeEq sourceAvailableEq
        leftEmbedding rightEmbedding ⟨rightRoute'⟩ rawAligned leftProcess
        rightBoundary
      simpa only [← leftAbstractEq, ← rightAbstractEq] using aligned
    · have leftEndpointAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
          (mapTypeExpr (color.symbols rhoCIGSLT) leftReached.sourceType) := by
        rw [sourceTypeEq]
        exact rightEndpointAdmissible
      have leftProcess := rho_collectionPlan_sourceType_eq_proc
        leftReached.plan ⟨collectionType, leftCollection⟩
          leftEndpointAdmissible
      have aligned := rhoPlanStopProcessPartner_boundarySide_sourceAligned
        leftView rightView declarationColor rightRootAdmissible
        (fun stopped => stopped.1.2) closeSmaller callbackAvailable
        callbackScope leftReached rightReached sourceTypeEq sourceAvailableEq
        leftEmbedding rightEmbedding ⟨rightRoute'⟩ rawAligned leftProcess
        rightBoundary
      simpa only [← leftAbstractEq, ← rightAbstractEq] using aligned
    · exact (notBothBoundary ⟨leftBoundary', rightBoundary⟩).elim

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
