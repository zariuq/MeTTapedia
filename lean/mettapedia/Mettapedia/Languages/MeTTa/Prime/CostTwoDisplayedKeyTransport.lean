import Mettapedia.GSLT.LanguageDef.CostOneElaborationDisplayed
import Mettapedia.Languages.MeTTa.Prime.CostTwoImplementationKeyContract
import Mettapedia.Languages.MeTTa.Prime.NIKPolicyFamilyTransport

/-!
# Transport of Cost² implementation keys

The proof-relevant Cost elaboration carrier already reindexes structurally
along conservative Cost₁ morphisms.  This module proves that the global
compact implementation key is natural for that displayed transport.

The result is deliberately policy-relative.  A compact observation can be
pulled back along transport and admitted as a hot keyed operation without
replaying the elaboration tree.  Exact receipts remain governed by compact
erasure faithfulness; transport does not manufacture an inverse to a lossy
key.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime.CostTwoDisplayedKeyTransport

open CategoryTheory
open Mettapedia.GSLT.Core
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.NIKPolicyFamilyAdmission
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.Languages.MeTTa.Prime.PrimeAbstractImplementationModel
open Mettapedia.Languages.MeTTa.Prime.CostTwoCacheReplayBoundary
open Mettapedia.Languages.MeTTa.Prime.CostTwoImplementationKeyContract
open Mettapedia.Languages.MeTTa.Prime.CostTwoPolicyFamilyObservationBridge
open Mettapedia.Languages.MeTTa.Prime.CostTwoPolicyKeyNIKAdmission
open Mettapedia.Languages.MeTTa.Prime.NIKPolicyFamilyTransport

universe uPolicy uValue

/-! ## The compact transport forced by a continued morphism -/

/-- Map the complete intrinsically indexed compact Cost term.  This is the
proof-erased shadow of `mapCostElaborationFiber`; it retains the term and all
three dependent indices while forgetting only the selected elaboration tree.
-/
def mapCompactCostCarrier {source target : CIGSLT}
    (morphism : source.Morphism target)
    (scope : CostGeneratedReflectiveScopePreserving morphism) :
    CompactCostCarrier source → CompactCostCarrier target
  | ⟨index, term⟩ =>
      ⟨index.map morphism, morphism.mapCostOpenTerm scope term⟩

/-- Compact erasure is natural for structural transport of the full retained
Cost elaboration.  No recompilation or comparison of proof trees occurs. -/
@[simp] theorem compactCarrierKey_mapCostElaborationFiber
    {source target : CIGSLT}
    (morphism : source.Morphism target)
    (scope : CostGeneratedReflectiveScopePreserving morphism)
    (laws : CostElaborationReindexLaws morphism)
    (fiber : CostElaborationFiber source) :
    compactCarrierKey target
        (mapCostElaborationFiber morphism scope laws fiber) =
      mapCompactCostCarrier morphism scope
        (compactCarrierKey source fiber) := by
  rcases fiber with ⟨index, term, elaboration⟩
  rfl

/-! ## Specialization to the displayed Cost₁ category -/

/-- The compact action underlying one conservative lawful Cost₁ arrow. -/
def transportCompactCarrier {source target : CostElaborationBase}
    (morphism : source ⟶ target) :
    CompactCostCarrier source.toCostOne.source.toCIGSLT →
      CompactCostCarrier target.toCostOne.source.toCIGSLT :=
  mapCompactCostCarrier
    morphism.underlying.underlying.underlying
    (CostOneMorphismLaws.preservesGeneratedReflectiveScope
      morphism.underlying.laws.toCostOneMorphismLaws)

/-- The global compact key commutes with the chosen strongly cocartesian
displayed transport. -/
@[simp] theorem compactCarrierKey_transportFiber
    {source target : CostElaborationBase}
    (morphism : source ⟶ target)
    (fiber : CostElaborationFiber source.toCostOne.source.toCIGSLT) :
    compactCarrierKey target.toCostOne.source.toCIGSLT
        (CostOneElaborationTotal.transportFiber morphism fiber) =
      transportCompactCarrier morphism
        (compactCarrierKey source.toCostOne.source.toCIGSLT fiber) := by
  exact compactCarrierKey_mapCostElaborationFiber
    morphism.underlying.underlying.underlying
    (CostOneMorphismLaws.preservesGeneratedReflectiveScope
      morphism.underlying.laws.toCostOneMorphismLaws)
    morphism.reindexLaws fiber

/-- The source compact key is a concrete information refinement of the
target compact key after displayed state transport.  Its forgetting map is
the compact action induced by the Cost₁ morphism. -/
def compactTransportKeyRefinement {source target : CostElaborationBase}
    (morphism : source ⟶ target) :
    KeyRefinement
      (compactCarrierKey source.toCostOne.source.toCIGSLT)
      (compactCarrierKey target.toCostOne.source.toCIGSLT ∘
        CostOneElaborationTotal.transportFiber morphism) where
  forget := transportCompactCarrier morphism
  commutes := by
    funext fiber
    exact compactCarrierKey_transportFiber morphism fiber

/-- Any compact observation commutes with one displayed transport after
pullback along the induced compact action. -/
theorem compactPolicy_transport_agrees
    {source target : CostElaborationBase}
    (morphism : source ⟶ target)
    {Value : Type uValue}
    (observe : CompactCostCarrier target.toCostOne.source.toCIGSLT → Value)
    (fiber : CostElaborationFiber source.toCostOne.source.toCIGSLT) :
    observe
        (compactCarrierKey target.toCostOne.source.toCIGSLT
          (CostOneElaborationTotal.transportFiber morphism fiber)) =
      observe
        (transportCompactCarrier morphism
          (compactCarrierKey source.toCostOne.source.toCIGSLT fiber)) := by
  rw [compactCarrierKey_transportFiber]

/-- The commuting law composes for two successive displayed transports.
This statement does not identify the retained proof chosen by recompilation
with the structurally transported proof. -/
theorem compactPolicy_transport_comp_agrees
    {first second third : CostElaborationBase}
    (earlier : first ⟶ second) (later : second ⟶ third)
    {Value : Type uValue}
    (observe : CompactCostCarrier third.toCostOne.source.toCIGSLT → Value)
    (fiber : CostElaborationFiber first.toCostOne.source.toCIGSLT) :
    observe
        (compactCarrierKey third.toCostOne.source.toCIGSLT
          (CostOneElaborationTotal.transportFiber later
            (CostOneElaborationTotal.transportFiber earlier fiber))) =
      observe
        (transportCompactCarrier later
          (transportCompactCarrier earlier
            (compactCarrierKey first.toCostOne.source.toCIGSLT fiber))) := by
  rw [compactCarrierKey_transportFiber, compactCarrierKey_transportFiber]

/-! ## NIK admission is stable under policy pullback -/

/-- Pulling a target compact observation back along displayed transport gives
a policy-only NIK admission over the source compact key. -/
def transportedCompactPolicyAdmission
    (dependencies : DependencySystem) (revision : dependencies.Revision)
    {source target : CostElaborationBase} (morphism : source ⟶ target)
    {Value : Type uValue}
    (observe : CompactCostCarrier target.toCostOne.source.toCIGSLT → Value) :
    PolicyKeyAdmission dependencies revision
      (singlePolicyRequest
        (observe ∘ transportCompactCarrier morphism ∘
          compactCarrierKey source.toCostOne.source.toCIGSLT) False)
      (compactCarrierKey source.toCostOne.source.toCIGSLT) :=
  compactDerivedPolicyAdmission dependencies revision
    source.toCostOne.source.toCIGSLT
    (observe ∘ transportCompactCarrier morphism)

/-- The admitted source runner returns exactly the target compact policy on
the structurally transported semantic state. -/
@[simp] theorem transportedCompactPolicyAdmission_run
    (dependencies : DependencySystem) (revision : dependencies.Revision)
    {source target : CostElaborationBase} (morphism : source ⟶ target)
    {Value : Type uValue}
    (observe : CompactCostCarrier target.toCostOne.source.toCIGSLT → Value)
    (fiber : CostElaborationFiber source.toCostOne.source.toCIGSLT) :
    ((transportedCompactPolicyAdmission dependencies revision morphism observe).realize
      ()).run
        (compactCarrierKey source.toCostOne.source.toCIGSLT fiber) =
      observe
        (compactCarrierKey target.toCostOne.source.toCIGSLT
          (CostOneElaborationTotal.transportFiber morphism fiber)) := by
  rw [PolicyRealization.run_encode]
  exact (compactPolicy_transport_agrees morphism observe fiber).symm

/-! ## Dependent policy families transport together -/

/-- Pull a complete dependent target policy family back along one displayed
Cost transport.  The observations and their dependent result types are
retained.  Exact replay is deliberately not pulled back: it is a distinct
capability requiring a decoder for the source state. -/
def pullbackPolicyRequest
    {source target : CostElaborationBase} (morphism : source ⟶ target)
    (request : PolicyRequest
      (CostElaborationFiber target.toCostOne.source.toCIGSLT)) :
    PolicyRequest (CostElaborationFiber source.toCostOne.source.toCIGSLT) where
  Policy := request.Policy
  Value := request.Value
  observe := fun policy fiber =>
    request.observe policy
      (CostOneElaborationTotal.transportFiber morphism fiber)
  requiresExactReplay := False

/-- The Cost-specific dependent request is exactly the generic policy-family
pullback at every policy coordinate. -/
@[simp] theorem observationFamily_pullbackPolicyRequest_decide
    {source target : CostElaborationBase} (morphism : source ⟶ target)
    (request : PolicyRequest
      (CostElaborationFiber target.toCostOne.source.toCIGSLT))
    (policy : request.Policy)
    (fiber : CostElaborationFiber source.toCostOne.source.toCIGSLT) :
    (observationFamily (pullbackPolicyRequest morphism request)).decide
        policy fiber =
      ((observationFamily request).pullback
        (CostOneElaborationTotal.transportFiber morphism)).decide
          policy fiber :=
  rfl

/-- Every target policy runner admitted over the compact target key pulls back
to a runner over the compact source key.  This reuses the target executable
functions and the compact naturality square; it performs no proof replay. -/
def pullbackCompactPolicyAdmission
    (dependencies : DependencySystem) (revision : dependencies.Revision)
    {source target : CostElaborationBase} (morphism : source ⟶ target)
    {request : PolicyRequest
      (CostElaborationFiber target.toCostOne.source.toCIGSLT)}
    (targetAdmission : PolicyKeyAdmission dependencies revision request
      (compactCarrierKey target.toCostOne.source.toCIGSLT)) :
    PolicyKeyAdmission dependencies revision
      (pullbackPolicyRequest morphism request)
      (compactCarrierKey source.toCostOne.source.toCIGSLT) where
  realize := fun policy =>
    { run := (targetAdmission.realize policy).run ∘
        transportCompactCarrier morphism
      agrees := by
        funext fiber
        change request.observe policy
            (CostOneElaborationTotal.transportFiber morphism fiber) =
          (targetAdmission.realize policy).run
            (transportCompactCarrier morphism
              (compactCarrierKey source.toCostOne.source.toCIGSLT fiber))
        rw [← compactCarrierKey_transportFiber]
        exact congrFun (targetAdmission.realize policy).agrees
          (CostOneElaborationTotal.transportFiber morphism fiber) }
  replay := fun impossible => False.elim impossible

/-- The generic NIK route gives the same Cost pullback in two conceptual
steps: transport the admitted policy family along semantic state, then refine
the transported compact key to the source compact key. -/
def pullbackCompactPolicyAdmissionViaGeneric
    (dependencies : DependencySystem) (revision : dependencies.Revision)
    {source target : CostElaborationBase} (morphism : source ⟶ target)
    {request : PolicyRequest
      (CostElaborationFiber target.toCostOne.source.toCIGSLT)}
    (targetAdmission : PolicyKeyAdmission dependencies revision request
      (compactCarrierKey target.toCostOne.source.toCIGSLT)) :
    PolicyKeyAdmission dependencies revision
      (pullbackPolicyRequest morphism request)
      (compactCarrierKey source.toCostOne.source.toCIGSLT) :=
  PolicyKeyAdmission.pullback
    (ofGenericAdmissionPolicyOnly
      (PolicyFamilyAdmittedAt.pullbackState
        (CostOneElaborationTotal.transportFiber morphism)
        (toGenericAdmission targetAdmission))
      (by simp [pullbackPolicyRequest]))
    (compactTransportKeyRefinement morphism)

/-- The factorized generic construction retains exactly the same keyed
executable function as the direct Cost specialization. -/
@[simp] theorem pullbackCompactPolicyAdmissionViaGeneric_run
    (dependencies : DependencySystem) (revision : dependencies.Revision)
    {source target : CostElaborationBase} (morphism : source ⟶ target)
    {request : PolicyRequest
      (CostElaborationFiber target.toCostOne.source.toCIGSLT)}
    (targetAdmission : PolicyKeyAdmission dependencies revision request
      (compactCarrierKey target.toCostOne.source.toCIGSLT))
    (policy : request.Policy)
    (encoded : CompactCostCarrier source.toCostOne.source.toCIGSLT) :
    ((pullbackCompactPolicyAdmissionViaGeneric dependencies revision morphism
      targetAdmission).realize policy).run encoded =
      ((pullbackCompactPolicyAdmission dependencies revision morphism
        targetAdmission).realize policy).run encoded :=
  rfl

/-- Each pulled-back member of the dependent policy family returns exactly
the target observation of the structurally transported state. -/
@[simp] theorem pullbackCompactPolicyAdmission_run
    (dependencies : DependencySystem) (revision : dependencies.Revision)
    {source target : CostElaborationBase} (morphism : source ⟶ target)
    {request : PolicyRequest
      (CostElaborationFiber target.toCostOne.source.toCIGSLT)}
    (targetAdmission : PolicyKeyAdmission dependencies revision request
      (compactCarrierKey target.toCostOne.source.toCIGSLT))
    (policy : request.Policy)
    (fiber : CostElaborationFiber source.toCostOne.source.toCIGSLT) :
    ((pullbackCompactPolicyAdmission dependencies revision morphism
      targetAdmission).realize policy).run
        (compactCarrierKey source.toCostOne.source.toCIGSLT fiber) =
      request.observe policy
        (CostOneElaborationTotal.transportFiber morphism fiber) := by
  exact PolicyRealization.run_encode _ fiber

/-- Currentness transports without a second dependency test. -/
def pullbackCompactPolicyActive
    {dependencies : DependencySystem}
    {revision currentRevision : dependencies.Revision}
    {source target : CostElaborationBase} (morphism : source ⟶ target)
    {request : PolicyRequest
      (CostElaborationFiber target.toCostOne.source.toCIGSLT)}
    {targetAdmission : PolicyKeyAdmission dependencies revision request
      (compactCarrierKey target.toCostOne.source.toCIGSLT)}
    (active : targetAdmission.Active currentRevision) :
    (pullbackCompactPolicyAdmission dependencies revision morphism
      targetAdmission).Active currentRevision :=
  ⟨active.current⟩

/-- The current pulled-back hot runner is the already-admitted target runner
applied to the transported compact key. -/
@[simp] theorem pullbackCompactPolicyActive_runKey
    {dependencies : DependencySystem}
    {revision currentRevision : dependencies.Revision}
    {source target : CostElaborationBase} (morphism : source ⟶ target)
    {request : PolicyRequest
      (CostElaborationFiber target.toCostOne.source.toCIGSLT)}
    {targetAdmission : PolicyKeyAdmission dependencies revision request
      (compactCarrierKey target.toCostOne.source.toCIGSLT)}
    (active : targetAdmission.Active currentRevision)
    (policy : request.Policy)
    (fiber : CostElaborationFiber source.toCostOne.source.toCIGSLT) :
    (pullbackCompactPolicyActive morphism active).runKey policy
        (compactCarrierKey source.toCostOne.source.toCIGSLT fiber) =
      active.runKey policy
        (compactCarrierKey target.toCostOne.source.toCIGSLT
          (CostOneElaborationTotal.transportFiber morphism fiber)) := by
  change (targetAdmission.realize policy).run
      (transportCompactCarrier morphism
        (compactCarrierKey source.toCostOne.source.toCIGSLT fiber)) =
    (targetAdmission.realize policy).run
      (compactCarrierKey target.toCostOne.source.toCIGSLT
        (CostOneElaborationTotal.transportFiber morphism fiber))
  rw [compactCarrierKey_transportFiber]

/-- Pulling a dependent family back through two displayed transports retains
the target semantics for every policy. -/
@[simp] theorem pullbackCompactPolicyAdmission_comp_run
    (dependencies : DependencySystem) (revision : dependencies.Revision)
    {first second third : CostElaborationBase}
    (earlier : first ⟶ second) (later : second ⟶ third)
    {request : PolicyRequest
      (CostElaborationFiber third.toCostOne.source.toCIGSLT)}
    (targetAdmission : PolicyKeyAdmission dependencies revision request
      (compactCarrierKey third.toCostOne.source.toCIGSLT))
    (policy : request.Policy)
    (fiber : CostElaborationFiber first.toCostOne.source.toCIGSLT) :
    ((pullbackCompactPolicyAdmission dependencies revision earlier
      (pullbackCompactPolicyAdmission dependencies revision later
        targetAdmission)).realize policy).run
        (compactCarrierKey first.toCostOne.source.toCIGSLT fiber) =
      request.observe policy
        (CostOneElaborationTotal.transportFiber later
          (CostOneElaborationTotal.transportFiber earlier fiber)) := by
  exact PolicyRealization.run_encode _ fiber

/-! ## Axiom audit -/

#print axioms compactCarrierKey_mapCostElaborationFiber
#print axioms compactCarrierKey_transportFiber
#print axioms compactTransportKeyRefinement
#print axioms compactPolicy_transport_comp_agrees
#print axioms transportedCompactPolicyAdmission_run
#print axioms observationFamily_pullbackPolicyRequest_decide
#print axioms pullbackCompactPolicyAdmission_run
#print axioms pullbackCompactPolicyAdmissionViaGeneric_run
#print axioms pullbackCompactPolicyActive_runKey
#print axioms pullbackCompactPolicyAdmission_comp_run

end Mettapedia.Languages.MeTTa.Prime.CostTwoDisplayedKeyTransport
