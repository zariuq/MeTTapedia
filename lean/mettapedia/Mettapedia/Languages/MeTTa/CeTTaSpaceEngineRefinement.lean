import Mettapedia.Languages.MeTTa.AbstractMachineBoundary
import Mettapedia.Languages.MeTTa.HE.SpaceQuerySupport
import Mettapedia.Languages.ProcessCalculi.MORK.ExecutionBoundary

/-!
# CeTTa Space-Engine Refinement

Packages the honest CeTTa / HE / PathMap / MORK seam at the right abstraction
layer:

- shared support-level query semantics are expressed through `FaithfulBackend`
- native, PathMap, and MORK all host the shared query lane
- exec authority is still a separate claim and remains MORK-only
- swapping backends preserves query answers only when both backends refine the
  same HE space

Positive example:
- a faithful PathMap-like backend preserves HE query/type support.

Negative example:
- a faithful query backend does not by itself grant runtime-rule execution.
-/

namespace Mettapedia.Languages.MeTTa.CeTTaSpaceEngineRefinement

open Mettapedia.Languages.MeTTa.AbstractMachineBoundary
open Mettapedia.Languages.MeTTa.SpaceEngineBoundary
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.ElaboratedCore

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)

private abbrev HESpace := Mettapedia.Languages.MeTTa.HE.Space

/-- The honest query-side refinement seam for a CeTTa backend.

This is intentionally weaker than an execution theorem: it packages only
support-level agreement with an HE space, plus evidence that the chosen engine
actually hosts the shared runtime-query lane. -/
structure SharedQueryRefinement (S : Type*) [SpaceQuerySupport S]
    (engine : SpaceEngine) (heSpace : HESpace) where
  faithful : FaithfulBackend S heSpace
  queryLaneSupported :
    AbstractMachineLane.supportedByEngine
      AbstractMachineLane.runtimeQueryLane engine = true

/-- The backend carrier on the query seam. -/
abbrev SharedQueryRefinement.backend
    {S : Type*} [SpaceQuerySupport S]
    {engine : SpaceEngine} {heSpace : HESpace}
    (ref : SharedQueryRefinement S engine heSpace) : S :=
  ref.faithful.backend

/-- Re-export the already-proved MORK rule-firing boundary as the execution-side
counterpart to the present query-side refinement seam. -/
abbrev morkExecBridge := @Mettapedia.Languages.ProcessCalculi.MORK.ExecutionBoundary.fireCorrespondence

theorem backend_query_support_eq
    {S : Type*} [SpaceQuerySupport S]
    {engine : SpaceEngine} {heSpace : HESpace}
    (ref : SharedQueryRefinement S engine heSpace) (q : Atom) :
    SpaceQuerySupport.queryResultSupport ref.backend q =
      SpaceQuerySupport.queryResultSupport heSpace q :=
  ref.faithful.query_agree q

theorem backend_type_support_eq
    {S : Type*} [SpaceQuerySupport S]
    {engine : SpaceEngine} {heSpace : HESpace}
    (ref : SharedQueryRefinement S engine heSpace) (a : Atom) :
    SpaceQuerySupport.typeSupport ref.backend a =
      SpaceQuerySupport.typeSupport heSpace a :=
  ref.faithful.type_agree a

/-- Backend swaps preserve the shared query lane when both backends are faithful
to the same HE space. -/
theorem backend_swap_preserves_query_support
    {S T : Type*} [SpaceQuerySupport S] [SpaceQuerySupport T]
    {engineS engineT : SpaceEngine} {heSpace : HESpace}
    (refS : SharedQueryRefinement S engineS heSpace)
    (refT : SharedQueryRefinement T engineT heSpace)
    (q : Atom) :
    SpaceQuerySupport.queryResultSupport refS.backend q =
      SpaceQuerySupport.queryResultSupport refT.backend q := by
  rw [backend_query_support_eq refS q, backend_query_support_eq refT q]

theorem backend_swap_preserves_type_support
    {S T : Type*} [SpaceQuerySupport S] [SpaceQuerySupport T]
    {engineS engineT : SpaceEngine} {heSpace : HESpace}
    (refS : SharedQueryRefinement S engineS heSpace)
    (refT : SharedQueryRefinement T engineT heSpace)
    (a : Atom) :
    SpaceQuerySupport.typeSupport refS.backend a =
      SpaceQuerySupport.typeSupport refT.backend a := by
  rw [backend_type_support_eq refS a, backend_type_support_eq refT a]

/-- Native HE space is the self-refining baseline query backend. -/
def nativeSelfRefinement (heSpace : HESpace) :
    SharedQueryRefinement HESpace SpaceEngine.native heSpace where
  faithful := Space.selfBackend heSpace
  queryLaneSupported := runtimeQuery_supported_by_native

theorem nativeSelfRefinement_query_support
    (heSpace : HESpace) (q : Atom) :
    SpaceQuerySupport.queryResultSupport
        (nativeSelfRefinement heSpace).backend q =
      SpaceQuerySupport.queryResultSupport heSpace q := by
  exact backend_query_support_eq (nativeSelfRefinement heSpace) q

theorem native_query_refinement_not_exec_authority
    {S : Type*} [SpaceQuerySupport S] {heSpace : HESpace}
    (_ref : SharedQueryRefinement S SpaceEngine.native heSpace) :
    EngineCapability.execStep ∉ SpaceEngine.native.capabilities := by
  decide

theorem pathmap_query_refinement_not_exec_authority
    {S : Type*} [SpaceQuerySupport S] {heSpace : HESpace}
    (_ref : SharedQueryRefinement S SpaceEngine.pathmap heSpace) :
    EngineCapability.execStep ∉ SpaceEngine.pathmap.capabilities := by
  exact pathmap_query_surface_only

theorem pathmap_query_refinement_not_runtime_rule_lane
    {S : Type*} [SpaceQuerySupport S] {heSpace : HESpace}
    (_ref : SharedQueryRefinement S SpaceEngine.pathmap heSpace) :
    AbstractMachineLane.supportedByEngine
      AbstractMachineLane.runtimeRuleLane SpaceEngine.pathmap = false := by
  decide

theorem mork_query_refinement_carries_exec_authority
    {S : Type*} [SpaceQuerySupport S] {heSpace : HESpace}
    (_ref : SharedQueryRefinement S SpaceEngine.mork heSpace) :
    EngineCapability.equationQuery ∈ SpaceEngine.mork.capabilities ∧
    EngineCapability.execStep ∈ SpaceEngine.mork.capabilities := by
  decide

theorem act_attachment_stays_query_only :
    EngineCapability.equationQuery ∈ SpaceEngine.pathmap.capabilities ∧
    EngineCapability.execStep ∉ SpaceEngine.pathmap.capabilities ∧
    ArtifactSurface.act.grantsExec = false := by
  exact ⟨by decide, pathmap_query_surface_only, act_artifact_not_exec_authority⟩

/-- HE runtime queries live on the shared query seam and therefore may be
served by native, PathMap, or MORK backends. -/
theorem heRuntimeQuery_uses_shared_query_seam (pattern : Pattern) :
    SurfaceNode.abstractMachineLane (SurfaceNode.heRuntimeQuery pattern) =
      AbstractMachineLane.runtimeQueryLane ∧
    AbstractMachineLane.supportedByEngine
      AbstractMachineLane.runtimeQueryLane SpaceEngine.native = true ∧
    AbstractMachineLane.supportedByEngine
      AbstractMachineLane.runtimeQueryLane SpaceEngine.pathmap = true ∧
    AbstractMachineLane.supportedByEngine
      AbstractMachineLane.runtimeQueryLane SpaceEngine.mork = true := by
  exact ⟨(heRuntimeQuery_routes_to_query_backend pattern).1,
    runtimeQuery_supported_by_native,
    runtimeQuery_supported_by_pathmap,
    runtimeQuery_supported_by_mork⟩

/-- PeTTa runtime queries share the same query seam as HE runtime queries. -/
theorem pettaRuntimeQuery_uses_shared_query_seam (pattern : Pattern) :
    SurfaceNode.abstractMachineLane (SurfaceNode.pettaRuntimeQuery pattern) =
      AbstractMachineLane.runtimeQueryLane ∧
    AbstractMachineLane.supportedByEngine
      AbstractMachineLane.runtimeQueryLane SpaceEngine.native = true ∧
    AbstractMachineLane.supportedByEngine
      AbstractMachineLane.runtimeQueryLane SpaceEngine.pathmap = true ∧
    AbstractMachineLane.supportedByEngine
      AbstractMachineLane.runtimeQueryLane SpaceEngine.mork = true := by
  exact ⟨(pettaRuntimeQuery_routes_to_query_backend pattern).1,
    runtimeQuery_supported_by_native,
    runtimeQuery_supported_by_pathmap,
    runtimeQuery_supported_by_mork⟩

/-- HE runtime rules are not merely shared-query operations: they require the
MORK execution lane. -/
theorem heRuntimeRule_requires_mork_exec (pattern : Pattern) :
    SurfaceNode.abstractMachineLane (SurfaceNode.heRuntimeRule pattern) =
      AbstractMachineLane.runtimeRuleLane ∧
    AbstractMachineLane.supportedByEngine
      AbstractMachineLane.runtimeRuleLane SpaceEngine.pathmap = false ∧
    AbstractMachineLane.supportedByEngine
      AbstractMachineLane.runtimeRuleLane SpaceEngine.mork = true := by
  refine ⟨(heRuntimeRule_routes_to_exec_backend pattern).1, ?_, ?_⟩
  · decide
  · decide

/-- PeTTa runtime rules share the same execution requirement. -/
theorem pettaRuntimeRule_requires_mork_exec (pattern : Pattern) :
    SurfaceNode.abstractMachineLane (SurfaceNode.pettaRuntimeRule pattern) =
      AbstractMachineLane.runtimeRuleLane ∧
    AbstractMachineLane.supportedByEngine
      AbstractMachineLane.runtimeRuleLane SpaceEngine.pathmap = false ∧
    AbstractMachineLane.supportedByEngine
      AbstractMachineLane.runtimeRuleLane SpaceEngine.mork = true := by
  refine ⟨(pettaRuntimeRule_shares_exec_backend pattern).1, ?_, ?_⟩
  · decide
  · decide

/-! ## Examples -/

/-- Positive example: the native HE space refines its own shared query lane. -/
example (heSpace : HESpace) (q : Atom) :
    SpaceQuerySupport.queryResultSupport
        (nativeSelfRefinement heSpace).backend q =
      SpaceQuerySupport.queryResultSupport heSpace q := by
  exact nativeSelfRefinement_query_support heSpace q

/-- Negative example: a PathMap-side faithful query backend still does not get
runtime-rule authority for free. -/
example {S : Type*} [SpaceQuerySupport S] {heSpace : HESpace}
    (ref : SharedQueryRefinement S SpaceEngine.pathmap heSpace) :
    AbstractMachineLane.supportedByEngine
      AbstractMachineLane.runtimeRuleLane SpaceEngine.pathmap = false := by
  exact pathmap_query_refinement_not_runtime_rule_lane ref

end Mettapedia.Languages.MeTTa.CeTTaSpaceEngineRefinement
