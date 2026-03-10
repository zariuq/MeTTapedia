import Mettapedia.Languages.MeTTa.RuntimeKernel

/-!
# Runtime-Resource Layer

Adds the first explicit resource layer below exec/query/spaceEffect, describing
which resources the current MORK/MM2 backend supports and which remain
descriptor-only placeholders.

Aligned with MORK Rust reality:
- MORK is single-space-per-instance (`Space` struct with one `PathMap`)
- All formalized operations hardcode `&self` — no `new-space`, no `bind!`
- Only `defaultAtomSpace` has a proved direct-exec seam
- Solver resource (Z3) has a proved oracle contract seam (`Z3Oracle.lean`)
  but not a proved end-to-end exec seam
- Named spaces and external resources are descriptor-only

Positive example:
- Honestly distinguishes `hasProvedExecSeam` (direct-exec, only `defaultAtomSpace`)
  from `hasProvedOracleSeam` (oracle contract, Z3 via `Z3Oracle.lean`).

Negative example:
- Does not claim Z3 has a proved exec seam (it has an oracle seam).
- Does not claim ACT has any proved seam (not yet formalized).
-/

namespace Mettapedia.Languages.MeTTa.RuntimeResource

open Mettapedia.Languages.MeTTa.ElaboratedCore
open Mettapedia.Languages.MeTTa.RuntimeExec
open Mettapedia.Languages.MeTTa.RuntimeKernel
open MeTTailCore.MeTTaIL.EffectSafety

/-! ## 1. Resource descriptor -/

/-- Describes a resource kind: what kernel classes it supports, its effect
envelope, which proof seams exist, and which backend (if any) provides it.

Two independent seam status fields:
- `hasProvedExecSeam`: a proved direct-execution seam exists (matchPattern → fireRule
  → applySinks). Currently only `defaultAtomSpace`.
- `hasProvedOracleSeam`: a proved oracle contract seam exists (OracleQuery →
  OracleResponse → payload space → pattern matching). Currently only `solverResource`
  (Z3, via `Z3Oracle.lean`).

This is a *descriptor* (metadata), not a handle or allocation primitive. -/
structure ResourceDescriptor where
  resourceClass : RuntimeResourceClass
  supportedKernelClasses : List RuntimeKernelClass
  effectEnvelope : EffectClass
  backendName : String
  hasProvedExecSeam : Bool
  hasProvedOracleSeam : Bool
deriving Repr, DecidableEq

/-! ## 2. Current resource descriptors

Aligned with the MORK Rust implementation:
- `defaultAtomSpace`: single `Space` instance with `PathMap<()>`, fully backed
  (proved exec seam)
- `namedAtomSpace`: MORK has no multi-space support; descriptor-only
- `solverResource`: MORK spawns Z3 subprocesses; proved oracle contract seam
  via `Z3Oracle.lean`, no proved exec seam
- `externalResource`: MORK ACT files are read-only external data; no proved seam
-/

/-- The default `&self` atomspace: the only resource with full proved support.

MORK backing: `Space::new()` creates one workspace; all `add-atom`, `remove-atom`,
`match &self`, `get-atoms &self`, and eval/evalc steps operate on this single space. -/
def defaultAtomSpaceDescriptor : ResourceDescriptor where
  resourceClass := .defaultAtomSpace
  supportedKernelClasses := [.ruleExec, .query, .spaceEffect]
  effectEnvelope := .writesState
  backendName := "MORK/MM2"
  hasProvedExecSeam := true
  hasProvedOracleSeam := false

/-- Named atomspace descriptor. MORK is single-space-per-instance; `new-space`
and `in-space` are not formalized in the current PeTTa/MM2 stack.

`SpaceCoreFragment.lean` explicitly excludes `new-space` from scope. -/
def namedAtomSpaceDescriptor : ResourceDescriptor where
  resourceClass := .namedAtomSpace
  supportedKernelClasses := []
  effectEnvelope := .writesState
  backendName := "none"
  hasProvedExecSeam := false
  hasProvedOracleSeam := false

/-- Solver resource descriptor. MORK actively uses Z3 via `ResourceRequest::Z3`
in `space.rs`: it spawns Z3 subprocesses, sends `(check-sat)` / `(get-model)`,
and parses results back into `PathMap` zippers. This is a real execution path
in the Rust runtime.

Oracle contract seam proved via `Z3Oracle.lean`: `OracleEnv`, `oraclePayloadSpace`,
`oracleMatchPattern`, mock Z3 conformance. No proved end-to-end exec seam. -/
def solverResourceDescriptor : ResourceDescriptor where
  resourceClass := .solverResource
  supportedKernelClasses := [.oracle]
  effectEnvelope := .oracleIO
  backendName := "MORK/MM2"
  hasProvedExecSeam := false
  hasProvedOracleSeam := true

/-- External resource descriptor. MORK ACT files (`(I (BTM ...) (ACT name ...))`)
provide read-only external file-backed datasets joined with workspace facts.
This is a real execution path in MORK's Rust runtime, but not yet formalized
in Lean (`Syntax.lean:138`: "NOT yet formalized: `ACT`"). No proved seam. -/
def externalResourceDescriptor : ResourceDescriptor where
  resourceClass := .externalResource
  supportedKernelClasses := [.oracle]
  effectEnvelope := .oracleIO
  backendName := "MORK/MM2"
  hasProvedExecSeam := false
  hasProvedOracleSeam := false

/-! ## 3. Resource registry -/

/-- All currently known resource descriptors. `mapResource` and `queueResource`
from `RuntimeResourceClass` are omitted: no proved fragment, no MORK backing. -/
def resourceRegistry : List ResourceDescriptor :=
  [defaultAtomSpaceDescriptor,
   namedAtomSpaceDescriptor,
   solverResourceDescriptor,
   externalResourceDescriptor]

/-! ## 4. Resource profile -/

/-- Pairs a runtime kernel package with its resource descriptors and identifies
the primary resource backing the current triad. -/
structure ResourceProfile where
  kernelPackage : RuntimeKernelPackage
  resources : List ResourceDescriptor
  primaryResource : ResourceDescriptor

/-- Canonical MORK/MM2 resource profile. The primary resource is `defaultAtomSpace`,
which is the only resource with a proved direct-exec seam. -/
noncomputable def morkResourceProfile : ResourceProfile where
  kernelPackage := morkRuntimeKernelPackage
  resources := resourceRegistry
  primaryResource := defaultAtomSpaceDescriptor

/-! ## 5. Coverage theorems -/

section ProvedCoverage

theorem only_defaultAtomSpace_proved :
    defaultAtomSpaceDescriptor.hasProvedExecSeam = true := rfl
theorem namedAtomSpace_not_proved :
    namedAtomSpaceDescriptor.hasProvedExecSeam = false := rfl
theorem solver_not_proved :
    solverResourceDescriptor.hasProvedExecSeam = false := rfl
theorem external_not_proved :
    externalResourceDescriptor.hasProvedExecSeam = false := rfl

end ProvedCoverage

section EffectEnvelope

theorem defaultAtomSpace_envelope :
    defaultAtomSpaceDescriptor.effectEnvelope = .writesState := rfl
theorem namedAtomSpace_envelope :
    namedAtomSpaceDescriptor.effectEnvelope = .writesState := rfl
theorem solver_envelope :
    solverResourceDescriptor.effectEnvelope = .oracleIO := rfl
theorem external_envelope :
    externalResourceDescriptor.effectEnvelope = .oracleIO := rfl

end EffectEnvelope

section FragmentResourceAlignment

theorem exec_on_defaultAtomSpace :
    execFragment.resourceClass = defaultAtomSpaceDescriptor.resourceClass := rfl
theorem query_on_defaultAtomSpace :
    queryFragment.resourceClass = defaultAtomSpaceDescriptor.resourceClass := rfl
theorem spaceEffect_on_defaultAtomSpace :
    spaceEffectFragment.resourceClass = defaultAtomSpaceDescriptor.resourceClass := rfl

end FragmentResourceAlignment

section KernelClassMembership

theorem ruleExec_in_defaultAtomSpace :
    RuntimeKernelClass.ruleExec ∈
      defaultAtomSpaceDescriptor.supportedKernelClasses := by decide
theorem query_in_defaultAtomSpace :
    RuntimeKernelClass.query ∈
      defaultAtomSpaceDescriptor.supportedKernelClasses := by decide
theorem spaceEffect_in_defaultAtomSpace :
    RuntimeKernelClass.spaceEffect ∈
      defaultAtomSpaceDescriptor.supportedKernelClasses := by decide

theorem namedAtomSpace_no_kernel_classes :
    namedAtomSpaceDescriptor.supportedKernelClasses = [] := rfl

theorem oracle_in_solver :
    RuntimeKernelClass.oracle ∈
      solverResourceDescriptor.supportedKernelClasses := by decide
theorem oracle_in_external :
    RuntimeKernelClass.oracle ∈
      externalResourceDescriptor.supportedKernelClasses := by decide

end KernelClassMembership

section OracleSeamCoverage

/-- Only the solver resource has a proved oracle seam (Z3, via Z3Oracle.lean). -/
theorem solver_has_oracle_seam :
    solverResourceDescriptor.hasProvedOracleSeam = true := rfl

/-- The default atomspace has no oracle seam (it's exec/query/spaceEffect). -/
theorem defaultAtomSpace_no_oracle_seam :
    defaultAtomSpaceDescriptor.hasProvedOracleSeam = false := rfl

/-- Named atomspace has no oracle seam. -/
theorem namedAtomSpace_no_oracle_seam :
    namedAtomSpaceDescriptor.hasProvedOracleSeam = false := rfl

/-- External resource has no proved oracle seam yet (ACT not formalized). -/
theorem external_no_oracle_seam :
    externalResourceDescriptor.hasProvedOracleSeam = false := rfl

/-- The solver resource has an oracle seam but NOT an exec seam.
    This is the key status distinction: Z3Oracle.lean proves the oracle
    contract (query → response → payload → matching), but does NOT prove
    end-to-end subprocess execution correctness. -/
theorem solver_oracle_but_no_exec :
    solverResourceDescriptor.hasProvedOracleSeam = true ∧
    solverResourceDescriptor.hasProvedExecSeam = false :=
  ⟨rfl, rfl⟩

end OracleSeamCoverage

section OracleResourceRouting

open Mettapedia.Languages.MeTTa.Core (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (OracleQuery OracleResponse ResourceRequest)

/-- Z3 check-sat queries route to the `.z3` resource request. -/
theorem z3CheckSat_routes_to_z3 (name : String) (assertions : List Atom) :
    (OracleQuery.z3CheckSat name assertions).resourceRequest = .z3 name := rfl

/-- Z3 get-model queries route to the `.z3` resource request. -/
theorem z3GetModel_routes_to_z3 (name : String) (assertions : List Atom) :
    (OracleQuery.z3GetModel name assertions).resourceRequest = .z3 name := rfl

/-- ACT match queries route to the `.act` resource request. -/
theorem actMatch_routes_to_act (name : String) (pat : Atom) :
    (OracleQuery.actMatch name pat).resourceRequest = .act name := rfl

/-- The solver resource descriptor's class is `.solverResource`. -/
theorem solver_resourceClass :
    solverResourceDescriptor.resourceClass = .solverResource := rfl

/-- The external resource descriptor's class is `.externalResource`. -/
theorem external_resourceClass :
    externalResourceDescriptor.resourceClass = .externalResource := rfl

/-- Solver resource supports the oracle kernel class. -/
theorem solver_supports_oracle :
    RuntimeKernelClass.oracle ∈
      solverResourceDescriptor.supportedKernelClasses := by decide

/-- External resource supports the oracle kernel class. -/
theorem external_supports_oracle :
    RuntimeKernelClass.oracle ∈
      externalResourceDescriptor.supportedKernelClasses := by decide

/-- Sat response has no payload atoms. -/
theorem sat_has_no_payload : OracleResponse.sat.hasPayload = false := rfl

/-- Unsat response has no payload atoms. -/
theorem unsat_has_no_payload : OracleResponse.unsat.hasPayload = false := rfl

/-- Model response always has payload. -/
theorem model_has_payload (atoms : List Atom) :
    (OracleResponse.model atoms).hasPayload = true := rfl

/-- FactSet response always has payload. -/
theorem factSet_has_payload (atoms : List Atom) :
    (OracleResponse.factSet atoms).hasPayload = true := rfl

end OracleResourceRouting

section ProfileFacts

theorem morkProfile_primary_is_default :
    morkResourceProfile.primaryResource = defaultAtomSpaceDescriptor := rfl

theorem morkProfile_primary_proved :
    morkResourceProfile.primaryResource.hasProvedExecSeam = true := rfl

theorem morkProfile_backend :
    morkResourceProfile.primaryResource.backendName = "MORK/MM2" := rfl

end ProfileFacts

/-! ## Canaries -/

section Canaries
#check @ResourceDescriptor
#check @defaultAtomSpaceDescriptor
#check @namedAtomSpaceDescriptor
#check @solverResourceDescriptor
#check @externalResourceDescriptor
#check @resourceRegistry
#check @ResourceProfile
#check @morkResourceProfile
#check @only_defaultAtomSpace_proved
#check @namedAtomSpace_not_proved
#check @ruleExec_in_defaultAtomSpace
#check @namedAtomSpace_no_kernel_classes
#check @morkProfile_primary_is_default
#check @solver_has_oracle_seam
#check @solver_oracle_but_no_exec
#check @z3CheckSat_routes_to_z3
#check @z3GetModel_routes_to_z3
#check @actMatch_routes_to_act
#check @solver_supports_oracle
#check @external_supports_oracle
end Canaries

/-! ## Axiom audit -/

section AxiomAudit
#print axioms only_defaultAtomSpace_proved
#print axioms namedAtomSpace_not_proved
#print axioms ruleExec_in_defaultAtomSpace
#print axioms namedAtomSpace_no_kernel_classes
#print axioms morkProfile_primary_is_default
#print axioms morkProfile_primary_proved
#print axioms solver_has_oracle_seam
#print axioms solver_oracle_but_no_exec
#print axioms z3CheckSat_routes_to_z3
#print axioms z3GetModel_routes_to_z3
#print axioms solver_supports_oracle
#print axioms external_supports_oracle
end AxiomAudit

end Mettapedia.Languages.MeTTa.RuntimeResource
