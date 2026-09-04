import Mettapedia.GSLT.LanguageDef.AtomlessBooleanBootstrapGrounding
import Mettapedia.GSLT.LanguageDef.MaximalNativeCalculus

/-!
# Request-indexed selection for a direct semantic ground

A decidable semantic ground has two legitimate operational faces on one exact
claim fibre: direct decision and an explicit thin boundary obtained from the
same decision procedure.  Neither globally dominates the other.  A request
for certificate-free decision selects the direct face; a request for an
explicit boundary selects the boundary face.

Neither face provides informative trace identity.  The maximal-native request
interface therefore proves that no feasible request for this family can
require that capability.  A proof-trace shield must be supplied as a new
qualified realization, not inferred from `Unit` evidence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NIKSemanticGroundSelection

open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.MaximalNativeCalculus

universe uClaim

/-! ## One exact semantic-decision fibre -/

inductive Face where
  | direct
  | thinBoundary
  deriving DecidableEq, Repr

/-- The two faces retain different boundary observations, so no global order
is imposed between them. -/
instance : PartialOrder Face where
  le := Eq
  le_refl := fun _face => rfl
  le_trans := fun _first _middle _last earlier later => earlier.trans later
  le_antisymm := fun _first _second forward _reverse => forward

inductive Capability where
  | exactDecision
  | certificateFree
  | explicitBoundary
  | informativeTrace
  deriving DecidableEq, Repr

def supports : Face -> Capability -> Prop
  | _, .exactDecision => True
  | .direct, .certificateFree => True
  | .thinBoundary, .explicitBoundary => True
  | _, _ => False

structure Query (Claim : Type uClaim) where
  claim : Claim

structure Result (Claim : Type uClaim) where
  face : Face
  claim : Claim
  accepted : Bool

def source (Claim : Type uClaim) : AdmissionObject.{uClaim} where
  Carrier := Query Claim
  Meaning := fun _query => True

def target {Claim : Type uClaim} (Meaning : Claim -> Prop) :
    AdmissionObject.{uClaim} where
  Carrier := Result Claim
  Meaning := fun result =>
    result.accepted = true <-> Meaning result.claim

def directOperation
    {Claim : Type uClaim} {Meaning : Claim -> Prop}
    (kernel : Checker.DecisionKernel Claim Meaning) :
    source Claim ⟶ target Meaning where
  run := fun query =>
    { face := .direct
      claim := query.claim
      accepted := kernel.decide query.claim }
  preserves := fun query _meaningful => kernel.correct query.claim

def boundaryOperation
    {Claim : Type uClaim} {Meaning : Claim -> Prop}
    (kernel : Checker.DecisionKernel Claim Meaning) :
    source Claim ⟶ target Meaning where
  run := fun query =>
    { face := .thinBoundary
      claim := query.claim
      accepted := kernel.toChecker.check query.claim () }
  preserves := fun query _meaningful => kernel.correct query.claim

/-- The Boolean answers agree, but retained boundary provenance does not. -/
theorem operation_receipts_distinct
    {Claim : Type uClaim} {Meaning : Claim -> Prop}
    (kernel : Checker.DecisionKernel Claim Meaning)
    (query : (source Claim).Carrier) :
    (directOperation kernel).run query ≠
      (boundaryOperation kernel).run query := by
  intro equal
  have facesEqual := congrArg
    (fun result : (target Meaning).Carrier => result.face) equal
  cases facesEqual

def family
    {Claim : Type uClaim} {Meaning : Claim -> Prop}
    (kernel : Checker.DecisionKernel Claim Meaning) :
    RecognizedFamily Face (source Claim) (target Meaning) where
  package
    | .direct => directOperation kernel
    | .thinBoundary => boundaryOperation kernel
  Capability := Capability
  supports := supports
  supports_mono := by
    intro weaker stronger related capability supported
    change weaker = stronger at related
    subst stronger
    exact supported
  strict_support_gain := by
    intro weaker stronger strict
    exact False.elim (strict.2 strict.1.symm)
  recognized := {.direct, .thinBoundary}
  licensed := {.direct, .thinBoundary}
  licensed_subset_recognized := Finset.Subset.rfl
  licensed_nonempty := ⟨.direct, by simp⟩

/-- The discrete face order is exactly inclusion of supported capabilities. -/
theorem order_iff_capability_inclusion
    {Claim : Type uClaim} {Meaning : Claim -> Prop}
    (kernel : Checker.DecisionKernel Claim Meaning) (first second : Face) :
    first ≤ second <->
      ∀ capability,
        (family kernel).supports first capability ->
          (family kernel).supports second capability := by
  constructor
  · intro related
    change first = second at related
    subst second
    exact fun _capability supported => supported
  · intro included
    cases first <;> cases second
    · rfl
    · have impossible := included .certificateFree
      simp [family, supports] at impossible
    · have impossible := included .explicitBoundary
      simp [family, supports] at impossible
    · rfl

/-! ## Exact capability requests -/

def directRequest
    {Claim : Type uClaim} {Meaning : Claim -> Prop}
    (kernel : Checker.DecisionKernel Claim Meaning) :
    (family kernel).CapabilityRequest where
  required := {.exactDecision, .certificateFree}
  candidates := {.direct}
  candidates_exact := by
    intro candidate
    cases candidate with
    | direct =>
        constructor
        · intro _member
          refine ⟨by simp [family], ?_⟩
          intro capability required
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at required
          rcases required with rfl | rfl <;> trivial
        · intro _qualified
          simp
    | thinBoundary =>
        constructor
        · intro impossible
          simp at impossible
        · rintro ⟨_licensed, supportsRequired⟩
          have impossible := supportsRequired .certificateFree (by simp)
          simp [family, supports] at impossible
  candidates_nonempty := by simp

def boundaryRequest
    {Claim : Type uClaim} {Meaning : Claim -> Prop}
    (kernel : Checker.DecisionKernel Claim Meaning) :
    (family kernel).CapabilityRequest where
  required := {.exactDecision, .explicitBoundary}
  candidates := {.thinBoundary}
  candidates_exact := by
    intro candidate
    cases candidate with
    | direct =>
        constructor
        · intro impossible
          simp at impossible
        · rintro ⟨_licensed, supportsRequired⟩
          have impossible := supportsRequired .explicitBoundary (by simp)
          simp [family, supports] at impossible
    | thinBoundary =>
        constructor
        · intro _member
          refine ⟨by simp [family], ?_⟩
          intro capability required
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at required
          rcases required with rfl | rfl <;> trivial
        · intro _qualified
          simp
  candidates_nonempty := by simp

def directSelection
    {Claim : Type uClaim} {Meaning : Claim -> Prop}
    (kernel : Checker.DecisionKernel Claim Meaning) :
    (directRequest kernel).StrongestNativeCalculusPrinciple where
  val := .direct
  property := by
    constructor
    · simp [RecognizedFamily.CapabilityRequest.restrictedFamily,
        directRequest]
    · intro candidate candidateMember
      have candidateEqual : candidate = .direct := by
        simpa [RecognizedFamily.CapabilityRequest.restrictedFamily,
          directRequest] using candidateMember
      subst candidate
      exact le_rfl

def boundarySelection
    {Claim : Type uClaim} {Meaning : Claim -> Prop}
    (kernel : Checker.DecisionKernel Claim Meaning) :
    (boundaryRequest kernel).StrongestNativeCalculusPrinciple where
  val := .thinBoundary
  property := by
    constructor
    · simp [RecognizedFamily.CapabilityRequest.restrictedFamily,
        boundaryRequest]
    · intro candidate candidateMember
      have candidateEqual : candidate = .thinBoundary := by
        simpa [RecognizedFamily.CapabilityRequest.restrictedFamily,
          boundaryRequest] using candidateMember
      subst candidate
      exact le_rfl

theorem directRequest_uniqueStrongest
    {Claim : Type uClaim} {Meaning : Claim -> Prop}
    (kernel : Checker.DecisionKernel Claim Meaning) :
    ∃! chosen,
      (directRequest kernel).restrictedFamily.IsGreatestLicensed chosen := by
  refine ⟨.direct, (directSelection kernel).2, ?_⟩
  intro candidate candidateGreatest
  exact RecognizedFamily.greatestLicensed_unique
    (directRequest kernel).restrictedFamily
    candidateGreatest (directSelection kernel).2

theorem boundaryRequest_uniqueStrongest
    {Claim : Type uClaim} {Meaning : Claim -> Prop}
    (kernel : Checker.DecisionKernel Claim Meaning) :
    ∃! chosen,
      (boundaryRequest kernel).restrictedFamily.IsGreatestLicensed chosen := by
  refine ⟨.thinBoundary, (boundarySelection kernel).2, ?_⟩
  intro candidate candidateGreatest
  exact RecognizedFamily.greatestLicensed_unique
    (boundaryRequest kernel).restrictedFamily
    candidateGreatest (boundarySelection kernel).2

@[simp] theorem directStrongestOperation_run
    {Claim : Type uClaim} {Meaning : Claim -> Prop}
    (kernel : Checker.DecisionKernel Claim Meaning)
    (query : (source Claim).Carrier) :
    ((directRequest kernel).strongestOperation
      (directSelection kernel)).run query =
        (directOperation kernel).run query :=
  rfl

@[simp] theorem boundaryStrongestOperation_run
    {Claim : Type uClaim} {Meaning : Claim -> Prop}
    (kernel : Checker.DecisionKernel Claim Meaning)
    (query : (source Claim).Carrier) :
    ((boundaryRequest kernel).strongestOperation
      (boundarySelection kernel)).run query =
        (boundaryOperation kernel).run query :=
  rfl

/-- No exact nonempty request over this family can demand informative trace
identity, because neither qualified realization provides it. -/
theorem informativeTrace_request_impossible
    {Claim : Type uClaim} {Meaning : Claim -> Prop}
    (kernel : Checker.DecisionKernel Claim Meaning) :
    ¬ (∃ request : (family kernel).CapabilityRequest,
      Capability.informativeTrace ∈ request.required) := by
  rintro ⟨request, traceRequired⟩
  obtain ⟨candidate, candidateMember⟩ := request.candidates_nonempty
  have candidateData :=
    (request.candidates_exact candidate).mp candidateMember
  have supportsTrace :=
    candidateData.2 Capability.informativeTrace traceRequired
  cases candidate <;> simp [family, supports] at supportsTrace

/-! ## The atomless model-soundness instance -/

namespace AtomlessCanary

open Mettapedia.GSLT.LanguageDef.AtomlessBooleanBootstrapGrounding
open Mettapedia.GSLT.LanguageDef.AtomlessBooleanMSOSemanticBridge

def kernel := grounding.lowerDecision

def gunkQuery : (source (LowerContract Statement 1)).Carrier where
  claim := lowerClaim .modelSound gunkSentence

theorem direct_gunk_accepted :
    ((directOperation kernel).run gunkQuery).accepted = true := by
  change layer.checker.check (lowerClaim .modelSound gunkSentence) () = true
  exact gunk_modelSound_accepted

theorem boundary_gunk_accepted :
    ((boundaryOperation kernel).run gunkQuery).accepted = true := by
  change layer.checker.check (lowerClaim .modelSound gunkSentence) () = true
  exact gunk_modelSound_accepted

theorem gunk_receipts_remain_distinct :
    (directOperation kernel).run gunkQuery ≠
      (boundaryOperation kernel).run gunkQuery :=
  operation_receipts_distinct kernel gunkQuery

theorem informative_trace_requires_another_realization :
    ¬ (∃ request : (family kernel).CapabilityRequest,
      Capability.informativeTrace ∈ request.required) :=
  informativeTrace_request_impossible kernel

end AtomlessCanary

#print axioms operation_receipts_distinct
#print axioms order_iff_capability_inclusion
#print axioms directRequest_uniqueStrongest
#print axioms boundaryRequest_uniqueStrongest
#print axioms directStrongestOperation_run
#print axioms boundaryStrongestOperation_run
#print axioms informativeTrace_request_impossible
#print axioms AtomlessCanary.direct_gunk_accepted
#print axioms AtomlessCanary.boundary_gunk_accepted
#print axioms AtomlessCanary.gunk_receipts_remain_distinct
#print axioms AtomlessCanary.informative_trace_requires_another_realization

end Mettapedia.GSLT.LanguageDef.NIKSemanticGroundSelection
