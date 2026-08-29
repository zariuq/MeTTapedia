import Mettapedia.GSLT.Dynamics.ParallelExecutionAuthority

/-!
# Proof-relevant semantic routes bound to physical operator articles

A structurally coherent operator receipt does not by itself prove that its
physical inputs encode the claimed semantic events or that its output encodes
an observation reached by semantic execution.  This module states the generic
additional authority without choosing a certificate or wire format.

One bound article retains a chronological semantic route and independently
decodable physical evidence for:

* the route identity;
* the ordered semantic event pair;
* the terminal semantic observation.

An exact `BindingAuthority` may be realized by deterministic recomputation,
proof-relevant replay, a generated checker, or another independently adequate
method.  It composes conjunctively with the existing structural parallel
article authority and enters the same open NIK family.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.SemanticPhysicalRouteBinding

open Mettapedia.GSLT.Dynamics.OperatorRealization
open Mettapedia.GSLT.Dynamics.ParallelExecutionAuthority
open Mettapedia.GSLT.Dynamics.QueryRevision
open Mettapedia.GSLT.Dynamics.EventValuation
open Mettapedia.GSLT.LanguageDef.CheckerAuthorityFamily
open Mettapedia.GSLT.LanguageDef.KernelAuthority

universe uWorld uRevision uQuery uObservation uRoute uOccurrence uClaim
universe uCertificate uAdmissionCertificate

/-! ## Semantic route and physical decoding contract -/

/-- One chronological execution of the article's named events.  `routeId` is
operational identity data; the two relation witnesses are semantic evidence. -/
structure SequentialRoute
    (theory : Theory)
    (claim : EventClaim theory)
    (RouteId : Type uRoute) where
  routeId : RouteId
  afterFirst : theory.World
  target : theory.World
  firstStep : theory.Step claim.first claim.source afterFirst
  secondStep : theory.Step claim.second afterFirst target

/-- Physical decoders used by a particular representation.  They inspect only
the physical snapshot, plan, and delta; none receives the semantic event claim
as an argument. -/
structure PhysicalBindingCodec
    (theory : Theory)
    (Backend StoreRevision Payload PlanId DeltaId : Type)
    (RouteId : Type uRoute) where
  route? : Snapshot Backend StoreRevision Payload ->
    OperatorPlan Backend StoreRevision theory.Query PlanId -> Option RouteId
  events? : Snapshot Backend StoreRevision Payload ->
    OperatorPlan Backend StoreRevision theory.Query PlanId ->
      Option (theory.Revision × theory.Revision)
  result? : Delta Backend StoreRevision Payload DeltaId ->
    Option theory.Observation

variable {theory : Theory}
variable {Backend StoreRevision Payload PlanId DeltaId : Type}
variable {RouteId : Type uRoute}

abbrev Article
    (theory : Theory)
    (Backend StoreRevision Payload PlanId DeltaId : Type) :=
  Claim theory Backend StoreRevision Payload PlanId DeltaId

/-- One semantic route together with exact physical representation equations. -/
structure BoundRoute
    (codec : PhysicalBindingCodec theory Backend StoreRevision Payload PlanId
      DeltaId RouteId)
    (claim : Article theory Backend StoreRevision Payload PlanId DeltaId) where
  route : SequentialRoute theory claim.event RouteId
  physicalRoute : codec.route? claim.snapshot claim.plan = some route.routeId
  physicalEvents : codec.events? claim.snapshot claim.plan =
    some (claim.event.first, claim.event.second)
  physicalResult : codec.result? claim.delta =
    some (theory.query route.target claim.event.request)

/-- The exact semantic scope of a result-binding checker.  The witness remains
available when the certificate language chooses to retain it. -/
def Bound
    (codec : PhysicalBindingCodec theory Backend StoreRevision Payload PlanId
      DeltaId RouteId)
    (claim : Article theory Backend StoreRevision Payload PlanId DeltaId) : Prop :=
  Nonempty (BoundRoute codec claim)

namespace BoundRoute

variable {codec : PhysicalBindingCodec theory Backend StoreRevision Payload
  PlanId DeltaId RouteId}
variable {claim : Article theory Backend StoreRevision Payload PlanId DeltaId}

/-- The retained route is an actual two-step semantic history. -/
def history (bound : BoundRoute codec claim) :
    theory.HistoryStep [claim.event.first, claim.event.second]
      claim.event.source bound.route.target :=
  .cons bound.route.firstStep (.single bound.route.secondStep)

/-- The emitted physical observation is exactly the observation reached by
the retained semantic route. -/
theorem emitted_eq_route_observation (bound : BoundRoute codec claim) :
    codec.result? claim.delta =
      some (theory.query bound.route.target claim.event.request) :=
  bound.physicalResult

end BoundRoute

/-! ## Arbitrary finite occurrence routes

The parallel article above names exactly two events because that is the
backend interface it refines.  Finite execution itself is not binary.  The
following envelope retains an arbitrary chronological semantic history and a
position-aligned physical occurrence list.  It is independent of any concrete
article or wire representation.
-/

/-- A finite semantic history paired positionally with its physical execution
occurrences.  Equal lengths ensure that neither side silently drops a step;
the codec below is responsible for decoding which revision each occurrence
denotes. -/
structure FiniteRoute
    (theory : Theory)
    (Occurrence : Type uOccurrence)
    (source : theory.World) where
  occurrences : List Occurrence
  revisions : List theory.Revision
  target : theory.World
  aligned : occurrences.length = revisions.length
  execution : theory.HistoryStep revisions source target

namespace FiniteRoute

variable {Occurrence : Type uOccurrence} {source : theory.World}

/-- Route equality is determined by its retained occurrences, revisions, and
target; alignment and execution witnesses are proof-irrelevant. -/
@[ext] theorem ext
    {left right : FiniteRoute theory Occurrence source}
    (occurrences : left.occurrences = right.occurrences)
    (revisions : left.revisions = right.revisions)
    (target : left.target = right.target) : left = right := by
  cases left
  cases right
  simp_all

/-- The empty route is the identity history at one world. -/
def nil (theory : Theory) (Occurrence : Type uOccurrence)
    (source : theory.World) : FiniteRoute theory Occurrence source where
  occurrences := []
  revisions := []
  target := source
  aligned := rfl
  execution := .nil source

/-- Concatenate occurrence identity and semantic chronology together. -/
def append (first : FiniteRoute theory Occurrence source)
    (second : FiniteRoute theory Occurrence first.target) :
    FiniteRoute theory Occurrence source where
  occurrences := first.occurrences ++ second.occurrences
  revisions := first.revisions ++ second.revisions
  target := second.target
  aligned := by
    simp only [List.length_append]
    rw [first.aligned, second.aligned]
  execution := first.execution.append second.execution

/-- One physical occurrence and one semantic revision form the atomic finite
route. -/
def single (occurrence : Occurrence) (revision : theory.Revision)
    (target : theory.World) (step : theory.Step revision source target) :
    FiniteRoute theory Occurrence source where
  occurrences := [occurrence]
  revisions := [revision]
  target := target
  aligned := rfl
  execution := .single step

@[simp] theorem append_occurrences
    (first : FiniteRoute theory Occurrence source)
    (second : FiniteRoute theory Occurrence first.target) :
    (first.append second).occurrences =
      first.occurrences ++ second.occurrences :=
  rfl

@[simp] theorem append_revisions
    (first : FiniteRoute theory Occurrence source)
    (second : FiniteRoute theory Occurrence first.target) :
    (first.append second).revisions =
      first.revisions ++ second.revisions :=
  rfl

@[simp] theorem append_target
    (first : FiniteRoute theory Occurrence source)
    (second : FiniteRoute theory Occurrence first.target) :
    (first.append second).target = second.target :=
  rfl

/-- Semantic concatenation visibly retains the physical prefix. -/
theorem occurrences_prefix_append
    (first : FiniteRoute theory Occurrence source)
    (second : FiniteRoute theory Occurrence first.target) :
    Exists fun tail =>
      (first.append second).occurrences = first.occurrences ++ tail :=
  ⟨second.occurrences, rfl⟩

/-- Semantic concatenation visibly retains the revision prefix. -/
theorem revisions_prefix_append
    (first : FiniteRoute theory Occurrence source)
    (second : FiniteRoute theory Occurrence first.target) :
    Exists fun tail =>
      (first.append second).revisions = first.revisions ++ tail :=
  ⟨second.revisions, rfl⟩

/-- A route cannot claim two semantic steps while retaining only one physical
occurrence, or vice versa. -/
theorem no_route_with_misaligned_lists
    (source : theory.World)
    (occurrences : List Occurrence)
    (revisions : List theory.Revision)
    (mismatch : occurrences.length ≠ revisions.length) :
    Not (Exists fun route : FiniteRoute theory Occurrence source =>
      route.occurrences = occurrences /\ route.revisions = revisions) := by
  rintro ⟨route, routeOccurrences, routeRevisions⟩
  apply mismatch
  calc
    occurrences.length = route.occurrences.length :=
      congrArg List.length routeOccurrences.symm
    _ = route.revisions.length := route.aligned
    _ = revisions.length := congrArg List.length routeRevisions

@[simp] theorem nil_append
    (route : FiniteRoute theory Occurrence source) :
    (nil theory Occurrence source).append route = route :=
  ext rfl rfl rfl

@[simp] theorem append_nil
    (route : FiniteRoute theory Occurrence source) :
    route.append (nil theory Occurrence route.target) = route :=
  ext (List.append_nil _) (List.append_nil _) rfl

/-- Finite route composition is associative while preserving both physical
occurrence chronology and semantic revision chronology. -/
theorem append_assoc
    (first : FiniteRoute theory Occurrence source)
    (second : FiniteRoute theory Occurrence first.target)
    (third : FiniteRoute theory Occurrence second.target) :
    (first.append second).append third =
      first.append (second.append third) :=
  ext (List.append_assoc _ _ _) (List.append_assoc _ _ _) rfl

end FiniteRoute

/-- A representation-neutral decoder for arbitrary finite route claims.  Its
claim may be a native article, a proof-relevant replay object, or a generated
wire record. -/
structure FiniteBindingCodec
    (theory : Theory)
    (Claim : Type uClaim)
    (Occurrence : Type uOccurrence) where
  source : Claim -> theory.World
  request : Claim -> theory.Query
  claimedRevisions : Claim -> List theory.Revision
  occurrences? : Claim -> Option (List Occurrence)
  revisions? : Claim -> Option (List theory.Revision)
  result? : Claim -> Option theory.Observation

/-- A finite physical article bound to one retained semantic history. -/
structure FiniteBoundRoute
    {Claim : Type uClaim}
    {Occurrence : Type uOccurrence}
    (codec : FiniteBindingCodec theory Claim Occurrence)
    (claim : Claim) where
  route : FiniteRoute theory Occurrence (codec.source claim)
  semanticRevisions : route.revisions = codec.claimedRevisions claim
  physicalOccurrences : codec.occurrences? claim = some route.occurrences
  physicalRevisions : codec.revisions? claim = some route.revisions
  physicalResult : codec.result? claim =
    some (theory.query route.target (codec.request claim))

def FiniteBound
    {Claim : Type uClaim}
    {Occurrence : Type uOccurrence}
    (codec : FiniteBindingCodec theory Claim Occurrence)
    (claim : Claim) : Prop :=
  Nonempty (FiniteBoundRoute codec claim)

/-- Exact executable authority for an arbitrary finite route scope. -/
structure FiniteBindingAuthority
    {Claim : Type uClaim}
    {Occurrence : Type uOccurrence}
    (codec : FiniteBindingCodec theory Claim Occurrence) where
  Certificate : Type uCertificate
  checker : Checker Claim Certificate
  authority : checker.Authority (FiniteBound codec)

namespace PhysicalBindingCodec

variable {Occurrence : Type uOccurrence}

/-- Regard a paired physical codec whose route identity is an occurrence list
as an arbitrary finite-route codec. -/
def toFinite
    (codec : PhysicalBindingCodec theory Backend StoreRevision Payload PlanId
      DeltaId (List Occurrence)) :
    FiniteBindingCodec theory
      (Article theory Backend StoreRevision Payload PlanId DeltaId)
      Occurrence where
  source := fun claim => claim.event.source
  request := fun claim => claim.event.request
  claimedRevisions := fun claim =>
    [claim.event.first, claim.event.second]
  occurrences? := fun claim => codec.route? claim.snapshot claim.plan
  revisions? := fun claim =>
    match codec.events? claim.snapshot claim.plan with
    | some (first, second) => some [first, second]
    | none => none
  result? := fun claim => codec.result? claim.delta

end PhysicalBindingCodec

namespace BoundRoute

variable {Occurrence : Type uOccurrence}
variable {codec : PhysicalBindingCodec theory Backend StoreRevision Payload
  PlanId DeltaId (List Occurrence)}
variable {claim : Article theory Backend StoreRevision Payload PlanId DeltaId}

/-- Every paired bound route embeds into the finite envelope when its route
identity records exactly two physical occurrences. -/
def toFinite (bound : BoundRoute codec claim)
    (twoOccurrences : bound.route.routeId.length = 2) :
    FiniteBoundRoute codec.toFinite claim where
  route := {
    occurrences := bound.route.routeId
    revisions := [claim.event.first, claim.event.second]
    target := bound.route.target
    aligned := by simpa using twoOccurrences
    execution := bound.history }
  semanticRevisions := rfl
  physicalOccurrences := bound.physicalRoute
  physicalRevisions := by
    change
      (match codec.events? claim.snapshot claim.plan with
        | some (first, second) => some [first, second]
        | none => none) =
      some [claim.event.first, claim.event.second]
    rw [bound.physicalEvents]
  physicalResult := bound.physicalResult

end BoundRoute

/-- Equal finite-route results likewise cannot reconstruct distinct exact
occurrence histories. -/
theorem no_finite_route_recovery_of_result_collision
    {Claim : Type uClaim}
    {Occurrence : Type uOccurrence}
    {codec : FiniteBindingCodec theory Claim Occurrence}
    {firstClaim secondClaim : Claim}
    (first : FiniteBoundRoute codec firstClaim)
    (second : FiniteBoundRoute codec secondClaim)
    (sameResult : codec.result? firstClaim = codec.result? secondClaim)
    (differentOccurrences :
      first.route.occurrences ≠ second.route.occurrences) :
    Not (Exists fun recover : Option theory.Observation -> List Occurrence =>
      recover (codec.result? firstClaim) = first.route.occurrences /\
      recover (codec.result? secondClaim) = second.route.occurrences) := by
  rintro ⟨recover, recoversFirst, recoversSecond⟩
  apply differentOccurrences
  exact recoversFirst.symm.trans
    ((congrArg recover sameResult).trans recoversSecond)

/-! ## Independently replayable result-binding authority -/

/-- An exact checker for one physical codec's proof-relevant bound-route
scope.  The certificate representation remains an implementation choice. -/
structure BindingAuthority
    (codec : PhysicalBindingCodec theory Backend StoreRevision Payload PlanId
      DeltaId RouteId) where
  Certificate : Type uCertificate
  checker : Checker
    (Article theory Backend StoreRevision Payload PlanId DeltaId) Certificate
  authority : checker.Authority (Bound codec)

namespace BindingAuthority

variable {codec : PhysicalBindingCodec theory Backend StoreRevision Payload
  PlanId DeltaId RouteId}

def projection (binding : BindingAuthority codec) :
    binding.checker.AuthorityProjection (Bound codec) (Bound codec) :=
  binding.authority.toProjection

end BindingAuthority

/-! ## Conjunction with the structural parallel authority -/

section Combined

variable {backend : ParallelBackend theory}
variable [DecidableEq Backend] [DecidableEq StoreRevision]
variable [DecidableEq theory.Query] [DecidableEq PlanId]
variable [DecidableEq DeltaId]
variable {codec : PhysicalBindingCodec theory Backend StoreRevision Payload
  PlanId DeltaId RouteId}

def combinedChecker
    (admission : AdmissionAuthority backend)
    (binding : BindingAuthority codec) :
    Checker
      (Article theory Backend StoreRevision Payload PlanId DeltaId)
      (admission.Certificate × binding.Certificate) :=
  Checker.conjunction (replayChecker admission) binding.checker

def CombinedCertified
    (codec : PhysicalBindingCodec theory Backend StoreRevision Payload PlanId
      DeltaId RouteId)
    (backend : ParallelBackend theory)
    (claim : Article theory Backend StoreRevision Payload PlanId DeltaId) : Prop :=
  Certified (backend := backend) claim /\ Bound codec claim

def CombinedMeaning
    (codec : PhysicalBindingCodec theory Backend StoreRevision Payload PlanId
      DeltaId RouteId)
    (backend : ParallelBackend theory)
    (claim : Article theory Backend StoreRevision Payload PlanId DeltaId) : Prop :=
  Meaning (backend := backend) claim /\ Bound codec claim

def combinedProjection
    (admission : AdmissionAuthority backend)
    (binding : BindingAuthority codec) :
    (combinedChecker admission binding).AuthorityProjection
      (CombinedCertified codec backend) (CombinedMeaning codec backend) :=
  (authorityProjection admission).conjunction binding.projection

/-- Structurally replayed and result-bound articles form one ordinary NIK
authority fibre, with paired evidence and no privileged evaluator branch. -/
def family
    (admission : AdmissionAuthority backend)
    (binding : BindingAuthority codec) : AuthorityFamily Unit where
  Claim := fun _ =>
    Article theory Backend StoreRevision Payload PlanId DeltaId
  Certificate := fun _ => admission.Certificate × binding.Certificate
  checker := fun _ => combinedChecker admission binding
  Certified := fun _ => CombinedCertified codec backend
  Meaning := fun _ => CombinedMeaning codec backend
  projection := fun _ => combinedProjection admission binding

end Combined

/-! ## Terminal observations cannot generally recover route identity -/

/-- Even two fully bound articles may expose the same terminal observation
while retaining distinct routes.  No observer-only recovery function can
return both route identities. -/
theorem no_route_recovery_of_result_collision
    {codec : PhysicalBindingCodec theory Backend StoreRevision Payload PlanId
      DeltaId RouteId}
    {firstClaim secondClaim :
      Article theory Backend StoreRevision Payload PlanId DeltaId}
    (first : BoundRoute codec firstClaim)
    (second : BoundRoute codec secondClaim)
    (sameResult : codec.result? firstClaim.delta =
      codec.result? secondClaim.delta)
    (differentRoute : first.route.routeId ≠ second.route.routeId) :
    Not (Exists fun recover : Option theory.Observation -> RouteId =>
      recover (codec.result? firstClaim.delta) = first.route.routeId /\
      recover (codec.result? secondClaim.delta) = second.route.routeId) := by
  rintro ⟨recover, recoversFirst, recoversSecond⟩
  apply differentRoute
  exact recoversFirst.symm.trans
    ((congrArg recover sameResult).trans recoversSecond)

#print axioms BoundRoute.history
#print axioms BoundRoute.emitted_eq_route_observation
#print axioms FiniteRoute.append
#print axioms FiniteRoute.nil_append
#print axioms FiniteRoute.append_nil
#print axioms FiniteRoute.append_assoc
#print axioms FiniteRoute.no_route_with_misaligned_lists
#print axioms BoundRoute.toFinite
#print axioms no_finite_route_recovery_of_result_collision
#print axioms combinedProjection
#print axioms no_route_recovery_of_result_collision

end Mettapedia.GSLT.Dynamics.SemanticPhysicalRouteBinding
