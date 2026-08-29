import Mettapedia.CognitiveArchitecture.ProtectedForegroundBackgroundNIKArticle
import Mettapedia.GSLT.Dynamics.SemanticPhysicalRouteBinding

/-!
# Semantic route binding for the foreground/background NIK article

This module instantiates the generic semantic--physical route authority on the
real foreground chaining and background premise-index workload.  The retained
route identity is the exact ordered list of revision-scoped source
occurrences.  Physical decoding then independently checks:

* that those occurrences resolve to the named semantic events;
* that the emitted payload is the observation reached by their semantic route.

The resulting authority composes with ordinary structural replay and enters
the ordinary NIK frontend.  Shifted occurrence identities provide the
negative discriminator: two valid articles can emit the same observation
while retaining different physical routes, so a terminal value cannot recover
execution identity.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.ForegroundBackgroundSemanticRouteBinding

open Mettapedia.CognitiveArchitecture.ForegroundBackgroundParallelWave
open Mettapedia.CognitiveArchitecture.ProtectedForegroundBackgroundNIKArticle
open Mettapedia.GSLT.Dynamics.EventValuation
open Mettapedia.GSLT.Dynamics.OperatorRealization
open Mettapedia.GSLT.Dynamics.ParallelExecutionAuthority
open Mettapedia.GSLT.Dynamics.SemanticPhysicalRouteBinding
open Mettapedia.GSLT.LanguageDef.CheckerAuthorityFamily
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKDefaultProfile
open Mettapedia.Machines

noncomputable section

/-! ## Physical codec and exact semantic route -/

/-- Operational route identity is occurrence identity, including store,
revision, order, position, and multiplicity. -/
abbrev WorkspaceRouteId := List (OccurrenceId Unit Nat)

/-- Decode the exact route, ordered work pair, and terminal observation using
only the physical snapshot, plan, and delta. -/
def workspaceCodec :
    PhysicalBindingCodec WorkspaceTheory Unit Nat PhysicalPayload Nat Nat
      WorkspaceRouteId where
  route? := fun _snapshot plan => some plan.authoredOccurrences
  events? := fun snapshot plan =>
    match plan.authoredOccurrences with
    | [firstId, secondId] =>
        match snapshot.resolve firstId, snapshot.resolve secondId with
        | some (.work first), some (.work second) => some (first, second)
        | _, _ => none
    | _ => none
  result? := fun delta =>
    match delta.entries with
    | [(_, .observed view)] => some view
    | _ => none

@[simp] theorem workspaceCodec_route (claim : Article) :
    workspaceCodec.route? claim.snapshot claim.plan =
      some claim.plan.authoredOccurrences :=
  rfl

theorem workspaceCodec_events (claim : Article) :
    workspaceCodec.events? claim.snapshot claim.plan =
      authoredWorkPair? claim :=
  rfl

theorem workspaceCodec_result (claim : Article) :
    workspaceCodec.result? claim.delta =
      emittedWorkspaceObservation? claim :=
  rfl

/-- Existing semantic--physical binding constructs an actual chronological
route rather than merely asserting equality of decoded endpoints. -/
def boundRouteOfSemanticallyBound (claim : Article)
    (bound : SemanticallyBound claim) : BoundRoute workspaceCodec claim where
  route := {
    routeId := claim.plan.authoredOccurrences
    afterFirst := workspaceStep claim.event.source claim.event.first
    target := semanticTarget claim
    firstStep := rfl
    secondStep := rfl }
  physicalRoute := rfl
  physicalEvents := by
    change authoredWorkPair? claim =
      some (claim.event.first, claim.event.second)
    exact bound.1
  physicalResult := by
    simpa [workspaceCodec_result, WorkspaceTheory,
      Mettapedia.GSLT.Dynamics.CertifiedBatchParallelBridge.deterministicTheory,
      semanticTerminalObservation] using bound.2

/-- Conversely, a retained semantic route forces the older endpoint binding.
The proof uses both step witnesses; the target is not trusted as an unrelated
field. -/
theorem semanticallyBound_of_boundRoute (claim : Article)
  (bound : BoundRoute workspaceCodec claim) : SemanticallyBound claim := by
  constructor
  · exact bound.physicalEvents
  · have targetEq : bound.route.target = semanticTarget claim := by
      calc
        bound.route.target =
            workspaceStep bound.route.afterFirst claim.event.second :=
          bound.route.secondStep
        _ = workspaceStep
              (workspaceStep claim.event.source claim.event.first)
              claim.event.second := by
          rw [bound.route.firstStep]
        _ = semanticTarget claim := rfl
    simpa [workspaceCodec_result, WorkspaceTheory,
      Mettapedia.GSLT.Dynamics.CertifiedBatchParallelBridge.deterministicTheory,
      semanticTerminalObservation, targetEq] using bound.physicalResult

theorem semanticallyBound_iff_bound (claim : Article) :
    SemanticallyBound claim <-> Bound workspaceCodec claim := by
  constructor
  · exact fun bound => ⟨boundRouteOfSemanticallyBound claim bound⟩
  · rintro ⟨bound⟩
    exact semanticallyBound_of_boundRoute claim bound

/-- Successful decoding of an authored work pair forces an exact two-element
occurrence route; no occurrence may be silently dropped or added. -/
theorem authoredWorkPair?_some_implies_two_occurrences
    (claim : Article) {pair : Work × Work}
    (decoded : authoredWorkPair? claim = some pair) :
    claim.plan.authoredOccurrences.length = 2 := by
  unfold authoredWorkPair? at decoded
  generalize occurrenceEq : claim.plan.authoredOccurrences = occurrences
    at decoded ⊢
  cases occurrences with
  | nil => simp at decoded
  | cons first rest =>
      cases rest with
      | nil => simp at decoded
      | cons second rest =>
          cases rest with
          | nil => rfl
          | cons third tail => simp at decoded

theorem boundRoute_twoOccurrences (claim : Article)
    (bound : BoundRoute workspaceCodec claim) :
    bound.route.routeId.length = 2 := by
  have planLength := authoredWorkPair?_some_implies_two_occurrences claim
    (semanticallyBound_of_boundRoute claim bound).1
  have routeEquality :
      claim.plan.authoredOccurrences = bound.route.routeId := by
    exact Option.some.inj bound.physicalRoute
  calc
    bound.route.routeId.length = claim.plan.authoredOccurrences.length :=
      congrArg List.length routeEquality.symm
    _ = 2 := planLength

/-- Deterministic workspace histories have the unique fold target. -/
theorem workspaceHistory_target
    : ∀ {revisions : List Work} {source target : Workspace},
      WorkspaceTheory.HistoryStep revisions source target ->
        target = revisions.foldl workspaceStep source
  | [], _, _, .nil _ => rfl
  | _ :: _, _, _, .cons step rest => by
      simp only [List.foldl_cons]
      rw [workspaceHistory_target rest, step]

/-- Paired binding always enters the arbitrary finite-route envelope. -/
def finiteBoundRouteOfBoundRoute (claim : Article)
    (bound : BoundRoute workspaceCodec claim) :
    FiniteBoundRoute workspaceCodec.toFinite claim :=
  bound.toFinite (boundRoute_twoOccurrences claim bound)

/-- For this deterministic workload, finite route binding reconstructs the
paired semantic route rather than merely agreeing on the endpoint. -/
def boundRouteOfFiniteBoundRoute (claim : Article)
    (finite : FiniteBoundRoute workspaceCodec.toFinite claim) :
    BoundRoute workspaceCodec claim := by
  have decodedRevisions := finite.physicalRevisions
  dsimp only [PhysicalBindingCodec.toFinite] at decodedRevisions
  have semanticRevisions := finite.semanticRevisions
  dsimp only [PhysicalBindingCodec.toFinite] at semanticRevisions
  rw [semanticRevisions] at decodedRevisions
  have decodedEvents :
      workspaceCodec.events? claim.snapshot claim.plan =
        some (claim.event.first, claim.event.second) := by
    cases events : workspaceCodec.events? claim.snapshot claim.plan with
    | none => simp [events] at decodedRevisions
    | some pair =>
        rcases pair with ⟨first, second⟩
        simp [events] at decodedRevisions
        rcases decodedRevisions with ⟨rfl, rfl⟩
        rfl
  have semanticHistory := finite.route.execution
  rw [semanticRevisions] at semanticHistory
  have folded := workspaceHistory_target semanticHistory
  apply boundRouteOfSemanticallyBound claim
  constructor
  · exact decodedEvents
  · have emitted := finite.physicalResult
    rw [folded] at emitted
    simpa [PhysicalBindingCodec.toFinite, workspaceCodec_result,
      WorkspaceTheory,
      Mettapedia.GSLT.Dynamics.CertifiedBatchParallelBridge.deterministicTheory,
      semanticTerminalObservation, semanticTarget, execute,
      workspaceStep] using emitted

theorem bound_iff_finiteBound (claim : Article) :
    Bound workspaceCodec claim <->
      FiniteBound workspaceCodec.toFinite claim := by
  constructor
  · rintro ⟨bound⟩
    exact ⟨finiteBoundRouteOfBoundRoute claim bound⟩
  · rintro ⟨finite⟩
    exact ⟨boundRouteOfFiniteBoundRoute claim finite⟩

/-! ## Reuse of the executable binding kernel -/

/-- The existing Boolean decoder is also an exact checker for the stronger,
proof-relevant route scope, because the deterministic semantic route is
constructible exactly when its physical endpoints are bound. -/
def workspaceBindingAuthority : BindingAuthority workspaceCodec where
  Certificate := Unit
  checker := bindingChecker
  authority := {
    sound := by
      intro claim _ accepted
      exact (semanticallyBound_iff_bound claim).mp
        ((bindingCheck_eq_true_iff claim).mp accepted)
    complete := by
      intro claim bound
      refine ⟨(), (bindingCheck_eq_true_iff claim).mpr ?_⟩
      exact (semanticallyBound_iff_bound claim).mpr bound }

/-- The same executable checker is exact for the arbitrary finite-route scope
on this workload; this is a theorem-backed change of meaning, not a second
checker. -/
def workspaceFiniteBindingAuthority :
    FiniteBindingAuthority workspaceCodec.toFinite where
  Certificate := Unit
  checker := bindingChecker
  authority := {
    sound := by
      intro claim _ accepted
      apply (bound_iff_finiteBound claim).mp
      apply (semanticallyBound_iff_bound claim).mp
      exact (bindingCheck_eq_true_iff claim).mp accepted
    complete := by
      intro claim finite
      refine ⟨(), (bindingCheck_eq_true_iff claim).mpr ?_⟩
      apply (semanticallyBound_iff_bound claim).mpr
      exact (bound_iff_finiteBound claim).mpr finite }

abbrev workspaceCombinedChecker :=
  combinedChecker replayableAdmission workspaceBindingAuthority

abbrev workspaceCombinedProjection :=
  combinedProjection replayableAdmission workspaceBindingAuthority

def workspaceRouteFamily : AuthorityFamily Unit :=
  Mettapedia.GSLT.Dynamics.SemanticPhysicalRouteBinding.family
    replayableAdmission workspaceBindingAuthority

def workspaceRouteFrontend := Frontend.typed workspaceRouteFamily

def usefulRouteSubmission : TypedSubmission workspaceRouteFamily :=
  ⟨(), physicalClaim, ((), ())⟩

theorem useful_route_article_accepted :
    workspaceCombinedChecker.check physicalClaim ((), ()) = true := by
  simp [workspaceCombinedChecker, combinedChecker, Checker.conjunction,
    physical_article_accepted, useful_binding_accepted,
    workspaceBindingAuthority]

theorem useful_route_article_meaning :
    CombinedMeaning workspaceCodec replayableParallelBackend physicalClaim :=
  workspaceCombinedProjection.sound physicalClaim ((), ())
    useful_route_article_accepted

theorem useful_finite_route_article_meaning :
    Meaning (backend := replayableParallelBackend) physicalClaim /\
      FiniteBound workspaceCodec.toFinite physicalClaim :=
  ⟨useful_route_article_meaning.1,
    (bound_iff_finiteBound physicalClaim).mp
      useful_route_article_meaning.2⟩

/-- The proof-relevant route article uses the same ordinary statusful NIK
frontend; no evaluator-specific acceptance branch is introduced. -/
theorem useful_route_article_defaultNIK_accepts :
    workspaceRouteFrontend.run
        (workspaceRouteFrontend.encode usefulRouteSubmission) =
      SubmissionOutcome.accepted
        (TypedSubmission.claim usefulRouteSubmission) := by
  have checked :
      (workspaceRouteFamily.checker ()).check
        physicalClaim ((), ()) = true := by
    change workspaceCombinedChecker.check physicalClaim ((), ()) = true
    exact useful_route_article_accepted
  rw [workspaceRouteFrontend.run_encode]
  simp [usefulRouteSubmission, checked]

/-! ## Forged representations remain refused -/

theorem forged_input_route_article_rejected :
    workspaceCombinedChecker.check forgedInputClaim ((), ()) = false := by
  simp [workspaceCombinedChecker, combinedChecker, Checker.conjunction,
    forged_input_base_article_accepted, forged_input_binding_rejected,
    workspaceBindingAuthority]

theorem forged_output_route_article_rejected :
    workspaceCombinedChecker.check forgedOutputClaim ((), ()) = false := by
  simp [workspaceCombinedChecker, combinedChecker, Checker.conjunction,
    forged_output_base_article_accepted, forged_output_binding_rejected,
    workspaceBindingAuthority]

/-! ## Binding is not protection -/

abbrev rewindCombinedChecker :=
  combinedChecker rewindAdmission workspaceBindingAuthority

theorem rewind_route_article_accepted :
    rewindCombinedChecker.check rewindPhysicalClaim ((), ()) = true := by
  simp [rewindCombinedChecker, combinedChecker, Checker.conjunction,
    rewind_base_article_accepted, rewind_binding_accepted,
    workspaceBindingAuthority]

/-- Exact semantic chronology and physical binding do not grant a wellbeing
or progress capability. -/
theorem route_binding_does_not_mint_protection :
    rewindCombinedChecker.check rewindPhysicalClaim ((), ()) = true /\
      (protectedChecker rewindAdmission).check
        rewindPhysicalClaim (((), ()), ()) = false :=
  ⟨rewind_route_article_accepted, rewind_protected_article_rejected⟩

/-! ## Same result, distinct physical routes -/

/-- A semantically identical source snapshot with an unrelated leading entry.
The two work occurrences therefore occupy different logical positions. -/
def shiftedPhysicalSnapshot : PhysicalSnapshot where
  storeId := ()
  revision := 0
  entries :=
    [.observed (observeWorkspace initialWorkspace),
      .work .foregroundBridge, .work .refreshPremiseIndex]

def shiftedForegroundOccurrence := shiftedPhysicalSnapshot.occurrenceId 1
def shiftedIndexerOccurrence := shiftedPhysicalSnapshot.occurrenceId 2

def shiftedPhysicalPlan : OperatorPlan Unit Nat Unit Nat where
  id := 18
  observer := ()
  sourceBackend := ()
  targetBackend := ()
  sourceRevision := 0
  authoredOccurrences :=
    [shiftedForegroundOccurrence, shiftedIndexerOccurrence]

def shiftedPhysicalReceipt : Receipt Unit Nat Unit Nat Nat where
  planId := shiftedPhysicalPlan.id
  observer := ()
  sourceBackend := ()
  targetBackend := ()
  sourceRevision := 0
  targetRevision := 1
  deltaId := physicalDelta.id
  mode := .parallel
  authoredOccurrences := shiftedPhysicalPlan.authoredOccurrences
  emittedOccurrences := physicalDelta.entries.map Prod.fst

def shiftedPhysicalClaim : Article where
  event := usefulEventClaim
  snapshot := shiftedPhysicalSnapshot
  plan := shiftedPhysicalPlan
  delta := physicalDelta
  receipt := shiftedPhysicalReceipt

theorem shifted_base_article_accepted :
    (replayChecker replayableAdmission).check shiftedPhysicalClaim () = true := by
  decide

theorem shifted_binding_accepted :
    bindingChecker.check shiftedPhysicalClaim () = true := by
  change bindingCheck shiftedPhysicalClaim = true
  exact (bindingCheck_eq_true_iff shiftedPhysicalClaim).2 ⟨rfl, rfl⟩

theorem shifted_route_article_accepted :
    workspaceCombinedChecker.check shiftedPhysicalClaim ((), ()) = true := by
  simp [workspaceCombinedChecker, combinedChecker, Checker.conjunction,
    shifted_base_article_accepted, shifted_binding_accepted,
    workspaceBindingAuthority]

theorem useful_semanticallyBound : SemanticallyBound physicalClaim :=
  ⟨rfl, rfl⟩

theorem shifted_semanticallyBound : SemanticallyBound shiftedPhysicalClaim :=
  ⟨rfl, rfl⟩

def usefulBoundRoute : BoundRoute workspaceCodec physicalClaim :=
  boundRouteOfSemanticallyBound physicalClaim useful_semanticallyBound

def shiftedBoundRoute : BoundRoute workspaceCodec shiftedPhysicalClaim :=
  boundRouteOfSemanticallyBound shiftedPhysicalClaim shifted_semanticallyBound

/-! ## Entry into the arbitrary finite-route envelope -/

def usefulFiniteBoundRoute :
    FiniteBoundRoute workspaceCodec.toFinite physicalClaim :=
  usefulBoundRoute.toFinite rfl

def shiftedFiniteBoundRoute :
    FiniteBoundRoute workspaceCodec.toFinite shiftedPhysicalClaim :=
  shiftedBoundRoute.toFinite rfl

def usefulForegroundRoute :
    FiniteRoute WorkspaceTheory (OccurrenceId Unit Nat) initialWorkspace :=
  FiniteRoute.single foregroundPhysicalOccurrence .foregroundBridge
    (workspaceStep initialWorkspace .foregroundBridge) rfl

def usefulIndexerRoute :
    FiniteRoute WorkspaceTheory (OccurrenceId Unit Nat)
      usefulForegroundRoute.target :=
  FiniteRoute.single indexerPhysicalOccurrence .refreshPremiseIndex
    (semanticTarget physicalClaim) rfl

/-- The worked parallel article is not an opaque binary primitive: its exact
finite route is the composition of the foreground step and background step. -/
theorem useful_finite_route_decomposes :
    usefulFiniteBoundRoute.route =
      usefulForegroundRoute.append usefulIndexerRoute := by
  apply FiniteRoute.ext <;> rfl

/-- Composition retains the exact foreground occurrence as a physical and
semantic prefix. -/
theorem useful_foreground_prefix_retained :
    Exists fun tail =>
      usefulFiniteBoundRoute.route.occurrences =
        usefulForegroundRoute.occurrences ++ tail := by
  rw [useful_finite_route_decomposes]
  exact FiniteRoute.occurrences_prefix_append
    usefulForegroundRoute usefulIndexerRoute

theorem useful_and_shifted_routes_differ :
    usefulBoundRoute.route.routeId ≠ shiftedBoundRoute.route.routeId := by
  decide

theorem useful_and_shifted_results_agree :
    workspaceCodec.result? physicalClaim.delta =
      workspaceCodec.result? shiftedPhysicalClaim.delta :=
  rfl

/-- Terminal observations cannot reconstruct exact execution identity even
inside the fully replayed and semantically bound subset. -/
theorem terminal_observation_does_not_recover_occurrence_route :
    Not (Exists fun recover : Option WorkspaceView -> WorkspaceRouteId =>
      recover (workspaceCodec.result? physicalClaim.delta) =
          usefulBoundRoute.route.routeId /\
        recover (workspaceCodec.result? shiftedPhysicalClaim.delta) =
          shiftedBoundRoute.route.routeId) :=
  no_route_recovery_of_result_collision
    usefulBoundRoute shiftedBoundRoute useful_and_shifted_results_agree
      useful_and_shifted_routes_differ

/-- The nonrecovery result survives embedding into the arbitrary finite-route
algebra. -/
theorem finite_terminal_observation_does_not_recover_occurrence_route :
    Not (Exists fun recover :
        Option WorkspaceView -> List (OccurrenceId Unit Nat) =>
      recover (workspaceCodec.toFinite.result? physicalClaim) =
          usefulFiniteBoundRoute.route.occurrences /\
        recover (workspaceCodec.toFinite.result? shiftedPhysicalClaim) =
          shiftedFiniteBoundRoute.route.occurrences) := by
  apply no_finite_route_recovery_of_result_collision
    usefulFiniteBoundRoute shiftedFiniteBoundRoute
  · rfl
  · decide

#print axioms semanticallyBound_iff_bound
#print axioms bound_iff_finiteBound
#print axioms workspaceFiniteBindingAuthority
#print axioms useful_route_article_meaning
#print axioms useful_finite_route_article_meaning
#print axioms useful_route_article_defaultNIK_accepts
#print axioms forged_input_route_article_rejected
#print axioms forged_output_route_article_rejected
#print axioms route_binding_does_not_mint_protection
#print axioms shifted_route_article_accepted
#print axioms useful_finite_route_decomposes
#print axioms useful_foreground_prefix_retained
#print axioms terminal_observation_does_not_recover_occurrence_route
#print axioms finite_terminal_observation_does_not_recover_occurrence_route

end

end Mettapedia.CognitiveArchitecture.ForegroundBackgroundSemanticRouteBinding
