import Mettapedia.GSLT.Dynamics.ContextualDeltaHandlers
import Mettapedia.GSLT.Dynamics.ContextualWorldMerge
import Mettapedia.GSLT.LanguageDef.GSLTILFiniteRevisionRouteBridge

/-!
# Contextual deltas and commit authority on retained GSLT-IL routes

An occurrence-retaining route may carry branch-local state effects without
performing them in the ambient world.  This module attaches two local displays
to every physical occurrence: a composable state delta and a list of deferred
external intents.  Both displays fold over the exact chronological route and
preserve route append.

Alternative route candidates share one parent state.  Retention, selection,
state commit, delta merge, and external-intent authorization remain distinct:

* selection proves only which retained route candidate was chosen;
* state commit additionally requires an authored policy witness;
* successful state commit exposes, but does not perform, deferred intents;
* intent execution requires a second policy witness; and
* alternative merge uses the existing permutation-invariant delta resolver.

The occurrence display must precede lossy path erasure.  The canary has two
routes with equal generated execution paths but different physical occurrence
identities and therefore different deltas.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.ContextualDeltaRouteBridge

open Mettapedia.GSLT.Dynamics.ContextualDeltaHandlers
open Mettapedia.GSLT.LanguageDef.GSLTIL.FiniteRevisionRouteBridge

universe u

/-! ## Compositional occurrence displays -/

/-- Candidate-local state and intent observations on exact route occurrences. -/
structure RouteEffectDisplay
    (Occurrence Delta Intent : Type u) where
  deltaAt : Occurrence → Delta
  intentsAt : Occurrence → List Intent

/-- Chronological delta fold.  `first :: rest` performs the first delta before
the folded remainder. -/
def historyDelta
    {State Delta Occurrence Intent : Type u}
    (algebra : DeltaAlgebra State Delta)
    (display : RouteEffectDisplay Occurrence Delta Intent) :
    List Occurrence → Delta
  | [] => algebra.empty
  | occurrence :: rest =>
      algebra.compose (display.deltaAt occurrence)
        (historyDelta algebra display rest)

/-- Deferred intents retain chronological occurrence order. -/
def historyIntents
    {Occurrence Delta Intent : Type u}
    (display : RouteEffectDisplay Occurrence Delta Intent)
    (occurrences : List Occurrence) : List Intent :=
  occurrences.flatMap display.intentsAt

@[simp] theorem historyDelta_nil
    {State Delta Occurrence Intent : Type u}
    (algebra : DeltaAlgebra State Delta)
    (display : RouteEffectDisplay Occurrence Delta Intent) :
    historyDelta algebra display [] = algebra.empty :=
  rfl

@[simp] theorem historyDelta_cons
    {State Delta Occurrence Intent : Type u}
    (algebra : DeltaAlgebra State Delta)
    (display : RouteEffectDisplay Occurrence Delta Intent)
    (occurrence : Occurrence) (rest : List Occurrence) :
    historyDelta algebra display (occurrence :: rest) =
      algebra.compose (display.deltaAt occurrence)
        (historyDelta algebra display rest) :=
  rfl

/-- Delta observation is a monoid homomorphism from route concatenation to
chronological delta composition. -/
theorem historyDelta_append
    {State Delta Occurrence Intent : Type u}
    (algebra : DeltaAlgebra State Delta)
    (display : RouteEffectDisplay Occurrence Delta Intent)
    (earlier later : List Occurrence) :
    historyDelta algebra display (earlier ++ later) =
      algebra.compose (historyDelta algebra display earlier)
        (historyDelta algebra display later) := by
  induction earlier with
  | nil =>
      simp [historyDelta, algebra.empty_compose]
  | cons occurrence rest inductionHypothesis =>
      simp only [List.cons_append, historyDelta_cons, inductionHypothesis]
      exact (algebra.compose_assoc _ _ _).symm

@[simp] theorem historyIntents_append
    {Occurrence Delta Intent : Type u}
    (display : RouteEffectDisplay Occurrence Delta Intent)
    (earlier later : List Occurrence) :
    historyIntents display (earlier ++ later) =
      historyIntents display earlier ++ historyIntents display later := by
  simp [historyIntents]

/-! ## Exact route observations -/

def routeDelta
    {theory : Mettapedia.GSLT.Dynamics.QueryRevision.Theory.{u, u, u, u}}
    {Occurrence State Delta Intent : Type u} {source : theory.World}
    (algebra : DeltaAlgebra State Delta)
    (display : RouteEffectDisplay Occurrence Delta Intent)
    (route : PathRetainingFiniteRoute theory Occurrence source) : Delta :=
  historyDelta algebra display route.occurrences

def routeIntents
    {theory : Mettapedia.GSLT.Dynamics.QueryRevision.Theory.{u, u, u, u}}
    {Occurrence Delta Intent : Type u} {source : theory.World}
    (display : RouteEffectDisplay Occurrence Delta Intent)
    (route : PathRetainingFiniteRoute theory Occurrence source) : List Intent :=
  historyIntents display route.occurrences

@[simp] theorem routeDelta_append
    {theory : Mettapedia.GSLT.Dynamics.QueryRevision.Theory.{u, u, u, u}}
    {Occurrence State Delta Intent : Type u} {source : theory.World}
    (algebra : DeltaAlgebra State Delta)
    (display : RouteEffectDisplay Occurrence Delta Intent)
    (earlier : PathRetainingFiniteRoute theory Occurrence source)
    (later : PathRetainingFiniteRoute theory Occurrence earlier.target) :
    routeDelta algebra display (earlier.append later) =
      algebra.compose (routeDelta algebra display earlier)
        (routeDelta algebra display later) := by
  exact historyDelta_append algebra display earlier.occurrences later.occurrences

@[simp] theorem routeIntents_append
    {theory : Mettapedia.GSLT.Dynamics.QueryRevision.Theory.{u, u, u, u}}
    {Occurrence Delta Intent : Type u} {source : theory.World}
    (display : RouteEffectDisplay Occurrence Delta Intent)
    (earlier : PathRetainingFiniteRoute theory Occurrence source)
    (later : PathRetainingFiniteRoute theory Occurrence earlier.target) :
    routeIntents display (earlier.append later) =
      routeIntents display earlier ++ routeIntents display later := by
  exact historyIntents_append display earlier.occurrences later.occurrences

/-! ## Isolated route families -/

/-- One retained alternative.  Its state and intents are computed from the
exact route rather than stored as independently editable copies. -/
structure RouteCandidate
    (theory : Mettapedia.GSLT.Dynamics.QueryRevision.Theory.{u, u, u, u})
    (Occurrence Answer : Type u) (source : theory.World) where
  branch : Mettapedia.GSLT.Dynamics.ContextualEffectHandlers.BranchTrace
  answer : Answer
  route : PathRetainingFiniteRoute theory Occurrence source

/-- All isolated candidates in one family share this exact parent state. -/
structure RouteFamily
    (theory : Mettapedia.GSLT.Dynamics.QueryRevision.Theory.{u, u, u, u})
    (Occurrence State Answer : Type u) (source : theory.World) where
  parent : State
  candidates : List (RouteCandidate theory Occurrence Answer source)

def RouteCandidate.delta
    {theory : Mettapedia.GSLT.Dynamics.QueryRevision.Theory.{u, u, u, u}}
    {Occurrence State Delta Answer Intent : Type u} {source : theory.World}
    (algebra : DeltaAlgebra State Delta)
    (display : RouteEffectDisplay Occurrence Delta Intent)
    (candidate : RouteCandidate theory Occurrence Answer source) : Delta :=
  routeDelta algebra display candidate.route

def RouteCandidate.intents
    {theory : Mettapedia.GSLT.Dynamics.QueryRevision.Theory.{u, u, u, u}}
    {Occurrence Delta Answer Intent : Type u} {source : theory.World}
    (display : RouteEffectDisplay Occurrence Delta Intent)
    (candidate : RouteCandidate theory Occurrence Answer source) : List Intent :=
  routeIntents display candidate.route

def RouteCandidate.state
    {theory : Mettapedia.GSLT.Dynamics.QueryRevision.Theory.{u, u, u, u}}
    {Occurrence State Delta Answer Intent : Type u} {source : theory.World}
    (algebra : DeltaAlgebra State Delta)
    (display : RouteEffectDisplay Occurrence Delta Intent)
    (parent : State)
    (candidate : RouteCandidate theory Occurrence Answer source) : State :=
  algebra.apply parent (candidate.delta algebra display)

/-! ## Selection, state commit, and intent authority -/

/-- An occurrence-position selection receipt.  It does not authorize commit. -/
structure Selection {Candidate : Type u} (candidates : List Candidate) where
  index : Nat
  candidate : Candidate
  selected : candidates[index]? = some candidate

/-- State-commit policy is independent of the resolver that produced a
selection receipt. -/
structure CommitPolicy (Candidate : Type u) where
  Allows : Candidate → Prop

/-- Commit authority is indexed by the exact selection it licenses.  Authority
for one retained occurrence therefore cannot be reused for a sibling. -/
structure AuthorizedSelection {Candidate : Type u}
    (policy : CommitPolicy Candidate) {candidates : List Candidate}
    (selection : Selection candidates) where
  allowed : policy.Allows selection.candidate

/-- A state-commit receipt retains the selected route and exposes its external
intents as still-deferred data. -/
structure StateCommit
    {theory : Mettapedia.GSLT.Dynamics.QueryRevision.Theory.{u, u, u, u}}
    {Occurrence State Delta Answer Intent : Type u} {source : theory.World}
    (algebra : DeltaAlgebra State Delta)
    (display : RouteEffectDisplay Occurrence Delta Intent)
    (family : RouteFamily theory Occurrence State Answer source)
    (policy : CommitPolicy (RouteCandidate theory Occurrence Answer source)) where
  selection : Selection family.candidates
  authorization : AuthorizedSelection policy selection
  delta : Delta
  state : State
  deferredIntents : List Intent
  deltaExact : delta = selection.candidate.delta algebra display
  stateExact : state = algebra.apply family.parent delta
  intentsExact : deferredIntents =
    selection.candidate.intents display

/-- Commit exactly the authorized candidate's state delta.  No sibling delta
or intent enters the receipt. -/
def commitState
    {theory : Mettapedia.GSLT.Dynamics.QueryRevision.Theory.{u, u, u, u}}
    {Occurrence State Delta Answer Intent : Type u} {source : theory.World}
    (algebra : DeltaAlgebra State Delta)
    (display : RouteEffectDisplay Occurrence Delta Intent)
    (family : RouteFamily theory Occurrence State Answer source)
    (policy : CommitPolicy (RouteCandidate theory Occurrence Answer source))
    (selection : Selection family.candidates)
    (authorization : AuthorizedSelection policy selection) :
    StateCommit algebra display family policy where
  selection := selection
  authorization := authorization
  delta := selection.candidate.delta algebra display
  state := selection.candidate.state algebra display family.parent
  deferredIntents := selection.candidate.intents display
  deltaExact := rfl
  stateExact := rfl
  intentsExact := rfl

/-- External authority is deliberately a second boundary after state commit. -/
structure IntentPolicy (Intent : Type u) where
  Allows : List Intent → Prop

structure AuthorizedIntents
    {theory : Mettapedia.GSLT.Dynamics.QueryRevision.Theory.{u, u, u, u}}
    {Occurrence State Delta Answer Intent : Type u} {source : theory.World}
    {algebra : DeltaAlgebra State Delta}
    {display : RouteEffectDisplay Occurrence Delta Intent}
    {family : RouteFamily theory Occurrence State Answer source}
    {commitPolicy : CommitPolicy
      (RouteCandidate theory Occurrence Answer source)}
    (intentPolicy : IntentPolicy Intent)
    (commit : StateCommit algebra display family commitPolicy) where
  allowed : intentPolicy.Allows commit.deferredIntents

/-! ## Permutation-invariant alternative merge -/

def candidateDeltas
    {theory : Mettapedia.GSLT.Dynamics.QueryRevision.Theory.{u, u, u, u}}
    {Occurrence State Delta Answer Intent : Type u} {source : theory.World}
    (algebra : DeltaAlgebra State Delta)
    (display : RouteEffectDisplay Occurrence Delta Intent)
    (candidates : List (RouteCandidate theory Occurrence Answer source)) :
    List Delta :=
  candidates.map fun candidate => candidate.delta algebra display

/-- Reordering route candidates cannot affect an authored unordered merge
decision. -/
theorem merge_candidateDeltas_perm
    {theory : Mettapedia.GSLT.Dynamics.QueryRevision.Theory.{u, u, u, u}}
    {Occurrence State Delta Answer Intent : Type u} {source : theory.World}
    (algebra : DeltaAlgebra State Delta)
    (display : RouteEffectDisplay Occurrence Delta Intent)
    (resolver : AlternativeMerge Delta)
    {first second : List (RouteCandidate theory Occurrence Answer source)}
    (permutation : first.Perm second) :
    resolver.merge (candidateDeltas algebra display first) =
      resolver.merge (candidateDeltas algebra display second) :=
  resolver.permutationInvariant (by
    simpa [candidateDeltas] using
      (permutation.map fun candidate => candidate.delta algebra display))

/-- A merge receipt changes only the state delta coordinate.  The retained
family remains an explicit parameter, and its intents gain no authority. -/
structure MergeReceipt
    {theory : Mettapedia.GSLT.Dynamics.QueryRevision.Theory.{u, u, u, u}}
    {Occurrence State Delta Answer Intent : Type u} {source : theory.World}
    (algebra : DeltaAlgebra State Delta)
    (display : RouteEffectDisplay Occurrence Delta Intent)
    (resolver : AlternativeMerge Delta)
    (family : RouteFamily theory Occurrence State Answer source) where
  delta : Delta
  state : State
  resolved : resolver.merge (candidateDeltas algebra display family.candidates) =
    some delta
  stateExact : state = algebra.apply family.parent delta

def mergeFamily?
    {theory : Mettapedia.GSLT.Dynamics.QueryRevision.Theory.{u, u, u, u}}
    {Occurrence State Delta Answer Intent : Type u} {source : theory.World}
    (algebra : DeltaAlgebra State Delta)
    (display : RouteEffectDisplay Occurrence Delta Intent)
    (resolver : AlternativeMerge Delta)
    (family : RouteFamily theory Occurrence State Answer source) :
    Option (MergeReceipt algebra display resolver family) :=
  match resolution :
      resolver.merge (candidateDeltas algebra display family.candidates) with
  | none => none
  | some delta =>
      some
        { delta := delta
          state := algebra.apply family.parent delta
          resolved := resolution
          stateExact := rfl }

/-! ## Positive and negative controls -/

namespace Canary

open Mettapedia.GSLT.Dynamics.ContextualDeltaHandlers.Canary
open Mettapedia.GSLT.LanguageDef.GSLTIL.FiniteRevisionRouteBridge.Canary

def display : RouteEffectDisplay Nat (Finset Nat) Bool where
  deltaAt occurrence := {occurrence}
  intentsAt occurrence := [occurrence = 1]

def leftCandidate :
    RouteCandidate collisionTheory Nat Bool () where
  branch := [false]
  answer := false
  route := falseRoute

def rightCandidate :
    RouteCandidate collisionTheory Nat Bool () where
  branch := [true]
  answer := true
  route := trueRoute

def family : RouteFamily collisionTheory Nat (Finset Nat) Bool () where
  parent := {42}
  candidates := [leftCandidate, rightCandidate]

def leftSelection : Selection family.candidates where
  index := 0
  candidate := leftCandidate
  selected := rfl

def rightSelection : Selection family.candidates where
  index := 1
  candidate := rightCandidate
  selected := rfl

/-- Only the left branch is authorized to alter the parent in this canary. -/
def leftOnly : CommitPolicy
    (RouteCandidate collisionTheory Nat Bool ()) where
  Allows candidate := candidate.branch = [false]

def leftAuthorization : AuthorizedSelection leftOnly leftSelection where
  allowed := rfl

def leftCommit : StateCommit factAlgebra display family leftOnly :=
  commitState factAlgebra display family leftOnly leftSelection leftAuthorization

/-- Selection of a retained candidate does not mint state-commit authority. -/
theorem right_selection_is_not_commit_authority :
    Nonempty (Selection family.candidates) ∧
      ¬ Nonempty (AuthorizedSelection leftOnly rightSelection) := by
  constructor
  · exact ⟨rightSelection⟩
  · rintro ⟨authorization⟩
    simpa [leftOnly, rightSelection, rightCandidate] using authorization.allowed

/-- The authorized state commit contains only the selected delta and retains
its external request as deferred data. -/
theorem selected_commit_excludes_loser :
    leftCommit.delta = {0} ∧
      leftCommit.state = {0, 42} ∧
      leftCommit.deferredIntents = [false] := by
  decide

/-- Even a completed state commit does not manufacture permission to perform
its deferred external request. -/
def noIntents : IntentPolicy Bool where
  Allows _ := False

theorem state_commit_does_not_authorize_intents :
    Nonempty (StateCommit factAlgebra display family leftOnly) ∧
      ¬ Nonempty (AuthorizedIntents noIntents leftCommit) := by
  constructor
  · exact ⟨leftCommit⟩
  · rintro ⟨authorization⟩
    exact authorization.allowed

/-- The occurrence-sensitive delta display distinguishes routes whose
generated execution paths are equal after identity erasure. -/
theorem effect_display_precedes_path_erasure :
    falseRoute.executionPath = trueRoute.executionPath ∧
      routeDelta factAlgebra display falseRoute = {0} ∧
      routeDelta factAlgebra display trueRoute = {1} := by
  exact ⟨projected_paths_equal, by decide, by decide⟩

/-- Join merge may combine compatible state deltas while the family still
retains both route occurrences. -/
def compatibleMergeReceipt :
    MergeReceipt factAlgebra display (joinMerge (Finset Nat)) family where
  delta := {0, 1}
  state := {0, 1, 42}
  resolved := by decide
  stateExact := by decide

theorem compatible_merge_retains_both_routes :
    ∃ receipt : MergeReceipt factAlgebra display (joinMerge (Finset Nat)) family,
      receipt.delta = {0, 1} ∧
        receipt.state = {0, 1, 42} ∧
        family.candidates.length = 2 := by
  exact ⟨compatibleMergeReceipt, by decide, by decide, by decide⟩

end Canary

#print axioms historyDelta_append
#print axioms historyIntents_append
#print axioms routeDelta_append
#print axioms routeIntents_append
#print axioms merge_candidateDeltas_perm
#print axioms Canary.right_selection_is_not_commit_authority
#print axioms Canary.selected_commit_excludes_loser
#print axioms Canary.state_commit_does_not_authorize_intents
#print axioms Canary.effect_display_precedes_path_erasure
#print axioms Canary.compatible_merge_retains_both_routes

end Mettapedia.GSLT.LanguageDef.GSLTIL.ContextualDeltaRouteBridge
