import Mettapedia.GSLT.LanguageDef.CandidateSupersetVerificationAlgebra
import Mettapedia.GSLT.LanguageDef.MatchDecisionContract

/-!
# Monotone partial-observation decisions

`MatchDecisionContract` proves that a candidate occurrence may be removed only
after an observed conflict.  This module exposes the corresponding resumable
decision interface.  An ordered finite plan returns one of three results:

* `reject path`: the query and candidate visibly conflict at `path`;
* `admit`: no inspected coordinate conflicts and no demandable coordinate is
  unresolved, so the canonical matcher may proceed;
* `need path`: `path` is required by the candidate but is not yet available.

`admit` is deliberately local to the finite decision plan.  It is not a claim
that the candidate canonically matches.  Survivors still pass through the
canonical matcher.

The central refinement theorem says that revealing more of a query can resolve
a `need` or prune a previously viable occurrence, but cannot retract a
`reject`.  Stable rejection filtering therefore preserves exact source order
and occurrence multiplicity.
Moving ready occurrences ahead of suspended ones is proved only as a list
permutation, making that scheduling freedom available to occurrence-bag
observers but not to exact-stream observers.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.MonotoneDecisionRefinement

open Mettapedia.GSLT.LanguageDef.MatchDecisionContract
open Mettapedia.GSLT.LanguageDef.CandidateSupersetVerificationAlgebra

namespace Shaped

abbrev Path := MatchDecisionContract.Path
abbrev Obs := MatchDecisionContract.Shaped.Obs
abbrev Skeleton := MatchDecisionContract.Shaped.Skeleton
abbrev Term := MatchDecisionContract.Shaped.Term
abbrev Candidate := MatchDecisionContract.Shaped.Candidate

/-- Result of one finite partial-observation decision plan. -/
inductive Result where
  | reject (path : Path)
  | admit
  | need (path : Path)
deriving DecidableEq, Repr

namespace Result

/-- Boolean projection used by stable candidate filtering. -/
def isReject : Result → Bool
  | .reject _ => true
  | .admit | .need _ => false

/-- A locally admitted candidate is ready for canonical matching. -/
def isAdmit : Result → Bool
  | .admit => true
  | .reject _ | .need _ => false

/-- An unavailable demanded coordinate suspends rather than rejects. -/
def isNeed : Result → Bool
  | .need _ => true
  | .reject _ | .admit => false

/-- Information refinement on results.  A rejection remains a rejection,
although a newly discovered earlier conflict may change its witness path.
Local admission may later reject but cannot become suspended.  `need` may
refine to any later outcome. -/
def LE : Result → Result → Prop
  | .reject _, .reject _ => True
  | .admit, .admit => True
  | .admit, .reject _ => True
  | .need _, _ => True
  | _, _ => False

theorem LE.refl (result : Result) : LE result result := by
  cases result <;> simp [LE]

theorem LE.trans {first second third : Result}
    (firstSecond : LE first second)
    (secondThird : LE second third) : LE first third := by
  cases first <;> cases second <;> cases third <;> simp_all [LE]

theorem reject_persists {path : Path} {later : Result}
    (refines : LE (Result.reject path) later) :
    ∃ laterPath, later = .reject laterPath := by
  cases later <;> simp_all [LE]

theorem admit_ne_need {later : Result}
    (refines : LE Result.admit later) :
    ∀ path, later ≠ .need path := by
  cases later <;> simp_all [LE]

theorem isReject_mono {earlier later : Result}
    (refines : LE earlier later)
    (rejected : earlier.isReject = true) : later.isReject = true := by
  cases earlier <;> cases later <;> simp_all [LE, isReject]

end Result

variable {V : Type*} [DecidableEq V]

/-- Inspect one coordinate under an explicit demand capability.  Unknown
candidate coordinates impose no demand.  A known candidate coordinate paired
with an unknown query coordinate produces `need` only when the provider says
that observation can be demanded.  A bindable logic variable is represented by
the same semantic `unknown` but with `canDemand = false`, so it proceeds to the
canonical matcher instead of suspending. -/
def decidePoint (canDemand : Bool) (path : Path) : Obs V → Obs V → Result
  | .unknown, .unknown => .admit
  | .unknown, .absent => if canDemand then .need path else .admit
  | .unknown, .present _ => if canDemand then .need path else .admit
  | .absent, .unknown => .admit
  | .absent, .absent => .admit
  | .absent, .present _ => .reject path
  | .present _, .unknown => .admit
  | .present _, .absent => .reject path
  | .present actual, .present expected =>
      if actual = expected then .admit else .reject path

@[simp] theorem decidePoint_isReject (canDemand : Bool) (path : Path)
    (query pattern : Obs V) :
    (decidePoint canDemand path query pattern).isReject =
      MatchDecisionContract.Shaped.Obs.conflictB query pattern := by
  cases canDemand <;> cases query <;> cases pattern <;>
    simp_all [decidePoint, Result.isReject,
      MatchDecisionContract.Shaped.Obs.conflictB]
  all_goals
    rename_i actual expected
    by_cases equal : actual = expected <;> simp_all

theorem decidePoint_need_iff {canDemand : Bool} {path : Path}
    {query pattern : Obs V} :
    decidePoint canDemand path query pattern = .need path ↔
      canDemand = true ∧ query = .unknown ∧ pattern ≠ .unknown := by
  cases canDemand <;> cases query <;> cases pattern <;>
    simp_all [decidePoint] <;>
    (rename_i actual expected
     by_cases equal : actual = expected <;> simp_all)

theorem decidePoint_eq_need_iff {canDemand : Bool} {path needed : Path}
    {query pattern : Obs V} :
    decidePoint canDemand path query pattern = .need needed ↔
      needed = path ∧ canDemand = true ∧ query = .unknown ∧
        pattern ≠ .unknown := by
  constructor
  · intro result
    cases canDemand <;> cases query <;> cases pattern <;>
      simp_all [decidePoint] <;>
      (rename_i actual expected
       by_cases equal : actual = expected <;> simp_all)
  · rintro ⟨rfl, facts⟩
    exact decidePoint_need_iff.mpr facts

/-- A point result is monotone in the information order. -/
theorem decidePoint_mono {canDemand : Bool} {path : Path}
    {query query' pattern : Obs V}
    (more : MatchDecisionContract.Shaped.Obs.le query query') :
    Result.LE (decidePoint canDemand path query pattern)
      (decidePoint canDemand path query' pattern) := by
  cases canDemand <;> cases query <;> cases query' <;> cases pattern <;>
    simp_all [MatchDecisionContract.Shaped.Obs.le, decidePoint, Result.LE] <;>
    split <;> simp_all

/-- Run the ordered plan until it rejects, needs an unavailable coordinate, or
has checked every coordinate.  The untouched tail is the resumable plan cursor. -/
def decideOn (demandable : Path → Bool) :
    List Path → Skeleton V → Skeleton V → Result
  | [], _, _ => .admit
  | path :: paths, query, pattern =>
      match decidePoint (demandable path) path (query path) (pattern path) with
      | .admit => decideOn demandable paths query pattern
      | result => result

/-- Monotonicity of the complete finite decision: revealing information may
resolve a need or refute a local admission; rejection remains rejection, and
admission never becomes suspension. -/
theorem decideOn_mono (demandable : Path → Bool) {paths : List Path}
    {query query' pattern : Skeleton V}
    (more : MatchDecisionContract.Shaped.Skeleton.LE query query') :
    Result.LE (decideOn demandable paths query pattern)
      (decideOn demandable paths query' pattern) := by
  induction paths with
  | nil => simp [decideOn, Result.LE]
  | cons path paths inductionHypothesis =>
      have pointRefines := decidePoint_mono
        (canDemand := demandable path)
        (path := path) (pattern := pattern path) (more path)
      cases oldPoint : decidePoint (demandable path) path
          (query path) (pattern path) with
      | reject rejectedPath =>
          obtain ⟨laterPath, fixed⟩ := Result.reject_persists
            (by simpa [oldPoint] using pointRefines)
          simp [decideOn, oldPoint, fixed, Result.LE]
      | admit =>
          have noNeed := Result.admit_ne_need
            (by simpa [oldPoint] using pointRefines)
          cases newPoint : decidePoint (demandable path) path
              (query' path) (pattern path) with
          | reject laterPath =>
              cases tailResult : decideOn demandable paths query pattern <;>
                simp [decideOn, oldPoint, newPoint, tailResult, Result.LE]
          | admit =>
              simpa [decideOn, oldPoint, newPoint] using inductionHypothesis
          | need neededPath =>
              exact absurd newPoint (noNeed neededPath)
      | need neededPath =>
          simp [decideOn, oldPoint, Result.LE]

theorem decideOn_reject_persists {paths : List Path}
    (demandable : Path → Bool)
    {query query' pattern : Skeleton V}
    (more : MatchDecisionContract.Shaped.Skeleton.LE query query')
    (rejected : (decideOn demandable paths query pattern).isReject = true) :
    (decideOn demandable paths query' pattern).isReject = true :=
  Result.isReject_mono (decideOn_mono demandable more) rejected

/-- A decision-plan rejection is one of the existing finite sampled
conflicts.  The converse need not hold: an earlier unavailable coordinate may
suspend before a later conflict is inspected. -/
theorem decideOn_reject_implies_conflictsOn {demandable : Path → Bool}
    {paths : List Path}
    {query pattern : Skeleton V} {path : Path}
    (rejected : decideOn demandable paths query pattern = .reject path) :
    MatchDecisionContract.Shaped.conflictsOn paths query pattern = true := by
  induction paths with
  | nil => simp [decideOn] at rejected
  | cons head tail inductionHypothesis =>
      cases point : decidePoint (demandable head) head
          (query head) (pattern head) with
      | reject rejectedPath =>
          have conflict : MatchDecisionContract.Shaped.Obs.conflictB
              (query head) (pattern head) = true := by
            rw [← decidePoint_isReject (demandable head) head
              (query head) (pattern head), point]
            rfl
          simp [MatchDecisionContract.Shaped.conflictsOn,
            MatchDecisionContract.Shaped.posConflict, conflict]
      | admit =>
          have tailConflict := inductionHypothesis (by
            simpa [decideOn, point] using rejected)
          rw [MatchDecisionContract.Shaped.conflictsOn]
          simp only [List.any_cons, Bool.or_eq_true]
          right
          simpa [MatchDecisionContract.Shaped.conflictsOn,
            MatchDecisionContract.Shaped.posConflict] using tailConflict
      | need neededPath =>
          simp [decideOn, point] at rejected

theorem decideOn_reject_sound {demandable : Path → Bool} {paths : List Path}
    {query pattern : Skeleton V} {path : Path}
    (rejected : decideOn demandable paths query pattern = .reject path) :
    MatchDecisionContract.Shaped.Conflicts query pattern :=
  MatchDecisionContract.Shaped.conflictsOn_sound
    (decideOn_reject_implies_conflictsOn rejected)

/-- No false negative: a common realizing term makes rejection impossible. -/
theorem decideOn_not_reject_of_realizes {demandable : Path → Bool}
    {paths : List Path}
    {query pattern : Skeleton V} {path : Path} {term : Term V}
    (queryRealizes : MatchDecisionContract.Shaped.Realizes term query)
    (patternRealizes : MatchDecisionContract.Shaped.Realizes term pattern) :
    decideOn demandable paths query pattern ≠ .reject path := by
  intro rejected
  obtain ⟨conflictPath, conflict⟩ := decideOn_reject_sound rejected
  exact MatchDecisionContract.Shaped.Obs.conflictB_sound conflict
    (queryRealizes conflictPath) (patternRealizes conflictPath)

/-- A `need` identifies a requested path which is unknown in the query and
constrained by the candidate. -/
theorem decideOn_need_path {demandable : Path → Bool} {paths : List Path}
    {query pattern : Skeleton V} {needed : Path}
    (result : decideOn demandable paths query pattern = .need needed) :
    needed ∈ paths ∧ demandable needed = true ∧
      query needed = .unknown ∧ pattern needed ≠ .unknown := by
  induction paths with
  | nil => simp [decideOn] at result
  | cons path paths inductionHypothesis =>
      cases point : decidePoint (demandable path) path
          (query path) (pattern path) with
      | reject rejectedPath => simp [decideOn, point] at result
      | admit =>
          have tail := inductionHypothesis (by simpa [decideOn, point] using result)
          exact ⟨by simp [tail.1], tail.2⟩
      | need pointPath =>
          obtain ⟨pointPathEqual, demandablePath, queryUnknown, patternKnown⟩ :=
            decidePoint_eq_need_iff.mp point
          subst pointPath
          have neededEqual : path = needed := by
            simpa [decideOn, point] using result
          subst needed
          exact ⟨by simp, demandablePath, queryUnknown, patternKnown⟩

/-- If no coordinate in the authored plan denotes demandable computation,
the decision layer never suspends.  In particular, unresolved bindable logic
variables remain the canonical matcher's responsibility. -/
theorem decideOn_ne_need_of_nondemandable
    {demandable : Path → Bool} {paths : List Path}
    {query pattern : Skeleton V} {needed : Path}
    (noneDemandable : ∀ path ∈ paths, demandable path = false) :
    decideOn demandable paths query pattern ≠ .need needed := by
  intro result
  obtain ⟨member, demandableNeeded, _, _⟩ := decideOn_need_path result
  rw [noneDemandable needed member] at demandableNeeded
  contradiction

/-! ## Provider-independent interface -/

/-- A dialect or machine exposes only partial path observations to this
decision layer.  Its term carrier, ownership scheme, and search strategy remain
abstract. -/
structure Provider (Query : Type*) (V : Type*) where
  observe : Query → Path → Obs V
  demandable : Query → Path → Bool

namespace Provider

def skeleton {Query : Type*} (provider : Provider Query V)
    (query : Query) : Skeleton V := provider.observe query

def QueryLE {Query : Type*} (provider : Provider Query V)
    (query query' : Query) : Prop :=
  MatchDecisionContract.Shaped.Skeleton.LE
      (provider.skeleton query) (provider.skeleton query') ∧
    provider.demandable query = provider.demandable query'

def decide {Query : Type*} (provider : Provider Query V)
    (paths : List Path) (query : Query) (pattern : Skeleton V) : Result :=
  decideOn (provider.demandable query) paths (provider.skeleton query) pattern

theorem decide_mono {Query : Type*} (provider : Provider Query V)
    {paths : List Path} {query query' : Query} {pattern : Skeleton V}
    (more : provider.QueryLE query query') :
    Result.LE (provider.decide paths query pattern)
      (provider.decide paths query' pattern) :=
  by
    rw [Provider.decide, Provider.decide, more.2]
    exact decideOn_mono (provider.demandable query') more.1

end Provider

/-! ## Stable narrowing and observation-relative scheduling -/

/-- Retain every locally admitted or suspended occurrence; remove only proved
rejections. -/
def mayRetain (demandable : Path → Bool) (paths : List Path)
    (query : Skeleton V)
    (candidate : Candidate V) : Bool :=
  !(decideOn demandable paths query candidate.pat).isReject

def refinedCandidates (demandable : Path → Bool) (paths : List Path)
    (query : Skeleton V)
    (source : List (Candidate V)) : List (Candidate V) :=
  source.filter (mayRetain demandable paths query)

theorem refinedCandidates_sublist (demandable : Path → Bool)
    (paths : List Path) (query : Skeleton V)
    (source : List (Candidate V)) :
    (refinedCandidates demandable paths query source).Sublist source :=
  List.filter_sublist

theorem mem_refinedCandidates_of_realizes {demandable : Path → Bool}
    {paths : List Path}
    {query : Skeleton V} {source : List (Candidate V)} {candidate : Candidate V}
    {term : Term V} (member : candidate ∈ source)
    (queryRealizes : MatchDecisionContract.Shaped.Realizes term query)
    (patternRealizes : MatchDecisionContract.Shaped.Realizes term candidate.pat) :
    candidate ∈ refinedCandidates demandable paths query source := by
  refine List.mem_filter.mpr ⟨member, ?_⟩
  simp only [mayRetain]
  cases result : decideOn demandable paths query candidate.pat with
  | reject path =>
      exact (decideOn_not_reject_of_realizes
        queryRealizes patternRealizes result).elim
  | admit | need => rfl

theorem refinedCandidates_antitone (demandable : Path → Bool)
    {paths : List Path}
    {query query' : Skeleton V}
    (more : MatchDecisionContract.Shaped.Skeleton.LE query query')
    (source : List (Candidate V)) :
    (refinedCandidates demandable paths query' source).Sublist
      (refinedCandidates demandable paths query source) := by
  apply List.monotone_filter_right
  intro candidate retainedLater
  unfold mayRetain at retainedLater ⊢
  cases rejectedEarlier :
      (decideOn demandable paths query candidate.pat).isReject with
  | false => rfl
  | true =>
      have rejectedLater := decideOn_reject_persists demandable more
        rejectedEarlier
      simp [rejectedLater] at retainedLater

/-- Any canonical matcher whose successes have common realizing terms is
retained by the monotone decision. -/
theorem retainsCanonical
    (demandable : Path → Bool) (paths : List Path) (query : Skeleton V)
    (canonical : Candidate V → Bool)
    (successRealizes : ∀ candidate, canonical candidate = true →
      ∃ term, MatchDecisionContract.Shaped.Realizes term query ∧
        MatchDecisionContract.Shaped.Realizes term candidate.pat) :
    RetainsCanonical canonical (mayRetain demandable paths query) := by
  intro candidate success
  obtain ⟨term, queryRealizes, patternRealizes⟩ := successRealizes candidate success
  simp only [mayRetain]
  cases result : decideOn demandable paths query candidate.pat with
  | reject path =>
      exact (decideOn_not_reject_of_realizes
        queryRealizes patternRealizes result).elim
  | admit | need => rfl

/-- Exact-stream law: stable narrowing followed by the canonical matcher is
exactly the authored canonical stream. -/
theorem canonicalRun_refined_exact
    (demandable : Path → Bool) (paths : List Path) (query : Skeleton V)
    (canonical : Candidate V → Bool)
    (successRealizes : ∀ candidate, canonical candidate = true →
      ∃ term, MatchDecisionContract.Shaped.Realizes term query ∧
        MatchDecisionContract.Shaped.Realizes term candidate.pat)
    (source : List (Candidate V)) :
    canonicalRun canonical (refinedCandidates demandable paths query source) =
      canonicalRun canonical source := by
  exact canonicalRun_indexed_exact canonical
    (mayRetain demandable paths query)
    (retainsCanonical demandable paths query canonical successRealizes) source

/-- Candidates whose finite plans are already admitted. -/
def readyCandidates (demandable : Path → Bool) (paths : List Path)
    (query : Skeleton V)
    (source : List (Candidate V)) : List (Candidate V) :=
  source.filter fun candidate =>
    (decideOn demandable paths query candidate.pat).isAdmit

/-- Candidates waiting for one demanded coordinate. -/
def suspendedCandidates (demandable : Path → Bool) (paths : List Path)
    (query : Skeleton V)
    (source : List (Candidate V)) : List (Candidate V) :=
  source.filter fun candidate =>
    (decideOn demandable paths query candidate.pat).isNeed

/-- Occurrence-bag law: executing ready candidates before suspended candidates
is a permutation of all retained occurrences.  This theorem does not claim
exact-stream equality. -/
theorem ready_append_suspended_perm_refined
    (demandable : Path → Bool) (paths : List Path) (query : Skeleton V)
    (source : List (Candidate V)) :
    (readyCandidates demandable paths query source ++
      suspendedCandidates demandable paths query source).Perm
        (refinedCandidates demandable paths query source) := by
  induction source with
  | nil => simp [readyCandidates, suspendedCandidates, refinedCandidates]
  | cons candidate source inductionHypothesis =>
      cases result : decideOn demandable paths query candidate.pat with
      | reject path =>
          simpa [readyCandidates, suspendedCandidates, refinedCandidates,
            mayRetain, result, Result.isReject, Result.isAdmit, Result.isNeed]
            using inductionHypothesis
      | admit =>
          simpa [readyCandidates, suspendedCandidates, refinedCandidates,
            mayRetain, result, Result.isReject, Result.isAdmit, Result.isNeed]
            using inductionHypothesis.cons candidate
      | need path =>
          have move :
              (candidate ::
                (readyCandidates demandable paths query source ++
                  suspendedCandidates demandable paths query source)).Perm
                (readyCandidates demandable paths query source ++
                  candidate ::
                    suspendedCandidates demandable paths query source) :=
            List.perm_cons_append_cons candidate (List.Perm.refl _)
          have resultPerm := move.symm.trans (inductionHypothesis.cons candidate)
          simpa [readyCandidates, suspendedCandidates, refinedCandidates,
            mayRetain, result, Result.isReject, Result.isAdmit, Result.isNeed]
            using resultPerm

/-! ## Explicit work model -/

/-- Run the same decision while counting inspected plan coordinates. -/
def decideWithCost (demandable : Path → Bool) :
    List Path → Skeleton V → Skeleton V → Result × Nat
  | [], _, _ => (.admit, 0)
  | path :: paths, query, pattern =>
      match decidePoint (demandable path) path (query path) (pattern path) with
      | .admit =>
          let tail := decideWithCost demandable paths query pattern
          (tail.1, tail.2 + 1)
      | result => (result, 1)

theorem decideWithCost_result (demandable : Path → Bool) (paths : List Path)
    (query pattern : Skeleton V) :
    (decideWithCost demandable paths query pattern).1 =
      decideOn demandable paths query pattern := by
  induction paths with
  | nil => rfl
  | cons path paths inductionHypothesis =>
      cases point : decidePoint (demandable path) path
          (query path) (pattern path) <;>
        simp [decideWithCost, decideOn, point, inductionHypothesis]

/-- The resumable decision never inspects more coordinates than the authored
plan contains.  This is a structural bound, not a machine-time claim. -/
theorem decideWithCost_le_length (demandable : Path → Bool)
    (paths : List Path)
    (query pattern : Skeleton V) :
    (decideWithCost demandable paths query pattern).2 ≤ paths.length := by
  induction paths with
  | nil => simp [decideWithCost]
  | cons path paths inductionHypothesis =>
      cases point : decidePoint (demandable path) path
          (query path) (pattern path) with
      | reject rejectedPath => simp [decideWithCost, point]
      | need neededPath => simp [decideWithCost, point]
      | admit =>
          simpa [decideWithCost, point, Nat.add_comm] using
            Nat.succ_le_succ inductionHypothesis

/-! ## Positive and negative canaries -/

private inductive Tag where
  | a
  | b
deriving DecidableEq, Repr

private def unknownQuery : Skeleton Tag := fun _ => .unknown

private def queryA : Skeleton Tag := fun path =>
  if path = [0] then .present .a else .unknown

private def queryB : Skeleton Tag := fun path =>
  if path = [0] then .present .b else .unknown

private def requiresA : Skeleton Tag := fun path =>
  if path = [0] then .present .a else .unknown

private def unconstrained : Skeleton Tag := fun _ => .unknown

private def demandEverywhere : Path → Bool := fun _ => true

private def demandNowhere : Path → Bool := fun _ => false

/-- Positive: an unavailable required coordinate is exposed as a need. -/
example : decideOn demandEverywhere [[0]] unknownQuery requiresA =
    .need [0] := by rfl

/-- A bindable variable has the same partial semantic observation but no
demand capability, so it remains available to the canonical matcher. -/
example : decideOn demandNowhere [[0]] unknownQuery requiresA = .admit := by
  rfl

/-- Positive: compatible information resolves that need to local admission. -/
example : decideOn demandEverywhere [[0]] queryA requiresA = .admit := by rfl

/-- Negative: incompatible information resolves it to rejection. -/
example : decideOn demandEverywhere [[0]] queryB requiresA = .reject [0] := by
  rfl

/-- Negative extra-behavior canary: treating `need` as rejection would remove
a candidate with a common realizing term. -/
example : ∃ term : Term Tag,
    MatchDecisionContract.Shaped.Realizes term unknownQuery ∧
      MatchDecisionContract.Shaped.Realizes term requiresA := by
  refine ⟨fun path => if path = [0] then some .a else none, ?_, ?_⟩
  · intro path
    simp [unknownQuery, MatchDecisionContract.Shaped.Obs.Holds]
  · intro path
    by_cases equal : path = [0]
    · subst path
      simp [requiresA, MatchDecisionContract.Shaped.Obs.Holds]
    · simp [requiresA, equal, MatchDecisionContract.Shaped.Obs.Holds]

private def needCandidate : Candidate Tag := ⟨0, requiresA⟩
private def readyCandidate : Candidate Tag := ⟨1, unconstrained⟩

/-- Exact-stream negative canary: ready-first scheduling changes authored
order, even though the occurrence bag is unchanged. -/
example :
    (readyCandidates demandEverywhere [[0]] unknownQuery
        [needCandidate, readyCandidate] ++
      suspendedCandidates demandEverywhere [[0]] unknownQuery
        [needCandidate, readyCandidate]).map (fun candidate => candidate.id) =
      [1, 0] := by
  rfl

example :
    (refinedCandidates demandEverywhere [[0]] unknownQuery
      [needCandidate, readyCandidate]).map (fun candidate => candidate.id) =
      [0, 1] := by
  rfl

/-- Positive cost canary: a first-coordinate need inspects one of four paths. -/
example :
    (decideWithCost demandEverywhere [[0], [1], [2], [3]]
      unknownQuery requiresA).2 = 1 := by
  rfl

/-- Negative cost canary: a fully compatible plan may inspect every path; no
unconditional speedup is claimed. -/
example :
    (decideWithCost demandEverywhere [[0], [1], [2], [3]]
      queryA unconstrained).2 = 4 := by
  rfl

#print axioms Result.LE.trans
#print axioms decidePoint_mono
#print axioms decideOn_mono
#print axioms decideOn_reject_sound
#print axioms decideOn_not_reject_of_realizes
#print axioms decideOn_need_path
#print axioms decideOn_ne_need_of_nondemandable
#print axioms Provider.decide_mono
#print axioms refinedCandidates_antitone
#print axioms canonicalRun_refined_exact
#print axioms ready_append_suspended_perm_refined
#print axioms decideWithCost_result
#print axioms decideWithCost_le_length

end Shaped

end Mettapedia.GSLT.LanguageDef.MonotoneDecisionRefinement
