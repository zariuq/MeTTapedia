import Mettapedia.Languages.MeTTa.PrimeDemandBoundary
import Mettapedia.Languages.MeTTa.PrimeNeedWorlds
import Mathlib.Data.Finset.Card

/-!
# Prime equation-call sharing tournament

This module isolates a design question that the demand boundary intentionally
leaves open: which equation candidates share a delayed source argument, and
which causal world receives each answer?

The module is non-normative.  It compares four sharing policies and keeps
candidate forking, answer publication, and effect publication as independent
axes.  In particular, sharing one dynamic source-argument cell does not imply
that every candidate must evolve in one universal call frontier.

The first policy lattice concerns identity only:

* `perUse`: each use site receives a fresh implicit cell;
* `perCandidate`: uses within one equation candidate share;
* `perSource`: candidates share one dynamic call-argument occurrence;
* `perOrigin`: all dynamically distinct occurrences with equal origins share.

Explicit suspension cells retain their own identity in the first three
policies.  The strict inclusions are proved with concrete witnesses.  A small
abstract scheduler then exposes a separate issue: carrying every candidate
through irrelevant forced branches makes answer multiplicity depend on which
argument is forced first.  The executable runtime tournament must decide the
operational policy; these definitions only make the alternatives and their
discriminators precise.
-/

namespace Mettapedia.Languages.MeTTa.PrimeCallSharingTournament

/-! ## Dynamic source identity and sharing policies -/

/-- Implicit arguments are identified by dynamic call and argument position.
Explicit suspensions already carry a cell identity of their own. -/
inductive SourceIdentity (Call Argument Cell : Type*) where
  | implicit (call : Call) (argument : Argument)
  | explicit (cell : Cell)
deriving DecidableEq, Repr

/-- A demand site distinguishes the admitted equation occurrence from a
particular use within that candidate. -/
structure DemandSite
    (Call Argument Cell Candidate Use : Type*) where
  source : SourceIdentity Call Argument Cell
  candidate : Candidate
  use : Use
deriving DecidableEq, Repr

inductive SharingPolicy where
  | perUse
  | perCandidate
  | perSource
  | perOrigin
deriving DecidableEq, Repr

/-- One key type makes every sharing policy an equality relation. -/
inductive SharingKey
    (Call Argument Cell Candidate Use Origin : Type*) where
  | explicit (cell : Cell)
  | use (call : Call) (argument : Argument)
      (candidate : Candidate) (use : Use)
  | candidate (call : Call) (argument : Argument)
      (candidate : Candidate)
  | source (call : Call) (argument : Argument)
  | origin (origin : Origin)
deriving DecidableEq, Repr

def sourceOrigin
    (implicitOrigin : Call → Argument → Origin)
    (cellOrigin : Cell → Origin) :
    SourceIdentity Call Argument Cell → Origin
  | .implicit call argument => implicitOrigin call argument
  | .explicit cell => cellOrigin cell

def sharingKey
    (implicitOrigin : Call → Argument → Origin)
    (cellOrigin : Cell → Origin)
    (policy : SharingPolicy)
    (site : DemandSite Call Argument Cell Candidate Use) :
    SharingKey Call Argument Cell Candidate Use Origin :=
  match policy, site.source with
  | .perUse, .implicit call argument =>
      .use call argument site.candidate site.use
  | .perCandidate, .implicit call argument =>
      .candidate call argument site.candidate
  | .perSource, .implicit call argument => .source call argument
  | .perOrigin, source => .origin (sourceOrigin implicitOrigin cellOrigin source)
  | _, .explicit cell => .explicit cell

/-- Two demand sites share exactly when the selected policy assigns the same
cell key. -/
def Shares
    (implicitOrigin : Call → Argument → Origin)
    (cellOrigin : Cell → Origin)
    (policy : SharingPolicy)
    (left right : DemandSite Call Argument Cell Candidate Use) : Prop :=
  sharingKey implicitOrigin cellOrigin policy left =
    sharingKey implicitOrigin cellOrigin policy right

theorem shares_refl
    (implicitOrigin : Call → Argument → Origin)
    (cellOrigin : Cell → Origin) (policy : SharingPolicy)
    (site : DemandSite Call Argument Cell Candidate Use) :
    Shares implicitOrigin cellOrigin policy site site :=
  rfl

theorem shares_symm
    (implicitOrigin : Call → Argument → Origin)
    (cellOrigin : Cell → Origin) (policy : SharingPolicy)
    {left right : DemandSite Call Argument Cell Candidate Use}
    (h : Shares implicitOrigin cellOrigin policy left right) :
    Shares implicitOrigin cellOrigin policy right left :=
  h.symm

theorem shares_trans
    (implicitOrigin : Call → Argument → Origin)
    (cellOrigin : Cell → Origin) (policy : SharingPolicy)
    {first second third : DemandSite Call Argument Cell Candidate Use}
    (h₁ : Shares implicitOrigin cellOrigin policy first second)
    (h₂ : Shares implicitOrigin cellOrigin policy second third) :
    Shares implicitOrigin cellOrigin policy first third :=
  h₁.trans h₂

/-- Reusing one explicit suspension cell preserves its identity independently
of candidate and use-site labels. -/
theorem explicit_same_cell_always_shares
    (implicitOrigin : Call → Argument → Origin)
    (cellOrigin : Cell → Origin) (policy : SharingPolicy)
    (cell : Cell) (leftCandidate rightCandidate : Candidate)
    (leftUse rightUse : Use) :
    Shares implicitOrigin cellOrigin policy
      { source := .explicit cell
        candidate := leftCandidate
        use := leftUse }
      { source := .explicit cell
        candidate := rightCandidate
        use := rightUse } := by
  cases policy <;> rfl

/-- `perSource` is exactly dynamic source identity; it neither splits one
source occurrence nor merges distinct occurrences. -/
theorem perSource_iff_same_source
    (implicitOrigin : Call → Argument → Origin)
    (cellOrigin : Cell → Origin)
    (left right : DemandSite Call Argument Cell Candidate Use) :
    Shares implicitOrigin cellOrigin .perSource left right ↔
      left.source = right.source := by
  rcases left with ⟨leftSource, leftCandidate, leftUse⟩
  rcases right with ⟨rightSource, rightCandidate, rightUse⟩
  cases leftSource <;> cases rightSource <;>
    simp [Shares, sharingKey]

def eraseUse :
    SharingKey Call Argument Cell Candidate Use Origin →
      SharingKey Call Argument Cell Candidate Use Origin
  | .use call argument candidate _ => .candidate call argument candidate
  | key => key

def eraseCandidate :
    SharingKey Call Argument Cell Candidate Use Origin →
      SharingKey Call Argument Cell Candidate Use Origin
  | .candidate call argument _ => .source call argument
  | key => key

def eraseSource
    (implicitOrigin : Call → Argument → Origin)
    (cellOrigin : Cell → Origin) :
    SharingKey Call Argument Cell Candidate Use Origin →
      SharingKey Call Argument Cell Candidate Use Origin
  | .source call argument => .origin (implicitOrigin call argument)
  | .explicit cell => .origin (cellOrigin cell)
  | key => key

@[simp] theorem eraseUse_sharingKey
    (implicitOrigin : Call → Argument → Origin)
    (cellOrigin : Cell → Origin)
    (site : DemandSite Call Argument Cell Candidate Use) :
    eraseUse (sharingKey implicitOrigin cellOrigin .perUse site) =
      sharingKey implicitOrigin cellOrigin .perCandidate site := by
  rcases site with ⟨source, candidate, use⟩
  cases source <;> rfl

@[simp] theorem eraseCandidate_sharingKey
    (implicitOrigin : Call → Argument → Origin)
    (cellOrigin : Cell → Origin)
    (site : DemandSite Call Argument Cell Candidate Use) :
    eraseCandidate
        (sharingKey implicitOrigin cellOrigin .perCandidate site) =
      sharingKey implicitOrigin cellOrigin .perSource site := by
  rcases site with ⟨source, candidate, use⟩
  cases source <;> rfl

@[simp] theorem eraseSource_sharingKey
    (implicitOrigin : Call → Argument → Origin)
    (cellOrigin : Cell → Origin)
    (site : DemandSite Call Argument Cell Candidate Use) :
    eraseSource implicitOrigin cellOrigin
        (sharingKey implicitOrigin cellOrigin .perSource site) =
      sharingKey implicitOrigin cellOrigin .perOrigin site := by
  rcases site with ⟨source, candidate, use⟩
  cases source <;> rfl

theorem perUse_in_perCandidate
    {Call Argument Origin Cell Candidate Use : Type*}
    (implicitOrigin : Call → Argument → Origin)
    (cellOrigin : Cell → Origin) :
    PrimeDemandBoundary.RelationIncluded
      (Shares (Candidate := Candidate) (Use := Use)
        implicitOrigin cellOrigin .perUse)
      (Shares (Candidate := Candidate) (Use := Use)
        implicitOrigin cellOrigin .perCandidate) := by
  intro left right h
  have := congrArg eraseUse h
  simpa [Shares] using this

theorem perCandidate_in_perSource
    {Call Argument Origin Cell Candidate Use : Type*}
    (implicitOrigin : Call → Argument → Origin)
    (cellOrigin : Cell → Origin) :
    PrimeDemandBoundary.RelationIncluded
      (Shares (Candidate := Candidate) (Use := Use)
        implicitOrigin cellOrigin .perCandidate)
      (Shares (Candidate := Candidate) (Use := Use)
        implicitOrigin cellOrigin .perSource) := by
  intro left right h
  have := congrArg eraseCandidate h
  simpa [Shares] using this

theorem perSource_in_perOrigin
    {Call Argument Origin Cell Candidate Use : Type*}
    (implicitOrigin : Call → Argument → Origin)
    (cellOrigin : Cell → Origin) :
    PrimeDemandBoundary.RelationIncluded
      (Shares (Candidate := Candidate) (Use := Use)
        implicitOrigin cellOrigin .perSource)
      (Shares (Candidate := Candidate) (Use := Use)
        implicitOrigin cellOrigin .perOrigin) := by
  intro left right h
  have := congrArg (eraseSource implicitOrigin cellOrigin) h
  simpa [Shares] using this

/-! ## Concrete strictness witnesses -/

abbrev DemoSite := DemandSite Nat Nat Nat Nat Nat

def demoImplicitOrigin (_call _argument : Nat) : Nat := 0
def demoCellOrigin (cell : Nat) : Nat := cell

def DemoShares (policy : SharingPolicy) : DemoSite → DemoSite → Prop :=
  Shares (Candidate := Nat) (Use := Nat)
    demoImplicitOrigin demoCellOrigin policy

def demoUseZero : DemoSite :=
  { source := .implicit 0 0, candidate := 0, use := 0 }

def demoUseOne : DemoSite :=
  { source := .implicit 0 0, candidate := 0, use := 1 }

def demoCandidateOne : DemoSite :=
  { source := .implicit 0 0, candidate := 1, use := 0 }

def demoOtherCall : DemoSite :=
  { source := .implicit 1 0, candidate := 0, use := 0 }

theorem demo_perUse_strictly_finer_perCandidate :
    PrimeDemandBoundary.StrictlyFiner
      (DemoShares .perUse) (DemoShares .perCandidate) := by
  constructor
  · exact perUse_in_perCandidate _ _
  · refine ⟨demoUseZero, demoUseOne, ?_, ?_⟩ <;>
      simp [DemoShares, Shares, sharingKey, demoUseZero, demoUseOne]

theorem demo_perCandidate_strictly_finer_perSource :
    PrimeDemandBoundary.StrictlyFiner
      (DemoShares .perCandidate) (DemoShares .perSource) := by
  constructor
  · exact perCandidate_in_perSource _ _
  · refine ⟨demoUseZero, demoCandidateOne, ?_, ?_⟩ <;>
      simp [DemoShares, Shares, sharingKey, demoUseZero, demoCandidateOne]

theorem demo_perSource_strictly_finer_perOrigin :
    PrimeDemandBoundary.StrictlyFiner
      (DemoShares .perSource) (DemoShares .perOrigin) := by
  constructor
  · exact perSource_in_perOrigin _ _
  · refine ⟨demoUseZero, demoOtherCall, ?_, ?_⟩ <;>
      simp [DemoShares, Shares, sharingKey, sourceOrigin,
        demoImplicitOrigin, demoUseZero, demoOtherCall]

/-- This restricted three-law screen is a discriminator, not a language-law
ratification.  It asks for repeated-use sharing, cross-candidate sharing of one
source occurrence, and isolation of dynamically distinct calls with equal
origins. -/
def DemoIdentityScreen (policy : SharingPolicy) : Prop :=
  DemoShares policy demoUseZero demoUseOne ∧
  DemoShares policy demoUseZero demoCandidateOne ∧
  ¬ DemoShares policy demoUseZero demoOtherCall

theorem demo_identity_screen_iff_perSource (policy : SharingPolicy) :
    DemoIdentityScreen policy ↔ policy = .perSource := by
  cases policy <;>
    simp [DemoIdentityScreen, DemoShares, Shares, sharingKey, sourceOrigin,
      demoImplicitOrigin, demoUseZero, demoUseOne, demoCandidateOne,
      demoOtherCall]

/-! ## Independent operational axes -/

/-- Cell sharing does not decide how candidate worlds fork. -/
inductive CandidateFrontier where
  | monolithic
  | candidateLocal
  | demandCohort
  | supportDirected
deriving DecidableEq, Repr

/-- Answer placement is independent of the cell-sharing key. -/
inductive AnswerPublication where
  | leastDependencyWorld
  | candidateWorld
  | callRoot
deriving DecidableEq, Repr

/-- Effects may be retained as evidence without all being committed to an
ambient store. -/
inductive EffectPublication where
  | receiptsOnly
  | compatibleJoin
  | selectedBranch
  | externalImmediate
deriving DecidableEq, Repr

structure ExperimentDesign where
  sharing : SharingPolicy
  frontier : CandidateFrontier
  answers : AnswerPublication
  effects : EffectPublication
deriving DecidableEq, Repr

/-! ## A derived declaration-order countermodel -/

/-- One admitted equation occurrence and the argument positions it must
observe before it can answer.  Two structurally equal records remain two list
occurrences. -/
structure CandidateSpec (Argument Answer : Type*) where
  support : Finset Argument
  answer : Answer
deriving DecidableEq

/-- Prefix of a force order traversed before every required argument has been
observed. -/
def readinessPrefix [DecidableEq Argument] :
    List Argument → Finset Argument → List Argument
  | [], _ => []
  | argument :: rest, support =>
      if support = ∅ then []
      else argument :: readinessPrefix rest (support.erase argument)

def irrelevantBeforeReady [DecidableEq Argument]
    (order : List Argument) (support : Finset Argument) : List Argument :=
  (readinessPrefix order support).filter fun argument => argument ∉ support

/-- A monolithic frontier inherits every earlier irrelevant branch. -/
def inheritedMultiplicity [DecidableEq Argument]
    (branchCount : Argument → Nat)
    (order : List Argument) (support : Finset Argument) : Nat :=
  (irrelevantBeforeReady order support).foldl
    (fun total argument => total * branchCount argument) 1

def monolithicAnswers [DecidableEq Argument]
    (branchCount : Argument → Nat) (order : List Argument)
    (candidates : List (CandidateSpec Argument Answer)) : List Answer :=
  candidates.flatMap fun candidate =>
    List.replicate
      (inheritedMultiplicity branchCount order candidate.support)
      candidate.answer

/-- A support-directed account emits each admitted candidate occurrence once;
irrelevant branch choices do not multiply it. -/
def supportDirectedAnswers
    (candidates : List (CandidateSpec Argument Answer)) : List Answer :=
  candidates.map CandidateSpec.answer

/-! ## Occurrence-labelled support-directed answer bags -/

/-- Candidate occurrence is separate from its structural support. -/
structure AdmittedCandidate (Candidate Argument : Type*) where
  occurrence : Candidate
  support : Finset Argument
deriving DecidableEq

/-- Candidate-local evaluation may produce several relevant observations,
effects, or answers.  It cannot mention an unrelated candidate frontier. -/
structure LocalCandidateOutcome (Observation Effect Answer : Type*) where
  observations : List Observation
  effects : List Effect
  answer : Answer
deriving DecidableEq

/-- A published support-directed answer carries its admitted occurrence and
exact authored support independently from its result payload. -/
structure SupportDirectedAnswer
    (Candidate Argument Observation Effect Answer : Type*) where
  candidate : Candidate
  dependencies : Finset Argument
  observations : List Observation
  effects : List Effect
  answer : Answer
deriving DecidableEq

def attachCandidate
    (candidate : AdmittedCandidate Candidate Argument)
    (outcome : LocalCandidateOutcome Observation Effect Answer) :
    SupportDirectedAnswer Candidate Argument Observation Effect Answer :=
  { candidate := candidate.occurrence
    dependencies := candidate.support
    observations := outcome.observations
    effects := outcome.effects
    answer := outcome.answer }

/-- Each candidate is evaluated in its own support projection.  Shared source
cells may supply the local evaluator, but unrelated candidate branches are not
an input to it. -/
def supportDirectedRun
    (evaluate : AdmittedCandidate Candidate Argument →
      List (LocalCandidateOutcome Observation Effect Answer))
    (candidates : List (AdmittedCandidate Candidate Argument)) :
    List (SupportDirectedAnswer Candidate Argument Observation Effect Answer) :=
  candidates.flatMap fun candidate =>
    (evaluate candidate).map (attachCandidate candidate)

def supportDirectedAnswerBag
    (answers :
      List (SupportDirectedAnswer Candidate Argument Observation Effect Answer)) :
    Multiset
      (SupportDirectedAnswer Candidate Argument Observation Effect Answer) :=
  answers

@[simp] theorem attachCandidate_exact_support
    (candidate : AdmittedCandidate Candidate Argument)
    (outcome : LocalCandidateOutcome Observation Effect Answer) :
    (attachCandidate candidate outcome).dependencies = candidate.support :=
  rfl

/-- Reordering admitted candidates changes only list presentation: the full
occurrence-labelled multiset, including dependencies and effects, is invariant.
-/
theorem supportDirectedRun_order_invariant
    (evaluate : AdmittedCandidate Candidate Argument →
      List (LocalCandidateOutcome Observation Effect Answer))
    {left right : List (AdmittedCandidate Candidate Argument)}
    (permutation : left.Perm right) :
    supportDirectedAnswerBag (supportDirectedRun evaluate left) =
      supportDirectedAnswerBag (supportDirectedRun evaluate right) := by
  apply Multiset.coe_eq_coe.mpr
  exact permutation.flatMap fun _ _ => List.Perm.refl _

inductive CrossArgument where
  | first
  | second
deriving DecidableEq, Repr

inductive CrossAnswer where
  | left
  | right
  | both
deriving DecidableEq, Repr

def crossBranchCount (_ : CrossArgument) : Nat := 2

def leftCandidate : CandidateSpec CrossArgument CrossAnswer :=
  { support := {.first}, answer := .left }

def rightCandidate : CandidateSpec CrossArgument CrossAnswer :=
  { support := {.second}, answer := .right }

def crossCandidates : List (CandidateSpec CrossArgument CrossAnswer) :=
  [leftCandidate, rightCandidate]

theorem first_argument_first_multiplicity :
    monolithicAnswers crossBranchCount [.first, .second] crossCandidates =
      [.left, .right, .right] := by
  decide

theorem second_argument_first_multiplicity :
    monolithicAnswers crossBranchCount [.second, .first] crossCandidates =
      [.left, .left, .right] := by
  decide

/-- The abstract monolithic scheduler is not invariant under force-order
reversal, even though candidate occurrences and their supports are unchanged. -/
theorem monolithic_force_order_changes_answer_bag :
    monolithicAnswers crossBranchCount [.first, .second] crossCandidates ≠
      monolithicAnswers crossBranchCount [.second, .first] crossCandidates := by
  decide

theorem support_directed_avoids_irrelevant_multiplicity :
    supportDirectedAnswers crossCandidates = [.left, .right] := by
  decide

/-- Occurrence lists preserve duplicate admitted equations rather than
quotienting them by structural equality. -/
theorem support_directed_preserves_duplicate_occurrences :
    supportDirectedAnswers [leftCandidate, leftCandidate] = [.left, .left] := by
  decide

/-! ## Candidate-local small steps and support publication -/

/-- A candidate frontier distinguishes demands still needed from observations
already made.  The two sets are kept separate because observing an argument is
an operational event, not merely a Boolean readiness test. -/
@[ext] structure CandidateConfiguration (Argument : Type*) where
  pending : Finset Argument
  observed : Finset Argument
deriving DecidableEq

def initialCandidateConfiguration
    (candidate : CandidateSpec Argument Answer) :
    CandidateConfiguration Argument :=
  { pending := candidate.support, observed := ∅ }

/-- One small step transfers one pending demand into the observed support. -/
inductive CandidateStep [DecidableEq Argument] :
    CandidateConfiguration Argument → Argument →
      CandidateConfiguration Argument → Prop where
  | observe (configuration : CandidateConfiguration Argument)
      (argument : Argument) (demanded : argument ∈ configuration.pending) :
      CandidateStep configuration argument
        { pending := configuration.pending.erase argument
          observed := insert argument configuration.observed }

/-- A finite order is a derived batch view of the small-step machine.  It
records exactly the arguments in the order that were still pending. -/
def runCandidate [DecidableEq Argument]
    (configuration : CandidateConfiguration Argument)
    (order : List Argument) : CandidateConfiguration Argument :=
  { pending := configuration.pending \ order.toFinset
    observed := configuration.observed ∪
      (configuration.pending ∩ order.toFinset) }

theorem candidateStep_run_singleton [DecidableEq Argument]
    (configuration : CandidateConfiguration Argument) (argument : Argument)
    (demanded : argument ∈ configuration.pending) :
    CandidateStep configuration argument
      (runCandidate configuration [argument]) := by
  simpa [runCandidate, demanded, Finset.sdiff_singleton_eq_erase] using
    CandidateStep.observe configuration argument demanded

theorem no_candidateStep_without_demand [DecidableEq Argument]
    (configuration : CandidateConfiguration Argument) (argument : Argument)
    (notDemanded : argument ∉ configuration.pending) :
    ¬ ∃ after, CandidateStep configuration argument after := by
  rintro ⟨after, step⟩
  cases step with
  | observe demanded => exact notDemanded demanded

theorem candidateStep_preserves_footprint [DecidableEq Argument]
    {before after : CandidateConfiguration Argument} {argument : Argument}
    (step : CandidateStep before argument after) :
    after.pending ∪ after.observed = before.pending ∪ before.observed := by
  cases step with
  | observe demanded =>
      ext item
      by_cases hItem : item = argument
      · subst item
        simp [demanded]
      · simp [hItem]

theorem candidateStep_removes_observed_demand [DecidableEq Argument]
    {before after : CandidateConfiguration Argument} {argument : Argument}
    (step : CandidateStep before argument after) :
    argument ∉ after.pending ∧ argument ∈ after.observed := by
  cases step
  simp

theorem runCandidate_order_invariant [DecidableEq Argument]
    (configuration : CandidateConfiguration Argument)
    {leftOrder rightOrder : List Argument}
    (sameArguments : leftOrder.toFinset = rightOrder.toFinset) :
    runCandidate configuration leftOrder =
      runCandidate configuration rightOrder := by
  simp [runCandidate, sameArguments]

theorem runCandidate_complete [DecidableEq Argument]
    (candidate : CandidateSpec Argument Answer) (order : List Argument)
    (complete : candidate.support ⊆ order.toFinset) :
    runCandidate (initialCandidateConfiguration candidate) order =
      { pending := ∅, observed := candidate.support } := by
  change CandidateConfiguration.mk
      (candidate.support \ order.toFinset)
      (∅ ∪ (candidate.support ∩ order.toFinset)) = _
  rw [Finset.sdiff_eq_empty_iff_subset.mpr complete,
      Finset.empty_union, Finset.inter_eq_left.mpr complete]

/-- The roots published for one candidate are its observations, not the
frontier traversed by unrelated candidates. -/
def candidateReceipt
    (configuration : CandidateConfiguration Argument) :
    PrimeNeedWorlds.DependencyReceipt Argument :=
  { roots := configuration.observed }

theorem candidateReceipt_roots
    (configuration : CandidateConfiguration Argument) :
    (candidateReceipt configuration).roots = configuration.observed :=
  rfl

/-- Causal publication of a ready candidate is the least valid world that
contains its exact observed support. -/
theorem candidate_publication_least
    [DecidableEq Argument]
    {basis : PrimeNeedWorlds.FiniteCausalBasis Argument}
    {conflict : Argument → Argument → Prop}
    (configuration : CandidateConfiguration Argument)
    (valid : PrimeNeedWorlds.ConflictFree conflict
      (basis.close (candidateReceipt configuration).roots))
    (world : PrimeNeedWorlds.Configuration basis conflict)
    (containsObservations : configuration.observed ⊆ world.events) :
    (candidateReceipt configuration).publish valid ≤ world := by
  exact PrimeNeedWorlds.DependencyReceipt.publish_least
    (candidateReceipt configuration) valid world containsObservations

/-! ## Exact demand cohorts: positive cases and the overlap counterexample -/

/-- The experimental native contender shares a producer within candidates
whose matcher-demand sets are exactly equal. -/
def demandCohortSupports [DecidableEq Argument]
    (candidates : List (CandidateSpec Argument Answer)) :
    List (Finset Argument) :=
  (candidates.map CandidateSpec.support).dedup

/-- Exact-support cohorts force every demanded argument once per distinct
cohort.  This is deliberately not claimed to be globally support-directed. -/
def demandCohortProducerFirings [DecidableEq Argument]
  (candidates : List (CandidateSpec Argument Answer)) : Nat :=
  (demandCohortSupports candidates).foldl
    (fun total (support : Finset Argument) => total + support.card) 0

/-- A fully support-directed frontier needs only one producer family per
argument occurrence in the union of admitted supports. -/
def supportDirectedProducerFirings [DecidableEq Argument]
  (candidates : List (CandidateSpec Argument Answer)) : Nat :=
  (candidates.foldl
    (fun support (candidate : CandidateSpec Argument Answer) =>
      support ∪ candidate.support) ∅).card

def bothCandidate : CandidateSpec CrossArgument CrossAnswer :=
  { support := {.first, .second}, answer := .both }

def overlapCandidates : List (CandidateSpec CrossArgument CrossAnswer) :=
  [leftCandidate, rightCandidate, bothCandidate]

/-- Positive: exact cohorts share equal supports and retain duplicate rule
occurrences while forcing their common argument once. -/
theorem demand_cohort_shares_equal_support :
    demandCohortProducerFirings [leftCandidate, leftCandidate] = 1 := by
  decide

/-- Positive: disjoint singleton supports are order-insensitive and cost one
producer family each. -/
theorem demand_cohort_disjoint_support_cost :
    demandCohortProducerFirings crossCandidates = 2 ∧
    demandCohortProducerFirings crossCandidates.reverse = 2 := by
  decide

/-- Negative: exact-support cohorts repeat producers across overlapping but
unequal supports.  The live contender exhibits this four-versus-two gap. -/
theorem demand_cohort_overlap_repeats_producers :
    demandCohortProducerFirings overlapCandidates = 4 ∧
    supportDirectedProducerFirings overlapCandidates = 2 := by
  decide

/-- Positive and negative executable examples for the derived batch view. -/
example :
    runCandidate (initialCandidateConfiguration bothCandidate)
        [.first, .second] =
      runCandidate (initialCandidateConfiguration bothCandidate)
        [.second, .first] := by
  apply runCandidate_order_invariant
  decide

example :
    (runCandidate (initialCandidateConfiguration bothCandidate) [.first]).pending =
      {.second} := by
  decide

/-! ## Receipt carrier and tournament inventory -/

/-- Equal payloads at different occurrences remain distinct receipt events. -/
structure EventOccurrence (Payload : Type*) where
  occurrence : Nat
  payload : Payload
deriving DecidableEq, Repr

inductive CallEvent
    (Argument Candidate Observation Effect : Type*) where
  | observed (argument : Argument) (observation : Observation)
  | matched (candidate : Candidate)
  | effect (effect : Effect)
deriving DecidableEq, Repr

abbrev CallReceipt (Argument Candidate Observation Effect : Type*) :=
  PrimeNeedWorlds.DependencyReceipt
    (EventOccurrence (CallEvent Argument Candidate Observation Effect))

/-- Runnable cases required to distinguish identity, frontier, publication,
and effect policies. -/
inductive TournamentCase where
  | unusedDivergentArgument
  | sameArgumentStrictStrict
  | strictAndWildcardUsingArgument
  | strictAndWildcardConstant
  | disjointDemandedArguments
  | candidateOrderReversal
  | overlappingSupport
  | aliasedVersusTextuallyRepeatedSource
  | sameVersusIdenticalLookingContext
  | duplicateEquationOccurrences
  | delayVersusResample
  | transactionalEffects
  | conflictingVersusCompatibleSiblings
  | persistenceRoundTrip
deriving DecidableEq, Repr

/-- The observation record deliberately keeps answers, producer firings,
receipts, ambient effects, and residual forms separate. -/
structure TournamentObservation (Answer Receipt Residual : Type*) where
  answers : List Answer
  producerFirings : Nat
  receipts : List Receipt
  ambientEffectCommits : Nat
  residuals : List Residual
deriving DecidableEq, Repr

/-- The finite inventory is executable data: every constructor is enumerated
exactly once for a runner or coverage gate. -/
def allTournamentCases : List TournamentCase :=
  [ .unusedDivergentArgument
  , .sameArgumentStrictStrict
  , .strictAndWildcardUsingArgument
  , .strictAndWildcardConstant
  , .disjointDemandedArguments
  , .candidateOrderReversal
  , .overlappingSupport
  , .aliasedVersusTextuallyRepeatedSource
  , .sameVersusIdenticalLookingContext
  , .duplicateEquationOccurrences
  , .delayVersusResample
  , .transactionalEffects
  , .conflictingVersusCompatibleSiblings
  , .persistenceRoundTrip ]

theorem allTournamentCases_complete :
    allTournamentCases.length = 14 := by
  decide

theorem allTournamentCases_contains (testCase : TournamentCase) :
    testCase ∈ allTournamentCases := by
  cases testCase <;> decide

theorem allTournamentCases_nodup : allTournamentCases.Nodup := by
  decide

end Mettapedia.Languages.MeTTa.PrimeCallSharingTournament
