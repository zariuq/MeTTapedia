import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.PatternFootprints.PolicyTable

/-!
# Waves by claims: removals among positive steps

A removal leaves the monotone fragment, and it does not leave it as a guard for
absence or a complete read does.  No addition disables a removal; what removals
compete for is occurrences.  So for proposals whose steps are positive
(`Step.Positive`: additions, removals, cell writes, reads of a presence) and whose
answers read nothing, a wave is a matter of counting, and no footprint is
compared.

* `ClaimsOn shared proposals claims views`: every proposal has a **claim** and a
  view.  From its claim beside the shared part it publishes to its view beside
  the shared part.  The shared part is what the proposals may read and must leave
  as it is; a claim is what a proposal may take.
* `HasClaims proposals world final`: the world is the claims beside a shared part,
  and `final` is the views beside it.
* `HasClaims.publishAll_perm`: **the frame rule for a wave.**  Positive proposals
  that have claims on a world are published from it in every order, to one state.
* `wave_of_claims_every_order`, `Region.Positive.wave_every_order`: with the
  answers.  Every order is published, each proposal validated by replay when its
  turn comes, and is the committed run of the alternatives that answered.
* `removals_hasClaims_iff`: **two removals of one kind have claims exactly where
  there are two occurrences.**  By footprints the two write one kind, and both
  validations by footprints report a conflict
  (`ClaimControls.seeThenTake_two_tokens`).
* `hasClaims_of_deltas`: proposals that only add have claims on every state they
  are published from: nothing is claimed and the whole state is shared.
* `ClaimsAvailable`: **the test, computed at the grain of kinds.**  What all the
  steps of the wave consume fits in the world, and each proposal is published
  again from what it takes beside what nobody takes.  The test is sound
  (`hasClaims_of_claimsAvailable`), by conservation (`publish_add_stepsTaken`):
  what a publication leaves, beside what its steps took, is the state it started
  from beside what they added.
* `Policy.publishWaveOnClaims`: the wave validated on its claims, each outcome
  validated by replay when its turn comes.  Whenever it publishes, the answers and
  the state are those of the committed run in the order of evaluation, for every
  region (`Region.observe_publishWaveOnClaims_serializable`).  For a positive
  region whose claims are available it publishes, and every order of the outcomes
  reaches that state (`Region.Positive.observe_publishWaveOnClaims`); so on
  positive siblings the observation does not depend on the order of evaluation
  (`Region.Positive.observe_publishWaveOnClaims_perm`).  Outside the positive
  regions it does (`ClaimControls.claims_order_matters_for_an_absence_guard`).  On
  the five programs of `PatternFootprints.PolicyTable`:
  `ClaimControls.programs_on_claims`.

Positive: two readers share one occurrence (`ClaimControls.readers_share`); a
reader and a taker with two occurrences; an addition and a removal of one kind
(`ClaimControls.addition_and_removal`); two siblings that each see a token and
take it, with two tokens (`ClaimControls.seeThenTake_two_tokens`).  Negative: a
reader and a taker with one occurrence (`ClaimControls.reader_and_taker`); the two
siblings with one token (`ClaimControls.seeThenTake_one_token`).

The test by counting is computed, for the instances of a resource system, in
`GSLT.Causality.ResourceWaves`: a wave is admitted when the consumptions of all
its instances, added, fit beside the largest of their reads
(`System.StepEnables`), and it is fired in every order to one bag
(`System.selectWave_every_order`).  `Regions.ResourceWaveComparison` compares that
test with footprints, and `Regions.Consume` has two `consume`s of two occurrences
in one store (`SpaceRules.consume_two_occurrences`).  There the consumptions are
the claims, and the reads lie in the shared part.  This module states the law
behind that test for proposals: several steps each, any positive guards, any
separation algebra in which every two resources are separate.

What claims do not cover: a guard that asks for an absence, and an answer that
reads.  An addition invalidates those, and they are validated by what they read
(`PatternFootprints.Validations`, `PatternFootprints.PatternWaves`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.FootprintedSpaceTransactions
open Mettapedia.GSLT.SeparationAlgebra

universe u v w

variable {Location : Type u} {Value : Type v} {Answer : Type w}

section Claims

variable [DecidableEq Location] [Zero Value] [Add Value] [SepAlgebra Value]

/-- **Claims of a list of proposals over a shared part.**  Each proposal has a
claim and a view: from its claim beside the shared part it publishes to its view
beside the shared part.  `claims` is the claims together, and `views` the views. -/
inductive ClaimsOn (shared : Location → Value) :
    List (Proposal Location Value Answer) → (Location → Value) → (Location → Value) → Prop
  | nil : ClaimsOn shared [] 0 0
  | cons {proposal : Proposal Location Value Answer}
      {rest : List (Proposal Location Value Answer)} {claim view claims views : Location → Value}
      (published : publish proposal.steps (claim + shared) = some (view + shared))
      (restClaims : ClaimsOn shared rest claims views) :
      ClaimsOn shared (proposal :: rest) (claim + claims) (view + views)

/-- **A world on which the proposals have claims**: it is their claims beside a
shared part, and `final` is their views beside that part. -/
def HasClaims (proposals : List (Proposal Location Value Answer))
    (world final : Location → Value) : Prop :=
  ∃ shared claims views : Location → Value,
    ClaimsOn shared proposals claims views ∧ world = claims + shared ∧ final = views + shared

/-- Proposals that are published one after another, with answers that do not
depend on the state, are published in order with those answers. -/
theorem publishInOrder_of_publishAll [DecidableEq Answer]
    {outcomes : List (Answer × Proposal Location Value Answer)} {world final : Location → Value}
    (answers : ∀ outcome ∈ outcomes, ∀ state, outcome.2.readout.value state = outcome.1)
    (published : publishAll (outcomes.map Prod.snd) world = some final) :
    publishInOrder outcomes world = some final := by
  induction outcomes generalizing world with
  | nil => exact published
  | cons outcome rest ih =>
      rw [List.map_cons, publishAll_cons, Option.bind_eq_some_iff] at published
      obtain ⟨next, headPublished, tail⟩ := published
      rw [publishInOrder, headPublished, Option.bind_some,
        if_pos (answers outcome List.mem_cons_self next)]
      exact ih (fun other member => answers other (List.mem_cons_of_mem outcome member)) tail

variable [AllSeparate Value]

/-- Claims do not depend on the order of the proposals. -/
theorem ClaimsOn.perm {shared claims views : Location → Value}
    {proposals reordered : List (Proposal Location Value Answer)}
    (claimed : ClaimsOn shared proposals claims views) (perm : proposals.Perm reordered) :
    ClaimsOn shared reordered claims views := by
  induction perm generalizing claims views with
  | nil => exact claimed
  | cons proposal _ ih =>
      cases claimed with
      | cons published restClaimed => exact .cons published (ih restClaimed)
  | swap first second rest =>
      cases claimed with
      | @cons _ _ secondClaim secondView _ _ secondPublished restClaimed =>
          cases restClaimed with
          | @cons _ _ firstClaim firstView tailClaims tailViews firstPublished tailClaimed =>
              have swapped :=
                ClaimsOn.cons firstPublished (ClaimsOn.cons secondPublished tailClaimed)
              rwa [AllSeparate.add_left_comm firstClaim secondClaim,
                AllSeparate.add_left_comm firstView secondView] at swapped
  | trans _ _ ihFirst ihSecond => exact ihSecond (ihFirst claimed)

/-- Positive proposals with claims are published one after another, beside any
frame: each takes its claim, reads the shared part, and leaves its view. -/
theorem ClaimsOn.publishAll_add {shared claims views : Location → Value}
    {proposals : List (Proposal Location Value Answer)}
    (claimed : ClaimsOn shared proposals claims views)
    (positive : ∀ proposal ∈ proposals, ∀ step ∈ proposal.steps, step.Positive)
    (frame : Location → Value) :
    publishAll proposals (claims + shared + frame) = some (views + shared + frame) := by
  induction proposals generalizing claims views frame with
  | nil =>
      cases claimed
      rfl
  | cons proposal rest ih =>
      cases claimed with
      | @cons _ _ claim view restClaims restViews published restClaimed =>
          have stable : proposal.StableUnder (restClaims + frame) :=
            fun step member state =>
              positive proposal List.mem_cons_self step member state (restClaims + frame)
          have head := stable.publish_add published
          have source : claim + restClaims + shared + frame =
              claim + shared + (restClaims + frame) :=
            (congrArg (· + frame) (AllSeparate.add_right_comm claim restClaims shared)).trans
              (AllSeparate.add_assoc (claim + shared) restClaims frame)
          have middle : view + shared + (restClaims + frame) =
              restClaims + shared + (view + frame) :=
            (AllSeparate.add_left_comm (view + shared) restClaims frame).trans
              ((congrArg (restClaims + ·)
                ((congrArg (· + frame) (AllSeparate.add_comm view shared)).trans
                  (AllSeparate.add_assoc shared view frame))).trans
                (AllSeparate.add_assoc restClaims shared (view + frame)).symm)
          have target : restViews + shared + (view + frame) =
              view + restViews + shared + frame :=
            (AllSeparate.add_left_comm (restViews + shared) view frame).trans
              ((AllSeparate.add_assoc view (restViews + shared) frame).symm.trans
                (congrArg (· + frame) (AllSeparate.add_assoc view restViews shared).symm))
          rw [publishAll_cons, source, head, Option.bind_some, middle,
            ih restClaimed
              (fun other member => positive other (List.mem_cons_of_mem proposal member))
              (view + frame),
            target]

/-- **The frame rule for a wave.**  Positive proposals that have claims on a
world are published from it in every order, to one state: the views beside the
shared part.  No footprint is compared. -/
theorem HasClaims.publishAll_perm {proposals order : List (Proposal Location Value Answer)}
    {world final : Location → Value} (claims : HasClaims proposals world final)
    (positive : ∀ proposal ∈ proposals, ∀ step ∈ proposal.steps, step.Positive)
    (perm : proposals.Perm order) : publishAll order world = some final := by
  obtain ⟨shared, taken, views, claimsOn, rfl, rfl⟩ := claims
  have published := (claimsOn.perm perm).publishAll_add
    (fun proposal member => positive proposal (perm.mem_iff.mpr member)) 0
  rwa [SepAlgebra.add_zero, SepAlgebra.add_zero] at published

/-- **A wave by claims is serializable in every order.**  Outcomes explored from
one state, of positive proposals that have claims on it, are published from it in
every order, each validated by replay when its turn comes; all orders reach one
state; and every order is the committed run of the alternatives that answered,
with the answers that were returned. -/
theorem wave_of_claims_every_order [DecidableEq Answer]
    {outcomes order : List (Answer × Proposal Location Value Answer)}
    {world final : Location → Value}
    (positive : ∀ outcome ∈ outcomes, outcome.2.Positive)
    (claims : HasClaims (outcomes.map Prod.snd) world final)
    (explored : ∀ outcome ∈ outcomes, outcome.2.outcome? world = some outcome)
    (perm : outcomes.Perm order) :
    publishInOrder order world = some final ∧
      (Region.alternatives (order.map fun outcome => outcome.2.region)).committed world =
        (order.map Prod.fst, final) := by
  have published : publishInOrder order world = some final := by
    refine publishInOrder_of_publishAll (fun outcome member state => ?_) ?_
    · have inside := perm.mem_iff.mpr member
      obtain ⟨view, -, same⟩ := Proposal.outcome?_eq_some_iff.mp (explored outcome inside)
      exact (Readout.value_eq_of_reads_empty (positive outcome inside).constant state view).trans
        (congrArg Prod.fst same)
    · exact claims.publishAll_perm
        (fun proposal member => by
          obtain ⟨outcome, inside, rfl⟩ := List.mem_map.mp member
          exact (positive outcome inside).steps)
        (perm.map Prod.snd)
  exact ⟨published, publishInOrder_serializable published⟩

/-- **A positive region needs only its claims.**  When the proposals of its
outcomes from a world have claims on that world, every order of the outcomes is
published, each validated by replay, to one state, and is a committed run with
the answers returned. -/
theorem Region.Positive.wave_every_order [DecidableEq Answer]
    {region : Region Location Value Answer} (positive : region.Positive)
    {world final : Location → Value}
    (claims : HasClaims ((region.branchLocal world).map Prod.snd) world final)
    {order : List (Answer × Proposal Location Value Answer)}
    (perm : (region.branchLocal world).Perm order) :
    publishInOrder order world = some final ∧
      (Region.alternatives (order.map fun outcome => outcome.2.region)).committed world =
        (order.map Prod.fst, final) :=
  wave_of_claims_every_order
    (fun _ member => positive.proposal_positive (Region.mem_branchLocal_iff.mp member).1)
    claims (fun _ member => (Region.mem_branchLocal_iff.mp member).2) perm

/-- **Proposals that only add have claims on every state they are published
from**: nothing is claimed, the whole state is shared, and the views are what
they add. -/
theorem hasClaims_of_deltas {proposals : List (Proposal Location Value Answer)}
    (deltas : ∀ proposal ∈ proposals, proposal.IsDelta) {world : Location → Value}
    (explored : ∀ proposal ∈ proposals, (publish proposal.steps world).isSome) :
    HasClaims proposals world
      (world + stepsAdded (proposals.flatMap fun proposal => proposal.steps)) := by
  have claimed : ∃ claims views : Location → Value,
      ClaimsOn world proposals claims views ∧ claims = 0 ∧
        views = stepsAdded (proposals.flatMap fun proposal => proposal.steps) := by
    induction proposals with
    | nil => exact ⟨0, 0, .nil, rfl, rfl⟩
    | cons proposal rest ih =>
        obtain ⟨claims, views, restClaimed, rfl, rfl⟩ :=
          ih (fun other member => deltas other (List.mem_cons_of_mem proposal member))
            (fun other member => explored other (List.mem_cons_of_mem proposal member))
        obtain ⟨view, published⟩ :=
          Option.isSome_iff_exists.mp (explored proposal List.mem_cons_self)
        have adds := (deltas proposal List.mem_cons_self).publish_eq_add published
        have claimedHead :
            publish proposal.steps (0 + world) = some (proposal.added + world) := by
          rw [SepAlgebra.zero_add, published, adds, AllSeparate.add_comm]
        refine ⟨0 + 0, proposal.added + _, .cons claimedHead restClaimed,
          SepAlgebra.zero_add 0, ?_⟩
        rw [List.flatMap_cons, stepsAdded_append]
        rfl
  obtain ⟨claims, views, claimsOn, rfl, rfl⟩ := claimed
  exact ⟨world, 0, _, claimsOn, (SepAlgebra.zero_add world).symm, AllSeparate.add_comm _ _⟩

end Claims

/-! ## What steps take, and conservation -/

section Taken

variable [DecidableEq Location] [Zero Value] [Add Value] [SepAlgebra Value]

/-- **What a list of steps takes**: what its steps consume, together. -/
def stepsTaken : List (Step Location Value) → (Location → Value)
  | [] => 0
  | step :: rest => step.rule.consumed + stepsTaken rest

/-- **What a proposal takes.** -/
def Proposal.taken (proposal : Proposal Location Value Answer) : Location → Value :=
  stepsTaken proposal.steps

/-- What a list of steps takes vanishes outside the locations they write. -/
theorem stepsTaken_outside (steps : List (Step Location Value)) {location : Location}
    (outside : location ∉ stepsWrites steps) : stepsTaken steps location = 0 := by
  induction steps with
  | nil => rfl
  | cons step rest ih =>
      have notStep : location ∉ step.rule.writes :=
        fun written => outside (Finset.mem_union_left _ written)
      have notRest : location ∉ stepsWrites rest :=
        fun written => outside (Finset.mem_union_right _ written)
      show step.rule.consumed location + stepsTaken rest location = 0
      rw [step.rule.consumed_outside location notStep, ih notRest, SepAlgebra.zero_add]

/-- The locations a list of steps writes do not depend on their order. -/
theorem stepsWrites_perm {steps reordered : List (Step Location Value)}
    (perm : steps.Perm reordered) : stepsWrites steps = stepsWrites reordered := by
  induction perm with
  | nil => rfl
  | cons step _ ih => exact congrArg (step.rule.writes ∪ ·) ih
  | swap first second rest => exact Finset.union_left_comm _ _ _
  | trans _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond

variable [AllSeparate Value]

theorem stepsTaken_append (first second : List (Step Location Value)) :
    stepsTaken (first ++ second) = stepsTaken first + stepsTaken second := by
  induction first with
  | nil => exact (SepAlgebra.zero_add _).symm
  | cons step rest ih =>
      show step.rule.consumed + stepsTaken (rest ++ second) = _
      rw [ih]
      exact (AllSeparate.add_assoc _ _ _).symm

/-- What a list of steps takes does not depend on their order. -/
theorem stepsTaken_perm {steps reordered : List (Step Location Value)}
    (perm : steps.Perm reordered) : stepsTaken steps = stepsTaken reordered := by
  induction perm with
  | nil => rfl
  | cons step _ ih => exact congrArg (step.rule.consumed + ·) ih
  | swap first second rest => exact AllSeparate.add_left_comm _ _ _
  | trans _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond

/-- **Conservation.**  What a publication leaves, beside what its steps took, is
the state it started from beside what its steps added. -/
theorem publish_add_stepsTaken {steps : List (Step Location Value)}
    {state view : Location → Value} (published : publish steps state = some view) :
    view + stepsTaken steps = state + stepsAdded steps := by
  induction steps generalizing state with
  | nil =>
      cases published
      rfl
  | cons step rest ih =>
      rw [publish_cons, Option.bind_eq_some_iff] at published
      obtain ⟨middle, fired, restPublished⟩ := published
      obtain ⟨-, frame, -, -, sourceEq, middleEq⟩ := step.fire_eq_some_iff.mp fired
      have conserved := ih restPublished
      show view + (step.rule.consumed + stepsTaken rest) =
        state + (step.rule.produced + stepsAdded rest)
      calc view + (step.rule.consumed + stepsTaken rest)
          = step.rule.consumed + (view + stepsTaken rest) := AllSeparate.add_left_comm _ _ _
        _ = step.rule.consumed + (step.rule.produced + frame + stepsAdded rest) := by
            rw [conserved, middleEq]
        _ = step.rule.consumed + (frame + (step.rule.produced + stepsAdded rest)) := by
            rw [AllSeparate.add_comm step.rule.produced frame,
              AllSeparate.add_assoc frame step.rule.produced (stepsAdded rest)]
        _ = step.rule.consumed + frame + (step.rule.produced + stepsAdded rest) :=
            (AllSeparate.add_assoc _ _ _).symm
        _ = state + (step.rule.produced + stepsAdded rest) := by rw [sourceEq]

end Taken

/-! ## The test, computed at the grain of kinds -/

section Counted

variable [DecidableEq Location]

/-- A proposal over multiplicities that is published from what it takes beside a
rest leaves what it adds beside that rest. -/
theorem publish_taken_add_eq {proposal : Proposal Location ℕ Answer} {rest view : Location → ℕ}
    (published : publish proposal.steps (proposal.taken + rest) = some view) :
    view = proposal.added + rest := by
  funext location
  have conserved : view location + stepsTaken proposal.steps location =
      stepsTaken proposal.steps location + rest location + stepsAdded proposal.steps location :=
    congrFun (publish_add_stepsTaken published) location
  show view location = stepsAdded proposal.steps location + rest location
  omega

/-- **The claims of a wave are available on a world**: what all the steps consume
fits in the world, and each proposal is published from what it takes beside what
nobody takes. -/
def ClaimsAvailable (proposals : List (Proposal Location ℕ Answer)) (world : Location → ℕ) :
    Prop :=
  (∀ location ∈ stepsWrites (proposals.flatMap fun proposal => proposal.steps),
      stepsTaken (proposals.flatMap fun proposal => proposal.steps) location ≤ world location) ∧
    ∀ proposal ∈ proposals,
      (publish proposal.steps
        (proposal.taken +
          (world - stepsTaken (proposals.flatMap fun proposal => proposal.steps)))).isSome

/-- The test is computed: finitely many comparisons, and one publication for each
proposal. -/
instance ClaimsAvailable.decidable (proposals : List (Proposal Location ℕ Answer))
    (world : Location → ℕ) : Decidable (ClaimsAvailable proposals world) :=
  inferInstanceAs (Decidable
    ((∀ location ∈ stepsWrites (proposals.flatMap fun proposal => proposal.steps),
        stepsTaken (proposals.flatMap fun proposal => proposal.steps) location ≤
          world location) ∧
      ∀ proposal ∈ proposals,
        (publish proposal.steps
          (proposal.taken +
            (world - stepsTaken (proposals.flatMap fun proposal => proposal.steps)))).isSome))

/-- The test does not depend on the order of the proposals. -/
theorem ClaimsAvailable.perm {proposals reordered : List (Proposal Location ℕ Answer)}
    {world : Location → ℕ} (available : ClaimsAvailable proposals world)
    (perm : proposals.Perm reordered) : ClaimsAvailable reordered world := by
  have steps := perm.flatMap_right fun proposal : Proposal Location ℕ Answer => proposal.steps
  unfold ClaimsAvailable at available ⊢
  rw [← stepsWrites_perm steps, ← stepsTaken_perm steps]
  exact ⟨available.1, fun proposal member => available.2 proposal (perm.mem_iff.mpr member)⟩

/-- Proposals that are each published from what they take beside a shared part
have claims over it: what they take, and what they add. -/
theorem claimsOn_of_published {shared : Location → ℕ}
    {proposals : List (Proposal Location ℕ Answer)}
    (each : ∀ proposal ∈ proposals, (publish proposal.steps (proposal.taken + shared)).isSome) :
    ∃ claims views : Location → ℕ, ClaimsOn shared proposals claims views ∧
      claims = stepsTaken (proposals.flatMap fun proposal => proposal.steps) ∧
      views = stepsAdded (proposals.flatMap fun proposal => proposal.steps) := by
  induction proposals with
  | nil => exact ⟨0, 0, .nil, rfl, rfl⟩
  | cons proposal rest ih =>
      obtain ⟨claims, views, restClaimed, rfl, rfl⟩ :=
        ih fun other member => each other (List.mem_cons_of_mem proposal member)
      obtain ⟨view, published⟩ :=
        Option.isSome_iff_exists.mp (each proposal List.mem_cons_self)
      have head : publish proposal.steps (proposal.taken + shared) =
          some (proposal.added + shared) := by
        rw [← publish_taken_add_eq published]
        exact published
      refine ⟨proposal.taken + _, proposal.added + _, .cons head restClaimed, ?_, ?_⟩
      · rw [List.flatMap_cons, stepsTaken_append]
        rfl
      · rw [List.flatMap_cons, stepsAdded_append]
        rfl

/-- **The computed test is sound**: where the claims are available the proposals
have claims, with what nobody takes as the shared part. -/
theorem hasClaims_of_claimsAvailable {proposals : List (Proposal Location ℕ Answer)}
    {world : Location → ℕ} (available : ClaimsAvailable proposals world) :
    HasClaims proposals world
      (stepsAdded (proposals.flatMap fun proposal => proposal.steps) +
        (world - stepsTaken (proposals.flatMap fun proposal => proposal.steps))) := by
  obtain ⟨fits, each⟩ := available
  obtain ⟨claims, views, claimsOn, rfl, rfl⟩ := claimsOn_of_published each
  refine ⟨_, _, _, claimsOn, ?_, rfl⟩
  funext location
  show world location =
    stepsTaken (proposals.flatMap fun proposal => proposal.steps) location +
      (world location - stepsTaken (proposals.flatMap fun proposal => proposal.steps) location)
  by_cases written : location ∈ stepsWrites (proposals.flatMap fun proposal => proposal.steps)
  · have fitsHere := fits location written
    omega
  · rw [stepsTaken_outside _ written]
    omega

/-- **A wave validated on its claims.**  Every answer is returned.  If the claims
are available on the enclosing state the outcomes are published in the order of
evaluation, each validated by replay when its turn comes; otherwise a conflict is
reported. -/
def Policy.publishWaveOnClaims [DecidableEq Answer] : Policy Location ℕ Answer where
  returned outcomes := outcomes.map Prod.fst
  change outcomes world :=
    if ClaimsAvailable (outcomes.map Prod.snd) world then publishInOrder outcomes world else none

/-- **Whenever the wave on claims publishes, it is a serial committed run**: the
answers and the state are those of the alternatives that answered, run in the
committed mode in the order of evaluation.  This holds of every region. -/
theorem Region.observe_publishWaveOnClaims_serializable [DecidableEq Answer]
    (region : Region Location ℕ Answer) {world final : Location → ℕ}
    (published : (region.observe Policy.publishWaveOnClaims world).2 = some final) :
    (Region.alternatives
        ((region.branchLocal world).map fun outcome => outcome.2.region)).committed world =
      ((region.branchLocal world).map Prod.fst, final) := by
  have change : (if ClaimsAvailable ((region.branchLocal world).map Prod.snd) world then
      publishInOrder (region.branchLocal world) world else none) = some final := published
  split at change
  · exact publishInOrder_serializable change
  · cases change

/-- **A positive region whose claims are available is published**, and every
order of its outcomes, each validated by replay, reaches the state published. -/
theorem Region.Positive.observe_publishWaveOnClaims [DecidableEq Answer]
    {region : Region Location ℕ Answer} (positive : region.Positive) {world : Location → ℕ}
    (available : ClaimsAvailable ((region.branchLocal world).map Prod.snd) world) :
    ∃ final,
      region.observe Policy.publishWaveOnClaims world =
          ((region.branchLocal world).map Prod.fst, some final) ∧
        ∀ order, (region.branchLocal world).Perm order →
          publishInOrder order world = some final := by
  have claims := hasClaims_of_claimsAvailable available
  refine ⟨_, ?_, fun order perm => (positive.wave_every_order claims perm).1⟩
  show ((region.branchLocal world).map Prod.fst,
    if ClaimsAvailable ((region.branchLocal world).map Prod.snd) world then
      publishInOrder (region.branchLocal world) world else none) = _
  rw [if_pos available, (positive.wave_every_order claims (List.Perm.refl _)).1]

/-- **On positive siblings the wave on claims does not depend on the order of
evaluation.**  Reordering the siblings reorders the answers, and leaves what is
published, or the conflict, as it is. -/
theorem Region.Positive.observe_publishWaveOnClaims_perm [DecidableEq Answer]
    {siblings reordered : List (Region Location ℕ Answer)}
    (positive : (Region.alternatives siblings).Positive) (perm : siblings.Perm reordered)
    (world : Location → ℕ) :
    ((Region.alternatives siblings).observe Policy.publishWaveOnClaims world).1.Perm
        ((Region.alternatives reordered).observe Policy.publishWaveOnClaims world).1 ∧
      ((Region.alternatives siblings).observe Policy.publishWaveOnClaims world).2 =
        ((Region.alternatives reordered).observe Policy.publishWaveOnClaims world).2 := by
  have outcomes := Region.branchLocal_alternatives_perm perm world
  refine ⟨outcomes.map Prod.fst, ?_⟩
  show (if ClaimsAvailable (((Region.alternatives siblings).branchLocal world).map Prod.snd)
        world then
      publishInOrder ((Region.alternatives siblings).branchLocal world) world else none) =
    (if ClaimsAvailable (((Region.alternatives reordered).branchLocal world).map Prod.snd)
        world then
      publishInOrder ((Region.alternatives reordered).branchLocal world) world else none)
  by_cases available :
      ClaimsAvailable (((Region.alternatives siblings).branchLocal world).map Prod.snd) world
  · have claims := hasClaims_of_claimsAvailable available
    rw [if_pos available, if_pos (available.perm (outcomes.map Prod.snd)),
      (positive.wave_every_order claims (List.Perm.refl _)).1,
      (positive.wave_every_order claims outcomes).1]
  · rw [if_neg available, if_neg fun reorderedAvailable =>
      available (reorderedAvailable.perm (outcomes.map Prod.snd).symm)]

end Counted

/-! ## Removals at the grain of kinds -/

section Kinds

variable [DecidableEq Location]

/-- **Two removals of one kind have claims exactly where there are two
occurrences.**  With two occurrences each removal claims one; with fewer there is
no such split, and one of the two is refused. -/
theorem removals_hasClaims_iff (kind : Location) (first second : Answer)
    (world : Location → ℕ) :
    (∃ final, HasClaims
        [(⟨[removeKind kind], Readout.const first⟩ : Proposal Location ℕ Answer),
          ⟨[removeKind kind], Readout.const second⟩] world final) ↔
      2 ≤ world kind := by
  constructor
  · rintro ⟨final, claims⟩
    have published := claims.publishAll_perm
      (fun proposal member step inside => by
        have steps : proposal.steps = [removeKind kind] := by
          rcases List.mem_cons.mp member with rfl | later
          · rfl
          · rw [List.mem_singleton.mp later]
        rw [steps, List.mem_singleton] at inside
        rw [inside]
        exact removeKind_positive kind)
      (List.Perm.refl _)
    have fired : ((removeKind kind).fire world).bind
        (fun middle => ((removeKind kind).fire middle).bind (publish [])) = some final :=
      published
    obtain ⟨middle, firstFired, rest⟩ := Option.bind_eq_some_iff.mp fired
    obtain ⟨last, secondFired, -⟩ := Option.bind_eq_some_iff.mp rest
    have atFirst := congrFun ((fire_removeKind_eq_some_iff kind world middle).mp firstFired) kind
    have atSecond := congrFun ((fire_removeKind_eq_some_iff kind middle last).mp secondFired) kind
    have single : (Pi.single kind 1 : Location → ℕ) kind = 1 := Pi.single_eq_same kind 1
    have firstCount : world kind = middle kind + 1 := by rw [atFirst]; exact congrArg _ single
    have secondCount : middle kind = last kind + 1 := by rw [atSecond]; exact congrArg _ single
    omega
  · intro two
    have taken : ∀ rest : Location → ℕ,
        publish [removeKind kind] (Pi.single kind 1 + rest) = some (0 + rest) := fun rest => by
      rw [publish_cons, (fire_removeKind_eq_some_iff kind _ rest).mpr (add_comm _ _),
        Option.bind_some, publish_nil, zero_add]
    refine ⟨_, world - (Pi.single kind 1 + Pi.single kind 1), _, _,
      .cons (taken _) (.cons (taken _) .nil), ?_, rfl⟩
    funext location
    by_cases same : location = kind
    · subst same
      simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply, Pi.single_eq_same]
      omega
    · simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply, Pi.single_eq_of_ne same]
      omega

end Kinds

/-! ## Controls -/

namespace ClaimControls

open AddOnly (Kind noKinds)
open KindControls (oneA)
open DeltaControls (addA seeA removeA)

/-- Two `a`. -/
def twoA : Kind → ℕ := Pi.single Kind.a 2

/-- The steps of a reader and a taker are positive. -/
theorem reader_taker_positive :
    ∀ proposal ∈ [seeA, removeA], ∀ step ∈ proposal.steps, step.Positive := by
  intro proposal member step inside
  rcases List.mem_cons.mp member with rfl | later
  · rw [List.mem_singleton.mp inside]
    exact seeKind_positive _
  · rw [List.mem_singleton.mp later] at inside
    rw [List.mem_singleton.mp inside]
    exact removeKind_positive _

/-- **Positive, shared**: two readers of one `a`.  Neither claims anything; the
`a` is shared, and it is still there. -/
theorem readers_share : HasClaims [seeA, seeA] oneA oneA := by
  have seen : publish [seeKind Kind.a] ((0 : Kind → ℕ) + oneA) = some (0 + oneA) := by
    rw [publish_seeKind, if_pos (by decide)]
  exact ⟨oneA, 0 + (0 + 0), 0 + (0 + 0), .cons seen (.cons seen .nil), by simp, by simp⟩

/-- **Positive, a claim beside what is shared**: a reader and a taker of `a`, with
two occurrences.  The taker claims one, the other is shared.  **Negative**: with
one occurrence there are no claims: published after the taker, the reader is
refused. -/
theorem reader_and_taker :
    HasClaims [seeA, removeA] twoA oneA ∧ ¬ ∃ final, HasClaims [seeA, removeA] oneA final := by
  constructor
  · have seen : publish [seeKind Kind.a] ((0 : Kind → ℕ) + oneA) = some (0 + oneA) := by
      rw [publish_seeKind, if_pos (by decide)]
    have taken : publish [removeKind Kind.a] (Pi.single Kind.a 1 + oneA) = some (0 + oneA) := by
      rw [publish_cons, (fire_removeKind_eq_some_iff Kind.a _ oneA).mpr (add_comm _ _),
        Option.bind_some, publish_nil, zero_add]
    refine ⟨oneA, 0 + (Pi.single Kind.a 1 + 0), 0 + (0 + 0), .cons seen (.cons taken .nil), ?_,
      by simp⟩
    funext kind
    cases kind <;> rfl
  · rintro ⟨final, claims⟩
    have published := claims.publishAll_perm reader_taker_positive (List.Perm.swap removeA seeA [])
    have refused : (publishAll [removeA, seeA] oneA).isSome = false := by decide
    rw [published] at refused
    cases refused

/-- The outcome of a sibling that sees a token and takes it. -/
def tookOutcome (first : Bool) : Probes.Reply × Proposal Kind ℕ Probes.Reply :=
  (.got first, ⟨[seeKind .a, removeKind .a], Readout.const (.got first)⟩)

/-- The two siblings that each see a token and take it are a positive region. -/
theorem seeThenTake_positive : Probes.seeThenTake.Positive :=
  .orElse (.step (seeKind_positive _) (.step (removeKind_positive _) (.answer rfl)))
    (.orElse (.step (seeKind_positive _) (.step (removeKind_positive _) (.answer rfl))) .fail)

/-- **Two siblings that each see a token and take it, with two tokens, are a wave
by claims.**  Each claims one token.  Every order of the two outcomes is
published, each validated by replay, to the empty space, and the committed run
returns both receipts.  Validated by footprints, on writes only or on reads as
well, the two conflict: both write the kind of the token. -/
theorem seeThenTake_two_tokens :
    HasClaims ((Probes.seeThenTake.branchLocal twoA).map Prod.snd) twoA noKinds ∧
      publishInOrder (Probes.seeThenTake.branchLocal twoA) twoA = some noKinds ∧
      publishInOrder (Probes.seeThenTake.branchLocal twoA).reverse twoA = some noKinds ∧
      (Probes.seeThenTake.committed twoA).1 = [.got true, .got false] ∧
      (Probes.seeThenTake.observe Policy.publishWaveOnWrites twoA).2.isNone = true ∧
      (Probes.seeThenTake.observe Policy.publishWave twoA).2.isNone = true := by
  have outcomes : Probes.seeThenTake.branchLocal twoA = [tookOutcome true, tookOutcome false] :=
    rfl
  have taken : publish [seeKind Kind.a, removeKind Kind.a] (Pi.single Kind.a 1 + noKinds) =
      some (0 + noKinds) := by
    rw [publish_cons, (fire_seeKind_eq_some_iff Kind.a _ _).mpr ⟨by decide, rfl⟩,
      Option.bind_some, publish_cons,
      (fire_removeKind_eq_some_iff Kind.a _ (0 + noKinds)).mpr
        (by funext kind; cases kind <;> rfl),
      Option.bind_some, publish_nil]
  have claims :
      HasClaims ((Probes.seeThenTake.branchLocal twoA).map Prod.snd) twoA noKinds := by
    rw [outcomes]
    refine ⟨noKinds, Pi.single Kind.a 1 + (Pi.single Kind.a 1 + 0), 0 + (0 + 0),
      .cons taken (.cons taken .nil), ?_, ?_⟩ <;>
    · funext kind
      cases kind <;> rfl
  exact ⟨claims, (seeThenTake_positive.wave_every_order claims (List.Perm.refl _)).1,
    (seeThenTake_positive.wave_every_order claims (List.reverse_perm _).symm).1, by decide,
    by decide, by decide⟩

/-- **With one token the two siblings have no claims**: their proposals are not
published together. -/
theorem seeThenTake_one_token :
    ¬ ∃ final,
      HasClaims ((Probes.seeThenTake.branchLocal Probes.oneToken).map Prod.snd) Probes.oneToken
        final := by
  rintro ⟨final, claims⟩
  have published := claims.publishAll_perm
    (fun proposal member => by
      obtain ⟨outcome, inside, rfl⟩ := List.mem_map.mp member
      exact (seeThenTake_positive.proposal_positive (Region.mem_branchLocal_iff.mp inside).1).steps)
    (List.Perm.refl _)
  have refused : (publishAll ((Probes.seeThenTake.branchLocal Probes.oneToken).map Prod.snd)
      Probes.oneToken).isSome = false := by decide
  rw [published] at refused
  cases refused

/-- **An addition and a removal of one kind are a wave by claims** wherever the
removal has an outcome: the removal claims the occurrence that is there, and the
addition claims nothing.  Both orders are published, to one state.  By footprints
the two write one kind and conflict. -/
theorem addition_and_removal :
    ClaimsAvailable [addA, removeA] oneA ∧
      (publishAll [addA, removeA] oneA).map (fun world => world .a) = some 1 ∧
      (publishAll [removeA, addA] oneA).map (fun world => world .a) = some 1 ∧
      ¬ addA.WritesApart removeA := by
  decide

/-- **Positive, what a proposal takes**: the taker takes one `a`, and it adds
nothing.  **Negative**: the reader takes nothing. -/
theorem taken_instances :
    removeA.taken Kind.a = 1 ∧ removeA.added Kind.a = 0 ∧ seeA.taken Kind.a = 0 := by
  decide

/-- **Positive, the computed test**: two takers and two occurrences; a reader and
a taker and two occurrences; two readers and one occurrence.  **Negative**: two
takers and one occurrence; a reader and a taker and one occurrence. -/
theorem claimsAvailable_instances :
    ClaimsAvailable [removeA, removeA] twoA ∧ ClaimsAvailable [seeA, removeA] twoA ∧
      ClaimsAvailable [seeA, seeA] oneA ∧ ¬ ClaimsAvailable [removeA, removeA] oneA ∧
      ¬ ClaimsAvailable [seeA, removeA] oneA := by
  decide

/-- **The wave on claims, on the siblings that each see a token and take it.**
With two tokens it publishes: both receipts, and the space is empty.  With one
token it reports a conflict and the token stays. -/
theorem seeThenTake_on_claims :
    (Probes.seeThenTake.observe Policy.publishWaveOnClaims twoA).1 = [.got true, .got false] ∧
      (Probes.seeThenTake.observe Policy.publishWaveOnClaims twoA).2.map
        (fun world => (world .a, world .b)) = some (0, 0) ∧
      (Probes.seeThenTake.observe Policy.publishWaveOnClaims Probes.oneToken).2.isNone = true := by
  decide

/-- **The five programs under the wave on claims.**

* Each sibling adds an atom and reads the pattern: nothing is claimed; the replay
  finds that the second answer is not the answer any more, and a conflict is
  reported, as when reads are validated.
* Each sibling adds an atom and answers with it, the first answer returned: both
  atoms.
* Each sibling sees the one token and takes it: a conflict; with two tokens, both
  receipts and no token.
* One sibling adds and fails, the other adds and answers: the atom of the sibling
  that answered.
* Each sibling adds an atom: both atoms. -/
theorem programs_on_claims :
    (runDirectives Policy.publishWaveOnClaims [Probes.addThenReadAll, Probes.readSpace]
        noKinds).1 = [([.bag 1 0, .bag 0 1], true), ([.bag 0 0], false)] ∧
      (runDirectives Policy.publishWaveOnClaims.returningFirst
        [Probes.addThenAnswer, Probes.readSpace] noKinds).1 =
        [([.atom .a], false), ([.bag 1 1], false)] ∧
      (runDirectives Policy.publishWaveOnClaims [Probes.seeThenTake, Probes.readSpace]
        Probes.oneToken).1 = [([.got true, .got false], true), ([.bag 1 0], false)] ∧
      (runDirectives Policy.publishWaveOnClaims [Probes.seeThenTake, Probes.readSpace] twoA).1 =
        [([.got true, .got false], false), ([.bag 0 0], false)] ∧
      (runDirectives Policy.publishWaveOnClaims [Probes.addThenFail, Probes.readSpace]
        noKinds).1 = [([.atom .b], false), ([.bag 0 1], false)] ∧
      (runDirectives Policy.publishWaveOnClaims [Probes.addOnly, Probes.readSpace] noKinds).1 =
        [([.done, .done], false), ([.bag 1 1], false)] := by
  decide

/-- **What the wave on claims accepts and the waves by footprints refuse**: the
chain of an addition and a rule that reads it, and two additions of one kind. -/
theorem claims_accept_the_monotone :
    (MonotoneControls.chain.observe Policy.publishWaveOnClaims KindControls.oneA).2.map
        (fun world => (world .a, world .b)) = some (2, 1) ∧
      (MonotoneControls.chain.observe Policy.publishWave KindControls.oneA).2.isNone = true ∧
      (Policy.publishWaveOnClaims.change
        [((), (⟨[addKind Kind.a], Readout.const ()⟩ : Proposal Kind ℕ Unit)),
          ((), ⟨[addKind Kind.a], Readout.const ()⟩)] noKinds).map (fun world => world .a) =
        some 2 ∧
      (Policy.publishWaveOnWrites.change
        [((), (⟨[addKind Kind.a], Readout.const ()⟩ : Proposal Kind ℕ Unit)),
          ((), ⟨[addKind Kind.a], Readout.const ()⟩)] noKinds).isNone = true := by
  decide

/-- **Outside the positive regions the wave on claims depends on the order of
evaluation.**  A guard for the absence of `a` and an addition of `a` claim nothing.
With the guard first both are published; with the addition first the replay of
the guard is refused. -/
theorem claims_order_matters_for_an_absence_guard :
    (Policy.publishWaveOnClaims.change
        [ValidationControls.guardedOutcome, ValidationControls.markerOutcome] noKinds).isSome =
        true ∧
      (Policy.publishWaveOnClaims.change
        [ValidationControls.markerOutcome, ValidationControls.guardedOutcome] noKinds).isSome =
        false := by
  decide

/-- An instance of `removals_hasClaims_iff`: two takers of `a` have claims with
two occurrences, and none with one. -/
theorem takers_instances :
    (∃ final, HasClaims [removeA, removeA] twoA final) ∧
      ¬ ∃ final, HasClaims [removeA, removeA] oneA final :=
  ⟨(removals_hasClaims_iff Kind.a () () twoA).mpr (by decide),
    fun claims => absurd ((removals_hasClaims_iff Kind.a () () oneA).mp claims) (by decide)⟩

end ClaimControls

#print axioms publishInOrder_of_publishAll
#print axioms ClaimsOn.perm
#print axioms ClaimsOn.publishAll_add
#print axioms HasClaims.publishAll_perm
#print axioms wave_of_claims_every_order
#print axioms Region.Positive.wave_every_order
#print axioms hasClaims_of_deltas
#print axioms stepsTaken_outside
#print axioms stepsTaken_append
#print axioms publish_add_stepsTaken
#print axioms publish_taken_add_eq
#print axioms claimsOn_of_published
#print axioms hasClaims_of_claimsAvailable
#print axioms Region.observe_publishWaveOnClaims_serializable
#print axioms Region.Positive.observe_publishWaveOnClaims
#print axioms stepsWrites_perm
#print axioms stepsTaken_perm
#print axioms ClaimsAvailable.perm
#print axioms Region.Positive.observe_publishWaveOnClaims_perm
#print axioms removals_hasClaims_iff
#print axioms ClaimControls.reader_taker_positive
#print axioms ClaimControls.readers_share
#print axioms ClaimControls.reader_and_taker
#print axioms ClaimControls.seeThenTake_positive
#print axioms ClaimControls.seeThenTake_two_tokens
#print axioms ClaimControls.seeThenTake_one_token
#print axioms ClaimControls.takers_instances
#print axioms ClaimControls.addition_and_removal
#print axioms ClaimControls.taken_instances
#print axioms ClaimControls.claimsAvailable_instances
#print axioms ClaimControls.seeThenTake_on_claims
#print axioms ClaimControls.programs_on_claims
#print axioms ClaimControls.claims_accept_the_monotone
#print axioms ClaimControls.claims_order_matters_for_an_absence_guard

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions
