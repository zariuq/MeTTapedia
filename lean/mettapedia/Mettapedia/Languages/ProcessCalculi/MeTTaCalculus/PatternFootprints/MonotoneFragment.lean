import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.PatternFootprints.Deltas
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.PatternFootprints.MatchReadings

/-!
# The monotone fragment

A region is **monotone** when it is built from additions and positive reads only:
every step consumes nothing and has a guard that no addition to the state
disables (`Step.Monotone`), and every answer reads nothing, so that it is known
from which alternative answered (`Region.Monotone`, `Proposal.Monotone`).  The
setting is a separation algebra in which every two resources are separate
(`AllSeparate`); "a larger state" is a state with something added.

A region is **positive** when no addition disables a guard of it and every answer
reads nothing (`Region.Positive`); it may remove.  A monotone region is a positive
region that only adds (`Region.Monotone.positive`).

For a monotone region:

* `Region.Positive.branchLocal_sublist`: **every outcome from a snapshot is an
  outcome from every larger state**, in the same order and as often.  This law
  holds of every positive region, removals included.
* `Region.Monotone.wave_every_order`: **all proposals publish together, in every
  order, to one state**, from the snapshot and from every larger state, each
  validated by replay when its turn comes; and every such order is the committed
  run of the alternatives that answered, with the answers that were returned.
  No footprint is compared: the fragment needs no validation.  It is the wave of
  deltas (`wave_of_deltas_every_order`) where nothing is left to compare.
* `Proposal.stableUnder_of_positive_or_apart`: outside the fragment, only the
  steps that are not positive are compared with the locations that an addition
  touches; for the wave of deltas, with what another proposal writes.
* `Region.Monotone.answers_sublist_committed`: **the committed run of the region
  from the snapshot has every one of these answers**, in order; and possibly
  more (`MonotoneControls.committed_has_more`): an alternative without an outcome
  from the snapshot may have one after the additions of the others.  The state
  only grows (`Region.Monotone.committed_state`).

So what a serial run adds to the branch-local run of a monotone region are
further answers and no withdrawal of one, and running the region again from the
published state returns every earlier outcome
(`Region.Positive.branchLocal_sublist` at what was added).  This is forward
chaining to saturation; at the grain of a resource system it is
`GSLT.Causality.ResourceInteraction.inference_conflictFree`.

Three operations leave the fragment, and each breaks a law of it.  They do not
leave it alike.  A removal keeps the first law: its outcomes from a snapshot are
outcomes from every larger state (`MonotoneControls.positive_instances`); it
breaks the other two, because removals compete for occurrences.  A complete read
and a guard that asks for absence break the first law.

* **A removal** (`removeKind_not_monotone`).  Two takers of one token both
  answer from the snapshot; they are not published together, and the committed
  run has one of the two answers (`MonotoneControls.removal_leaves_the_fragment`).
* **A complete read** (an answer that reads).  The answer read from a snapshot is
  not the answer from a larger state, and the committed run of two siblings that
  each add an atom and read the pattern has an answer that neither gave from the
  snapshot and lacks one that was given
  (`MonotoneControls.complete_read_leaves_the_fragment`).
* **A guard that asks for absence** (`addKindUnless_not_monotone`).  Its outcome
  from a snapshot is no outcome from a larger state, and with the addition it
  watches it is published in one order and refused in the other
  (`MonotoneControls.absence_guard_leaves_the_fragment`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.FootprintedSpaceTransactions
open Mettapedia.GSLT.SeparationAlgebra

universe u v w

variable {Location : Type u} {Value : Type v} {Answer : Type w}

/-- An answer that reads nothing is the same from every state. -/
theorem Readout.value_eq_of_reads_empty [DecidableEq Location]
    {readout : Readout Location Value Answer} (constant : readout.reads = ∅)
    (state other : Location → Value) : readout.value state = readout.value other :=
  readout.value_local
    (constant ▸ fun location inside => absurd inside (Finset.notMem_empty location))

section Fragment

variable [DecidableEq Location] [Zero Value] [Add Value] [SepAlgebra Value]

/-! ## Positive regions -/

/-- **A positive proposal**: no addition to the state disables a guard of it, and
its answer reads nothing.  Its steps may consume. -/
structure Proposal.Positive (proposal : Proposal Location Value Answer) : Prop where
  steps : ∀ step ∈ proposal.steps, step.Positive
  constant : proposal.readout.reads = ∅

/-- **A positive region**: every step is positive and every answer reads nothing.
Removals and cell writes are admitted; guards that ask for an absence and answers
that read are not. -/
inductive Region.Positive : Region Location Value Answer → Prop
  | fail : Region.Positive .fail
  | answer {readout : Readout Location Value Answer} (constant : readout.reads = ∅) :
      Region.Positive (.answer readout)
  | step {first : Step Location Value} {rest : Region Location Value Answer}
      (positive : first.Positive) (restPositive : Region.Positive rest) :
      Region.Positive (.step first rest)
  | orElse {left right : Region Location Value Answer} (leftPositive : Region.Positive left)
      (rightPositive : Region.Positive right) : Region.Positive (.orElse left right)

/-- A positive proposal is stable under every addition. -/
theorem Proposal.Positive.stableUnder {proposal : Proposal Location Value Answer}
    (positive : proposal.Positive) (added : Location → Value) : proposal.StableUnder added :=
  fun step member state => positive.steps step member state added

/-- The alternatives of a positive region are positive proposals. -/
theorem Region.Positive.proposal_positive {region : Region Location Value Answer}
    (positive : region.Positive) {proposal : Proposal Location Value Answer}
    (member : proposal ∈ region.proposals) : proposal.Positive := by
  induction positive generalizing proposal with
  | fail => cases member
  | answer constant =>
      rw [Region.proposals, List.mem_singleton] at member
      subst member
      exact ⟨fun _ inside => (nomatch inside), constant⟩
  | @step first rest stepPositive _ ih =>
      rw [Region.proposals, List.mem_map] at member
      obtain ⟨inner, innerMember, rfl⟩ := member
      have innerPositive := ih innerMember
      refine ⟨fun step inside => ?_, innerPositive.constant⟩
      rcases List.mem_cons.mp inside with rfl | later
      · exact stepPositive
      · exact innerPositive.steps step later
  | orElse _ _ ihLeft ihRight =>
      rw [Region.proposals, List.mem_append] at member
      rcases member with inLeft | inRight
      · exact ihLeft inLeft
      · exact ihRight inRight

/-! ## Monotone regions -/

/-- **A monotone step**: an addition that is positive: it consumes nothing, and no
addition to the state disables its guard.  An addition without a guard and a read
of a presence are such. -/
structure Step.Monotone (step : Step Location Value) : Prop where
  isAddition : step.IsAddition
  positive : step.Positive

/-- **A monotone proposal**: its steps are monotone and its answer reads
nothing. -/
structure Proposal.Monotone (proposal : Proposal Location Value Answer) : Prop where
  steps : ∀ step ∈ proposal.steps, step.Monotone
  constant : proposal.readout.reads = ∅

/-- **A monotone region**: every step is monotone and every answer reads
nothing. -/
inductive Region.Monotone : Region Location Value Answer → Prop
  | fail : Region.Monotone .fail
  | answer {readout : Readout Location Value Answer} (constant : readout.reads = ∅) :
      Region.Monotone (.answer readout)
  | step {first : Step Location Value} {rest : Region Location Value Answer}
      (monotone : first.Monotone) (restMonotone : Region.Monotone rest) :
      Region.Monotone (.step first rest)
  | orElse {left right : Region Location Value Answer} (leftMonotone : Region.Monotone left)
      (rightMonotone : Region.Monotone right) : Region.Monotone (.orElse left right)

theorem Proposal.Monotone.isDelta {proposal : Proposal Location Value Answer}
    (monotone : proposal.Monotone) : proposal.IsDelta :=
  fun step member => (monotone.steps step member).isAddition

/-- A monotone proposal is positive. -/
theorem Proposal.Monotone.positive {proposal : Proposal Location Value Answer}
    (monotone : proposal.Monotone) : proposal.Positive :=
  ⟨fun step member => (monotone.steps step member).positive, monotone.constant⟩

/-- A monotone region is positive. -/
theorem Region.Monotone.positive {region : Region Location Value Answer}
    (monotone : region.Monotone) : region.Positive := by
  induction monotone with
  | fail => exact .fail
  | answer constant => exact .answer constant
  | step stepMonotone _ ih => exact .step stepMonotone.positive ih
  | orElse _ _ ihLeft ihRight => exact .orElse ihLeft ihRight

/-- **Two monotone proposals are independent by deltas**, whatever they read and
write. -/
theorem Proposal.Monotone.deltaIndependent {first second : Proposal Location Value Answer}
    (firstMonotone : first.Monotone) (secondMonotone : second.Monotone) :
    first.DeltaIndependent second :=
  ⟨firstMonotone.positive.stableUnder _, secondMonotone.positive.stableUnder _⟩

/-- **Two monotone proposals are compatible by deltas, answers included**: no
answer reads. -/
theorem Proposal.Monotone.deltaCompatible {first second : Proposal Location Value Answer}
    (firstMonotone : first.Monotone) (secondMonotone : second.Monotone) :
    first.DeltaCompatible second :=
  ⟨firstMonotone.deltaIndependent secondMonotone,
    firstMonotone.constant ▸ Finset.disjoint_empty_right _,
    secondMonotone.constant ▸ Finset.disjoint_empty_right _⟩

/-- The alternatives of a monotone region are monotone proposals. -/
theorem Region.Monotone.proposal_monotone {region : Region Location Value Answer}
    (monotone : region.Monotone) {proposal : Proposal Location Value Answer}
    (member : proposal ∈ region.proposals) : proposal.Monotone := by
  induction monotone generalizing proposal with
  | fail => cases member
  | answer constant =>
      rw [Region.proposals, List.mem_singleton] at member
      subst member
      exact ⟨fun _ inside => (nomatch inside), constant⟩
  | @step first rest stepMonotone _ ih =>
      rw [Region.proposals, List.mem_map] at member
      obtain ⟨inner, innerMember, rfl⟩ := member
      have innerMonotone := ih innerMember
      refine ⟨fun step inside => ?_, innerMonotone.constant⟩
      rcases List.mem_cons.mp inside with rfl | later
      · exact stepMonotone
      · exact innerMonotone.steps step later
  | orElse _ _ ihLeft ihRight =>
      rw [Region.proposals, List.mem_append] at member
      rcases member with inLeft | inRight
      · exact ihLeft inLeft
      · exact ihRight inRight

/-- Siblings are a monotone region exactly when each of them is. -/
theorem Region.monotone_alternatives_iff {siblings : List (Region Location Value Answer)} :
    (Region.alternatives siblings).Monotone ↔ ∀ sibling ∈ siblings, sibling.Monotone := by
  induction siblings with
  | nil => exact ⟨fun _ _ inside => (nomatch inside), fun _ => Region.Monotone.fail⟩
  | cons sibling rest ih =>
      constructor
      · intro monotone
        have split : Region.Monotone (.orElse sibling (Region.alternatives rest)) := monotone
        cases split with
        | orElse headMonotone restMonotone =>
            intro other inside
            rcases List.mem_cons.mp inside with rfl | later
            · exact headMonotone
            · exact ih.mp restMonotone other later
      · intro all
        exact .orElse (all sibling List.mem_cons_self)
          (ih.mpr fun other inside => all other (List.mem_cons_of_mem sibling inside))

variable [AllSeparate Value]

/-- **The outcome of a positive proposal from a state is its outcome from every
larger state.**  The proposal may remove. -/
theorem Proposal.Positive.outcome?_add {proposal : Proposal Location Value Answer}
    (positive : proposal.Positive) {state : Location → Value}
    {outcome : Answer × Proposal Location Value Answer}
    (explored : proposal.outcome? state = some outcome) (added : Location → Value) :
    proposal.outcome? (state + added) = some outcome :=
  (positive.stableUnder added).outcome?_add
    (fun location inside => absurd (positive.constant ▸ inside) (Finset.notMem_empty location))
    explored

omit [AllSeparate Value] in
/-- **A proposal whose every step is positive, or apart from what an addition
touches, is stable under that addition.**  Only the guards that an addition can
disable are compared with the locations it touches. -/
theorem Proposal.stableUnder_of_positive_or_apart {proposal : Proposal Location Value Answer}
    {added : Location → Value} {touched : Finset Location}
    (untouched : ∀ location, location ∉ touched → added location = 0)
    (each : ∀ step ∈ proposal.steps,
      step.Positive ∨ Disjoint touched (step.rule.reads ∪ step.rule.writes)) :
    proposal.StableUnder added := by
  intro step member state guarded
  rcases each step member with positive | apart
  · exact positive state _ guarded
  · refine step.rule.guard_local (fun location inside => ?_) guarded
    have outside : location ∉ touched := fun written =>
      Finset.disjoint_left.mp apart written inside
    show state location = state location + added location
    rw [untouched location outside, SepAlgebra.add_zero]

omit [AllSeparate Value] in
/-- So it is stable under what another proposal adds, when each of its steps is
positive or apart from what that proposal writes. -/
example {proposal other : Proposal Location Value Answer}
    (each : ∀ step ∈ proposal.steps,
      step.Positive ∨ Disjoint other.writes (step.rule.reads ∪ step.rule.writes)) :
    proposal.StableUnder other.added :=
  Proposal.stableUnder_of_positive_or_apart
    (fun _ outside => stepsAdded_outside other.steps outside) each

/-- **Every outcome of a positive region from a snapshot is an outcome from every
larger state**: the outcomes from the snapshot are, in order and as often, among
the outcomes from the larger state.  The region may remove: an addition takes
nothing away. -/
theorem Region.Positive.branchLocal_sublist {region : Region Location Value Answer}
    (positive : region.Positive) (state added : Location → Value) :
    (region.branchLocal state).Sublist (region.branchLocal (state + added)) := by
  induction positive generalizing state with
  | fail => exact List.Sublist.refl _
  | @answer readout constant =>
      show [(readout.value state, (⟨[], readout⟩ : Proposal Location Value Answer))].Sublist
        [(readout.value (state + added), ⟨[], readout⟩)]
      rw [Readout.value_eq_of_reads_empty constant (state + added) state]
  | @step first rest stepPositive _ ih =>
      cases fired : first.fire state with
      | none =>
          simp only [Region.branchLocal, fired]
          exact List.nil_sublist _
      | some next =>
          simp only [Region.branchLocal, fired, stepPositive.fire_add fired added]
          exact (ih next).map _
  | orElse _ _ ihLeft ihRight => exact (ihLeft state).append (ihRight state)

/-- **The committed run of a monotone region only adds to the state.** -/
theorem Region.Monotone.committed_state {region : Region Location Value Answer}
    (monotone : region.Monotone) (world : Location → Value) :
    ∃ more, (region.committed world).2 = world + more := by
  induction monotone generalizing world with
  | fail => exact ⟨0, (SepAlgebra.add_zero world).symm⟩
  | answer _ => exact ⟨0, (SepAlgebra.add_zero world).symm⟩
  | @step first rest stepMonotone _ ih =>
      cases fired : first.fire world with
      | none =>
          simp only [Region.committed, fired]
          exact ⟨0, (SepAlgebra.add_zero world).symm⟩
      | some next =>
          simp only [Region.committed, fired]
          obtain ⟨more, same⟩ := ih next
          refine ⟨first.rule.produced + more, ?_⟩
          rw [same, (stepMonotone.isAddition.eq_add fired).2]
          exact AllSeparate.add_assoc _ _ _
  | @orElse left right _ _ ihLeft ihRight =>
      obtain ⟨leftMore, leftSame⟩ := ihLeft world
      obtain ⟨rightMore, rightSame⟩ := ihRight (left.committed world).2
      refine ⟨leftMore + rightMore, ?_⟩
      show (right.committed (left.committed world).2).2 = _
      rw [rightSame, leftSame]
      exact AllSeparate.add_assoc _ _ _

/-- **The committed run of a monotone region has every answer of its branch-local
run**, in order: from the snapshot, and from every larger state. -/
theorem Region.Monotone.answers_sublist_committed {region : Region Location Value Answer}
    (monotone : region.Monotone) (snapshot added : Location → Value) :
    ((region.branchLocal snapshot).map Prod.fst).Sublist
      (region.committed (snapshot + added)).1 := by
  induction monotone generalizing snapshot added with
  | fail => exact List.nil_sublist _
  | @answer readout constant =>
      show [readout.value snapshot].Sublist [readout.value (snapshot + added)]
      rw [Readout.value_eq_of_reads_empty constant (snapshot + added) snapshot]
  | @step first rest stepMonotone _ ih =>
      cases fired : first.fire snapshot with
      | none =>
          simp only [Region.branchLocal, fired]
          exact List.nil_sublist _
      | some next =>
          simp only [Region.branchLocal, Region.committed, fired,
            stepMonotone.positive.fire_add fired added, List.map_map]
          exact ih next added
  | @orElse left right leftMonotone _ ihLeft ihRight =>
      obtain ⟨more, same⟩ := leftMonotone.committed_state (snapshot + added)
      show ((left.branchLocal snapshot ++ right.branchLocal snapshot).map Prod.fst).Sublist
        ((left.committed (snapshot + added)).1 ++
          (right.committed (left.committed (snapshot + added)).2).1)
      rw [List.map_append, same, AllSeparate.add_assoc]
      exact (ihLeft snapshot added).append (ihRight snapshot (added + more))

/-- **All proposals of a monotone region publish together**, in every order,
from the snapshot and from every larger state, to the state with all they add. -/
theorem Region.Monotone.publishAll_perm {region : Region Location Value Answer}
    (monotone : region.Monotone) (snapshot added : Location → Value)
    {order : List (Proposal Location Value Answer)}
    (perm : ((region.branchLocal snapshot).map Prod.snd).Perm order) :
    publishAll order (snapshot + added) =
      some (snapshot + added +
        stepsAdded (((region.branchLocal snapshot).map Prod.snd).flatMap fun proposal =>
          proposal.steps)) := by
  have proposalMonotone : ∀ proposal ∈ order, proposal.Monotone := by
    intro proposal member
    obtain ⟨outcome, explored, rfl⟩ := List.mem_map.mp (perm.mem_iff.mpr member)
    exact monotone.proposal_monotone (Region.mem_branchLocal_iff.mp explored).1
  rw [publishAll_of_deltaIndependent
      (fun proposal member => (proposalMonotone proposal member).isDelta)
      (List.pairwise_of_forall_mem_list fun first firstMember second secondMember =>
        (proposalMonotone first firstMember).deltaIndependent
          (proposalMonotone second secondMember))
      (fun proposal member => by
        obtain ⟨outcome, explored, rfl⟩ := List.mem_map.mp (perm.mem_iff.mpr member)
        obtain ⟨view, published, -⟩ := Region.committed_of_mem_branchLocal explored
        rw [((proposalMonotone outcome.2 member).positive.stableUnder added).publish_add
          published]
        rfl),
    stepsAdded_perm (perm.flatMap_right _).symm]

/-- **The monotone fragment needs no validation.**  The outcomes of a monotone
region from a snapshot are published in every order, from the snapshot and from
every larger state, each validated by replay when its turn comes; every order
reaches the state with all that the proposals add; and every order is the
committed run of the alternatives that answered, with the answers returned. -/
theorem Region.Monotone.wave_every_order [DecidableEq Answer]
    {region : Region Location Value Answer} (monotone : region.Monotone)
    (snapshot added : Location → Value) {order : List (Answer × Proposal Location Value Answer)}
    (perm : (region.branchLocal snapshot).Perm order) :
    publishInOrder order (snapshot + added) =
        some (snapshot + added +
          stepsAdded (((region.branchLocal snapshot).map Prod.snd).flatMap fun proposal =>
            proposal.steps)) ∧
      (Region.alternatives (order.map fun outcome => outcome.2.region)).committed
          (snapshot + added) =
        (order.map Prod.fst, snapshot + added +
          stepsAdded (((region.branchLocal snapshot).map Prod.snd).flatMap fun proposal =>
            proposal.steps)) := by
  have proposalMonotone : ∀ outcome ∈ region.branchLocal snapshot, outcome.2.Monotone :=
    fun outcome member => monotone.proposal_monotone (Region.mem_branchLocal_iff.mp member).1
  exact wave_of_deltas_every_order
    (fun outcome member => (proposalMonotone outcome member).isDelta)
    (List.pairwise_of_forall_mem_list fun first firstMember second secondMember =>
      (proposalMonotone first firstMember).deltaCompatible (proposalMonotone second secondMember))
    (fun outcome member =>
      (proposalMonotone outcome member).positive.outcome?_add
        (Region.mem_branchLocal_iff.mp member).2 added)
    perm

end Fragment

/-! ## The steps at the grain of kinds -/

section Kinds

variable [DecidableEq Location]

/-- **An addition of a kind is monotone.** -/
theorem addKind_monotone (kind : Location) : (addKind kind).Monotone :=
  ⟨addKind_isAddition kind, addKind_positive kind⟩

/-- **A read of a presence is monotone.** -/
theorem seeKind_monotone (kind : Location) : (seeKind kind).Monotone :=
  ⟨seeKind_isAddition kind, seeKind_positive kind⟩

/-- **A removal is not monotone**: it consumes. -/
theorem removeKind_not_monotone (kind : Location) : ¬ (removeKind kind).Monotone :=
  fun monotone => removeKind_not_isAddition kind monotone.isAddition

/-- **The write of a cell is not monotone**: it consumes the old value. -/
theorem replaceKind_not_monotone (old new : Location) : ¬ (replaceKind old new).Monotone := by
  intro monotone
  have consumes : marking ({old} : Multiset Location) = 0 := monotone.isAddition
  have atOld := congrFun consumes old
  rw [marking_singleton] at atOld
  simp at atOld

/-- **A guard that asks for absence is not monotone**: the addition of the kind
it watches disables it. -/
theorem addKindUnless_not_monotone (kind watched : Location) :
    ¬ (addKindUnless kind watched).Monotone :=
  fun monotone => addKindUnless_not_positive kind watched monotone.positive

/-- One answer of a match is a monotone proposal. -/
theorem oneAnswer_monotone (kind : Location) (answer : Answer) :
    (oneAnswer kind answer).Monotone :=
  ⟨fun step member => by
      rw [List.mem_singleton.mp member]
      exact seeKind_monotone kind,
    rfl⟩

/-- **A match over candidate kinds is a monotone region.** -/
theorem Region.matchKinds_monotone (candidates : List (Location × Answer)) :
    (Region.matchKinds candidates).Monotone := by
  refine Region.monotone_alternatives_iff.mpr fun sibling member => ?_
  obtain ⟨candidate, -, rfl⟩ := List.mem_map.mp member
  exact .step (seeKind_monotone candidate.1) (.answer rfl)

end Kinds

/-! ## Controls -/

namespace MonotoneControls

open AddOnly (Kind noKinds kindReader)
open KindControls (oneA)

/-- Add an `a` and answer `1`. -/
def adder : Region Kind ℕ ℕ :=
  .step (addKind .a) (.answer (Readout.const 1))

/-- If an `a` is there, add a `b` and answer `2`: a rule that reads its premise. -/
def rule : Region Kind ℕ ℕ :=
  .step (seeKind .a) (.step (addKind .b) (.answer (Readout.const 2)))

/-- The two as siblings. -/
def chain : Region Kind ℕ ℕ :=
  Region.alternatives [adder, rule]

/-- **Positive, a monotone region.** -/
theorem chain_monotone : chain.Monotone :=
  Region.monotone_alternatives_iff.mpr fun sibling member => by
    rcases List.mem_cons.mp member with rfl | later
    · exact .step (addKind_monotone _) (.answer rfl)
    · rw [List.mem_singleton.mp later]
      exact .step (seeKind_monotone _) (.step (addKind_monotone _) (.answer rfl))

/-- **Positive, a monotone proposal**: one answer of a match.  **Negative**: the
proposal that takes an `a`. -/
theorem proposal_instances :
    (oneAnswer Kind.a ()).Monotone ∧
      ¬ (⟨[removeKind Kind.a], Readout.const ()⟩ : Proposal Kind ℕ Unit).Monotone :=
  ⟨oneAnswer_monotone _ _, fun monotone =>
    removeKind_not_monotone Kind.a (monotone.steps _ List.mem_cons_self)⟩

/-- **The committed run has more.**  From the empty state only the adder has an
outcome; the committed run answers for the rule as well, which finds the `a` the
adder left.  From the state the adder publishes, the rule has its outcome too. -/
theorem committed_has_more :
    (chain.branchLocal noKinds).map Prod.fst = [1] ∧ (chain.committed noKinds).1 = [1, 2] ∧
      (chain.branchLocal oneA).map Prod.fst = [1, 2] := by
  decide

/-- An instance of `Region.Monotone.answers_sublist_committed`. -/
theorem chain_answers_sublist :
    ((chain.branchLocal noKinds).map Prod.fst).Sublist (chain.committed noKinds).1 := by
  have sublist := chain_monotone.answers_sublist_committed noKinds 0
  rwa [add_zero] at sublist

/-- Take an `a` and answer. -/
def take (who : ℕ) : Region Kind ℕ ℕ :=
  .step (removeKind .a) (.answer (Readout.const who))

/-- **A removal leaves the fragment.**  Two takers of one `a` are not a monotone
region.  Both answer from the snapshot; their proposals are not published
together; and the committed run has one of the two answers. -/
theorem removal_leaves_the_fragment :
    ¬ (Region.alternatives [take 1, take 2]).Monotone ∧
      ((Region.alternatives [take 1, take 2]).branchLocal oneA).map Prod.fst = [1, 2] ∧
      (publishAll (((Region.alternatives [take 1, take 2]).branchLocal oneA).map Prod.snd)
        oneA).isSome = false ∧
      ((Region.alternatives [take 1, take 2]).committed oneA).1 = [1] := by
  refine ⟨fun monotone => ?_, by decide, by decide, by decide⟩
  have first := Region.monotone_alternatives_iff.mp monotone (take 1) List.mem_cons_self
  cases first with
  | step stepMonotone _ => exact removeKind_not_monotone Kind.a stepMonotone

/-- **A complete read leaves the fragment.**  Two siblings each add an atom and
answer with the multiplicities of both kinds.  The region is not monotone: the
answer reads.  The answer of a sibling from the snapshot is not its answer from a
larger state; and the committed run has an answer that neither sibling gave from
the snapshot and lacks one that was given. -/
theorem complete_read_leaves_the_fragment :
    ¬ (Region.alternatives [kindReader .a, kindReader .b]).Monotone ∧
      ((kindReader .a).branchLocal noKinds).map Prod.fst = [(1, 0)] ∧
      ((kindReader .a).branchLocal (noKinds + Pi.single Kind.b 1)).map Prod.fst = [(1, 1)] ∧
      ((Region.alternatives [kindReader .a, kindReader .b]).branchLocal noKinds).map Prod.fst =
        [(1, 0), (0, 1)] ∧
      ((Region.alternatives [kindReader .a, kindReader .b]).committed noKinds).1 =
        [(1, 0), (1, 1)] := by
  refine ⟨fun monotone => ?_, by decide, by decide, by decide, by decide⟩
  have first := Region.monotone_alternatives_iff.mp monotone (kindReader .a) List.mem_cons_self
  cases first with
  | step _ restMonotone =>
      cases restMonotone with
      | answer constant => exact absurd constant (by decide)

/-- Add a `b` unless an `a` is there, and answer. -/
def guarded : Region Kind ℕ Unit :=
  .step (addKindUnless .b .a) (.answer (Readout.const ()))

/-- Add an `a`, and answer. -/
def marker : Region Kind ℕ Unit :=
  .step (addKind .a) (.answer (Readout.const ()))

/-- **A guard that asks for absence leaves the fragment.**  The guarded addition
is not a monotone region.  It has an outcome from the empty state and none from
the larger state with an `a`; and with the addition of that `a` it is published
in one order and refused in the other. -/
theorem absence_guard_leaves_the_fragment :
    ¬ guarded.Monotone ∧
      (guarded.branchLocal noKinds).length = 1 ∧ (guarded.branchLocal oneA).length = 0 ∧
      (publishAll ((guarded.branchLocal noKinds).map Prod.snd ++
        (marker.branchLocal noKinds).map Prod.snd) noKinds).isSome = true ∧
      (publishAll ((marker.branchLocal noKinds).map Prod.snd ++
        (guarded.branchLocal noKinds).map Prod.snd) noKinds).isSome = false := by
  refine ⟨fun monotone => ?_, by decide, by decide, by decide, by decide⟩
  cases monotone with
  | step stepMonotone _ => exact addKindUnless_not_monotone Kind.b Kind.a stepMonotone

/-- **Positive, a positive proposal**: the proposal that takes an `a`: it removes,
and no addition disables it.  **Negative**: the proposal that adds a `b` unless an
`a` is there. -/
theorem positive_proposal_instances :
    (⟨[removeKind Kind.a], Readout.const ()⟩ : Proposal Kind ℕ Unit).Positive ∧
      ¬ (⟨[addKindUnless Kind.b Kind.a], Readout.const ()⟩ : Proposal Kind ℕ Unit).Positive :=
  ⟨⟨fun step member => by
      rw [List.mem_singleton.mp member]
      exact removeKind_positive Kind.a,
    rfl⟩,
    fun positive => addKindUnless_not_positive Kind.b Kind.a (positive.steps _ List.mem_cons_self)⟩

/-- **Positive, a positive region**: two takers of an `a`.  They remove, so the
region is not monotone; and no addition disables them: their outcomes from the
state with one `a` are outcomes from the state with two.  **Negative**: the guarded
addition is not a positive region. -/
theorem positive_instances :
    (Region.alternatives [take 1, take 2]).Positive ∧
      ¬ (Region.alternatives [take 1, take 2]).Monotone ∧
      ((Region.alternatives [take 1, take 2]).branchLocal oneA).Sublist
        ((Region.alternatives [take 1, take 2]).branchLocal (oneA + oneA)) ∧
      ¬ guarded.Positive := by
  have positive : (Region.alternatives [take 1, take 2]).Positive :=
    .orElse (.step (removeKind_positive _) (.answer rfl))
      (.orElse (.step (removeKind_positive _) (.answer rfl)) .fail)
  refine ⟨positive, removal_leaves_the_fragment.1, positive.branchLocal_sublist oneA oneA,
    fun guardedPositive => ?_⟩
  cases guardedPositive with
  | step stepPositive _ => exact addKindUnless_not_positive Kind.b Kind.a stepPositive

/-- **Positive, no validation**: the two outcomes of the chain from the state
with an `a` are published in both orders, to one state. -/
theorem chain_publishes_in_both_orders :
    (publishInOrder (chain.branchLocal oneA) oneA).map (fun world => (world .a, world .b)) =
        some (2, 1) ∧
      (publishInOrder (chain.branchLocal oneA).reverse oneA).map
        (fun world => (world .a, world .b)) = some (2, 1) := by
  decide

end MonotoneControls

#print axioms Region.Monotone.proposal_monotone
#print axioms Region.monotone_alternatives_iff
#print axioms Region.Positive.proposal_positive
#print axioms Region.Monotone.positive
#print axioms Proposal.Monotone.deltaIndependent
#print axioms Proposal.Positive.outcome?_add
#print axioms Region.Positive.branchLocal_sublist
#print axioms Region.Monotone.committed_state
#print axioms Region.Monotone.answers_sublist_committed
#print axioms Region.Monotone.publishAll_perm
#print axioms Proposal.Monotone.deltaCompatible
#print axioms Proposal.stableUnder_of_positive_or_apart
#print axioms Region.Monotone.wave_every_order
#print axioms addKind_monotone
#print axioms seeKind_monotone
#print axioms removeKind_not_monotone
#print axioms replaceKind_not_monotone
#print axioms addKindUnless_not_monotone
#print axioms oneAnswer_monotone
#print axioms Region.matchKinds_monotone
#print axioms MonotoneControls.chain_monotone
#print axioms MonotoneControls.proposal_instances
#print axioms MonotoneControls.committed_has_more
#print axioms MonotoneControls.chain_answers_sublist
#print axioms MonotoneControls.removal_leaves_the_fragment
#print axioms MonotoneControls.complete_read_leaves_the_fragment
#print axioms MonotoneControls.absence_guard_leaves_the_fragment
#print axioms MonotoneControls.positive_proposal_instances
#print axioms MonotoneControls.positive_instances
#print axioms MonotoneControls.chain_publishes_in_both_orders

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions
