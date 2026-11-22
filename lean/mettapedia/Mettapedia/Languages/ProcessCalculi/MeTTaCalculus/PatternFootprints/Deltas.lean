import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.PatternFootprints.Kinds
import Mettapedia.GSLT.Dynamics.ContextualDeltaHandlers

/-!
# Additions as deltas

Two steps that each add an atom to one space write one location.  By read and
write sets they are not independent, and yet they commute: multiplicities add,
and addition is commutative.  This module states independence for proposals
whose steps only add, so that it sees this, and compares it with independence by
read and write sets and with the merge by join.

The setting is a separation algebra in which every two resources are separate
(`AllSeparate`): a commutative monoid.  Multiplicities, bags, and families of
them are such; exclusive cells are not (`not_allSeparate_excl`).

* `Step.IsAddition`: a step that consumes nothing.  When it fires it adds what it
  produces (`Step.IsAddition.fire_eq_some_iff`).  `stepsAdded`, `Proposal.added`:
  what a list of steps, a proposal, adds.  `Proposal.IsDelta`: every step is an
  addition; then publication adds the delta (`Proposal.IsDelta.publish_eq_add`).
* `Proposal.StableUnder`: an addition to the state disables no guard of the
  proposal.  `Proposal.DeltaIndependent`: each of two proposals is stable under
  what the other adds.  Written locations may be shared.
* `Step.fire_add_of_guard`, `Proposal.StableUnder.publish_add`: **the frame
  rule.**  What fires on a state fires on a larger state on which its guards still
  hold, with the same change, and what was added is carried along.  It holds of a
  step that consumes as of one that adds (`fire_removeKind_add`).  A step whose
  guard no addition disables is positive (`Step.Positive`): an addition, a
  removal, a cell write, a read of a presence are; a guard that asks for an
  absence is not (`addKindUnless_not_positive`).
* `Proposal.DeltaIndependent.publish_comm`: **two delta proposals that are
  independent by deltas, published from one state on which both publish, commute.**
  `publishAll_of_deltaIndependent`, `publishAll_perm_of_deltaIndependent`: any
  number of them, independent in pairs, publish from that state in every order to
  the state with all the deltas added.
* `Proposal.DeltaCompatible`, `wave_of_deltas_every_order`: with the answers.
  Proposals by deltas that are independent by deltas, and of which none writes
  what the answer of another reads, are published in every order, each validated
  by replay, and every order is a serial committed run with the answers returned.
  What is compared is only what an addition can invalidate.
* **Comparison with read and write sets.**  Independence by sets implies
  independence by deltas (`Proposal.Independent.deltaIndependent`).  The converse
  fails: two additions of one kind (`DeltaControls.same_kind_additions`), two
  additions to one space (`DeltaControls.same_space_additions`).  Independence by sets
  says more where it holds: from every state both orders publish to one state or
  both are refused (`publish_comm_of_independent`).  Independence by
  deltas says it only from a state on which both publish: an addition may enable
  a positive read, and then one order publishes and the other is refused
  (`DeltaControls.addition_enables_read`).
* **Comparison with the merge by join.**  `sumMerge` merges deltas by their sum,
  in every order, and the published state of a wave of delta proposals is the
  enclosing state with that sum (`publishAll_eq_sumMerge`).  The join of two
  deltas of multiplicities is their sum exactly when no location is added by both
  (`sup_eq_add_iff`): that is the case the read and write sets accept.  Where two
  proposals add one kind, the join keeps one occurrence and the publication has
  two (`DeltaControls.join_forgets_multiplicity`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.FootprintedSpaceTransactions
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SpaceInteraction
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Dynamics.MonotoneWorldHandler (joinDeltas sumDeltas)
open Mettapedia.GSLT.Dynamics.ContextualDeltaHandlers (AlternativeMerge joinMerge)

universe u v w

variable {Location : Type u} {Value : Type v} {Answer : Type w}

/-! ## Commutative monoids among the separation algebras -/

/-- **Every two resources are separate.**  The laws of a separation algebra then
hold without condition: the algebra is a commutative monoid. -/
class AllSeparate (Value : Type v) [Zero Value] [Add Value] [SepAlgebra Value] : Prop where
  separate : ∀ first second : Value, first ## second

namespace AllSeparate

variable [Zero Value] [Add Value] [SepAlgebra Value] [AllSeparate Value]

protected theorem add_comm (first second : Value) : first + second = second + first :=
  SepAlgebra.add_comm (separate first second)

protected theorem add_assoc (first second third : Value) :
    first + second + third = first + (second + third) :=
  SepAlgebra.add_assoc (separate first second) (separate second third) (separate first third)

protected theorem add_right_comm (first second third : Value) :
    first + second + third = first + third + second := by
  rw [AllSeparate.add_assoc, AllSeparate.add_comm second third, ← AllSeparate.add_assoc]

protected theorem add_left_comm (first second third : Value) :
    first + (second + third) = second + (first + third) := by
  rw [← AllSeparate.add_assoc, AllSeparate.add_comm first second, AllSeparate.add_assoc]

end AllSeparate

/-- Multiplicities. -/
instance instAllSeparateNat : AllSeparate ℕ :=
  ⟨fun _ _ => trivial⟩

/-- Bags. -/
instance instAllSeparateMultiset {Atom : Type v} : AllSeparate (Multiset Atom) :=
  ⟨fun _ _ => trivial⟩

/-- A family of them, at every location. -/
instance instAllSeparatePi [Zero Value] [Add Value] [SepAlgebra Value] [AllSeparate Value] :
    AllSeparate (Location → Value) :=
  ⟨fun _ _ _ => AllSeparate.separate _ _⟩

/-- **Negative**: exclusive cells are not such an algebra: two owned values are
not separate. -/
theorem not_allSeparate_excl : ¬ AllSeparate (Excl ℕ) := fun total =>
  Excl.not_separate_own 0 0 (total.separate _ _)

/-! ## Additions -/

section Additions

variable [DecidableEq Location] [Zero Value] [Add Value] [SepAlgebra Value]

/-- **An addition**: a step that consumes nothing.  Its guard may still ask
anything that is local. -/
def Step.IsAddition (step : Step Location Value) : Prop :=
  step.rule.consumed = 0

/-- An addition that fires had its guard, and adds what it produces. -/
theorem Step.IsAddition.eq_add {step : Step Location Value} (addition : step.IsAddition)
    {state target : Location → Value} (fires : step.fire state = some target) :
    step.rule.guard state ∧ target = state + step.rule.produced := by
  obtain ⟨guarded, frame, -, producedSeparate, sourceEq, targetEq⟩ :=
    step.fire_eq_some_iff.mp fires
  rw [show step.rule.consumed = 0 from addition, SepAlgebra.zero_add] at sourceEq
  subst sourceEq
  exact ⟨guarded, targetEq.trans (SepAlgebra.add_comm producedSeparate)⟩

/-- **An addition fires exactly when its guard holds, and adds what it
produces.** -/
theorem Step.IsAddition.fire_eq_some_iff [AllSeparate Value] {step : Step Location Value}
    (addition : step.IsAddition) {state target : Location → Value} :
    step.fire state = some target ↔
      step.rule.guard state ∧ target = state + step.rule.produced := by
  constructor
  · exact addition.eq_add
  · rintro ⟨guarded, rfl⟩
    refine step.fire_eq_some_iff.mpr ⟨guarded, state, ?_, AllSeparate.separate _ _, ?_,
      AllSeparate.add_comm _ _⟩
    · rw [show step.rule.consumed = 0 from addition]
      exact SepAlgebra.zero_separate state
    · rw [show step.rule.consumed = 0 from addition]
      exact (SepAlgebra.zero_add state).symm

/-- **A positive step**: no addition to the state disables its guard.  A step
without a guard and a read of a presence are such; a guard that asks for an
absence is not.  A positive step may consume. -/
def Step.Positive (step : Step Location Value) : Prop :=
  ∀ state added : Location → Value, step.rule.guard state → step.rule.guard (state + added)

/-- **The frame rule for a step.**  A step that fires on a state fires on a larger
state on which its guard holds, with the same change: what was added is carried
along.  The step may consume. -/
theorem Step.fire_add_of_guard [AllSeparate Value] {step : Step Location Value}
    {state target added : Location → Value} (fires : step.fire state = some target)
    (guarded : step.rule.guard (state + added)) :
    step.fire (state + added) = some (target + added) := by
  obtain ⟨-, frame, -, -, sourceEq, targetEq⟩ := step.fire_eq_some_iff.mp fires
  refine step.fire_eq_some_iff.mpr ⟨guarded, frame + added, AllSeparate.separate _ _,
    AllSeparate.separate _ _, ?_, ?_⟩
  · rw [sourceEq, AllSeparate.add_assoc]
  · rw [targetEq, AllSeparate.add_assoc]

/-- A positive step that fires on a state fires on every larger state, with the
same change. -/
theorem Step.Positive.fire_add [AllSeparate Value] {step : Step Location Value}
    (positive : step.Positive) {state target : Location → Value}
    (fires : step.fire state = some target) (added : Location → Value) :
    step.fire (state + added) = some (target + added) := by
  obtain ⟨guarded, -⟩ := step.fire_eq_some_iff.mp fires
  exact Step.fire_add_of_guard fires (positive state added guarded)

/-- **What a list of steps adds**: what its steps produce, together. -/
def stepsAdded : List (Step Location Value) → (Location → Value)
  | [] => 0
  | step :: rest => step.rule.produced + stepsAdded rest

/-- **What a proposal adds.** -/
def Proposal.added (proposal : Proposal Location Value Answer) : Location → Value :=
  stepsAdded proposal.steps

/-- **A proposal by deltas**: every step is an addition. -/
def Proposal.IsDelta (proposal : Proposal Location Value Answer) : Prop :=
  ∀ step ∈ proposal.steps, step.IsAddition

/-- **Stable under an addition**: adding `added` to the state disables no guard of
the proposal. -/
def Proposal.StableUnder (proposal : Proposal Location Value Answer)
    (added : Location → Value) : Prop :=
  ∀ step ∈ proposal.steps, ∀ state, step.rule.guard state → step.rule.guard (state + added)

/-- **Independence by deltas**: each proposal is stable under what the other
adds.  Nothing is asked of the written locations. -/
def Proposal.DeltaIndependent (first second : Proposal Location Value Answer) : Prop :=
  first.StableUnder second.added ∧ second.StableUnder first.added

theorem Proposal.DeltaIndependent.symm {first second : Proposal Location Value Answer}
    (independent : first.DeltaIndependent second) : second.DeltaIndependent first :=
  ⟨independent.2, independent.1⟩

/-- What a list of steps adds vanishes outside the locations they write. -/
theorem stepsAdded_outside (steps : List (Step Location Value)) {location : Location}
    (outside : location ∉ stepsWrites steps) : stepsAdded steps location = 0 := by
  induction steps with
  | nil => rfl
  | cons step rest ih =>
      have notStep : location ∉ step.rule.writes :=
        fun written => outside (Finset.mem_union_left _ written)
      have notRest : location ∉ stepsWrites rest :=
        fun written => outside (Finset.mem_union_right _ written)
      show step.rule.produced location + stepsAdded rest location = 0
      rw [step.rule.produced_outside location notStep, ih notRest, SepAlgebra.zero_add]

/-- A step of a list reads no more than the list. -/
theorem subset_stepsReads_of_mem {steps : List (Step Location Value)} {step : Step Location Value}
    (member : step ∈ steps) : step.rule.reads ⊆ stepsReads steps := by
  induction steps with
  | nil => cases member
  | cons head rest ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact Finset.subset_union_left
      · exact (ih later).trans Finset.subset_union_right

/-- A step of a list writes no more than the list. -/
theorem subset_stepsWrites_of_mem {steps : List (Step Location Value)}
    {step : Step Location Value} (member : step ∈ steps) :
    step.rule.writes ⊆ stepsWrites steps := by
  induction steps with
  | nil => cases member
  | cons head rest ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact Finset.subset_union_left
      · exact (ih later).trans Finset.subset_union_right

/-- **Independence by read and write sets implies independence by deltas.**  What
one proposal adds lies in the locations it writes, and those are neither read nor
written by the other. -/
theorem Proposal.Independent.deltaIndependent {first second : Proposal Location Value Answer}
    (independent : first.Independent second) : first.DeltaIndependent second := by
  have stable : ∀ {mover other : Proposal Location Value Answer},
      Disjoint other.writes (mover.reads ∪ mover.writes) → mover.StableUnder other.added := by
    intro mover other apart step member state guarded
    refine step.rule.guard_local (fun location inside => ?_) guarded
    have notWritten : location ∉ other.writes := fun written =>
      Finset.disjoint_left.mp apart written
        (Finset.union_subset_union
          ((subset_stepsReads_of_mem member).trans Finset.subset_union_left)
          (subset_stepsWrites_of_mem member) inside)
    show state location = state location + stepsAdded other.steps location
    rw [stepsAdded_outside other.steps notWritten, SepAlgebra.add_zero]
  exact ⟨stable independent.2, stable independent.1⟩

/-- **Compatible by deltas, answers included**: the two proposals are independent
by deltas, and neither writes a location that the answer of the other reads.
Guards that no addition disables, and locations that both write, are not
compared. -/
def Proposal.DeltaCompatible (first second : Proposal Location Value Answer) : Prop :=
  first.DeltaIndependent second ∧ Disjoint second.writes first.readout.reads ∧
    Disjoint first.writes second.readout.reads

theorem Proposal.DeltaCompatible.symm {first second : Proposal Location Value Answer}
    (compatible : first.DeltaCompatible second) : second.DeltaCompatible first :=
  ⟨compatible.1.symm, compatible.2.2, compatible.2.1⟩

/-- **Independence by read and write sets implies it.** -/
theorem Proposal.Independent.deltaCompatible {first second : Proposal Location Value Answer}
    (independent : first.Independent second) : first.DeltaCompatible second :=
  ⟨independent.deltaIndependent,
    independent.2.mono_right (Finset.subset_union_right.trans Finset.subset_union_left),
    independent.1.mono_right (Finset.subset_union_right.trans Finset.subset_union_left)⟩

/-- A sequence published in order is a publication of its proposals. -/
theorem publishAll_of_publishInOrder [DecidableEq Answer]
    {outcomes : List (Answer × Proposal Location Value Answer)} {world final : Location → Value}
    (published : publishInOrder outcomes world = some final) :
    publishAll (outcomes.map Prod.snd) world = some final := by
  induction outcomes generalizing world with
  | nil => exact published
  | cons outcome rest ih =>
      rw [publishInOrder, Option.bind_eq_some_iff] at published
      obtain ⟨next, headPublished, tail⟩ := published
      split at tail
      · rw [List.map_cons, publishAll_cons, headPublished]
        exact ih tail
      · cases tail

variable [AllSeparate Value]

theorem stepsAdded_append (first second : List (Step Location Value)) :
    stepsAdded (first ++ second) = stepsAdded first + stepsAdded second := by
  induction first with
  | nil => exact (SepAlgebra.zero_add _).symm
  | cons step rest ih =>
      show step.rule.produced + stepsAdded (rest ++ second) = _
      rw [ih]
      exact (AllSeparate.add_assoc _ _ _).symm

/-- What a list of steps adds does not depend on their order. -/
theorem stepsAdded_perm {steps reordered : List (Step Location Value)}
    (perm : steps.Perm reordered) : stepsAdded steps = stepsAdded reordered := by
  induction perm with
  | nil => rfl
  | cons step _ ih => exact congrArg (step.rule.produced + ·) ih
  | swap first second rest => exact AllSeparate.add_left_comm _ _ _
  | trans _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond

/-- **Publication of a proposal by deltas adds its delta.** -/
theorem Proposal.IsDelta.publish_eq_add {proposal : Proposal Location Value Answer}
    (delta : proposal.IsDelta) {state view : Location → Value}
    (published : publish proposal.steps state = some view) : view = state + proposal.added := by
  obtain ⟨steps, readout⟩ := proposal
  show view = state + stepsAdded steps
  induction steps generalizing state with
  | nil =>
      cases published
      exact (SepAlgebra.add_zero _).symm
  | cons step rest ih =>
      rw [publish_cons, Option.bind_eq_some_iff] at published
      obtain ⟨middle, fired, restPublished⟩ := published
      obtain ⟨-, rfl⟩ := (delta step List.mem_cons_self).eq_add fired
      rw [ih (fun other member => delta other (List.mem_cons_of_mem step member)) restPublished]
      exact AllSeparate.add_assoc _ _ _

/-- **The frame rule for a proposal.**  A proposal that is stable under an
addition publishes after it, with that addition in the result.  Its steps may
consume. -/
theorem Proposal.StableUnder.publish_add {proposal : Proposal Location Value Answer}
    {added : Location → Value} (stable : proposal.StableUnder added)
    {state view : Location → Value} (published : publish proposal.steps state = some view) :
    publish proposal.steps (state + added) = some (view + added) := by
  obtain ⟨steps, readout⟩ := proposal
  induction steps generalizing state with
  | nil =>
      cases published
      rfl
  | cons step rest ih =>
      rw [publish_cons, Option.bind_eq_some_iff] at published
      obtain ⟨middle, fired, restPublished⟩ := published
      obtain ⟨guarded, -⟩ := step.fire_eq_some_iff.mp fired
      rw [publish_cons,
        Step.fire_add_of_guard fired (stable step List.mem_cons_self state guarded),
        Option.bind_some]
      exact ih (fun other member => stable other (List.mem_cons_of_mem step member)) restPublished

/-- **Two proposals by deltas that are independent by deltas commute**, from a
state on which both publish: each publishes after the other, and both orders
reach the state with both deltas added. -/
theorem Proposal.DeltaIndependent.publish_comm {first second : Proposal Location Value Answer}
    (firstDelta : first.IsDelta) (secondDelta : second.IsDelta)
    (independent : first.DeltaIndependent second) {state afterFirst afterSecond : Location → Value}
    (firstPublished : publish first.steps state = some afterFirst)
    (secondPublished : publish second.steps state = some afterSecond) :
    publish second.steps afterFirst = some (state + first.added + second.added) ∧
      publish first.steps afterSecond = some (state + first.added + second.added) := by
  have firstAdds := firstDelta.publish_eq_add firstPublished
  have secondAdds := secondDelta.publish_eq_add secondPublished
  constructor
  · rw [firstAdds, independent.2.publish_add secondPublished, secondAdds,
      AllSeparate.add_right_comm]
  · rw [secondAdds, independent.1.publish_add firstPublished, firstAdds]

/-- **A wave by deltas.**  Proposals by deltas that are independent by deltas in
pairs, each of which publishes on a state, are all published from that state,
and the result is the state with everything they add. -/
theorem publishAll_of_deltaIndependent {proposals : List (Proposal Location Value Answer)}
    (deltas : ∀ proposal ∈ proposals, proposal.IsDelta)
    (independent : proposals.Pairwise Proposal.DeltaIndependent) {world : Location → Value}
    (explored : ∀ proposal ∈ proposals, (publish proposal.steps world).isSome) :
    publishAll proposals world =
      some (world + stepsAdded (proposals.flatMap fun proposal => proposal.steps)) := by
  induction proposals generalizing world with
  | nil => exact congrArg some (SepAlgebra.add_zero world).symm
  | cons proposal rest ih =>
      obtain ⟨headIndependent, restIndependent⟩ := List.pairwise_cons.mp independent
      obtain ⟨next, published⟩ :=
        Option.isSome_iff_exists.mp (explored proposal List.mem_cons_self)
      have headDelta := deltas proposal List.mem_cons_self
      have adds := headDelta.publish_eq_add published
      rw [publishAll_cons, published, Option.bind_some,
        ih (fun other member => deltas other (List.mem_cons_of_mem proposal member))
          restIndependent (world := next) (fun other member => by
            obtain ⟨view, otherPublished⟩ :=
              Option.isSome_iff_exists.mp (explored other (List.mem_cons_of_mem proposal member))
            rw [adds, (headIndependent other member).2.publish_add otherPublished]
            rfl),
        List.flatMap_cons, stepsAdded_append, adds]
      exact congrArg some (AllSeparate.add_assoc _ _ _)

/-- **Every order of the wave reaches one state.** -/
theorem publishAll_perm_of_deltaIndependent
    {proposals reordered : List (Proposal Location Value Answer)}
    (deltas : ∀ proposal ∈ proposals, proposal.IsDelta)
    (independent : proposals.Pairwise Proposal.DeltaIndependent) {world : Location → Value}
    (explored : ∀ proposal ∈ proposals, (publish proposal.steps world).isSome)
    (perm : proposals.Perm reordered) :
    publishAll reordered world = publishAll proposals world := by
  rw [publishAll_of_deltaIndependent deltas independent explored,
    publishAll_of_deltaIndependent
      (fun proposal member => deltas proposal (perm.mem_iff.mpr member))
      ((perm.pairwise_iff Proposal.DeltaIndependent.symm).mp independent)
      (fun proposal member => explored proposal (perm.mem_iff.mpr member)),
    stepsAdded_perm (perm.flatMap_right _).symm]

/-- **The outcome of a proposal survives an addition** that its guards are stable
under and that its answer does not read. -/
theorem Proposal.StableUnder.outcome?_add {proposal : Proposal Location Value Answer}
    {added : Location → Value} (stable : proposal.StableUnder added)
    (unread : ∀ location ∈ proposal.readout.reads, added location = 0)
    {state : Location → Value} {outcome : Answer × Proposal Location Value Answer}
    (explored : proposal.outcome? state = some outcome) :
    proposal.outcome? (state + added) = some outcome := by
  obtain ⟨view, published, rfl⟩ := Proposal.outcome?_eq_some_iff.mp explored
  refine Proposal.outcome?_eq_some_iff.mpr
    ⟨view + added, stable.publish_add published, ?_⟩
  have sameAnswer : proposal.readout.value (view + added) = proposal.readout.value view :=
    proposal.readout.value_local fun location inside => by
      show view location + added location = view location
      rw [unread location inside, SepAlgebra.add_zero]
  rw [sameAnswer]

/-- Outcomes by deltas that a state has, compatible in pairs, are published from
it in order, each validated by replay when its turn comes. -/
theorem publishInOrder_of_deltaCompatible [DecidableEq Answer]
    {outcomes : List (Answer × Proposal Location Value Answer)}
    (deltas : ∀ outcome ∈ outcomes, outcome.2.IsDelta)
    (compatible : outcomes.Pairwise fun first second => first.2.DeltaCompatible second.2)
    {world : Location → Value}
    (explored : ∀ outcome ∈ outcomes, outcome.2.outcome? world = some outcome) :
    ∃ final, publishInOrder outcomes world = some final := by
  induction outcomes generalizing world with
  | nil => exact ⟨world, rfl⟩
  | cons outcome rest ih =>
      obtain ⟨headCompatible, restCompatible⟩ := List.pairwise_cons.mp compatible
      obtain ⟨view, published, same⟩ :=
        Proposal.outcome?_eq_some_iff.mp (explored outcome List.mem_cons_self)
      have adds := (deltas outcome List.mem_cons_self).publish_eq_add published
      obtain ⟨final, restPublished⟩ :=
        ih (fun other member => deltas other (List.mem_cons_of_mem outcome member))
          restCompatible (world := view) (fun other member => by
            have pair := headCompatible other member
            rw [adds]
            exact pair.1.2.outcome?_add
              (fun location inside => stepsAdded_outside outcome.2.steps fun written =>
                Finset.disjoint_left.mp pair.2.2 written inside)
              (explored other (List.mem_cons_of_mem outcome member)))
      refine ⟨final, ?_⟩
      rw [publishInOrder, published, Option.bind_some, if_pos (congrArg Prod.fst same)]
      exact restPublished

/-- **A wave of proposals by deltas, validated only on what an addition can
invalidate, is serializable in every order.**  The outcomes are explored from one
state; the proposals only add; in pairs they are compatible by deltas.  Then
every order of them is published from that state, each validated by replay when
its turn comes, to the state with all they add; and every order is the committed
run of the alternatives that answered, with the answers that were returned. -/
theorem wave_of_deltas_every_order [DecidableEq Answer]
    {outcomes order : List (Answer × Proposal Location Value Answer)}
    (deltas : ∀ outcome ∈ outcomes, outcome.2.IsDelta)
    (compatible : outcomes.Pairwise fun first second => first.2.DeltaCompatible second.2)
    {world : Location → Value}
    (explored : ∀ outcome ∈ outcomes, outcome.2.outcome? world = some outcome)
    (perm : outcomes.Perm order) :
    publishInOrder order world =
        some (world +
          stepsAdded ((outcomes.map Prod.snd).flatMap fun proposal => proposal.steps)) ∧
      (Region.alternatives (order.map fun outcome => outcome.2.region)).committed world =
        (order.map Prod.fst, world +
          stepsAdded ((outcomes.map Prod.snd).flatMap fun proposal => proposal.steps)) := by
  have orderDeltas : ∀ outcome ∈ order, outcome.2.IsDelta :=
    fun outcome member => deltas outcome (perm.mem_iff.mpr member)
  have orderCompatible : order.Pairwise fun first second => first.2.DeltaCompatible second.2 :=
    (perm.pairwise_iff fun related => Proposal.DeltaCompatible.symm related).mp compatible
  have orderExplored : ∀ outcome ∈ order, outcome.2.outcome? world = some outcome :=
    fun outcome member => explored outcome (perm.mem_iff.mpr member)
  obtain ⟨final, published⟩ :=
    publishInOrder_of_deltaCompatible orderDeltas orderCompatible orderExplored
  have all := publishAll_of_deltaIndependent (proposals := order.map Prod.snd) (world := world)
    (fun proposal member => by
      obtain ⟨outcome, inside, rfl⟩ := List.mem_map.mp member
      exact orderDeltas outcome inside)
    (List.pairwise_map.mpr (orderCompatible.imp fun related => related.1))
    (fun proposal member => by
      obtain ⟨outcome, inside, rfl⟩ := List.mem_map.mp member
      obtain ⟨view, viewPublished, -⟩ :=
        Proposal.outcome?_eq_some_iff.mp (orderExplored outcome inside)
      rw [viewPublished]
      rfl)
  have same : final = world +
      stepsAdded ((outcomes.map Prod.snd).flatMap fun proposal => proposal.steps) := by
    rw [stepsAdded_perm ((perm.map Prod.snd).flatMap_right _)]
    exact Option.some.inj ((publishAll_of_publishInOrder published).symm.trans all)
  rw [same] at published
  exact ⟨published, publishInOrder_serializable published⟩

end Additions

/-! ## The merge by sum, and the merge by join -/

/-- **The merge of deltas by their sum**: in a commutative monoid it does not
depend on the order of the deltas, and it counts every occurrence. -/
def sumMerge (Delta : Type u) [AddCommMonoid Delta] : AlternativeMerge Delta where
  merge deltas := some (sumDeltas deltas)
  permutationInvariant := by
    intro first second perm
    refine congrArg some ?_
    induction perm with
    | nil => rfl
    | cons delta _ ih => exact congrArg (delta + ·) ih
    | swap first second rest => exact add_left_comm _ _ _
    | trans _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond

/-- The sum of deltas of a list that is put together from two. -/
theorem sumDeltas_append (first second : List (Location → ℕ)) :
    sumDeltas (first ++ second) = sumDeltas first + sumDeltas second := by
  induction first with
  | nil => exact (zero_add _).symm
  | cons delta rest ih =>
      show delta + sumDeltas (rest ++ second) = delta + sumDeltas rest + sumDeltas second
      rw [ih, add_assoc]

/-- **The join of two deltas of multiplicities is their sum exactly when no
location is added by both.** -/
theorem sup_eq_add_iff (first second : Location → ℕ) :
    first ⊔ second = first + second ↔ ∀ location, first location = 0 ∨ second location = 0 := by
  constructor
  · intro same location
    have atLocation : max (first location) (second location) = first location + second location :=
      congrFun same location
    omega
  · intro apart
    funext location
    show max (first location) (second location) = first location + second location
    rcases apart location with zero | zero <;> rw [zero] <;> simp

section Counts

variable [DecidableEq Location]

/-- What a list of steps over multiplicities adds is the sum of what they
produce. -/
theorem stepsAdded_eq_sumDeltas (steps : List (Step Location ℕ)) :
    stepsAdded steps = sumDeltas (steps.map fun step => step.rule.produced) := by
  induction steps with
  | nil => rfl
  | cons step rest ih => exact congrArg (step.rule.produced + ·) ih

/-- **A wave of delta proposals over multiplicities is the merge by sum**: the
published state is the enclosing state with the sum of the deltas. -/
theorem publishAll_eq_sumMerge {proposals : List (Proposal Location ℕ Answer)}
    (deltas : ∀ proposal ∈ proposals, proposal.IsDelta)
    (independent : proposals.Pairwise Proposal.DeltaIndependent) {world : Location → ℕ}
    (explored : ∀ proposal ∈ proposals, (publish proposal.steps world).isSome) :
    publishAll proposals world =
      ((sumMerge (Location → ℕ)).merge (proposals.map Proposal.added)).map (world + ·) := by
  rw [publishAll_of_deltaIndependent deltas independent explored]
  refine congrArg (fun total => some (world + total)) ?_
  clear deltas independent explored
  induction proposals with
  | nil => rfl
  | cons proposal rest ih =>
      rw [List.flatMap_cons, stepsAdded_append, ih]
      rfl

end Counts

/-! ## The steps at the grain of kinds -/

section Kinds

variable [DecidableEq Location]

/-- Adding a kind is an addition. -/
theorem addKind_isAddition (kind : Location) : (addKind kind).IsAddition :=
  marking_zero

/-- Seeing a kind is an addition: of nothing. -/
theorem seeKind_isAddition (kind : Location) : (seeKind kind).IsAddition :=
  rfl

/-- The guarded addition is an addition. -/
theorem addKindUnless_isAddition (kind watched : Location) :
    (addKindUnless kind watched).IsAddition :=
  rfl

/-- **Negative**: removing a kind is not an addition: it consumes the kind. -/
theorem removeKind_not_isAddition (kind : Location) : ¬ (removeKind kind).IsAddition := by
  intro addition
  have consumes : marking ({kind} : Multiset Location) = 0 := addition
  have atKind := congrFun consumes kind
  rw [marking_singleton] at atKind
  simp at atKind

/-- Adding a kind is positive: it has no guard. -/
theorem addKind_positive (kind : Location) : (addKind kind).Positive :=
  fun _ _ _ => trivial

/-- **Removing a kind is positive**: it has no guard.  That the kind is there is
asked by what it consumes, and an addition takes nothing away. -/
theorem removeKind_positive (kind : Location) : (removeKind kind).Positive :=
  fun _ _ _ => trivial

/-- The write of a cell is positive. -/
theorem replaceKind_positive (old new : Location) : (replaceKind old new).Positive :=
  fun _ _ _ => trivial

/-- Seeing a kind is positive: a presence stays a presence. -/
theorem seeKind_positive (kind : Location) : (seeKind kind).Positive :=
  fun _ _ present => Nat.lt_of_lt_of_le present (Nat.le_add_right _ _)

/-- A consumption is positive when no addition disables its guard. -/
theorem consumeKind_positive (kind : Location) (guard : Readout Location ℕ Prop)
    (decideGuard : DecidablePred guard.value)
    (stable : ∀ state added : Location → ℕ, guard.value state → guard.value (state + added)) :
    (consumeKind kind guard decideGuard).Positive :=
  stable

/-- **Negative**: the guard that asks for an absence is not positive: the addition
of the kind it watches disables it. -/
theorem addKindUnless_not_positive (kind watched : Location) :
    ¬ (addKindUnless kind watched).Positive := by
  intro positive
  have disabled : ((0 : Location → ℕ) + (Pi.single watched 1 : Location → ℕ)) watched = 0 :=
    positive 0 (Pi.single watched 1) rfl
  simp at disabled

/-- **The frame rule, for a removal**: a removal that fires on a state fires on
every larger state, and leaves what was added. -/
theorem fire_removeKind_add (kind : Location) {state target : Location → ℕ}
    (fires : (removeKind kind).fire state = some target) (added : Location → ℕ) :
    (removeKind kind).fire (state + added) = some (target + added) :=
  (removeKind_positive kind).fire_add fires added

end Kinds

/-! ## Controls -/

namespace DeltaControls

open AddOnly (Kind noKinds noAtoms)

/-- Add one `a`, the space read by kinds. -/
def addA : Proposal Kind ℕ Unit :=
  ⟨[addKind .a], Readout.const ()⟩

/-- Remove one `a`. -/
def removeA : Proposal Kind ℕ Unit :=
  ⟨[removeKind .a], Readout.const ()⟩

/-- Answer when an `a` is there. -/
def seeA : Proposal Kind ℕ Unit :=
  ⟨[seeKind .a], Readout.const ()⟩

/-- Add one `b` unless an `a` is there. -/
def addBUnlessA : Proposal Kind ℕ Unit :=
  ⟨[addKindUnless .b .a], Readout.const ()⟩

/-- **Positive, a proposal by deltas**: adding a kind consumes nothing. -/
theorem addA_isDelta : addA.IsDelta := by
  intro step member
  rw [List.mem_singleton.mp member]
  exact addKind_isAddition _

/-- **Negative, a proposal by deltas**: removing a kind consumes it. -/
theorem removeA_not_isDelta : ¬ removeA.IsDelta := fun delta =>
  removeKind_not_isAddition Kind.a (delta _ List.mem_cons_self)

/-- **Positive, what a proposal adds**: one `a`, and publication adds it. -/
theorem addA_added :
    addA.added = Pi.single Kind.a 1 ∧
      publish addA.steps noKinds = some (noKinds + addA.added) := by
  have added : addA.added = Pi.single Kind.a 1 := by
    show marking {Kind.a} + 0 = Pi.single Kind.a 1
    rw [marking_singleton, add_zero]
  refine ⟨added, ?_⟩
  rw [added]
  show ((addKind Kind.a).fire noKinds).bind (publish []) = _
  rw [fire_addKind]
  rfl

/-- **Negative, what a proposal adds**: a removal produces nothing.  Its
publication has no `a`, and the state with what it adds has one. -/
theorem removeA_added :
    removeA.added = 0 ∧
      (publish removeA.steps (Pi.single Kind.a 1)).map (fun world => world .a) = some 0 ∧
      ((Pi.single Kind.a 1 : Kind → ℕ) + removeA.added) Kind.a = 1 := by
  have added : removeA.added = 0 := by
    show marking 0 + 0 = 0
    rw [marking_zero, add_zero]
  refine ⟨added, by decide, ?_⟩
  rw [added]
  rfl

/-- **Positive, stability**: the read of a presence is stable under every
addition. -/
theorem seeA_stableUnder (added : Kind → ℕ) : seeA.StableUnder added := by
  intro step member state present
  rw [List.mem_singleton.mp member] at present ⊢
  exact Nat.lt_of_lt_of_le present (Nat.le_add_right _ _)

/-- **Negative, stability**: the guard that asks for the absence of `a` is not
stable under the addition of an `a`. -/
theorem addBUnlessA_not_stableUnder : ¬ addBUnlessA.StableUnder (Pi.single Kind.a 1) := by
  intro stable
  have disabled : (noKinds + (Pi.single Kind.a 1 : Kind → ℕ)) Kind.a = 0 :=
    stable _ List.mem_cons_self noKinds rfl
  exact absurd disabled (by decide)

/-- **Two additions of one kind are independent by deltas and not by read and
write sets.**  Both write the kind, and published one after the other they leave
two occurrences. -/
theorem same_kind_additions :
    addA.DeltaIndependent addA ∧ ¬ addA.Independent addA ∧
      (publishAll [addA, addA] noKinds).map (fun world => world .a) = some 2 := by
  refine ⟨⟨?_, ?_⟩, by decide, by decide⟩ <;>
  · intro step member state _
    rw [List.mem_singleton.mp member]
    trivial

/-- An addition of an atom to the space, the space as one location. -/
def addToSpace (atom : Kind) : Proposal Controls.Store (Multiset Kind) Unit :=
  ⟨[Step.addAtom .space atom], Readout.const ()⟩

/-- **Two additions to one space are independent by deltas at the grain of the
space as well.**  They write the one location, and both orders publish to one
state. -/
theorem same_space_additions :
    (addToSpace .a).DeltaIndependent (addToSpace .b) ∧
      ¬ (addToSpace .a).Independent (addToSpace .b) ∧
      (publishAll [addToSpace .a, addToSpace .b] noAtoms).map (fun world => world .space) =
        some {.a, .b} ∧
      (publishAll [addToSpace .b, addToSpace .a] noAtoms).map (fun world => world .space) =
        some {.a, .b} := by
  refine ⟨⟨?_, ?_⟩, by decide, by decide, by decide⟩ <;>
  · intro step member state _
    rw [List.mem_singleton.mp member]
    trivial

/-- **Negative, independence by deltas**: the guard that asks for the absence of
`a`, and the addition of an `a`. -/
theorem absence_not_deltaIndependent : ¬ addBUnlessA.DeltaIndependent addA := fun independent =>
  addBUnlessA_not_stableUnder (addA_added.1 ▸ independent.1)

/-- Add one `b`. -/
def addB : Proposal Kind ℕ Unit :=
  ⟨[addKind .b], Readout.const ()⟩

/-- **Positive, compatible by deltas**: the addition of a `b` guarded by the
absence of `a`, and an addition of a `b`.  Both write the kind `b`, so they are not
independent by read and write sets; the guard does not watch what the other
adds, and neither answer reads.  Both orders are published, to one state. -/
theorem guarded_and_same_kind :
    addBUnlessA.DeltaCompatible addB ∧ ¬ addBUnlessA.Independent addB ∧
      (publishInOrder [((), addBUnlessA), ((), addB)] noKinds).map (fun world => world .b) =
        some 2 ∧
      (publishInOrder [((), addB), ((), addBUnlessA)] noKinds).map (fun world => world .b) =
        some 2 := by
  refine ⟨⟨⟨?_, ?_⟩, by decide, by decide⟩, by decide, by decide, by decide⟩
  · intro step member state absent
    rw [List.mem_singleton.mp member] at absent ⊢
    have added : addB.added = Pi.single Kind.b 1 := by
      show marking {Kind.b} + 0 = Pi.single Kind.b 1
      rw [marking_singleton, add_zero]
    rw [added]
    show state Kind.a + (Pi.single Kind.b 1 : Kind → ℕ) Kind.a = 0
    rw [Pi.single_eq_of_ne (by decide), add_zero]
    exact absent
  · intro step member state _
    rw [List.mem_singleton.mp member]
    trivial

/-- Answer with the number of `a`. -/
def countA : Proposal Kind ℕ ℕ :=
  ⟨[], Readout.valueAt Kind.a⟩

/-- Add one `a` and answer `0`. -/
def addAndAnswer : Proposal Kind ℕ ℕ :=
  ⟨[addKind .a], Readout.const 0⟩

/-- **Negative, compatible by deltas**: an addition of an `a`, and an answer that
reads the number of `a`.  No guard is disabled, so the two are independent by
deltas; and they are not compatible: the addition writes what the answer reads. -/
theorem answer_reads_what_is_added :
    countA.DeltaIndependent addAndAnswer ∧ ¬ countA.DeltaCompatible addAndAnswer := by
  refine ⟨⟨fun step member => (nomatch member), ?_⟩, fun compatible => ?_⟩
  · intro step member state _
    rw [List.mem_singleton.mp member]
    trivial
  · exact absurd compatible.2.1 (by decide)

/-- **The wave of deltas needs proposals by deltas.**  A removal adds nothing, so
the reader of its kind is stable under what it adds; and the removal is not a
proposal by deltas: after it the reader is refused. -/
theorem removal_is_no_delta :
    seeA.DeltaIndependent removeA ∧ ¬ removeA.IsDelta ∧
      (publishAll [seeA, removeA] (Pi.single Kind.a 1)).isSome = true ∧
      (publishAll [removeA, seeA] (Pi.single Kind.a 1)).isSome = false := by
  refine ⟨⟨?_, ?_⟩, removeA_not_isDelta, by decide, by decide⟩
  · rw [removeA_added.1]
    intro step member state present
    exact present
  · intro step member state _
    rw [List.mem_singleton.mp member]
    trivial

/-- **Independence by deltas does not say what independence by sets says from
every state.**  An addition and the read of a presence of its kind are
independent by deltas.  From the state without the kind the read alone has no
outcome; after the addition it has one: one order publishes and the other is
refused.  From a state on which both publish, both orders publish to one state. -/
theorem addition_enables_read :
    addA.DeltaIndependent seeA ∧
      (publishAll [addA, seeA] noKinds).isSome = true ∧
      (publishAll [seeA, addA] noKinds).isSome = false ∧
      (publishAll [addA, seeA] (Pi.single Kind.a 1)).map (fun world => world .a) = some 2 ∧
      (publishAll [seeA, addA] (Pi.single Kind.a 1)).map (fun world => world .a) = some 2 := by
  refine ⟨⟨?_, seeA_stableUnder _⟩, by decide, by decide, by decide, by decide⟩
  intro step member state _
  rw [List.mem_singleton.mp member]
  trivial

/-- **The join forgets multiplicity where two proposals add one kind.**  The join
of the two deltas has one occurrence; their sum has two; and the publication of
the two additions has two. -/
theorem join_forgets_multiplicity :
    ((joinMerge (Kind → ℕ)).merge [addA.added, addA.added]).map (fun delta => delta .a) =
        some 1 ∧
      ((sumMerge (Kind → ℕ)).merge [addA.added, addA.added]).map (fun delta => delta .a) =
        some 2 ∧
      (publishAll [addA, addA] noKinds).map (fun world => world .a) = some 2 := by
  refine ⟨?_, ?_, by decide⟩
  · show some ((addA.added ⊔ (addA.added ⊔ ⊥)) Kind.a) = some 1
    rw [addA_added.1]
    rfl
  · show some ((addA.added + (addA.added + 0)) Kind.a) = some 2
    rw [addA_added.1]
    rfl

/-- **Positive, the join**: where two proposals add two kinds, the join of their
deltas is their sum. -/
theorem join_is_sum_on_two_kinds :
    (Pi.single Kind.a 1 : Kind → ℕ) ⊔ Pi.single Kind.b 1 =
      Pi.single Kind.a 1 + Pi.single Kind.b 1 :=
  (sup_eq_add_iff _ _).mpr fun kind => by cases kind <;> simp

end DeltaControls

#print axioms not_allSeparate_excl
#print axioms Step.IsAddition.eq_add
#print axioms Step.IsAddition.fire_eq_some_iff
#print axioms stepsAdded_outside
#print axioms Proposal.Independent.deltaIndependent
#print axioms stepsAdded_append
#print axioms stepsAdded_perm
#print axioms Proposal.IsDelta.publish_eq_add
#print axioms Step.fire_add_of_guard
#print axioms Step.Positive.fire_add
#print axioms Proposal.StableUnder.publish_add
#print axioms Proposal.DeltaIndependent.publish_comm
#print axioms publishAll_of_deltaIndependent
#print axioms publishAll_perm_of_deltaIndependent
#print axioms Proposal.Independent.deltaCompatible
#print axioms publishAll_of_publishInOrder
#print axioms Proposal.StableUnder.outcome?_add
#print axioms publishInOrder_of_deltaCompatible
#print axioms wave_of_deltas_every_order
#print axioms sumMerge
#print axioms stepsAdded_eq_sumDeltas
#print axioms publishAll_eq_sumMerge
#print axioms sup_eq_add_iff
#print axioms removeKind_not_isAddition
#print axioms addKind_positive
#print axioms removeKind_positive
#print axioms replaceKind_positive
#print axioms seeKind_positive
#print axioms consumeKind_positive
#print axioms addKindUnless_not_positive
#print axioms fire_removeKind_add
#print axioms DeltaControls.addA_isDelta
#print axioms DeltaControls.removeA_not_isDelta
#print axioms DeltaControls.addA_added
#print axioms DeltaControls.removeA_added
#print axioms DeltaControls.seeA_stableUnder
#print axioms DeltaControls.addBUnlessA_not_stableUnder
#print axioms DeltaControls.absence_not_deltaIndependent
#print axioms DeltaControls.guarded_and_same_kind
#print axioms DeltaControls.answer_reads_what_is_added
#print axioms DeltaControls.same_kind_additions
#print axioms DeltaControls.same_space_additions
#print axioms DeltaControls.removal_is_no_delta
#print axioms DeltaControls.addition_enables_read
#print axioms DeltaControls.join_forgets_multiplicity
#print axioms DeltaControls.join_is_sum_on_two_kinds

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions
