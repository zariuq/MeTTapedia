import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.PatternFootprints.MonotoneFragment

/-!
# What a wave validates: its writes only, or its reads as well

`Regions.Policies` has one wave: every proposal is published when the proposals
are independent in pairs, which asks of each pair that the writes of either meet
neither the reads nor the writes of the other.  That wave validates reads as
well as writes.  A wave may ask less: that the proposals are **writes apart**
(`Proposal.WritesApart`), no location written by two.  Then what a proposal read
may have been written by another, and it matters what publication does.

* **Replay** (`Policy.publishWaveOnWrites`): the rule instances of the proposals
  are fired again, one proposal after another.
* **Installation** (`Policy.installWaveOnWrites`): each proposal puts, at the
  locations it wrote, the values its private view holds, and nothing is fired
  (`Proposal.install`, `installAll`).

Results.

* **Where reads are validated as well, the three agree**: proposals independent
  in pairs are installed to the state that replay reaches
  (`installAll_eq_publishAll_of_independent`, `waves_agree_of_independent`).
* **Installation on writes only is a function of the bag of outcomes**
  (`installAll_perm`, `Policy.installWaveOnWrites_orderFree`).  **Replay on
  writes only is not** (`ValidationControls.publishWaveOnWrites_not_orderFree`):
  a guard whose read was not validated holds in one order and not in the other.
* **Isolation holds under every one of them.**  The answers returned are those of
  the branch-local run, so the bag of answers does not depend on the order of the
  siblings (`Region.answers_alternatives_perm`); under a policy that is a function
  of the bag, neither does the state (`Policy.OrderFree.observe_alternatives_perm`).
* **Serializability holds where reads are validated**
  (`Region.observe_publishWave_of_independent`) **and not on writes only.**
  `ValidationControls.sibling_reads_separate_the_validations`: two siblings each
  add an atom and answer with the multiplicities of the whole pattern.  Validated
  on writes only both are published, and the two answers are those of no order of
  the siblings run serially; validated on reads as well they conflict.
* What goes wrong on writes only depends on what publication does.  Replay keeps
  the state that of a serial run of the published alternatives
  (`publishAll_committed_state`) and lets stale answers through.  Installation
  lets through a state that no serial run reaches
  (`ValidationControls.write_skew`): two additions, each guarded by the absence of
  what the other adds.
* **For a monotone region the answers under either validation are answers of the
  serial run**, in order, and the serial run may have more
  (`Region.Monotone.wave_answers_sublist_committed`): nothing returned is
  withdrawn.
* **A validation between the two, for proposals that only add.**  Such proposals
  need to be compared only on what an addition can invalidate: a guard that is not
  positive, and an answer that reads (`Proposal.DeltaCompatible`).  That
  validation is serializable in every order (`wave_of_deltas_every_order`).  It
  accepts every monotone region, which the wave on reads may refuse
  (`ValidationControls.chain_is_a_wave_of_deltas`), and two additions of one
  kind, which both waves refuse (`ValidationControls.wave_on_writes_instances`,
  `DeltaControls.same_kind_additions`); and it refuses the siblings that read the
  pattern (`ValidationControls.sibling_reads_not_deltaCompatible`).  It is stated
  as a condition on the outcomes: a policy that computes it needs every step to
  carry whether its guard is positive.  And it is a function of the bag of
  outcomes only for outcomes explored from the state it is applied to: from
  another state an addition may enable a read that has no outcome there, and then
  the order matters (`DeltaControls.addition_enables_read`).
* **For proposals that remove, counting.**  Two removals of one kind write one
  kind, and both validations by footprints report a conflict, with one occurrence
  or with many.  Where no addition disables a guard and no answer reads, the
  proposals are a wave exactly as far as each can be given its own occurrences
  (`PatternFootprints.Claims`: `HasClaims.publishAll_perm`,
  `removals_hasClaims_iff`, and the policy `Policy.publishWaveOnClaims`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.FootprintedSpaceTransactions
open Mettapedia.GSLT.SeparationAlgebra

universe u v w

variable {Location : Type u} {Value : Type v} {Answer : Type w}

section Validations

variable [DecidableEq Location] [Zero Value] [Add Value] [SepAlgebra Value]

/-- **Writes apart**: the two proposals write no location in common.  What either
reads is not asked. -/
def Proposal.WritesApart (first second : Proposal Location Value Answer) : Prop :=
  Disjoint first.writes second.writes

instance Proposal.decidableWritesApart (first second : Proposal Location Value Answer) :
    Decidable (first.WritesApart second) :=
  inferInstanceAs (Decidable (Disjoint first.writes second.writes))

theorem Proposal.WritesApart.symm {first second : Proposal Location Value Answer}
    (apart : first.WritesApart second) : second.WritesApart first :=
  Disjoint.symm apart

/-- Independent proposals are writes apart. -/
theorem Proposal.Independent.writesApart {first second : Proposal Location Value Answer}
    (independent : first.Independent second) : first.WritesApart second :=
  independent.1.mono_right Finset.subset_union_right

/-- **A wave validated on its writes only, published by replay**: every answer is
returned; the proposals are fired one after another if no location is written by
two, and otherwise a conflict is reported. -/
def Policy.publishWaveOnWrites : Policy Location Value Answer where
  returned outcomes := outcomes.map Prod.fst
  change outcomes world :=
    if (outcomes.map Prod.snd).Pairwise Proposal.WritesApart then
      publishAll (outcomes.map Prod.snd) world
    else none

/-- **Installation of a proposal**: at the locations it wrote, the values of the
private view it reached from the snapshot; every other location of the live state
as it is.  Nothing is fired on the live state. -/
def Proposal.install (proposal : Proposal Location Value Answer)
    (snapshot live : Location → Value) : Option (Location → Value) :=
  (publish proposal.steps snapshot).map fun view => proposal.writes.piecewise view live

/-- Install proposals from one snapshot, one after another. -/
def installAll (snapshot : Location → Value) :
    List (Proposal Location Value Answer) → (Location → Value) → Option (Location → Value)
  | [], live => some live
  | proposal :: rest, live => (proposal.install snapshot live).bind (installAll snapshot rest)

/-- **A wave validated on its writes only, published by installation.** -/
def Policy.installWaveOnWrites : Policy Location Value Answer where
  returned outcomes := outcomes.map Prod.fst
  change outcomes world :=
    if (outcomes.map Prod.snd).Pairwise Proposal.WritesApart then
      installAll world (outcomes.map Prod.snd) world
    else none

/-- **Where the reads are kept, installation is replay.** -/
theorem Proposal.install_eq_publish_of_readsKept (proposal : Proposal Location Value Answer)
    {snapshot live : Location → Value} (kept : proposal.ReadsKept snapshot live) :
    proposal.install snapshot live = publish proposal.steps live := by
  unfold Proposal.install
  cases published : publish proposal.steps snapshot with
  | none =>
      exact (publish_eq_none_of_agreesOn
        (agreesOn_mono
          (Finset.union_subset_union Finset.subset_union_left (Finset.Subset.refl _)) kept)
        published).symm
  | some view => exact (proposal.publish_eq_piecewise published kept).symm

/-- **Proposals independent in pairs are installed to the state that replay
reaches**, from every live state on which the reads of all of them are kept. -/
theorem installAll_eq_publishAll_of_independent {snapshot : Location → Value}
    {proposals : List (Proposal Location Value Answer)}
    (independent : proposals.Pairwise Proposal.Independent) {live : Location → Value}
    (kept : ∀ proposal ∈ proposals, proposal.ReadsKept snapshot live) :
    installAll snapshot proposals live = publishAll proposals live := by
  induction proposals generalizing live with
  | nil => rfl
  | cons proposal rest ih =>
      obtain ⟨headIndependent, restIndependent⟩ := List.pairwise_cons.mp independent
      rw [installAll, publishAll_cons,
        proposal.install_eq_publish_of_readsKept (kept proposal List.mem_cons_self)]
      cases published : publish proposal.steps live with
      | none => rfl
      | some next =>
          exact ih restIndependent fun other member =>
            agreesOn_trans (kept other (List.mem_cons_of_mem proposal member))
              (Proposal.readsKept_of_independent (headIndependent other member) published)

/-- **Installation of proposals that are writes apart does not depend on their
order.** -/
theorem installAll_perm {snapshot : Location → Value}
    {proposals reordered : List (Proposal Location Value Answer)} (perm : proposals.Perm reordered)
    (apart : proposals.Pairwise Proposal.WritesApart) (live : Location → Value) :
    installAll snapshot proposals live = installAll snapshot reordered live := by
  induction perm generalizing live with
  | nil => rfl
  | cons proposal _ ih =>
      show (proposal.install snapshot live).bind _ = (proposal.install snapshot live).bind _
      congr 1
      funext next
      exact ih (List.pairwise_cons.mp apart).2 next
  | swap first second rest =>
      have apartPair : second.WritesApart first :=
        (List.pairwise_cons.mp apart).1 first List.mem_cons_self
      show (second.install snapshot live).bind
          (fun next => (first.install snapshot next).bind (installAll snapshot rest)) =
        (first.install snapshot live).bind
          (fun next => (second.install snapshot next).bind (installAll snapshot rest))
      unfold Proposal.install
      cases publish second.steps snapshot with
      | none => cases publish first.steps snapshot <;> rfl
      | some secondView =>
          cases publish first.steps snapshot with
          | none => rfl
          | some firstView =>
              show installAll snapshot rest
                  (first.writes.piecewise firstView (second.writes.piecewise secondView live)) =
                installAll snapshot rest
                  (second.writes.piecewise secondView (first.writes.piecewise firstView live))
              congr 1
              funext location
              by_cases inFirst : location ∈ first.writes
              · have notSecond : location ∉ second.writes := fun inSecond =>
                  Finset.disjoint_left.mp apartPair inSecond inFirst
                rw [Finset.piecewise_eq_of_mem _ _ _ inFirst,
                  Finset.piecewise_eq_of_notMem _ _ _ notSecond,
                  Finset.piecewise_eq_of_mem _ _ _ inFirst]
              · rw [Finset.piecewise_eq_of_notMem _ _ _ inFirst]
                by_cases inSecond : location ∈ second.writes
                · rw [Finset.piecewise_eq_of_mem _ _ _ inSecond,
                    Finset.piecewise_eq_of_mem _ _ _ inSecond]
                · rw [Finset.piecewise_eq_of_notMem _ _ _ inSecond,
                    Finset.piecewise_eq_of_notMem _ _ _ inSecond,
                    Finset.piecewise_eq_of_notMem _ _ _ inFirst]
  | trans firstPerm _ ihFirst ihSecond =>
      rw [ihFirst apart live,
        ihSecond ((firstPerm.pairwise_iff Proposal.WritesApart.symm).mp apart) live]

/-- **Installation on writes only is a function of the bag of outcomes.** -/
theorem Policy.installWaveOnWrites_orderFree :
    (Policy.installWaveOnWrites : Policy Location Value Answer).OrderFree := by
  intro outcomes reordered perm
  refine ⟨perm.map _, ?_⟩
  funext world
  have proposalsPerm :=
    perm.map (Prod.snd : Answer × Proposal Location Value Answer → Proposal Location Value Answer)
  show (if (outcomes.map Prod.snd).Pairwise Proposal.WritesApart then
      installAll world (outcomes.map Prod.snd) world else none) =
    (if (reordered.map Prod.snd).Pairwise Proposal.WritesApart then
      installAll world (reordered.map Prod.snd) world else none)
  by_cases apart : (outcomes.map Prod.snd).Pairwise Proposal.WritesApart
  · rw [if_pos apart, if_pos ((proposalsPerm.pairwise_iff Proposal.WritesApart.symm).mp apart)]
    exact installAll_perm proposalsPerm apart world
  · rw [if_neg apart, if_neg fun reorderedApart =>
      apart ((proposalsPerm.pairwise_iff Proposal.WritesApart.symm).mpr reorderedApart)]

/-- **Where reads are validated as well, the three waves agree**: on outcomes
whose proposals are independent in pairs, replay on writes only and installation
on writes only do what the wave of `Regions.Policies` does. -/
theorem waves_agree_of_independent {outcomes : List (Answer × Proposal Location Value Answer)}
    (independent : (outcomes.map Prod.snd).Pairwise Proposal.Independent)
    (world : Location → Value) :
    Policy.publishWaveOnWrites.change outcomes world = Policy.publishWave.change outcomes world ∧
      Policy.installWaveOnWrites.change outcomes world =
        Policy.publishWave.change outcomes world := by
  have apart : (outcomes.map Prod.snd).Pairwise Proposal.WritesApart :=
    independent.imp Proposal.Independent.writesApart
  constructor
  · show (if (outcomes.map Prod.snd).Pairwise Proposal.WritesApart then
        publishAll (outcomes.map Prod.snd) world else none) =
      (if (outcomes.map Prod.snd).Pairwise Proposal.Independent then
        publishAll (outcomes.map Prod.snd) world else none)
    rw [if_pos apart, if_pos independent]
  · show (if (outcomes.map Prod.snd).Pairwise Proposal.WritesApart then
        installAll world (outcomes.map Prod.snd) world else none) =
      (if (outcomes.map Prod.snd).Pairwise Proposal.Independent then
        publishAll (outcomes.map Prod.snd) world else none)
    rw [if_pos apart, if_pos independent]
    exact installAll_eq_publishAll_of_independent independent fun _ _ => agreesOn_refl _ world

/-- **Under a policy that is a function of the bag of outcomes, an observation of
siblings does not depend on their order**: the answers are reordered, and the
enclosing state is the same. -/
theorem Policy.OrderFree.observe_alternatives_perm {policy : Policy Location Value Answer}
    (orderFree : policy.OrderFree) {siblings reordered : List (Region Location Value Answer)}
    (perm : siblings.Perm reordered) (world : Location → Value) :
    (((Region.alternatives siblings).observe policy world).1).Perm
        ((Region.alternatives reordered).observe policy world).1 ∧
      ((Region.alternatives siblings).observe policy world).2 =
        ((Region.alternatives reordered).observe policy world).2 := by
  obtain ⟨returned, change⟩ := orderFree (Region.branchLocal_alternatives_perm perm world)
  exact ⟨returned, congrFun change world⟩

/-- **Replay keeps the state that of a serial run.**  Proposals that are
published one after another leave the state of the committed run of their
alternatives in that order, whatever was validated.  The answers of that run are
not said to be the answers that were returned. -/
theorem publishAll_committed_state {proposals : List (Proposal Location Value Answer)}
    {world final : Location → Value} (published : publishAll proposals world = some final) :
    ((Region.alternatives (proposals.map Proposal.region)).committed world).2 = final := by
  induction proposals generalizing world with
  | nil =>
      cases published
      rfl
  | cons proposal rest ih =>
      rw [publishAll_cons, Option.bind_eq_some_iff] at published
      obtain ⟨next, headPublished, tail⟩ := published
      show ((Region.alternatives (rest.map Proposal.region)).committed
        (proposal.region.committed world).2).2 = final
      rw [proposal.region_committed headPublished]
      exact ih tail

variable [AllSeparate Value]

/-- **For a monotone region the answers under either validation are answers of
the serial run**, in order; the serial run may have more.  Nothing that was
returned is withdrawn. -/
theorem Region.Monotone.wave_answers_sublist_committed {region : Region Location Value Answer}
    (monotone : region.Monotone) (world : Location → Value) :
    ((region.observe Policy.publishWaveOnWrites world).1).Sublist (region.committed world).1 ∧
      ((region.observe Policy.publishWave world).1).Sublist (region.committed world).1 := by
  have sublist := monotone.answers_sublist_committed world 0
  rw [SepAlgebra.add_zero] at sublist
  exact ⟨sublist, sublist⟩

/-- And where the wave on writes only publishes a monotone region, the state is
the enclosing state with all that the proposals add. -/
theorem Region.Monotone.observe_publishWaveOnWrites {region : Region Location Value Answer}
    (monotone : region.Monotone) (world : Location → Value)
    (apart : ((region.branchLocal world).map Prod.snd).Pairwise Proposal.WritesApart) :
    (region.observe Policy.publishWaveOnWrites world).2 =
      some (world +
        stepsAdded (((region.branchLocal world).map Prod.snd).flatMap fun proposal =>
          proposal.steps)) := by
  show (if ((region.branchLocal world).map Prod.snd).Pairwise Proposal.WritesApart then
    publishAll ((region.branchLocal world).map Prod.snd) world else none) = _
  rw [if_pos apart]
  have published := monotone.publishAll_perm world 0 (List.Perm.refl _)
  rwa [SepAlgebra.add_zero] at published

end Validations

/-! ## Controls -/

namespace ValidationControls

open AddOnly (Kind noKinds kindReader)
open MonotoneControls (guarded marker)

/-- **Positive, writes apart**: additions of two kinds.  **Negative**: two
additions of one kind. -/
theorem writesApart_instances :
    (⟨[addKind Kind.a], Readout.const ()⟩ : Proposal Kind ℕ Unit).WritesApart
        ⟨[addKind Kind.b], Readout.const ()⟩ ∧
      ¬ (⟨[addKind Kind.a], Readout.const ()⟩ : Proposal Kind ℕ Unit).WritesApart
        ⟨[addKind Kind.a], Readout.const ()⟩ := by
  decide

/-- **Positive, a wave on writes**: additions of two kinds are published, by
replay and by installation.  **Negative**: two additions of one kind are reported
as a conflict by both, although the two additions commute. -/
theorem wave_on_writes_instances :
    (Policy.publishWaveOnWrites.change
        [((), (⟨[addKind Kind.a], Readout.const ()⟩ : Proposal Kind ℕ Unit)),
          ((), ⟨[addKind Kind.b], Readout.const ()⟩)] noKinds).map
        (fun world => (world .a, world .b)) = some (1, 1) ∧
      (Policy.installWaveOnWrites.change
        [((), (⟨[addKind Kind.a], Readout.const ()⟩ : Proposal Kind ℕ Unit)),
          ((), ⟨[addKind Kind.b], Readout.const ()⟩)] noKinds).map
        (fun world => (world .a, world .b)) = some (1, 1) ∧
      (Policy.publishWaveOnWrites.change
        [((), (⟨[addKind Kind.a], Readout.const ()⟩ : Proposal Kind ℕ Unit)),
          ((), ⟨[addKind Kind.a], Readout.const ()⟩)] noKinds).isNone = true ∧
      (Policy.installWaveOnWrites.change
        [((), (⟨[addKind Kind.a], Readout.const ()⟩ : Proposal Kind ℕ Unit)),
          ((), ⟨[addKind Kind.a], Readout.const ()⟩)] noKinds).isNone = true := by
  decide

/-- **Positive, installation**: an addition explored from the empty snapshot is
installed on a live state that has a `b`, and the `b` stays.  **Negative**: a
removal that has no outcome from the snapshot is not installed, although the live
state has what it would take. -/
theorem install_instances :
    ((⟨[addKind Kind.a], Readout.const ()⟩ : Proposal Kind ℕ Unit).install noKinds
        (Pi.single Kind.b 1)).map (fun world => (world .a, world .b)) = some (1, 1) ∧
      ((⟨[removeKind Kind.a], Readout.const ()⟩ : Proposal Kind ℕ Unit).install noKinds
        (Pi.single Kind.a 1)).isSome = false := by
  decide

/-- **Two siblings that each add an atom and read the whole pattern separate the
two validations.**  Each sibling answers with the multiplicities of both kinds as
its own view has them.

* Validated on writes only, both are published, by replay and by installation;
  the answers are `(1, 0)` and `(0, 1)`, and the state has both atoms.
* Those two answers are the answers of no serial run: run in the committed mode
  in either order, the second sibling answers `(1, 1)`.
* Validated on reads as well, the two conflict and nothing is published. -/
theorem sibling_reads_separate_the_validations :
    ((Region.alternatives [kindReader .a, kindReader .b]).observe Policy.publishWaveOnWrites
        noKinds).1 = [(1, 0), (0, 1)] ∧
      ((Region.alternatives [kindReader .a, kindReader .b]).observe Policy.publishWaveOnWrites
        noKinds).2.map (fun world => (world .a, world .b)) = some (1, 1) ∧
      ((Region.alternatives [kindReader .a, kindReader .b]).observe Policy.installWaveOnWrites
        noKinds).2.map (fun world => (world .a, world .b)) = some (1, 1) ∧
      ((Region.alternatives [kindReader .a, kindReader .b]).committed noKinds).1 =
        [(1, 0), (1, 1)] ∧
      ((Region.alternatives [kindReader .b, kindReader .a]).committed noKinds).1 =
        [(0, 1), (1, 1)] ∧
      ((Region.alternatives [kindReader .a, kindReader .b]).observe Policy.publishWave
        noKinds).2.isNone = true := by
  decide

/-- So the bag of answers returned on writes only is the bag of answers of
neither serial order. -/
theorem sibling_reads_not_serializable :
    ((([(1, 0), (0, 1)] : List (ℕ × ℕ)) : Multiset (ℕ × ℕ)) ≠
        ((Region.alternatives [kindReader .a, kindReader .b]).committed noKinds).1) ∧
      ((([(1, 0), (0, 1)] : List (ℕ × ℕ)) : Multiset (ℕ × ℕ)) ≠
        ((Region.alternatives [kindReader .b, kindReader .a]).committed noKinds).1) := by
  decide

/-- **Isolation under both validations**, on the same siblings: the bag of answers
is the same for the two orders of the siblings. -/
theorem sibling_reads_isolated :
    (((Region.alternatives [kindReader .a, kindReader .b]).observe Policy.publishWaveOnWrites
        noKinds).1 : Multiset (ℕ × ℕ)) =
      ((Region.alternatives [kindReader .b, kindReader .a]).observe Policy.publishWaveOnWrites
        noKinds).1 :=
  Region.answers_alternatives_perm (List.Perm.swap _ _ []) noKinds

/-- The outcome of the guarded addition from the empty state. -/
def guardedOutcome : Unit × Proposal Kind ℕ Unit :=
  ((), ⟨[addKindUnless .b .a], Readout.const ()⟩)

/-- The outcome of the addition it watches. -/
def markerOutcome : Unit × Proposal Kind ℕ Unit :=
  ((), ⟨[addKind .a], Readout.const ()⟩)

/-- They are the outcomes of the two regions from the empty state, and they are
writes apart. -/
theorem guarded_marker_outcomes :
    guarded.branchLocal noKinds = [guardedOutcome] ∧ marker.branchLocal noKinds = [markerOutcome] ∧
      guardedOutcome.2.WritesApart markerOutcome.2 :=
  ⟨rfl, rfl, by decide⟩

/-- **Replay on writes only is not a function of the bag of outcomes.**  The read
of the guard is not validated; fired after the addition it watches, the guard
does not hold, and the wave is refused; fired before, both are published. -/
theorem publishWaveOnWrites_not_orderFree :
    ¬ (Policy.publishWaveOnWrites : Policy Kind ℕ Unit).OrderFree := by
  intro orderFree
  have same := congrFun (orderFree (List.Perm.swap markerOutcome guardedOutcome [])).2 noKinds
  exact absurd (congrArg Option.isSome same) (by decide)

/-- Installation of the same two is the same in both orders: an instance of
`Policy.installWaveOnWrites_orderFree`. -/
theorem installWaveOnWrites_both_orders :
    (Policy.installWaveOnWrites.change [guardedOutcome, markerOutcome] noKinds).map
        (fun world => (world .a, world .b)) = some (1, 1) ∧
      (Policy.installWaveOnWrites.change [markerOutcome, guardedOutcome] noKinds).map
        (fun world => (world .a, world .b)) = some (1, 1) := by
  decide

/-- Add an `a` unless a `b` is there, and answer. -/
def addAUnlessB : Region Kind ℕ Unit :=
  .step (addKindUnless .a .b) (.answer (Readout.const ()))

/-- Add a `b` unless an `a` is there, and answer. -/
def addBUnlessA : Region Kind ℕ Unit :=
  .step (addKindUnless .b .a) (.answer (Readout.const ()))

/-- **Installation on writes only reaches a state of no serial run.**  Each of
two siblings adds an atom unless the atom of the other is there.  From the empty
state both have an outcome, and they write two kinds.

* Installed on writes only, both atoms are in the state.
* Run serially in either order, the second sibling finds the atom of the first
  and adds nothing: one atom.
* Replayed on writes only, the second guard does not hold and the wave is refused,
  in both orders.
* Validated on reads as well, the two conflict. -/
theorem write_skew :
    ((Region.alternatives [addAUnlessB, addBUnlessA]).observe Policy.installWaveOnWrites
        noKinds).2.map (fun world => (world .a, world .b)) = some (1, 1) ∧
      (((Region.alternatives [addAUnlessB, addBUnlessA]).committed noKinds).2 .a,
        ((Region.alternatives [addAUnlessB, addBUnlessA]).committed noKinds).2 .b) = (1, 0) ∧
      (((Region.alternatives [addBUnlessA, addAUnlessB]).committed noKinds).2 .a,
        ((Region.alternatives [addBUnlessA, addAUnlessB]).committed noKinds).2 .b) = (0, 1) ∧
      ((Region.alternatives [addAUnlessB, addBUnlessA]).observe Policy.publishWaveOnWrites
        noKinds).2.isNone = true ∧
      ((Region.alternatives [addBUnlessA, addAUnlessB]).observe Policy.publishWaveOnWrites
        noKinds).2.isNone = true ∧
      ((Region.alternatives [addAUnlessB, addBUnlessA]).observe Policy.publishWave
        noKinds).2.isNone = true := by
  decide

/-- **Positive, a monotone region under both validations**: the chain of an
addition and a rule that reads it.  From the state with an `a` both alternatives
answer; they write two kinds, so the wave on writes only publishes; the rule read
the kind the addition writes, so the wave on reads as well reports a conflict.
The answers are the same, and they are answers of the committed run. -/
theorem chain_under_both_validations :
    (MonotoneControls.chain.observe Policy.publishWaveOnWrites KindControls.oneA).1 = [1, 2] ∧
      (MonotoneControls.chain.observe Policy.publishWaveOnWrites KindControls.oneA).2.map
        (fun world => (world .a, world .b)) = some (2, 1) ∧
      (MonotoneControls.chain.observe Policy.publishWave KindControls.oneA).1 = [1, 2] ∧
      (MonotoneControls.chain.observe Policy.publishWave KindControls.oneA).2.isNone = true ∧
      (MonotoneControls.chain.committed KindControls.oneA).1 = [1, 2] := by
  decide

/-- **The wave of deltas accepts a monotone region that the wave on reads
refuses.**  The two outcomes of the chain from the state with an `a` are compatible
by deltas and not independent by read and write sets; published in either order,
each validated by replay, they reach one state. -/
theorem chain_is_a_wave_of_deltas :
    (MonotoneControls.chain.branchLocal KindControls.oneA).Pairwise
        (fun first second => first.2.DeltaCompatible second.2) ∧
      ¬ ((MonotoneControls.chain.branchLocal KindControls.oneA).map Prod.snd).Pairwise
        Proposal.Independent ∧
      (publishInOrder (MonotoneControls.chain.branchLocal KindControls.oneA)
        KindControls.oneA).map (fun world => (world .a, world .b)) = some (2, 1) ∧
      (publishInOrder (MonotoneControls.chain.branchLocal KindControls.oneA).reverse
        KindControls.oneA).map (fun world => (world .a, world .b)) = some (2, 1) := by
  refine ⟨?_, by decide, by decide, by decide⟩
  exact List.pairwise_of_forall_mem_list fun first firstMember second secondMember =>
    (MonotoneControls.chain_monotone.proposal_monotone
      (Region.mem_branchLocal_iff.mp firstMember).1).deltaCompatible
      (MonotoneControls.chain_monotone.proposal_monotone
        (Region.mem_branchLocal_iff.mp secondMember).1)

/-- **The wave of deltas refuses the siblings that read the pattern**: each writes
a kind that the answer of the other reads. -/
theorem sibling_reads_not_deltaCompatible :
    ¬ ((Region.alternatives [kindReader .a, kindReader .b]).branchLocal noKinds).Pairwise
      (fun first second => first.2.DeltaCompatible second.2) := fun compatible =>
  absurd (compatible.imp fun related => related.2) (by decide)

end ValidationControls

#print axioms Proposal.install_eq_publish_of_readsKept
#print axioms installAll_eq_publishAll_of_independent
#print axioms installAll_perm
#print axioms Policy.installWaveOnWrites_orderFree
#print axioms waves_agree_of_independent
#print axioms Policy.OrderFree.observe_alternatives_perm
#print axioms publishAll_committed_state
#print axioms Region.Monotone.wave_answers_sublist_committed
#print axioms Region.Monotone.observe_publishWaveOnWrites
#print axioms ValidationControls.writesApart_instances
#print axioms ValidationControls.wave_on_writes_instances
#print axioms ValidationControls.install_instances
#print axioms ValidationControls.sibling_reads_separate_the_validations
#print axioms ValidationControls.sibling_reads_not_serializable
#print axioms ValidationControls.sibling_reads_isolated
#print axioms ValidationControls.guarded_marker_outcomes
#print axioms ValidationControls.publishWaveOnWrites_not_orderFree
#print axioms ValidationControls.installWaveOnWrites_both_orders
#print axioms ValidationControls.write_skew
#print axioms ValidationControls.chain_under_both_validations
#print axioms ValidationControls.chain_is_a_wave_of_deltas
#print axioms ValidationControls.sibling_reads_not_deltaCompatible

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions
