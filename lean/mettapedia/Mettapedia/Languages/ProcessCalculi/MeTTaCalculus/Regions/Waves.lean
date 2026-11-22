import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions.Validation

/-!
# Waves and races

Two proposals are **independent** (`Proposal.Independent`) when the locations
either writes meet neither the locations the other reads nor the locations the
other writes.  This is `FootprintedSpaceTransactions.IndependentEffects` at the
footprints of the proposals; locations that both only read are not mentioned.

**Waves.**

* `publish_comm_of_independent`: independent lists of steps commute as partial
  functions of the state: in either order both are published with one result, or
  both orders are refused.
* `Proposal.readsKept_of_independent`: after an independent proposal is
  published, the reads of the other are kept.
* `publishAll_perm`: proposals that are independent in pairs are published in
  every order with one result, or refused in every order.
* `wave_every_order`: outcomes explored from one snapshot whose proposals are
  independent in pairs are published from that snapshot in every order, each
  validated by kept reads when its turn comes, with one final state.  With
  `publishWithKeptReads_serializable` every order is a serial committed run with
  the answers that were returned.
* Shared reads do not conflict: `Proposal.independent_of_no_writes`, and
  `Controls.shared_gate_independent` with `Controls.shared_gate_both_orders`.

**Races.**  `Controls.absence_race`: one proposal adds an atom that the guard of
another requires to be absent.  They are not independent.  Published first, the
addition refuses the guarded proposal under both validations
(`Controls.absence_race_reads_not_kept` for the first); published second, it is
accepted.  So the result depends on the order of publication, and the refusal
has to be reported.  `Controls.takers_race`: two takers of one token are not
independent, and the second to be published is refused.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.FootprintedSpaceTransactions
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SpaceInteraction
open Mettapedia.GSLT.SeparationAlgebra

universe u v w

variable {Location : Type u} {Value : Type v} {Answer : Type w}

section Waves

variable [DecidableEq Location] [Zero Value] [Add Value] [SepAlgebra Value]

/-- **Independent lists of steps commute** as partial functions of the state:
shared reads are permitted, and the writes of each avoid everything the other
reads or writes. -/
theorem publish_comm_of_independent {first second : List (Step Location Value)}
    (independent : IndependentEffects (stepsReads first) (stepsWrites first)
      (stepsReads second) (stepsWrites second))
    (world : Location → Value) :
    (publish first world).bind (publish second) = (publish second world).bind (publish first) :=
  bind_comm_of_independent (publish_effectFootprinted first) (publish_effectFootprinted second)
    independent world

/-- **Independent proposals**: the writes of each meet neither the reads nor the
writes of the other. -/
def Proposal.Independent (first second : Proposal Location Value Answer) : Prop :=
  IndependentEffects first.reads first.writes second.reads second.writes

instance Proposal.decidableIndependent (first second : Proposal Location Value Answer) :
    Decidable (first.Independent second) :=
  inferInstanceAs
    (Decidable (IndependentEffects first.reads first.writes second.reads second.writes))

theorem Proposal.Independent.symm {first second : Proposal Location Value Answer}
    (independent : first.Independent second) : second.Independent first :=
  independentEffects_symm independent

/-- Independence of proposals is independence of their steps. -/
theorem Proposal.Independent.steps {first second : Proposal Location Value Answer}
    (independent : first.Independent second) :
    IndependentEffects (stepsReads first.steps) (stepsWrites first.steps)
      (stepsReads second.steps) (stepsWrites second.steps) :=
  ⟨independent.1.mono_right
      (Finset.union_subset_union Finset.subset_union_left (Finset.Subset.refl _)),
    independent.2.mono_right
      (Finset.union_subset_union Finset.subset_union_left (Finset.Subset.refl _))⟩

/-- **Shared reads do not conflict**: proposals that write nothing are
independent, whatever they read. -/
theorem Proposal.independent_of_no_writes {first second : Proposal Location Value Answer}
    (firstWritesNothing : first.writes = ∅) (secondWritesNothing : second.writes = ∅) :
    first.Independent second := by
  unfold Proposal.Independent IndependentEffects
  rw [firstWritesNothing, secondWritesNothing]
  exact ⟨Finset.disjoint_empty_left _, Finset.disjoint_empty_left _⟩

/-- **Each stays valid after the other**: when a proposal is published, the reads
of every proposal independent of it are kept. -/
theorem Proposal.readsKept_of_independent {first second : Proposal Location Value Answer}
    (independent : first.Independent second) {world next : Location → Value}
    (published : publish first.steps world = some next) : second.ReadsKept world next :=
  agreesOn_of_preservesOutside independent.1
    ((publish_effectFootprinted first.steps).preserves published)

/-- Publish proposals one after another, as one publication of their steps. -/
def publishAll (proposals : List (Proposal Location Value Answer)) (world : Location → Value) :
    Option (Location → Value) :=
  publish (proposals.flatMap fun proposal => proposal.steps) world

@[simp] theorem publishAll_nil (world : Location → Value) :
    publishAll ([] : List (Proposal Location Value Answer)) world = some world :=
  rfl

theorem publishAll_cons (proposal : Proposal Location Value Answer)
    (rest : List (Proposal Location Value Answer)) (world : Location → Value) :
    publishAll (proposal :: rest) world =
      (publish proposal.steps world).bind (publishAll rest) := by
  unfold publishAll
  rw [List.flatMap_cons, publish_append]

/-- **A wave has one result.**  Proposals that are independent in pairs are
published in every order with the same final state, or refused in every order. -/
theorem publishAll_perm {proposals reordered : List (Proposal Location Value Answer)}
    (perm : proposals.Perm reordered) (independent : proposals.Pairwise Proposal.Independent)
    (world : Location → Value) : publishAll proposals world = publishAll reordered world := by
  induction perm generalizing world with
  | nil => rfl
  | cons proposal _ ih =>
      rw [publishAll_cons, publishAll_cons]
      congr 1
      funext next
      exact ih (List.pairwise_cons.mp independent).2 next
  | swap first second rest =>
      have independentPair : second.Independent first :=
        (List.pairwise_cons.mp independent).1 first List.mem_cons_self
      calc publishAll (second :: first :: rest) world
          = ((publish second.steps world).bind (publish first.steps)).bind (publishAll rest) := by
            rw [publishAll_cons, Option.bind_assoc]
            congr 1
            funext next
            exact publishAll_cons first rest next
        _ = ((publish first.steps world).bind (publish second.steps)).bind (publishAll rest) := by
            rw [publish_comm_of_independent independentPair.steps world]
        _ = publishAll (first :: second :: rest) world := by
            rw [publishAll_cons, Option.bind_assoc]
            congr 1
            funext next
            exact (publishAll_cons second rest next).symm
  | trans firstPerm _ ihFirst ihSecond =>
      rw [ihFirst independent world,
        ihSecond ((firstPerm.pairwise_iff Proposal.Independent.symm).mp independent) world]

/-- A sequence published with kept reads is a publication of its proposals. -/
theorem publishAll_of_keptReads [DecidableEq Value]
    {entries : List ((Location → Value) × (Answer × Proposal Location Value Answer))}
    {world final : Location → Value} (published : publishWithKeptReads entries world = some final) :
    publishAll (entries.map fun entry => entry.2.2) world = some final := by
  induction entries generalizing world with
  | nil => exact published
  | cons entry rest ih =>
      rw [publishWithKeptReads] at published
      split at published
      · rw [Option.bind_eq_some_iff] at published
        obtain ⟨next, headPublished, tail⟩ := published
        rw [List.map_cons, publishAll_cons, headPublished]
        exact ih tail
      · cases published

/-- Outcomes explored from one snapshot whose proposals are independent in pairs
are published with kept reads from every state on which the reads of all of them
are kept. -/
theorem publishWithKeptReads_of_independent [DecidableEq Value] {snapshot : Location → Value}
    {outcomes : List (Answer × Proposal Location Value Answer)}
    (explored : ∀ outcome ∈ outcomes, outcome.2.outcome? snapshot = some outcome)
    (independent : outcomes.Pairwise fun first second => first.2.Independent second.2)
    {world : Location → Value}
    (kept : ∀ outcome ∈ outcomes, outcome.2.ReadsKept snapshot world) :
    ∃ final,
      publishWithKeptReads (outcomes.map fun outcome => (snapshot, outcome)) world =
        some final := by
  induction outcomes generalizing world with
  | nil => exact ⟨world, rfl⟩
  | cons outcome rest ih =>
      have headKept := kept outcome List.mem_cons_self
      have replayed : outcome.2.outcome? world = some outcome :=
        (outcome.2.outcome?_congr headKept) ▸ explored outcome List.mem_cons_self
      obtain ⟨next, headPublished, -⟩ := Proposal.outcome?_eq_some_iff.mp replayed
      obtain ⟨headIndependent, restIndependent⟩ := List.pairwise_cons.mp independent
      obtain ⟨final, restPublished⟩ :=
        ih (fun other member => explored other (List.mem_cons_of_mem outcome member))
          restIndependent (world := next) fun other member =>
            agreesOn_trans (kept other (List.mem_cons_of_mem outcome member))
              (Proposal.readsKept_of_independent (headIndependent other member) headPublished)
      refine ⟨final, ?_⟩
      rw [List.map_cons, publishWithKeptReads, if_pos headKept, headPublished]
      exact restPublished

/-- **Waves.**  Outcomes explored from one snapshot whose proposals are
independent in pairs are published from that snapshot in every order: each is
validated by kept reads when its turn comes, so each stays valid after the
others, and every order reaches one final state. -/
theorem wave_every_order [DecidableEq Value] {snapshot : Location → Value}
    {outcomes reordered : List (Answer × Proposal Location Value Answer)}
    (explored : ∀ outcome ∈ outcomes, outcome.2.outcome? snapshot = some outcome)
    (independent : outcomes.Pairwise fun first second => first.2.Independent second.2)
    (perm : outcomes.Perm reordered) :
    ∃ final,
      publishWithKeptReads (outcomes.map fun outcome => (snapshot, outcome)) snapshot = some final ∧
        publishWithKeptReads (reordered.map fun outcome => (snapshot, outcome)) snapshot =
          some final := by
  obtain ⟨final, published⟩ :=
    publishWithKeptReads_of_independent explored independent (world := snapshot)
      fun outcome _ => agreesOn_refl _ snapshot
  have reorderedIndependent :
      reordered.Pairwise fun first second => first.2.Independent second.2 :=
    (perm.pairwise_iff fun related => Proposal.Independent.symm related).mp independent
  obtain ⟨reorderedFinal, reorderedPublished⟩ :=
    publishWithKeptReads_of_independent
      (fun outcome member => explored outcome (perm.mem_iff.mpr member)) reorderedIndependent
      (world := snapshot) fun outcome _ => agreesOn_refl _ snapshot
  have raw := publishAll_of_keptReads published
  have reorderedRaw := publishAll_of_keptReads reorderedPublished
  rw [List.map_map] at raw reorderedRaw
  have same :=
    publishAll_perm (perm.map fun outcome : Answer × Proposal Location Value Answer => outcome.2)
      (List.pairwise_map.mpr independent) snapshot
  have sameFinal : final = reorderedFinal :=
    Option.some.inj (raw.symm.trans (same.trans reorderedRaw))
  exact ⟨final, published, sameFinal ▸ reorderedPublished⟩

end Waves

/-! ## Controls -/

namespace Controls

/-- If the gate holds `4`, add `1` to the space. -/
def gatedAddToSpace : Proposal Store (Multiset ℕ) Unit :=
  ⟨[Step.observeAtom .cell 4, Step.addAtom .space 1], Readout.const ()⟩

/-- If the gate holds `4`, answer. -/
def gatedAnswer : Proposal Store (Multiset ℕ) Unit :=
  ⟨[Step.observeAtom .cell 4], Readout.const ()⟩

/-- The gate holds `4`. -/
def gateOpen : Network Store ℕ := Pi.single .cell {4}

/-- **Positive, independence**: two proposals that read one location, of which
one writes another location, are independent. -/
theorem shared_gate_independent : gatedAddToSpace.Independent gatedAnswer := by
  decide

/-- Both orders publish, with one result. -/
theorem shared_gate_both_orders :
    (publishAll [gatedAddToSpace, gatedAnswer] gateOpen).map (fun world => world .space) =
        some {1} ∧
      (publishAll [gatedAnswer, gatedAddToSpace] gateOpen).map (fun world => world .space) =
        some {1} := by
  decide

/-- **Negative, independence**: two takers of a token in one space. -/
theorem takers_not_independent : ¬ takeToken.Independent takeToken := by
  decide

/-- **Negative, publication of several**: two takers of one token are refused
together, and nothing is returned but the refusal. -/
theorem takers_refused_together :
    (publishAll [takeToken, takeToken] oneToken).isSome = false := by
  decide

/-- **A race on one token**: from the snapshot with one token each taker has its
outcome; published one after the other, the second is refused, in the only
order there is. -/
theorem takers_race :
    (takeToken.outcome? oneToken).isSome ∧
      (publishWithKeptReads [(oneToken, ((), takeToken)), (oneToken, ((), takeToken))]
        oneToken).isSome = false ∧
      (publishInOrder [((), takeToken), ((), takeToken)] oneToken).isSome = false := by
  decide

/-- Add `1` to the space unless the cell holds `9`. -/
def addUnlessMarked : Proposal Store (Multiset ℕ) Unit :=
  ⟨[Step.ofBagRule (SpaceRules.addUnless .space .cell 1 9) fun state =>
      inferInstanceAs (Decidable (9 ∉ state Store.cell))], Readout.const ()⟩

/-- Put `9` in the cell. -/
def mark : Proposal Store (Multiset ℕ) Unit :=
  ⟨[Step.addAtom .cell 9], Readout.const ()⟩

/-- **A race in which one writes what the other read.**  The two proposals are
not independent; both have an outcome from the empty snapshot; publishing the
mark first refuses the guarded addition, and publishing it second does not. -/
theorem absence_race :
    ¬ mark.Independent addUnlessMarked ∧
      (addUnlessMarked.outcome? empty).isSome ∧ (mark.outcome? empty).isSome ∧
      (publishInOrder [((), mark), ((), addUnlessMarked)] empty).isSome = false ∧
      (publishInOrder [((), addUnlessMarked), ((), mark)] empty).isSome = true := by
  decide

/-- The first validation refuses the guarded addition after the mark as well. -/
theorem absence_race_reads_not_kept :
    (publishWithKeptReads [(empty, ((), mark)), (empty, ((), addUnlessMarked))] empty).isSome =
      false := by
  decide

end Controls

#print axioms publish_comm_of_independent
#print axioms Proposal.independent_of_no_writes
#print axioms Proposal.readsKept_of_independent
#print axioms publishAll_perm
#print axioms publishAll_of_keptReads
#print axioms publishWithKeptReads_of_independent
#print axioms wave_every_order
#print axioms Controls.shared_gate_independent
#print axioms Controls.shared_gate_both_orders
#print axioms Controls.takers_not_independent
#print axioms Controls.takers_refused_together
#print axioms Controls.takers_race
#print axioms Controls.absence_race
#print axioms Controls.absence_race_reads_not_kept

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions
