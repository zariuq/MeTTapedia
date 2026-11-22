import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions.CapturedReads
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions.Cells
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions.CommitBorder
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions.ConsumeConservation
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions.DeltaMerge
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions.Granularity
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions.Handlers
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions.ResourceWaveComparison
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions.SearchCode

/-!
# Regions, modes, the commit border and `consume`: the laws

A region is a finite program of local rule instances with answers.  It runs in
one of two modes over a located state: committed, where every step changes the
shared state at once, or branch-local, where it runs on a private view of a
snapshot and returns outcomes, each an answer with a proposal.  Publication
validates a proposal against the live state and applies it as one step, or
refuses it.  An observation closes a region with a policy that says which answers
are returned and which proposals are published.  `consume` is the smallest
publication: one step that matches an occurrence, checks a guard and removes the
occurrence.

This module imports the development and lists where each law is proved.

* **Two modes.**  The committed run and the branch-local run of a region are the
  shared and the isolated handler of one free computation with choice and state.
  `Region.runShared_toProgram`, `Region.runWorlds_toProgram`.
* **One region alone.**  Publishing the proposal on the unchanged snapshot is the
  committed run.
  `Proposal.modes_agree`, `Region.committed_of_mem_branchLocal`.
* **Frame.**  The outcomes of a branch-local region depend only on the snapshot
  restricted to what the region reads and writes; a branch-local region changes
  no store.
  `Region.branchLocal_congr`, `Proposal.outcome?_congr`,
  `Region.observe_publishNone`; from `publish_effectFootprinted` and
  `comp_effectFootprinted`.
* **Isolation.**  The outcomes of siblings from one snapshot are those of each
  sibling alone, so the bag of answers is the same for every order of the
  siblings.
  `Region.branchLocal_eq_flatMap`, `Region.branchLocal_alternatives`,
  `Region.branchLocal_alternatives_perm`, `Region.answers_alternatives_perm`.
* **The committed mode breaks frame and isolation.**  Two siblings that add an
  atom to one space and read it return two bags of answers in the two orders; the
  atom of a sibling that failed stays.
  `SharedSpace.committed_bags_differ`,
  `SharedSpace.committed_not_order_independent`,
  `FailedSibling.committed_keeps_failed_effect`.  The committed mode is the
  semantics of the search regions of the flat code, whose world effects persist:
  `Region.committed_eq_source`, `Region.committed_compiled`.
* **Validation is sound.**  If the live state agrees with the snapshot on what a
  proposal read and wrote, the region replayed on the live state has that
  outcome.  The converse fails.  The validation of the atomic boundary implies
  the first.
  `Region.stillHas_of_readsKept`; `Controls.second_copy_stillHas` with
  `Controls.second_copy_reads_not_kept`; `Explored.readsKept_of_matches`.  The
  first validation is the publication contract of a captured read view:
  `Proposal.readsKept_iff_canPublish`.
* **Publication is a step of the committed state.**  A sequence of valid
  publications is the committed run of the published alternatives in the order
  of publication.
  `publishInOrder_serializable`, `publishWithKeptReads_serializable`.
* **Waves.**  Proposals from one snapshot whose writes meet no other's reads or
  writes are published in every order with one result, and each stays valid
  after the others; shared reads do not conflict.
  `publish_comm_of_independent`, `publishAll_perm`, `wave_every_order`,
  `Proposal.readsKept_of_independent`, `Proposal.independent_of_no_writes`; and
  against the wave of a resource system, `stepEnables_of_independent`,
  `independent_entries_every_order`.  The grain at which a store is read as
  locations decides what is a wave: `AddOnly.kind_grain_additions_are_a_wave`
  against `AddOnly.space_grain_additions_conflict`.  The merge of a wave is an
  order-free merge of deltas whose order-freedom is proved from the footprints:
  `waveMerge`, `publishWave_change_eq_merge`.
* **A race is a conflict, and it is reported.**  If one proposal writes what
  another read or wrote, publishing the first may refuse the second; the refused
  one changes nothing and keeps its work.
  `Explored.publication_of_reads_not_kept`, `Explored.publication_ledger`,
  `Explored.independent_sibling_survives_commit`, `Controls.absence_race`,
  `Controls.second_taker_refused`.
* **Selection is not publication.**  The answers returned and the proposals
  published are two things a policy declares; a policy that is a function of the
  bag of outcomes does not depend on the order of evaluation.
  `Policy`, `Policy.publishNone_orderFree`, `Policy.publishWave_orderFree`,
  `Policy.publishChosenBy_orderFree`,
  `OnceOverAdditions.publishChosen_not_orderFree`,
  `CellWrite.same_answers_different_states`,
  `Region.observe_publishWave_of_independent`.
* **`consume` is one step.**  Its guard and its removal are one firing; two of
  them on one occurrence are a race, on two occurrences a wave; the two-step form
  lets both agents proceed past the read.
  `SpaceRules.consume_fires_iff`, `SpaceRules.consume_footprint`,
  `SpaceRules.consume_race`, `SpaceRules.consume_wave`,
  `SpaceRules.consume_two_occurrences`, `TokenRace.both_proceed_past_the_read`,
  `OneToken.race_decided_at_publication`, `consume_then_add_keeps_count`,
  `observe_then_add_adds_one`, `consume_keeps_tokens`, `observe_doubles_tokens`.

The development is stated over any separation algebra of values whose rule
instances fire as partial functions (`Step`).  The instances are given over
networks of occurrence stores, and for state cells also over exclusive cells
(`Regions.Cells`).

Not in this development: a grade on steps that says which of them may run in the
branch-local mode, and the passage of counted evidence across the commit border.
-/
