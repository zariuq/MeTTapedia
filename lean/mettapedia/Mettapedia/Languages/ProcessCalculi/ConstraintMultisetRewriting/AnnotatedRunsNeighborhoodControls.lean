import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsNeighborhood
import Mathlib.Data.List.Permutation

/-!
# Evidence and belief over the round of the taker and the reader

The run category of the control signature, from the start configuration with occurrences `0 : f(X)`
and `1 : X`. The taker takes `0` and makes `2`; the reader reads `1` and makes `3`. Both orders run
and are one contextual trace.

## Provenance evidence from the ledger

The evidence space holds the outputs `2` and `3`. Each observation reports that it was made in the
history (`AnnotatedRuns.NeighborhoodRuns.madeIn`), a report that is true of every history that
leaves it present (`AnnotatedRuns.NeighborhoodRuns.madeIn_of_mem_ledger`). Where the round ends:

* the evidence is the two reports (`provenance_pieces`);
* there is evidence that `2` was made and that `3` was made, and none that both were
  (`provenance_not_normal`); the taker alone and the reader alone separate the two reports;
* belief combines the two consistent pieces: both were made (`provenance_belief`);
* the point is not Kripke-representable (`provenance_not_kripke`).

## Conflicting reports of the order

Two reports of the order of the round, one for each order, are evidence where the round ends:

* there is evidence for each order (`order_evidence`), and belief in neither
  (`order_not_believed`);
* belief is what both orders entail: the taker fired is believed (`taker_fired_believed`);
* what is believed of the round's end is a predicate on traces (`believed_round_trace_predicate`),
  while one order alone is not (`AnnotatedRuns.PredicateControls.order_not_trace_predicate`).
-/

set_option autoImplicit false

open CategoryTheory

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

namespace NeighborhoodRuns

namespace NeighborhoodControls

open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature A)
open AnnotatedRuns.Controls (label Run taker reader start taker_valid taker_then_reader
  shared_variables_swap)
open Mettapedia.GSLT.Causality.OccurrenceHistory (OccurrencePath)
open Mettapedia.GSLT.Causality.TraceCostValuation (traceFunctor)
open Mettapedia.PLN.Bridges.GSLT.NeighborhoodProofAuthority

/-- The evidence space: the outputs `1` and `0` of the taker and the reader. -/
def space : Term signature → Bool
  | .const 0 => true
  | .const 1 => true
  | _ => false

abbrev root : Runs A label := runObject A label start

/-- The class where the round ends. -/
abbrev roundEnd : Runs A label := classOf A label (follow label start [taker, reader])

/-- The provenance evidence model. -/
abbrev provenance : EvidenceModel root :=
  ledgerEvidenceModel A label space start (madeIn A label start)

theorem roundEnd_ledger : ledgerClass A label space roundEnd = {2, 3} := by
  rw [ledgerClass_classOf]
  decide

/-- **The evidence where the round ends is the two provenance reports.** -/
theorem provenance_pieces (h : root ⟶ roundEnd) :
    provenance h = {madeIn A label start 2, madeIn A label start 3} := by
  change madeIn A label start '' ↑(ledgerClass A label space roundEnd) = _
  rw [roundEnd_ledger, Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq,
    Set.image_singleton]

theorem taker_alone : Executable A label start [taker] :=
  ⟨taker_valid, taker_valid.firing.consistent⟩

theorem reader_alone : Executable A label start [reader] :=
  ⟨shared_variables_swap.1.1, shared_variables_swap.1.1.firing.consistent⟩

/-- **The two reports are separated** at every history ending where the round ends: the taker
alone makes `2` and not `3`, the reader alone makes `3` and not `2`. -/
theorem reports_separated_at (h : root ⟶ roundEnd) :
    ∀ X ∈ provenance h, ¬ X ≤ madeIn A label start 2 ⊓ madeIn A label start 3 := by
  intro X member below
  rw [provenance_pieces] at member
  obtain ⟨takerPath, takerSites⟩ := exists_path A label start [taker] taker_alone _ rfl
  obtain ⟨readerPath, readerSites⟩ := exists_path A label start [reader] reader_alone _ rfl
  rcases member with rfl | rfl
  · have made : takerPath ∈ madeIn A label start 2 _ :=
      ⟨taker, by rw [takerSites]; exact List.mem_singleton_self _, by decide⟩
    obtain ⟨f, inSites, three⟩ := (below _ made).2
    rw [takerSites] at inSites
    obtain rfl : f = taker := List.mem_singleton.mp inSites
    revert three
    decide
  · have made : readerPath ∈ madeIn A label start 3 _ :=
      ⟨reader, by rw [readerSites]; exact List.mem_singleton_self _, by decide⟩
    obtain ⟨f, inSites, two⟩ := (below _ made).1
    rw [readerSites] at inSites
    obtain rfl : f = reader := List.mem_singleton.mp inSites
    revert two
    decide

/-- **Provenance evidence is not normal**: evidence that `2` was made and that `3` was made, none
that both were. -/
theorem provenance_not_normal (h : root ⟶ roundEnd) :
    h ∈ evidenceFor provenance (madeIn A label start 2) roundEnd ∧
      h ∈ evidenceFor provenance (madeIn A label start 3) roundEnd ∧
      h ∉ evidenceFor provenance (madeIn A label start 2 ⊓ madeIn A label start 3) roundEnd :=
  evidence_not_normal (by rw [provenance_pieces]; exact Or.inl rfl)
    (by rw [provenance_pieces]; exact Or.inr rfl) (reports_separated_at h)

/-- **Belief combines the consistent pieces**: both were made. -/
theorem provenance_belief (h : root ⟶ roundEnd) :
    h ∈ belief provenance (madeIn A label start 2 ⊓ madeIn A label start 3) roundEnd := by
  obtain ⟨p, _, pSites, _, _⟩ := PathControls.round_paths_one_trace
  refine (belief_pair_consistent (provenance_pieces h) ⟨roundEnd, p, ?_, ?_⟩ _).mpr le_rfl
  · exact ⟨taker, by rw [pSites]; exact List.mem_cons_self, by decide⟩
  · exact ⟨reader, by rw [pSites]; exact List.mem_cons_of_mem _ List.mem_cons_self, by decide⟩

/-- **The provenance point is not Kripke-representable.** -/
theorem provenance_not_kripke (h : root ⟶ roundEnd) :
    ¬ KripkeBoundary.KripkeRepresentable
      ⟨evidenceModel provenance (pairValuation (madeIn A label start 2) (madeIn A label start 3)),
        ⟨roundEnd, h⟩⟩ :=
  evidence_point_not_representable (by rw [provenance_pieces]; exact Or.inl rfl)
    (by rw [provenance_pieces]; exact Or.inr rfl) (reports_separated_at h)

/-! ## Conflicting reports of the order -/

/-- "The taker fired, then the reader." -/
def takerFirst : Family root := fun _ => {h | OccurrencePath.sites h = [taker, reader]}

/-- "The reader fired, then the taker." -/
def readerFirst : Family root := fun _ => {h | OccurrencePath.sites h = [reader, taker]}

/-- "The taker fired." -/
def takerFired : Family root := fun _ => {h | taker ∈ OccurrencePath.sites h}

/-- Two reports of the order, available everywhere. -/
def orderReports : EvidenceModel root := fun _ _ => {takerFirst, readerFirst}

theorem orders_apart :
    ∀ (y : Runs A label) (k : root ⟶ y), k ∈ takerFirst y → k ∉ readerFirst y := by
  intro y k first second
  have both : [taker, reader] = [reader, taker] := (first : _ = _).symm.trans second
  exact AnnotationControls.taker_ne_reader (List.cons.inj both).1

theorem orders_occur :
    (∃ (y : Runs A label) (k : root ⟶ y), k ∈ takerFirst y) ∧
      ∃ (y : Runs A label) (k : root ⟶ y), k ∈ readerFirst y := by
  obtain ⟨p, q, pSites, qSites, -⟩ := PathControls.round_paths_one_trace
  exact ⟨⟨roundEnd, p, pSites⟩, ⟨roundEnd, q, qSites⟩⟩

theorem order_belief_iff {x : Runs A label} (h : root ⟶ x) (χ : Family root) :
    h ∈ belief orderReports χ x ↔ takerFirst ≤ χ ∧ readerFirst ≤ χ :=
  belief_pair_conflict rfl orders_apart orders_occur.1 orders_occur.2 χ

/-- **Evidence for each order.** -/
theorem order_evidence {x : Runs A label} (h : root ⟶ x) :
    h ∈ evidenceFor orderReports takerFirst x ∧ h ∈ evidenceFor orderReports readerFirst x :=
  ⟨⟨takerFirst, Or.inl rfl, le_rfl⟩, ⟨readerFirst, Or.inr rfl, le_rfl⟩⟩

/-- **Belief in neither order.** -/
theorem order_not_believed {x : Runs A label} (h : root ⟶ x) :
    h ∉ belief orderReports takerFirst x ∧ h ∉ belief orderReports readerFirst x := by
  obtain ⟨⟨y, k, first⟩, ⟨y', k', second⟩⟩ := orders_occur
  constructor
  · intro believed
    exact orders_apart y' k' (((order_belief_iff h _).mp believed).2 y' second) second
  · intro believed
    exact orders_apart y k first (((order_belief_iff h _).mp believed).1 y first)

/-- **What both orders entail is believed**: the taker fired. -/
theorem taker_fired_believed {x : Runs A label} (h : root ⟶ x) :
    h ∈ belief orderReports takerFired x := by
  refine (order_belief_iff h _).mpr ⟨fun y k first => ?_, fun y k second => ?_⟩
  · change taker ∈ OccurrencePath.sites k
    rw [show OccurrencePath.sites k = [taker, reader] from first]
    exact List.mem_cons_self
  · change taker ∈ OccurrencePath.sites k
    rw [show OccurrencePath.sites k = [reader, taker] from second]
    exact List.mem_cons_of_mem _ List.mem_cons_self

/-- **What is believed of the round's end is a predicate on traces**: the two orders together are
closed under round equivalence. -/
theorem believed_round_trace_predicate :
    ∃ ψ, pullbackAlong root (traceFunctor (concurrency A label).tiles) ψ =
      (takerFirst roundEnd ∪ readerFirst roundEnd : Set (root ⟶ roundEnd)) := by
  refine (tracePredicate_iff A label start _).mpr ?_
  intro p q equivalent
  have perm := RoundEquiv.perm A label equivalent
  have toPair : ∀ {l l' : List Run}, l.Perm l' → (l = [taker, reader] ∨ l = [reader, taker]) →
      (l' = [taker, reader] ∨ l' = [reader, taker]) := by
    intro l l' perm' cases'
    rcases cases' with rfl | rfl
    · exact List.pair_perm.mp perm'
    · rcases List.pair_perm.mp perm' with same | same
      · exact Or.inr same
      · exact Or.inl same
  exact ⟨fun inP => toPair perm inP, fun inQ => toPair perm.symm inQ⟩

end NeighborhoodControls

end NeighborhoodRuns

open NeighborhoodRuns

#print axioms NeighborhoodControls.roundEnd_ledger
#print axioms NeighborhoodControls.provenance_pieces
#print axioms NeighborhoodControls.reports_separated_at
#print axioms NeighborhoodControls.provenance_not_normal
#print axioms NeighborhoodControls.provenance_belief
#print axioms NeighborhoodControls.provenance_not_kripke
#print axioms NeighborhoodControls.order_belief_iff
#print axioms NeighborhoodControls.order_evidence
#print axioms NeighborhoodControls.order_not_believed
#print axioms NeighborhoodControls.taker_fired_believed
#print axioms NeighborhoodControls.believed_round_trace_predicate

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
