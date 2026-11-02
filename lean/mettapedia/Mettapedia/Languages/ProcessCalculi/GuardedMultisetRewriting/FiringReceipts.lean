import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.TierZeroKernel

/-!
# Receipts identify the occurrences actually selected by a guarded rewriting firing

Equal store effects do not identify a rule's reads. A receipt records the
assignment, ordered take/read/output selections and one observed occurrence
set per check. Its validity connects those selections directly to the rule's
own matcher and templates. The existing guarded rewriting step and its declarative rule
instance are derived from that connection.

Observed regions are exact snapshots. They retain checks even when those
checks mention no variable of the conclusion. The abstract construction uses
the semantic region; an executable matcher must separately realize that
region on its admitted input profile.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources

universe uO uV uT uP uN
variable {O : Type uO} {V : Type uV} {T : Type uT} {P : Type uP} {N : Type uN}

structure FiringReceipt (O : Type uO) (V : Type uV) (T : Type uT) where
  assignment : Subst V T
  takes : List O
  reads : List O
  outputs : List O
  observations : List (Finset O)

namespace FiringReceipt

variable [DecidableEq O]

noncomputable def queries (receipt : FiringReceipt O V T) (layer : TermLayer V T P) (rule : Rule V T P) :
    List (PredicateQuery O T) :=
  (rule.checks.zip receipt.observations).map fun pair =>
    ⟨semRegion layer receipt.assignment pair.1.pattern, pair.2⟩

noncomputable def commit (receipt : FiringReceipt O V T) (layer : TermLayer V T P) (rule : Rule V T P) : Commit O T :=
  ⟨receipt.takes.toFinset, receipt.reads.toFinset, receipt.outputs.toFinset, receipt.queries layer rule⟩

structure ValidAt (receipt : FiringReceipt O V T) (layer : TermLayer V T P) (rule : Rule V T P)
    (label : O → T) (before : Finset O) : Prop where
  uniqueTakes : receipt.takes.Nodup
  uniqueOutputs : receipt.outputs.Nodup
  takesPresent : receipt.takes.toFinset ⊆ before
  readsPresent : receipt.reads.toFinset ⊆ before
  apart : Disjoint receipt.takes.toFinset receipt.reads.toFinset
  fresh : Disjoint receipt.outputs.toFinset before
  binds : BindsOnlyGathers layer rule receipt.assignment
  takesMatch : List.Forall₂ (layer.Solves receipt.assignment) rule.take (receipt.takes.map label)
  readsMatch : List.Forall₂ (layer.Solves receipt.assignment) rule.read (receipt.reads.map label)
  makes : instTemplate layer receipt.assignment rule.produce = some (receipt.outputs.map label)
  checks : List.Forall₂ (fun check seen =>
    (⟨semRegion layer receipt.assignment check.pattern, seen⟩ : PredicateQuery O T).Holds label before ∧
      check.holds receipt.assignment (labels label seen)) rule.checks receipt.observations

variable {receipt : FiringReceipt O V T} {layer : TermLayer V T P} {rule : Rule V T P}
variable {label : O → T} {before : Finset O}

theorem ValidAt.enabled (valid : receipt.ValidAt layer rule label before) :
    Enabled label before (receipt.commit layer rule) := by
  refine ⟨valid.takesPresent, valid.readsPresent, valid.apart, valid.fresh, ?_⟩
  intro query member
  obtain ⟨pair, pairMember, rfl⟩ := List.mem_map.mp member
  exact (List.forall₂_zip valid.checks pairMember).1

theorem ValidAt.checks_hold (valid : receipt.ValidAt layer rule label before) :
    ∀ check ∈ rule.checks, check.holds receipt.assignment
      (matchesIn layer receipt.assignment check.pattern (labels label before)) := by
  intro check member
  obtain ⟨seen, _, observation, accepted⟩ := mem_of_forall₂ valid.checks.flip check member
  rw [matchesIn_labels]
  change regionOf label before (semRegion layer receipt.assignment check.pattern) = seen at observation
  rw [observation]
  exact accepted

/-- Reuse of a fixed receipt is controlled by its occurrence requirements and
exact observations. Its original matching and template evidence stays valid. -/
theorem ValidAt.reuse (valid : receipt.ValidAt layer rule label before) {later : Finset O}
    (enabled : Enabled label later (receipt.commit layer rule)) : receipt.ValidAt layer rule label later := by
  refine ⟨valid.uniqueTakes, valid.uniqueOutputs, enabled.taken_subset, enabled.kept_subset,
    enabled.apart, enabled.fresh, valid.binds, valid.takesMatch, valid.readsMatch, valid.makes, ?_⟩
  apply List.forall₂_iff_zip.mpr
  refine ⟨valid.checks.length_eq, ?_⟩
  intro check seen member
  refine ⟨?_, (List.forall₂_zip valid.checks member).2⟩
  apply enabled.queries_hold
  exact List.mem_map.mpr ⟨(check, seen), member, rfl⟩

theorem ValidAt.reuse_iff (valid : receipt.ValidAt layer rule label before) (later : Finset O) :
    receipt.ValidAt layer rule label later ↔ Enabled label later (receipt.commit layer rule) :=
  ⟨ValidAt.enabled, valid.reuse⟩

theorem ValidAt.partition (valid : receipt.ValidAt layer rule label before) :
    labels label before = labels label (before \ (receipt.takes.toFinset ∪ receipt.reads.toFinset)) +
      ((receipt.takes.map label : List T) : Multiset T) + labels label receipt.reads.toFinset := by
  have included : receipt.takes.toFinset ∪ receipt.reads.toFinset ⊆ before :=
    Finset.union_subset valid.takesPresent valid.readsPresent
  rw [add_assoc, ← labels_toFinset label valid.uniqueTakes, ← labels_union_of_disjoint label valid.apart,
    ← labels_union_of_disjoint label Finset.sdiff_disjoint, Finset.sdiff_union_of_subset included]

/-- This is the core step itself, with the recorded selections as its witnesses. -/
theorem ValidAt.step [DecidableEq T] (valid : receipt.ValidAt layer rule label before) :
    Step layer rule (labels label before) (labels label (fire before (receipt.commit layer rule))) := by
  obtain ⟨readCount, readMembers⟩ := labels_toFinset_reads label receipt.reads
  refine ⟨receipt.assignment, labels label (before \ (receipt.takes.toFinset ∪ receipt.reads.toFinset)),
    receipt.takes.map label, labels label receipt.reads.toFinset, receipt.outputs.map label,
    valid.binds, ⟨_, valid.takesMatch, rfl⟩, ⟨_, valid.readsMatch, readCount, readMembers⟩,
    valid.partition, valid.checks_hold, valid.makes, ?_⟩
  rw [labels_fire valid.enabled]
  change labels label before - labels label receipt.takes.toFinset + labels label receipt.outputs.toFinset = _
  rw [labels_toFinset label valid.uniqueTakes, labels_toFinset label valid.uniqueOutputs, valid.partition]
  rw [add_right_comm, add_tsub_cancel_right]

/-- The retained premise occurrences are selected by the receipt, not inferred
from equality of the final stores. Equal-valued occurrences remain distinct. -/
def premiseOccurrences (receipt : FiringReceipt O V T) (space : T → N) [DecidableEq N]
    (label : O → T) (theorems : N) : Finset O :=
  (receipt.takes.toFinset ∪ receipt.reads.toFinset).filter fun occurrence => space (label occurrence) = theorems

theorem ValidAt.premise_labels [DecidableEq N] (valid : receipt.ValidAt layer rule label before)
    (space : T → N) (theorems : N) :
    labels label (receipt.premiseOccurrences space label theorems) =
      snapshot space theorems (labels label receipt.takes.toFinset + labels label receipt.reads.toFinset) := by
  rw [← labels_union_of_disjoint label valid.apart]
  simp only [premiseOccurrences, labels, snapshot, Finset.filter_val, Multiset.filter_map, Function.comp_def]

theorem ValidAt.ruleInstance [DecidableEq N] {C : Calculus V T P N} {contract : Contract}
    (valid : receipt.ValidAt (C.readers.layer contract) rule label before) (theorems : N)
    {output : O} (produced : output ∈ receipt.outputs) (atTheorems : C.space (label output) = theorems) :
    TierZeroKernel.RuleInstance C contract rule theorems
      (snapshot C.space theorems (labels label receipt.takes.toFinset + labels label receipt.reads.toFinset))
      (label output) := by
  obtain ⟨readCount, readMembers⟩ := labels_toFinset_reads label receipt.reads
  refine ⟨receipt.assignment, labels label (before \ (receipt.takes.toFinset ∪ receipt.reads.toFinset)),
    receipt.takes.map label, labels label receipt.reads.toFinset, receipt.outputs.map label,
    valid.binds, ⟨_, valid.takesMatch, rfl⟩, ⟨_, valid.readsMatch, readCount, readMembers⟩,
    ?_, valid.makes, ?_, List.mem_map.mpr ⟨output, produced, rfl⟩, atTheorems⟩
  · rw [← valid.partition]
    exact valid.checks_hold
  · rw [labels_toFinset label valid.uniqueTakes]

theorem ValidAt.ruleInstance_occurrences [DecidableEq N] {C : Calculus V T P N} {contract : Contract}
    (valid : receipt.ValidAt (C.readers.layer contract) rule label before) (theorems : N)
    {output : O} (produced : output ∈ receipt.outputs) (atTheorems : C.space (label output) = theorems) :
    TierZeroKernel.RuleInstance C contract rule theorems
      (labels label (receipt.premiseOccurrences C.space label theorems)) (label output) := by
  rw [valid.premise_labels]
  exact valid.ruleInstance theorems produced atTheorems

end FiringReceipt
end Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting
