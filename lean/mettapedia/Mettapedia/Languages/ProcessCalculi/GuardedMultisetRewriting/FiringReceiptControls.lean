import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.FiringReceipts

/-! # Actual read selections, equal-valued occurrences and retained absence checks -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.FiringReceiptControls

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources.Commutative
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources.Controls

def label (occurrence : Nat) : Tm Sig := if occurrence = 2 then k .out else k .tok

def shared : FiringReceipt Nat Nat (Tm Sig) := ⟨empty, [], [0, 0], [2], []⟩
def distinct : FiringReceipt Nat Nat (Tm Sig) := ⟨empty, [], [0, 1], [2], []⟩

theorem shared_valid : shared.ValidAt Ls Examples.twoReads label {0} := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    fun _ _ => rfl, .nil, .cons Examples.solves_tok (.cons Examples.solves_tok .nil), rfl, .nil⟩

theorem distinct_valid : distinct.ValidAt Ls Examples.twoReads label {0, 1} := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    fun _ _ => rfl, .nil, .cons Examples.solves_tok (.cons Examples.solves_tok .nil), rfl, .nil⟩

theorem shared_read_interface : shared.premiseOccurrences (fun _ => ()) label () = {0} := by decide
theorem distinct_read_interface : distinct.premiseOccurrences (fun _ => ()) label () = {0, 1} := by decide

def oneRead : Rule Nat (Tm Sig) (Pat Nat Sig) := ⟨[], [.leaf .tok], [], [.leaf .out]⟩
def firstRead : FiringReceipt Nat Nat (Tm Sig) := ⟨empty, [], [0], [2], []⟩
def secondRead : FiringReceipt Nat Nat (Tm Sig) := ⟨empty, [], [1], [2], []⟩

theorem first_valid : firstRead.ValidAt Ls oneRead label {0, 1} := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    fun _ _ => rfl, .nil, .cons Examples.solves_tok .nil, rfl, .nil⟩

theorem second_valid : secondRead.ValidAt Ls oneRead label {0, 1} := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    fun _ _ => rfl, .nil, .cons Examples.solves_tok .nil, rfl, .nil⟩

/-- Identical before/after occurrence stores do not determine which equal-valued
occurrence supplied the premise. Both receipts are actual valid firings. -/
theorem same_effect_different_premises :
    fire {0, 1} (firstRead.commit Ls oneRead) = fire {0, 1} (secondRead.commit Ls oneRead) ∧
      firstRead.premiseOccurrences (fun _ => ()) label () ≠ secondRead.premiseOccurrences (fun _ => ()) label () :=
  ⟨rfl, by decide⟩

def duplicateTake : FiringReceipt Nat Nat (Tm Sig) := ⟨empty, [0, 0], [], [2], []⟩

theorem duplicate_consumption_refused (rule : Rule Nat (Tm Sig) (Pat Nat Sig)) (before : Finset Nat) :
    ¬duplicateTake.ValidAt Ls rule label before := by
  intro valid
  have impossible := valid.uniqueTakes
  simp [duplicateTake] at impossible

def guarded : Rule Nat (Tm Sig) (Pat Nat Sig) :=
  ⟨[], [.leaf .tok], [Check.absent (.leaf .lock)], [.leaf .out]⟩

def guardedLabel (occurrence : Nat) : Tm Sig :=
  if occurrence = 1 then k .lock else label occurrence

def observedAbsent : FiringReceipt Nat Nat (Tm Sig) := ⟨empty, [], [0], [2], [∅]⟩

theorem absence_receipt_valid : observedAbsent.ValidAt Ls guarded guardedLabel {0} := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    fun _ _ => rfl, .nil, .cons Examples.solves_tok .nil, rfl, .cons ⟨?_, rfl⟩ .nil⟩
  change regionOf guardedLabel {0} (semRegion Ls empty (.leaf .lock)) = ∅
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro occurrence member
  obtain ⟨present, matchesLock⟩ := Finset.mem_filter.mp member
  have same : occurrence = 0 := by simpa using present
  subst occurrence
  have equal := Examples.covers_leaf_iff.mp ((semRegion_eq_true _).mp matchesLock)
  simp [guardedLabel, label, k] at equal

theorem added_blocker_refuses_receipt : ¬observedAbsent.ValidAt Ls guarded guardedLabel {0, 1} := by
  intro valid
  have absent := valid.checks_hold (Check.absent (.leaf .lock)) (by simp [guarded])
  change matchesIn Ls empty (.leaf .lock) (labels guardedLabel {0, 1}) = 0 at absent
  have member : k .lock ∈ matchesIn Ls empty (.leaf .lock) (labels guardedLabel {0, 1}) := by
    apply mem_matchesIn.mpr
    refine ⟨?_, Examples.covers_leaf_iff.mpr rfl⟩
    apply Multiset.mem_map.mpr
    exact ⟨1, by simp, rfl⟩
  rw [absent] at member
  exact Multiset.notMem_zero _ member

end Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.FiringReceiptControls
