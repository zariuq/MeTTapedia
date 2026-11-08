import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypingScopeCapture
import Mettapedia.Machines.RevisionedOccurrenceStore
import Mettapedia.Machines.OrderedDependencyOverlay

/-!
# Editable typing-scope publication and physical occurrence identity

The source correction is extended to removal and replacement of a particular
occurrence, not removal by payload equality. Full revisions invalidate old
position tokens on every successful write. Typing revisions advance when an
old or new row can affect typing. Prefix-rewrite epochs advance on deletion
and replacement, including data-only edits: inherited overlay coordinates
must not silently refer to a shifted row.

These are executable source publication operations. They derive unchanged
typing-packet and inherited-prefix laws for arbitrary mixed edit histories.
Their native realization still requires the corrected classifier and the
runtime's publication/overflow discipline.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypingScopeEdits

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Machines
open NativeTypingScopeCapture TypeScopeClosure

/-- The repaired ordinary-atom native classifier: literal typing rows, or
the shared outer-open predicate, publish a declaration/opaque mutation. -/
def repairedNativeRelevant (row : Atom) : Bool := nativeDeclarationRow row || openRow row

theorem repaired_classifier_covers_potential (row : Atom) (potential : potentialTypingRow row = true) :
    repairedNativeRelevant row = true := by
  cases opened : openRow row with
  | true => simp [repairedNativeRelevant, opened]
  | false => simp [repairedNativeRelevant, opened, potential_with_closed_head_is_literal row potential opened]

theorem repaired_data_only_is_irrelevant (row : Atom) (dataOnly : repairedNativeRelevant row = false) :
    potentialTypingRow row = false := by
  cases relevant : potentialTypingRow row with
  | false => rfl
  | true => have yes := repaired_classifier_covers_potential row relevant; simp_all

theorem capture_eraseIdx (rows : List Atom) (index : Nat)
    (irrelevant : ∀ row, rows[index]? = some row → potentialTypingRow row = false) :
    capture (rows.eraseIdx index) = capture rows := by
  induction rows generalizing index with
  | nil => simp [capture]
  | cons row rows ih =>
      cases index with
      | zero =>
          have skip := irrelevant row rfl
          simp [capture, skip]
      | succ index =>
          have tail := ih index (fun other found => irrelevant other (by simpa using found))
          simpa [capture, List.eraseIdx_cons_succ, List.filter_cons] using
            congrArg (fun remaining => if potentialTypingRow row then row :: remaining else remaining) tail

theorem capture_set (rows : List Atom) (index : Nat) (replacement : Atom)
    (oldIrrelevant : ∀ row, rows[index]? = some row → potentialTypingRow row = false)
    (newIrrelevant : potentialTypingRow replacement = false) :
    capture (rows.set index replacement) = capture rows := by
  induction rows generalizing index with
  | nil => simp [capture]
  | cons row rows ih =>
      cases index with
      | zero =>
          have skip := oldIrrelevant row rfl
          simp [capture, skip, newIrrelevant]
      | succ index =>
          have tail := ih index (fun other found => oldIrrelevant other (by simpa using found))
          simpa [capture, List.filter_cons] using
            congrArg (fun remaining => if potentialTypingRow row then row :: remaining else remaining) tail

structure State where
  view : RevisionedStoreView Nat Nat Atom
  typingRevision : Nat
  prefixEpoch : Nat

/-- Unordered native removal fills the selected hole with the last row.
Both the removed row and the relocated row contribute to classification. -/
def prepareSwapErase (rows : List Atom) (index : Nat) : Option (List Atom × Bool) :=
  match rows.drop index with
  | [] => none
  | old :: suffix =>
      match suffix.getLast? with
      | none => some (rows.take index, potentialTypingRow old)
      | some last => some (rows.take index ++ last :: suffix.dropLast,
          potentialTypingRow old || potentialTypingRow last)

theorem swap_erase_capture (before : List Atom) (index : Nat) (after : List Atom) (relevant : Bool)
    (prepared : prepareSwapErase before index = some (after, relevant)) (dataOnly : relevant = false) :
    capture after = capture before := by
  subst relevant
  cases dropped : before.drop index with
  | nil => simp [prepareSwapErase, dropped] at prepared
  | cons old suffix =>
      have splitRows : before = before.take index ++ old :: suffix := by
        simpa [dropped] using (List.take_append_drop index before).symm
      cases last : suffix.getLast? with
      | none =>
          have empty : suffix = [] := List.getLast?_eq_none_iff.mp last
          simp only [prepareSwapErase, dropped, last, Option.some.injEq, Prod.mk.injEq] at prepared
          rw [← prepared.1]
          conv_rhs => rw [splitRows, empty]
          simp [capture, List.filter_append, prepared.2]
      | some tail =>
          have suffixShape : suffix = suffix.dropLast ++ [tail] :=
            (List.dropLast_append_getLast? tail last).symm
          simp only [prepareSwapErase, dropped, last, Option.some.injEq, Prod.mk.injEq] at prepared
          have skipped : potentialTypingRow old = false ∧ potentialTypingRow tail = false :=
            Bool.or_eq_false_iff.mp prepared.2
          rw [← prepared.1]
          conv_rhs => rw [splitRows]
          have skippedSuffix : capture suffix = capture suffix.dropLast := by
            calc
              capture suffix = capture (suffix.dropLast ++ [tail]) := congrArg capture suffixShape
              _ = capture suffix.dropLast := by simp [capture, List.filter_append, skipped.2]
          simp only [capture, List.filter_append, List.filter_cons, skipped.1, skipped.2,
            Bool.false_eq_true, ↓reduceIte]
          exact congrArg (List.filter potentialTypingRow (before.take index) ++ ·) skippedSuffix.symm

inductive Edit where
  | append (row : Atom)
  | erase (index : Nat)
  | swapErase (index : Nat)
  | replace (index : Nat) (row : Atom)

def publish (before : State) (rows : List Atom) (relevant rewrites : Bool) : State :=
  ⟨before.view.replaceRevision (before.view.revision + 1) rows,
    before.typingRevision + if relevant then 1 else 0,
    before.prefixEpoch + if rewrites then 1 else 0⟩

def step (before : State) : Edit → State
  | .append row => publish before (before.view.entries ++ [row]) (potentialTypingRow row) false
  | .erase index => match before.view.entries[index]? with
      | none => before
      | some old => publish before (before.view.entries.eraseIdx index) (potentialTypingRow old) true
  | .swapErase index => match prepareSwapErase before.view.entries index with
      | none => before
      | some (rows, relevant) => publish before rows relevant true
  | .replace index row => match before.view.entries[index]? with
      | none => before
      | some old => publish before (before.view.entries.set index row)
          (potentialTypingRow old || potentialTypingRow row) true

theorem typingRevision_mono (before : State) (edit : Edit) :
    before.typingRevision ≤ (step before edit).typingRevision := by
  cases edit with
  | append row => simp only [step, publish]; omega
  | erase index =>
      simp only [step]
      split
      · exact Nat.le_refl _
      · simp only [publish]; omega
  | replace index row =>
      simp only [step]
      split
      · exact Nat.le_refl _
      · simp only [publish]; omega
  | swapErase index =>
      simp only [step]
      split
      · exact Nat.le_refl _
      · simp only [publish]; omega

theorem prefixEpoch_mono (before : State) (edit : Edit) :
    before.prefixEpoch ≤ (step before edit).prefixEpoch := by
  cases edit with
  | append row => simp [step, publish]
  | erase index =>
      simp only [step]
      split
      · exact Nat.le_refl _
      · simp [publish]
  | replace index row =>
      simp only [step]
      split
      · exact Nat.le_refl _
      · simp [publish]
  | swapErase index =>
      simp only [step]
      split
      · exact Nat.le_refl _
      · simp [publish]

theorem step_same_typing_capture (before : State) (edit : Edit)
    (same : (step before edit).typingRevision = before.typingRevision) :
    capture (step before edit).view.entries = capture before.view.entries := by
  cases edit with
  | append row =>
      cases relevant : potentialTypingRow row <;> simp [step, publish, relevant] at same ⊢
      simp [capture, List.filter_append, relevant, RevisionedStoreView.replaceRevision]
  | erase index =>
      cases found : before.view.entries[index]? with
      | none => simp [step, found]
      | some old =>
          have skip : potentialTypingRow old = false := by
            cases relevant : potentialTypingRow old <;> simp_all [step, publish]
          simp only [step, found, publish, RevisionedStoreView.replaceRevision]
          exact capture_eraseIdx _ index (fun row selected => by
            have sameRow := Option.some.inj (found.symm.trans selected)
            simpa [← sameRow] using skip)
  | replace index replacement =>
      cases found : before.view.entries[index]? with
      | none => simp [step, found]
      | some old =>
          have skip : potentialTypingRow old = false ∧ potentialTypingRow replacement = false := by
            cases oldRelevant : potentialTypingRow old <;>
              cases newRelevant : potentialTypingRow replacement <;>
                simp_all [step, publish]
          simp only [step, found, publish, RevisionedStoreView.replaceRevision]
          exact capture_set _ index replacement (fun row selected => by
            have sameRow := Option.some.inj (found.symm.trans selected)
            simpa [← sameRow] using skip.1) skip.2
  | swapErase index =>
      cases prepared : prepareSwapErase before.view.entries index with
      | none => simp [step, prepared]
      | some result =>
          obtain ⟨rows, relevant⟩ := result
          have dataOnly : relevant = false := by cases relevant <;> simp_all [step, publish]
          simpa [step, prepared, publish, RevisionedStoreView.replaceRevision] using
            swap_erase_capture before.view.entries index rows relevant prepared dataOnly

theorem step_same_prefix_epoch (before : State) (edit : Edit)
    (same : (step before edit).prefixEpoch = before.prefixEpoch) :
    before.view.entries <+: (step before edit).view.entries := by
  cases edit with
  | append row => simp [step, publish, RevisionedStoreView.replaceRevision]
  | erase index =>
      cases found : before.view.entries[index]? with
      | none => simp [step, found]
      | some old => simp [step, found, publish] at same
  | replace index row =>
      cases found : before.view.entries[index]? with
      | none => simp [step, found]
      | some old => simp [step, found, publish] at same
  | swapErase index =>
      cases prepared : prepareSwapErase before.view.entries index with
      | none => simp [step, prepared]
      | some result => obtain ⟨rows, relevant⟩ := result; simp [step, prepared, publish] at same

/-- Physical positions never acquire validity merely because the typing
projection happened not to change. -/
theorem published_occurrence_is_stale (before : State) (rows : List Atom)
    (relevant rewrites : Bool) (index : Nat) :
    (publish before rows relevant rewrites).view.resolve (before.view.occurrenceId index) = none :=
  before.view.old_occurrence_rejected_after_revision_change
    (before.view.revision + 1) rows (by omega) index

def execute (before : State) : List Edit → State
  | [] => before
  | edit :: rest => execute (step before edit) rest

theorem execute_typing_mono (before : State) (edits : List Edit) :
    before.typingRevision ≤ (execute before edits).typingRevision := by
  induction edits generalizing before with
  | nil => exact Nat.le_refl _
  | cons edit rest ih => exact (typingRevision_mono before edit).trans (ih _)

theorem execute_prefix_mono (before : State) (edits : List Edit) :
    before.prefixEpoch ≤ (execute before edits).prefixEpoch := by
  induction edits generalizing before with
  | nil => exact Nat.le_refl _
  | cons edit rest ih => exact (prefixEpoch_mono before edit).trans (ih _)

theorem execute_same_typing_capture (before : State) (edits : List Edit)
    (same : (execute before edits).typingRevision = before.typingRevision) :
    capture (execute before edits).view.entries = capture before.view.entries := by
  induction edits generalizing before with
  | nil => rfl
  | cons edit rest ih =>
      have first := typingRevision_mono before edit
      have later := execute_typing_mono (step before edit) rest
      have firstEq : (step before edit).typingRevision = before.typingRevision := by
        simp only [execute] at same
        omega
      have tailEq : (execute (step before edit) rest).typingRevision = (step before edit).typingRevision := by
        simpa [execute, firstEq] using same
      exact (ih _ tailEq).trans (step_same_typing_capture before edit firstEq)

theorem execute_same_prefix_epoch (before : State) (edits : List Edit)
    (same : (execute before edits).prefixEpoch = before.prefixEpoch) :
    before.view.entries <+: (execute before edits).view.entries := by
  induction edits generalizing before with
  | nil => exact List.prefix_refl _
  | cons edit rest ih =>
      have first := prefixEpoch_mono before edit
      have later := execute_prefix_mono (step before edit) rest
      have firstEq : (step before edit).prefixEpoch = before.prefixEpoch := by
        simp only [execute] at same
        omega
      have tailEq : (execute (step before edit) rest).prefixEpoch = (step before edit).prefixEpoch := by
        simpa [execute, firstEq] using same
      exact (step_same_prefix_epoch before edit firstEq).trans (ih _ tailEq)

theorem execute_same_typing_queries (before : State) (edits : List Edit)
    (same : (execute before edits).typingRevision = before.typingRevision)
    (subject input : Atom) (fresh : String) :
    getAnnotatedTypes ⟨(execute before edits).view.entries⟩ subject =
      getAnnotatedTypes ⟨before.view.entries⟩ subject ∧
    subtypeQuery rawWorld input fresh (execute before edits).view.entries =
      subtypeQuery rawWorld input fresh before.view.entries := by
  have captured := execute_same_typing_capture before edits same
  constructor
  · rw [← annotations_capture, captured, annotations_capture]
  · rw [← subtypeQuery_capture, captured, subtypeQuery_capture]

theorem layer_view_of_prefix (layer : OrderedDependencyOverlay.Layer Atom)
    (before after : List Atom) (isPrefix : before <+: after)
    (bound : layer.ceiling ≤ before.length) : layer.view after = layer.view before := by
  obtain ⟨suffix, rfl⟩ := isPrefix
  simp only [OrderedDependencyOverlay.Layer.view, List.take_append_of_le_length bound]

/-- A bounded inherited prefix survives the entire edit history when its
rewrite epoch stays unchanged. Later appends need not invalidate that prefix. -/
theorem inherited_overlay_of_same_prefix (before : State) (edits : List Edit)
    (layer : OrderedDependencyOverlay.Layer Atom) (bound : layer.ceiling ≤ before.view.entries.length)
    (same : (execute before edits).prefixEpoch = before.prefixEpoch) :
    layer.view (execute before edits).view.entries = layer.view before.view.entries :=
  layer_view_of_prefix layer _ _ (execute_same_prefix_epoch before edits same) bound

namespace Controls

def row : Atom := .expression [.symbol ":", .symbol "a", .symbol "A"]
def changed : Atom := .expression [.symbol ":", .symbol "a", .symbol "B"]
def note : Atom := .expression [.symbol "note", .symbol "x"]
def duplicates : State := ⟨⟨11, 4, [row, row]⟩, 8, 3⟩

theorem duplicate_occurrences_are_distinct :
    duplicates.view.occurrenceId 0 ≠ duplicates.view.occurrenceId 1 :=
  duplicates.view.occurrenceId_injective (by decide)

theorem erase_one_duplicate_invalidates :
    (step duplicates (.erase 0)).view.entries = [row] ∧
    (step duplicates (.erase 0)).typingRevision = 9 ∧
    (step duplicates (.erase 0)).view.resolve (duplicates.view.occurrenceId 1) = none := by decide

theorem replace_one_duplicate_preserves_other :
    (step duplicates (.replace 1 changed)).view.entries = [row, changed] ∧
    (step duplicates (.replace 1 changed)).typingRevision = 9 := by decide

def prefixed : State := ⟨⟨11, 4, [note, row]⟩, 8, 3⟩
def mask : OrderedDependencyOverlay.Layer Atom := ⟨2, {0}, []⟩

theorem unrelated_deletion_requires_overlay_epoch :
    (step prefixed (.erase 0)).typingRevision = prefixed.typingRevision ∧
    (step prefixed (.erase 0)).prefixEpoch ≠ prefixed.prefixEpoch ∧
    mask.view prefixed.view.entries = [row] ∧
    mask.view (step prefixed (.erase 0)).view.entries = [] := by decide

theorem append_beyond_ceiling_keeps_overlay :
    mask.view (step prefixed (.append changed)).view.entries = mask.view prefixed.view.entries ∧
    (step prefixed (.append changed)).prefixEpoch = prefixed.prefixEpoch := by decide

theorem relocated_tail_requires_typing_revision :
    let before : State := ⟨⟨11, 4, [note, row, changed]⟩, 8, 3⟩
    (step before (.swapErase 0)).view.entries = [changed, row] ∧
    (step before (.swapErase 0)).typingRevision = 9 ∧
    capture (step before (.swapErase 0)).view.entries ≠ capture before.view.entries := by decide

theorem data_only_swap_preserves_typing_occurrences :
    let before : State := ⟨⟨11, 4, [note, row, note]⟩, 8, 3⟩
    (step before (.swapErase 0)).view.entries = [note, row] ∧
    (step before (.swapErase 0)).typingRevision = 8 ∧
    capture (step before (.swapErase 0)).view.entries = capture before.view.entries := by decide

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypingScopeEdits
