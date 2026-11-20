import Mettapedia.Languages.MeTTa.PeTTa.MachineClauseActivation
import Mathlib.Data.List.FinRange

/-!
# Occurrence-sensitive head selection at a finite source snapshot

Each row is probed under the same incoming bindings with its own fresh opening.
Equal row payloads remain separate occurrences. Exhausted probes are retained
as unfinished work and prevent a completed uniqueness verdict. The semantic
connection uses the computed packet matcher and captured-row reading laws.

These are model selection laws. Native enumeration, source-stage transport and
the complete production machine correspondence remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MachineHeadSelection

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra (subst)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MetaMeTTaComparison (atomAction)
open Mettapedia.Languages.MeTTa.PeTTa.UnifyingConstraintPresentation (presentation)
open RuleSyntax OneFrame SchematicRows
open ListView Unifying UnifyingDisequality
open AtomFreshNamespaces (X)

def accepted : Unified → Bool
  | .ok _ => true
  | .clash | .exhausted => false

def unfinished : Unified → Bool
  | .exhausted => true
  | .ok _ | .clash => false

structure Scan (count : Nat) where
  matched : List (Fin count)
  pending : List (Fin count)
  deriving DecidableEq, Repr

def scan {count : Nat} (outcome : Fin count → Unified) : Scan count :=
  ⟨(List.finRange count).filter (accepted ∘ outcome),
    (List.finRange count).filter (unfinished ∘ outcome)⟩

theorem mem_matched {count : Nat} (outcome : Fin count → Unified) (position : Fin count) :
    position ∈ (scan outcome).matched ↔ accepted (outcome position) = true := by
  simp [scan]

theorem mem_pending {count : Nat} (outcome : Fin count → Unified) (position : Fin count) :
    position ∈ (scan outcome).pending ↔ outcome position = .exhausted := by
  simp only [scan, List.mem_filter, List.mem_finRange, true_and]
  cases evaluated : outcome position <;> simp [unfinished, evaluated]

theorem matched_nodup {count : Nat} (outcome : Fin count → Unified) :
    (scan outcome).matched.Nodup := (List.nodup_finRange count).filter _

theorem pending_empty_iff {count : Nat} (outcome : Fin count → Unified) :
    (scan outcome).pending = [] ↔ ∀ position, outcome position ≠ .exhausted := by
  rw [List.eq_nil_iff_forall_not_mem]
  simp only [mem_pending]

inductive Verdict (count : Nat) where
  | pending (matched unfinished : List (Fin count))
  | unique (position : Fin count)
  | nonunique
  deriving DecidableEq, Repr

def verdict {count : Nat} (result : Scan count) : Verdict count :=
  if result.pending = [] then
    match result.matched with
    | [position] => .unique position
    | _ => .nonunique
  else .pending result.matched result.pending

theorem pending_blocks_uniqueness {count : Nat} (result : Scan count)
    (waiting : result.pending ≠ []) :
    verdict result = .pending result.matched result.pending := by simp [verdict, waiting]

theorem unique_iff_singleton {count : Nat} (result : Scan count) (position : Fin count) :
    verdict result = .unique position ↔ result.pending = [] ∧ result.matched = [position] := by
  unfold verdict
  split
  · cases matched : result.matched with
    | nil => simp
    | cons first rest =>
        cases rest with
        | nil => simp_all
        | cons _ _ => simp
  · simp_all

private theorem singleton_of_nodup {α : Type*} {items : List α} (clean : items.Nodup)
    (item : α) (present : item ∈ items) (only : ∀ value ∈ items, value = item) :
    items = [item] := by
  cases items with
  | nil => cases present
  | cons first rest =>
      have same := only first (by simp)
      subst first
      have empty : rest = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro value member
        have equal := only value (List.mem_cons_of_mem _ member)
        subst value
        exact (List.nodup_cons.mp clean).1 member
      rw [empty]

theorem unique_iff_one_accepted {count : Nat} (outcome : Fin count → Unified)
    (position : Fin count) (settled : (scan outcome).pending = []) :
    verdict (scan outcome) = .unique position ↔
      accepted (outcome position) = true ∧
        ∀ other, accepted (outcome other) = true → other = position := by
  rw [unique_iff_singleton]
  simp only [settled, true_and]
  constructor
  · intro single
    constructor
    · apply (mem_matched outcome position).mp
      rw [single]
      simp
    · intro other success
      have member := (mem_matched outcome other).mpr success
      rw [single] at member
      exact List.mem_singleton.mp member
  · rintro ⟨success, only⟩
    exact singleton_of_nodup (matched_nodup outcome) position
      ((mem_matched outcome position).mpr success)
      (fun other member => only other ((mem_matched outcome other).mp member))

/-- A stored head remains one packet. -/
def row (function index pattern : Atom) : Atom :=
  .expression [.symbol "pm:heads", function, index, pattern]

def probe (bindings : Subst) (source query : Atom) : Unified :=
  unifyBinding bindings
    (GSLTBindingPatterns.quoted
      (LibTransformStep.rename (MachineClauseActivation.freshScope bindings query [])
        (MachineClauseActivation.packet source [])))
    (MachineClauseActivation.packet query [])

def Reading (bindings : Subst) (source query : Atom) : Prop :=
  ∃ caller : StepSubstitution, atomAction.Models caller (presentation bindings) ∧
    (MachineClauseActivation.closure PUnit.unit source [] []).ReadsAt X
      (b := PUnit.unit) caller (subst caller query)

theorem probe_iff_reading (bindings : Subst) (source query : Atom)
    (valid : Idempotent bindings) : accepted (probe bindings source query) = true ↔
      Reading bindings source query := by
  have reading := MachineClauseActivation.fresh_accepts_iff_reading
    (source := source) (query := query) (parameters := []) (arguments := []) PUnit.unit valid
  change (∃ bound, probe bindings source query = .ok bound) ↔ _ at reading
  unfold Reading
  rw [← reading]
  cases probe bindings source query <;> simp [accepted]

def snapshot (bindings : Subst) (query : Atom) (rows : List Atom) : Scan rows.length :=
  scan (fun position => probe bindings rows[position] query)

theorem snapshot_exact (bindings : Subst) (query : Atom) (rows : List Atom)
    (valid : Idempotent bindings) (position : Fin rows.length) :
    position ∈ (snapshot bindings query rows).matched ↔ Reading bindings rows[position] query := by
  rw [snapshot, mem_matched, probe_iff_reading bindings _ query valid]

theorem snapshot_unique_iff (bindings : Subst) (query : Atom) (rows : List Atom)
    (valid : Idempotent bindings) (position : Fin rows.length)
    (settled : (snapshot bindings query rows).pending = []) :
    verdict (snapshot bindings query rows) = .unique position ↔
      Reading bindings rows[position] query ∧
        ∀ other : Fin rows.length, Reading bindings rows[other] query → other = position := by
  rw [snapshot, unique_iff_one_accepted _ position settled]
  simp only [probe_iff_reading bindings _ query valid]

end Mettapedia.Languages.MeTTa.PeTTa.MachineHeadSelection
