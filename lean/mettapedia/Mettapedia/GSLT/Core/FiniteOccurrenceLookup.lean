import Mettapedia.GSLT.Core.LinkedInventoryLoader

/-!
# Finite occurrence-indexed lookup

A finite verifier lookup needs positive and negative observations.  Finding a
key is witnessed by its exact occurrence; failure is witnessed only after the
cursor reaches the explicit end of the inventory.  Absence is therefore never
inferred from enumeration order or from a temporarily missing runtime match.

The semantic lookup machine and its linked-row representation are kept
separate.  Each is a GSLT and receives its own OSLF-derived native type theory;
the reified inventory is the inspectable data boundary between them.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.FiniteOccurrenceLookup

open Mettapedia.GSLT

variable {Key Value : Type}

/-- One key/value occurrence in an authored finite inventory. -/
structure Entry (Key Value : Type) where
  key : Key
  value : Value
deriving DecidableEq

/-- A lookup cursor retains the already-visited prefix and remaining suffix.
Equal entries at different positions remain distinct occurrences. -/
structure Scan (Key Value : Type) where
  target : Key
  visited : List (Entry Key Value)
  remaining : List (Entry Key Value)
deriving DecidableEq

namespace Scan

/-- The complete ordered inventory carried by a lookup cursor. -/
def inventory (scan : Scan Key Value) : List (Entry Key Value) :=
  scan.visited ++ scan.remaining

/-- The exact occurrence currently under consideration. -/
def position (scan : Scan Key Value) : Nat := scan.visited.length

end Scan

/-- Public lookup observations.  A hit retains its occurrence position; a
miss retains the explicit end position reached by the scan. -/
inductive Observation (Value : Type) where
  | found (position : Nat) (value : Value)
  | missing (endPosition : Nat)
deriving DecidableEq

/-- State of the semantic lookup GSLT.  Terminal states retain the inventory
and target so observations cannot be detached from their source query. -/
inductive State (Key Value : Type) where
  | scanning (scan : Scan Key Value)
  | finished (target : Key) (inventory : List (Entry Key Value))
      (observation : Observation Value)
deriving DecidableEq

namespace State

/-- The complete ordered inventory represented by either kind of state. -/
def inventory : State Key Value → List (Entry Key Value)
  | .scanning scan => scan.inventory
  | .finished _ inventory _ => inventory

end State

/-- One finite-lookup step.  A mismatching occurrence advances the explicit
cursor, a matching occurrence returns its value and position, and failure is
possible only at the empty suffix. -/
inductive Step : State Key Value → State Key Value → Prop where
  | hit (target : Key) (visited : List (Entry Key Value))
      (next : Entry Key Value) (remaining : List (Entry Key Value))
      (same : next.key = target) :
      Step
        (.scanning ⟨target, visited, next :: remaining⟩)
        (.finished target (visited ++ next :: remaining)
          (.found visited.length next.value))
  | advance (target : Key) (visited : List (Entry Key Value))
      (next : Entry Key Value) (remaining : List (Entry Key Value))
      (different : next.key ≠ target) :
      Step
        (.scanning ⟨target, visited, next :: remaining⟩)
        (.scanning ⟨target, visited ++ [next], remaining⟩)
  | miss (target : Key) (visited : List (Entry Key Value)) :
      Step
        (.scanning ⟨target, visited, []⟩)
        (.finished target visited (.missing visited.length))

/-- Native operational theory of finite occurrence-indexed lookup. -/
def gslt (Key Value : Type) : GSLT where
  Term := State Key Value
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := Step
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

/-- OSLF-derived native modal theory of the semantic lookup machine. -/
def lookupNTT (Key Value : Type) :
    Mettapedia.OSLF.Framework.IndexedModalFunctor.ForwardModalPredicateTheory :=
  Mettapedia.OSLF.Framework.IndexedModalFunctor.oslfForwardModalObject
    (gslt Key Value)

/-- OSLF-derived native modal theory of the linked inventory that realizes
the lookup's finite occurrence carrier. -/
def inventoryNTT (Key Value : Type) :
    Mettapedia.OSLF.Framework.IndexedModalFunctor.ForwardModalPredicateTheory :=
  Mettapedia.OSLF.Framework.IndexedModalFunctor.oslfForwardModalObject
    (Mettapedia.GSLT.LinkedInventoryLoader.gslt (Entry Key Value))

/-- Initial query state over an authored occurrence sequence. -/
def initial (target : Key) (inventory : List (Entry Key Value)) :
    State Key Value :=
  .scanning ⟨target, [], inventory⟩

/-- Executable first-match observation, starting at an explicit occurrence. -/
def lookupFrom [DecidableEq Key] (position : Nat) (target : Key) :
    List (Entry Key Value) → Observation Value
  | [] => .missing position
  | next :: remaining =>
      if next.key = target then
        .found position next.value
      else
        lookupFrom (position + 1) target remaining

/-- Executable first-match observation from occurrence zero. -/
def lookup [DecidableEq Key] (target : Key)
    (inventory : List (Entry Key Value)) : Observation Value :=
  lookupFrom 0 target inventory

/-- Reify the exact lookup inventory as occurrence-indexed linked rows. -/
def reifiedInventory (inventory : List (Entry Key Value)) :
    Mettapedia.GSLT.LinkedInventoryLoader.ReifiedArtifact (Entry Key Value) :=
  Mettapedia.GSLT.LinkedInventoryLoader.reify inventory

/-- The linked representation decodes to the exact authored occurrence
sequence. -/
theorem reifiedInventory_decodes_exact
    (inventory : List (Entry Key Value)) :
    Mettapedia.GSLT.LinkedInventoryLoader.decodeInventory?
        (reifiedInventory inventory).target = some inventory := by
  exact Mettapedia.GSLT.LinkedInventoryLoader.decodeInventory?_reify inventory

/-- A row in the reified linked carrier retains a value from the authored
inventory.  This is the data-level no-invention lemma used by concrete lookup
instances before they reason about their target atom encoding. -/
theorem reifiedInventory_target_value_mem
    (inventory : List (Entry Key Value))
    (row : Mettapedia.GSLT.LinkedInventoryLoader.Row (Entry Key Value))
    (member : row ∈ (reifiedInventory inventory).target) :
    row.value ∈ inventory := by
  have sourceValue : ∀ (position : Nat)
      (entries : List (Entry Key Value))
      (candidate : Mettapedia.GSLT.LinkedInventoryLoader.Row
        (Entry Key Value)),
      candidate ∈
          Mettapedia.GSLT.LinkedInventoryLoader.rowsFrom position entries →
        candidate.value ∈ entries := by
    intro position entries
    induction entries generalizing position with
    | nil => simp
    | cons entry entries induction =>
        intro candidate member
        simp only [Mettapedia.GSLT.LinkedInventoryLoader.rowsFrom_cons,
          List.mem_cons] at member
        rcases member with rfl | member
        · simp
        · exact List.mem_cons_of_mem entry
            (induction (position + 1) candidate member)
  exact sourceValue 0 inventory row member

/-- Every lookup step preserves the complete ordered occurrence sequence. -/
theorem step_preserves_inventory {source target : State Key Value}
    (step : Step source target) :
    target.inventory = source.inventory := by
  cases step <;> simp [State.inventory, Scan.inventory, List.append_assoc]

/-- A successful one-step observation is backed by an exact source
occurrence. -/
theorem hit_step_has_source_occurrence
    {scan : Scan Key Value} {target : Key}
    {inventory : List (Entry Key Value)} {position : Nat} {value : Value}
    (step : Step (.scanning scan)
      (.finished target inventory (.found position value))) :
    ∃ entry ∈ scan.inventory,
      entry.key = scan.target ∧ entry.value = value ∧
        position = scan.position := by
  cases step with
  | hit _ visited next remaining same =>
      refine ⟨next, ?_, same, rfl, rfl⟩
      simp [Scan.inventory]

/-- A one-step missing observation is possible only at the explicit empty
suffix. -/
theorem miss_step_has_empty_suffix
    {scan : Scan Key Value} {target : Key}
    {inventory : List (Entry Key Value)} {endPosition : Nat}
    (step : Step (.scanning scan)
      (.finished target inventory (.missing endPosition))) :
    scan.remaining = [] ∧ endPosition = scan.position := by
  cases step with
  | miss _ visited => simp [Scan.position]

/-- The executable lookup cannot invent a successful key/value pair. -/
theorem lookupFrom_found_has_source_occurrence [DecidableEq Key]
    (start : Nat) (target : Key) (inventory : List (Entry Key Value))
    (position : Nat) (value : Value)
    (found : lookupFrom start target inventory = .found position value) :
    ∃ entry ∈ inventory, entry.key = target ∧ entry.value = value := by
  induction inventory generalizing start position with
  | nil => simp [lookupFrom] at found
  | cons next remaining induction =>
      by_cases same : next.key = target
      · simp [lookupFrom, same] at found
        obtain ⟨rfl, rfl⟩ := found
        exact ⟨next, by simp, same, rfl⟩
      · have tailFound :
            lookupFrom (start + 1) target remaining =
              .found position value := by
          simpa [lookupFrom, same] using found
        obtain ⟨entry, member, keyEqual, valueEqual⟩ :=
          induction (start + 1) position tailFound
        exact ⟨entry, by simp [member], keyEqual, valueEqual⟩

/-- Missing is exact: it is returned at the finite end precisely when no
inventory occurrence has the requested key. -/
theorem lookupFrom_missing_iff [DecidableEq Key]
    (start : Nat) (target : Key) (inventory : List (Entry Key Value)) :
    lookupFrom start target inventory =
        .missing (start + inventory.length) ↔
      ∀ entry ∈ inventory, entry.key ≠ target := by
  induction inventory generalizing start with
  | nil => simp [lookupFrom]
  | cons next remaining induction =>
      by_cases same : next.key = target
      · simp [lookupFrom, same]
      · constructor
        · intro missing
          have tailMissing :
              lookupFrom (start + 1) target remaining =
                .missing ((start + 1) + remaining.length) := by
            simpa only [lookupFrom, same, if_false, List.length_cons,
              Nat.add_assoc, Nat.one_add, Nat.add_one, Nat.add_succ,
              Nat.succ_add] using missing
          have tailAbsent :=
            (induction (start := start + 1)).mp tailMissing
          intro entry member
          rcases List.mem_cons.mp member with equal | member
          · simpa [equal] using same
          · exact tailAbsent entry member
        · intro absent
          have tailAbsent :
              ∀ entry ∈ remaining, entry.key ≠ target := by
            intro entry member
            exact absent entry (List.mem_cons_of_mem next member)
          have tailMissing :=
            (induction (start := start + 1)).mpr tailAbsent
          simpa only [lookupFrom, same, if_false, List.length_cons,
            Nat.add_assoc, Nat.one_add, Nat.add_one, Nat.add_succ,
            Nat.succ_add] using tailMissing

/-- Exact proof-relevant path from any lookup cursor to its executable
first-match observation. -/
def completeFrom [DecidableEq Key] (target : Key)
    (visited remaining : List (Entry Key Value)) :
    (gslt Key Value).RewritePath
      (.scanning ⟨target, visited, remaining⟩)
      (.finished target (visited ++ remaining)
        (lookupFrom visited.length target remaining)) := by
  induction remaining generalizing visited with
  | nil =>
      have step : (gslt Key Value).Step
          (.scanning ⟨target, visited, []⟩)
          (.finished target visited (.missing visited.length)) :=
        Step.miss target visited
      simpa [lookupFrom] using
        (GSLT.RewritePath.cons step
          (@GSLT.RewritePath.nil (gslt Key Value)
            (.finished target visited (.missing visited.length))))
  | cons next remaining induction =>
      by_cases same : next.key = target
      · have step : (gslt Key Value).Step
            (.scanning ⟨target, visited, next :: remaining⟩)
            (.finished target (visited ++ next :: remaining)
              (.found visited.length next.value)) :=
          Step.hit target visited next remaining same
        simpa [lookupFrom, same] using
          (GSLT.RewritePath.cons step
            (@GSLT.RewritePath.nil (gslt Key Value)
              (.finished target (visited ++ next :: remaining)
                (.found visited.length next.value))))
      · have step : (gslt Key Value).Step
            (.scanning ⟨target, visited, next :: remaining⟩)
            (.scanning ⟨target, visited ++ [next], remaining⟩) :=
          Step.advance target visited next remaining same
        refine GSLT.RewritePath.cons step ?_
        simpa [lookupFrom, same, List.append_assoc] using
          induction (visited ++ [next])

/-- Every finite query reaches its exact first-match or missing observation. -/
def complete [DecidableEq Key] (target : Key)
    (inventory : List (Entry Key Value)) :
    (gslt Key Value).RewritePath
      (initial target inventory)
      (.finished target inventory (lookup target inventory)) := by
  simpa [initial, lookup] using completeFrom target [] inventory

/-- Two equal values at different keys remain distinct lookup occurrences. -/
private def occurrenceCanary : List (Entry Nat String) :=
  [⟨4, "same"⟩, ⟨7, "same"⟩, ⟨9, "last"⟩]

example : lookup 7 occurrenceCanary = .found 1 "same" := by decide

example : lookup 8 occurrenceCanary = .missing 3 := by decide

example :
    ∃ entry ∈ occurrenceCanary,
      entry.key = 7 ∧ entry.value = "same" := by
  apply lookupFrom_found_has_source_occurrence 0 7 occurrenceCanary 1 "same"
  decide

#print axioms reifiedInventory_decodes_exact
#print axioms reifiedInventory_target_value_mem
#print axioms step_preserves_inventory
#print axioms hit_step_has_source_occurrence
#print axioms miss_step_has_empty_suffix
#print axioms lookupFrom_found_has_source_occurrence
#print axioms lookupFrom_missing_iff
#print axioms complete

end Mettapedia.GSLT.FiniteOccurrenceLookup
