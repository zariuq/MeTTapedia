import Mathlib.Tactic

/-!
# Reusing the checked arity of a nominal callable

An immutable callable identity denotes one parameter sequence. The source
inspects that sequence before classifying saturation; the target first checks
an existing full-entry receipt. Only an exact successful shape check publishes
a receipt, independently of whether worker preparation later succeeds.

This cache answers a signature question. It grants no execution authority and
retains no arguments, binding state or completed answer. Mutable program and
library admission, actual worker selection and native C correspondence remain
separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CallableArityCache

structure Entry where
  identity : Nat
  arity : Nat
  deriving DecidableEq, Repr

inductive Shape where
  | refused
  | undersupplied (missing : Nat)
  | full
  | excess (extra : Nat)
  deriving DecidableEq, Repr

variable {Name : Type}

abbrev Registry (Name : Type) := Nat → Option (List Name)

def declared (registry : Registry Name) (identity : Nat) : Option Nat :=
  (registry identity).map List.length

def Valid (registry : Registry Name) (cache : List Entry) : Prop :=
  ∀ entry ∈ cache, declared registry entry.identity = some entry.arity

def hit : List Entry → Nat → Nat → Bool
  | [], _, _ => false
  | entry :: rest, identity, supplied =>
      if entry.identity = identity ∧ entry.arity = supplied then true
      else hit rest identity supplied

def source (registry : Registry Name) (identity supplied : Nat) : Shape :=
  match declared registry identity with
  | none => .refused
  | some arity =>
      if supplied < arity then .undersupplied (arity - supplied)
      else if arity < supplied then .excess (supplied - arity)
      else .full

def target (registry : Registry Name) (cache : List Entry) (identity supplied : Nat) :
    Shape × Nat :=
  if hit cache identity supplied then (.full, 0)
  else (source registry identity supplied, 1)

def publish (registry : Registry Name) (cache : List Entry) (identity supplied : Nat) :
    List Entry :=
  if declared registry identity = some supplied then ⟨identity, supplied⟩ :: cache
  else cache

theorem empty_valid (registry : Registry Name) : Valid registry [] := by
  simp [Valid]

theorem publication_valid (registry : Registry Name) (cache : List Entry)
    (valid : Valid registry cache) (identity supplied : Nat) :
    Valid registry (publish registry cache identity supplied) := by
  unfold publish
  split
  · rename_i checked
    intro entry present
    rcases List.mem_cons.mp present with rfl | tail
    · exact checked
    · exact valid entry tail
  · exact valid

theorem hit_sound (registry : Registry Name) (cache : List Entry)
    (valid : Valid registry cache) (identity supplied : Nat)
    (found : hit cache identity supplied = true) :
    declared registry identity = some supplied := by
  induction cache with
  | nil => simp [hit] at found
  | cons entry rest ih =>
      by_cases same : entry.identity = identity ∧ entry.arity = supplied
      · obtain ⟨head, arity⟩ := same
        simpa [head, arity] using valid entry (List.mem_cons_self ..)
      · exact ih (fun item present => valid item (List.mem_cons_of_mem _ present))
          (by simpa [hit, same] using found)

theorem classification_refines (registry : Registry Name) (cache : List Entry)
    (valid : Valid registry cache) (identity supplied : Nat) :
    (target registry cache identity supplied).1 = source registry identity supplied := by
  unfold target
  split
  · rename_i found
    simp [source, hit_sound registry cache valid identity supplied found]
  · rfl

theorem cached_entry_reads_no_signature (registry : Registry Name) (cache : List Entry)
    (identity supplied : Nat) (found : hit cache identity supplied = true) :
    (target registry cache identity supplied).2 = 0 := by
  simp [target, found]

theorem different_arity_misses (identity known supplied : Nat) (different : known ≠ supplied) :
    hit [⟨identity, known⟩] identity supplied = false := by
  simp [hit, different]

theorem other_identity_misses (known identity supplied : Nat) (different : known ≠ identity) :
    hit [⟨known, supplied⟩] identity supplied = false := by
  simp [hit, different]

theorem unchecked_receipt_changes_partial :
    (target (fun _ => some [(), ()]) [⟨7, 1⟩] 7 1).1 ≠
      source (fun _ => some [(), ()]) 7 1 := by
  decide +kernel


section WorkerAvailability

variable {Input Output : Type}

inductive Worker (Input Output : Type) where
  | scalar (run : Input → Option Output)
  | answersOnly

def scalarProbe (worker : Worker Input Output) (input : Input) : Option Output :=
  match worker with
  | .scalar run => run input
  | .answersOnly => none

def sourceWorker (worker : Worker Input Output) (fallback : Input → Output)
    (input : Input) : Output × Nat :=
  ((scalarProbe worker input).getD (fallback input), 1)

def selectedWorker (worker : Worker Input Output) (fallback : Input → Output)
    (input : Input) : Output × Nat :=
  match worker with
  | .scalar run => ((run input).getD (fallback input), 1)
  | .answersOnly => (fallback input, 0)

theorem worker_selection_refines (worker : Worker Input Output)
    (fallback : Input → Output) (input : Input) :
    (selectedWorker worker fallback input).1 = (sourceWorker worker fallback input).1 := by
  cases worker <;> rfl

theorem absent_worker_avoids_probe (fallback : Input → Output) (input : Input) :
    selectedWorker .answersOnly fallback input = (fallback input, 0) := by
  rfl

theorem input_refusal_still_probes :
    let worker : Worker Nat Nat := .scalar (fun input => if input = 0 then none else some input)
    (selectedWorker worker (fun _ => 0) 0).1 = 0 ∧
    (selectedWorker worker (fun _ => 0) 1) = (1, 1) := by
  decide +kernel

theorem remembering_one_refusal_as_absence_changes_result :
    let worker : Worker Nat Nat := .scalar (fun input => if input = 0 then none else some input)
    scalarProbe worker 0 = none ∧
      (selectedWorker (Worker.answersOnly : Worker Nat Nat) (fun _ => 0) 1).1 ≠
        (sourceWorker worker (fun _ => 0) 1).1 := by
  decide +kernel

end WorkerAvailability

end Mettapedia.Machines.CallableArityCache

#print axioms Mettapedia.Machines.CallableArityCache.empty_valid
#print axioms Mettapedia.Machines.CallableArityCache.publication_valid
#print axioms Mettapedia.Machines.CallableArityCache.hit_sound
#print axioms Mettapedia.Machines.CallableArityCache.classification_refines
#print axioms Mettapedia.Machines.CallableArityCache.cached_entry_reads_no_signature
#print axioms Mettapedia.Machines.CallableArityCache.different_arity_misses
#print axioms Mettapedia.Machines.CallableArityCache.other_identity_misses
#print axioms Mettapedia.Machines.CallableArityCache.unchecked_receipt_changes_partial
#print axioms Mettapedia.Machines.CallableArityCache.worker_selection_refines
#print axioms Mettapedia.Machines.CallableArityCache.absent_worker_avoids_probe
#print axioms Mettapedia.Machines.CallableArityCache.input_refusal_still_probes
#print axioms Mettapedia.Machines.CallableArityCache.remembering_one_refusal_as_absence_changes_result
