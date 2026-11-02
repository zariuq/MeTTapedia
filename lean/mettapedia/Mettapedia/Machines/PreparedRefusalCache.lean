import Mettapedia.Machines.CompilerDemandTrace

/-!
# Revision-scoped refusals at distinct preparation stages

A completed source assessment can rule out pure entry while its frontend
still compiles. Frontend and source inquiries therefore remain distinct;
the entry inquiry may use either certificate. Only stable frontend errors
and completed negative source assessments are retained. The cache keeps no
operands, bindings, entered results or continuations.

The reference executes the compiler script under the callee's source policy.
The cache independently records, matches and validates refusal certificates.
Its shortcut preserves that reference and fallback. Authority stamps abstract
the complete native revision key. Correctness of the native effect classifier,
stamp construction, allocation, hashing and ABI correspondence are separate
obligations. `CompilerRefusalReport` supplies the demand-specific compiler
reporting and publication join; arbitrary compiler failure is not declared
stable. The work bound counts source observations, not instructions.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.PreparedRefusalCache

open CompilerDemandTrace

inductive Inquiry where
  | frontend (demand : Demand)
  | source
  | entry (demand : Demand)
  deriving DecidableEq, Repr

inductive Evidence where
  | frontend (demand : Demand) (reason : Nat)
  | source
  deriving DecidableEq, Repr

inductive Probe where
  | frontend (demand : Demand)
  | source (complete : Bool)
  deriving DecidableEq, Repr

structure Callee (Plan : Type) where
  pure : Bool
  compiler : Script Plan

def worker {Plan : Type} (callee : Callee Plan) (demand : Demand) : Option Plan :=
  if callee.pure then (reference demand callee.compiler).toOption else none

def meaning {Plan : Type} (callee : Callee Plan) : Inquiry → Prop
  | .source => callee.pure = false
  | .frontend demand => ∃ reason, reference demand callee.compiler = .error (.stable reason)
  | .entry demand => worker callee demand = none

def permits : Evidence → Inquiry → Bool
  | .source, .source | .source, .entry _ => true
  | .frontend first _, .frontend second | .frontend first _, .entry second =>
      decide (first = second)
  | _, _ => false

def observe {Plan : Type} (callee : Callee Plan) : Probe → Option Evidence
  | .source complete => if complete && !callee.pure then some .source else none
  | .frontend demand => match (inspect demand callee.compiler).result with
      | .error (.stable reason) => some (.frontend demand reason)
      | _ => none

def sound {Plan : Type} (callee : Callee Plan) : Evidence → Prop
  | .source => callee.pure = false
  | .frontend demand reason => reference demand callee.compiler = .error (.stable reason)

theorem observation_sound {Plan : Type} (callee : Callee Plan) (probe : Probe)
    {evidence : Evidence} (observed : observe callee probe = some evidence) :
    sound callee evidence := by
  cases probe with
  | source complete =>
      cases complete <;> cases policy : callee.pure <;>
        simp [observe, policy] at observed
      subst evidence
      exact policy
  | frontend demand =>
      rw [observe, inspect_refines] at observed
      cases result : reference demand callee.compiler with
      | ok plan => simp [result] at observed
      | error refusal =>
          cases refusal with
          | resource => simp [result] at observed
          | stable reason =>
              simp [result] at observed
              subst evidence
              exact result

theorem permitted_refusal {Plan : Type} (callee : Callee Plan) (evidence : Evidence)
    (inquiry : Inquiry) (valid : sound callee evidence)
    (allowed : permits evidence inquiry = true) : meaning callee inquiry := by
  cases evidence with
  | source =>
      cases inquiry <;> simp_all [permits, sound, meaning, worker]
  | frontend demand reason =>
      cases inquiry with
      | source => simp [permits] at allowed
      | frontend other =>
          have same : demand = other := by simpa [permits] using allowed
          subst other
          exact ⟨reason, valid⟩
      | entry other =>
          have same : demand = other := by simpa [permits] using allowed
          subst other
          change reference demand callee.compiler = .error (.stable reason) at valid
          simp [meaning, worker, valid, Except.toOption]

variable {Stamp Key Plan : Type} [DecidableEq Stamp] [DecidableEq Key]

structure Entry (Stamp Key : Type) where
  authority : Stamp
  key : Key
  evidence : Evidence
  deriving DecidableEq, Repr

abbrev Cache (Stamp Key : Type) := List (Entry Stamp Key)

def Valid (world : Stamp → Key → Callee Plan) (cache : Cache Stamp Key) : Prop :=
  ∀ entry ∈ cache, sound (world entry.authority entry.key) entry.evidence

def lookup (authority : Stamp) (key : Key) (inquiry : Inquiry) : Cache Stamp Key → Bool
  | [] => false
  | entry :: rest =>
      if entry.authority = authority ∧ entry.key = key ∧ permits entry.evidence inquiry = true
      then true else lookup authority key inquiry rest

def learn (world : Stamp → Key → Callee Plan) (before after : Stamp) (key : Key)
    (probe : Probe) (allocation : Bool) (cache : Cache Stamp Key) : Cache Stamp Key :=
  if before = after ∧ allocation = true then
    match observe (world before key) probe with
    | some evidence => ⟨before, key, evidence⟩ :: cache
    | none => cache
  else cache

omit [DecidableEq Stamp] [DecidableEq Key] in
theorem empty_valid (world : Stamp → Key → Callee Plan) : Valid world [] := by
  simp [Valid]

omit [DecidableEq Key] in
theorem learning_valid (world : Stamp → Key → Callee Plan) (before after : Stamp)
    (key : Key) (probe : Probe) (allocation : Bool) (cache : Cache Stamp Key)
    (valid : Valid world cache) : Valid world (learn world before after key probe allocation cache) := by
  unfold learn
  split
  · cases observed : observe (world before key) probe with
    | none => exact valid
    | some evidence =>
        intro entry member
        rcases List.mem_cons.mp member with rfl | later
        · exact observation_sound _ _ observed
        · exact valid entry later
  · exact valid

theorem lookup_sound (world : Stamp → Key → Callee Plan) (authority : Stamp)
    (key : Key) (inquiry : Inquiry) (cache : Cache Stamp Key)
    (valid : Valid world cache) (hit : lookup authority key inquiry cache = true) :
    meaning (world authority key) inquiry := by
  induction cache with
  | nil => simp [lookup] at hit
  | cons entry rest ih =>
      unfold lookup at hit
      split at hit
      · rename_i matchKey
        obtain ⟨sameAuthority, sameKey, allowed⟩ := matchKey
        subst authority
        subst key
        exact permitted_refusal _ _ _ (valid entry (by simp)) allowed
      · exact ih (fun item member => valid item (by simp [member])) hit

def execute (callee : Callee Plan) (demand : Demand) {Result : Type}
    (publish : Plan → Result) (fallback : Result) : Result :=
  match worker callee demand with
  | some plan => publish plan
  | none => fallback

def executeCached (world : Stamp → Key → Callee Plan) (authority : Stamp) (key : Key)
    (demand : Demand) (cache : Cache Stamp Key) {Result : Type}
    (publish : Plan → Result) (fallback : Result) : Result :=
  if lookup authority key (.entry demand) cache then fallback
  else execute (world authority key) demand publish fallback

theorem execution_exact (world : Stamp → Key → Callee Plan) (authority : Stamp)
    (key : Key) (demand : Demand) (cache : Cache Stamp Key) (valid : Valid world cache)
    {Result : Type} (publish : Plan → Result) (fallback : Result) :
    executeCached world authority key demand cache publish fallback =
      execute (world authority key) demand publish fallback := by
  unfold executeCached
  split
  · rename_i hit
    have refused := lookup_sound world authority key (.entry demand) cache valid hit
    simp [meaning] at refused
    simp [execute, refused]
  · rfl

omit [DecidableEq Key] in
theorem incomplete_not_retained (world : Stamp → Key → Callee Plan) (authority : Stamp)
    (key : Key) (allocation : Bool) (cache : Cache Stamp Key) :
    learn world authority authority key (.source false) allocation cache = cache := by
  simp [learn, observe]

omit [DecidableEq Key] in
theorem changed_authority_not_retained (world : Stamp → Key → Callee Plan)
    (before after : Stamp) (changed : before ≠ after) (key : Key) (probe : Probe)
    (allocation : Bool) (cache : Cache Stamp Key) :
    learn world before after key probe allocation cache = cache := by
  simp [learn, changed]

omit [DecidableEq Key] in
theorem allocation_failure_not_retained (world : Stamp → Key → Callee Plan)
    (before after : Stamp) (key : Key) (probe : Probe) (cache : Cache Stamp Key) :
    learn world before after key probe false cache = cache := by
  simp [learn]

theorem source_installation (world : Stamp → Key → Callee Plan) (authority : Stamp)
    (key : Key) (cache : Cache Stamp Key) (refused : (world authority key).pure = false) :
    lookup authority key .source
      (learn world authority authority key (.source true) true cache) = true := by
  simp [learn, observe, refused, lookup, permits]

/-- Each miss observes the source once; a hit observes no source. -/
def repeatSource (world : Stamp → Key → Callee Plan) (authority : Stamp) (key : Key) :
    Nat → Cache Stamp Key → Nat
  | 0, _ => 0
  | n + 1, cache =>
      if lookup authority key .source cache then repeatSource world authority key n cache
      else 1 + repeatSource world authority key n
        (learn world authority authority key (.source true) true cache)

theorem source_hits_observe_nothing (world : Stamp → Key → Callee Plan) (authority : Stamp)
    (key : Key) (cache : Cache Stamp Key) (hit : lookup authority key .source cache = true)
    (n : Nat) : repeatSource world authority key n cache = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [repeatSource, hit, ih]

theorem refused_source_observed_once (world : Stamp → Key → Callee Plan) (authority : Stamp)
    (key : Key) (refused : (world authority key).pure = false) (n : Nat) :
    repeatSource world authority key (n + 1) [] = 1 := by
  simp only [repeatSource, lookup, Bool.false_eq_true, ↓reduceIte]
  rw [source_hits_observe_nothing world authority key _
    (source_installation world authority key [] refused)]

namespace Controls

def dynamic : Callee Nat := ⟨false, .done 42⟩

theorem source_refusal_is_not_frontend_refusal :
    observe dynamic (.source true) = some .source ∧
    permits .source (.frontend .scalar) = false ∧
    reference .scalar dynamic.compiler = .ok 42 ∧ worker dynamic .scalar = none := by
  decide

theorem demand_specific_frontend_refusal :
    observe (⟨true, CompilerDemandTrace.Controls.scalarOnly⟩ : Callee Nat)
        (.frontend .scalar) = some (.frontend .scalar 7) ∧
    permits (.frontend .scalar 7) (.entry .answers) = false := by decide

theorem resource_refusal_is_retryable :
    observe (⟨true, .refuse .resource⟩ : Callee Nat) (.frontend .scalar) = none := by decide

theorem stale_record_does_not_hit :
    lookup 2 7 (.entry .scalar) [⟨1, 7, .source⟩] = false := by decide

theorem source_fact_covers_both_result_demands :
    permits .source (.entry .scalar) = true ∧ permits .source (.entry .answers) = true := by
  decide

end Controls
end Mettapedia.Machines.PreparedRefusalCache
