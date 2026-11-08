import Mettapedia.Machines.ReadOnlyQuerySafety
import Mettapedia.Machines.QueryState

/-!
# Pairwise relations for state-threaded adaptive queries

Related programs have the same valid reached question and agree recursively
on every valid reply. Their pure answers are identical and satisfy the
declared answer invariant. The syntax remains the existing adaptive query
tree. Services are compared at the current private state, not through one
fixed answer for each key; repeated occurrences may allocate fresh replies.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ReadOnlyQueryRelation

open ReadOnlyQuery ReadOnlyQueryDemand ReadOnlyQuerySafety

variable {Key Reply Answer Other State : Type}

inductive Related (validKey : Key → Prop) (validReply : Reply → Prop) (validAnswer : Answer → Prop) :
    Program Key Reply Answer → Program Key Reply Answer → Prop where
  | pure {answer : Answer} : validAnswer answer → Related validKey validReply validAnswer (.pure answer) (.pure answer)
  | read {key : Key} {first second : Reply → Program Key Reply Answer} :
      validKey key →
      (∀ reply, validReply reply → Related validKey validReply validAnswer (first reply) (second reply)) →
      Related validKey validReply validAnswer (.read key first) (.read key second)

theorem refl_of_guarantees (validKey : Key → Prop) (validReply : Reply → Prop) (validAnswer : Answer → Prop)
    (program : Program Key Reply Answer) (safe : Guarantees validKey validReply validAnswer program) :
    Related validKey validReply validAnswer program program := by
  induction safe with
  | pure good => exact .pure good
  | read keySafe children ih => exact .read keySafe ih

theorem left_guarantees (validKey : Key → Prop) (validReply : Reply → Prop) (validAnswer : Answer → Prop)
    {first second : Program Key Reply Answer} (related : Related validKey validReply validAnswer first second) :
    Guarantees validKey validReply validAnswer first := by
  induction related with
  | pure good => exact .pure good
  | read keySafe children ih => exact .read keySafe ih

theorem symmetric (validKey : Key → Prop) (validReply : Reply → Prop) (validAnswer : Answer → Prop)
    {first second : Program Key Reply Answer} (related : Related validKey validReply validAnswer first second) :
    Related validKey validReply validAnswer second first := by
  induction related with
  | pure good => exact .pure good
  | read keySafe children ih => exact .read keySafe ih

theorem right_guarantees (validKey : Key → Prop) (validReply : Reply → Prop) (validAnswer : Answer → Prop)
    {first second : Program Key Reply Answer} (related : Related validKey validReply validAnswer first second) :
    Guarantees validKey validReply validAnswer second :=
  left_guarantees validKey validReply validAnswer (symmetric validKey validReply validAnswer related)

theorem bind_related (validKey : Key → Prop) (validReply : Reply → Prop)
    (firstGood : Answer → Prop) (lastGood : Other → Prop)
    {first second : Program Key Reply Answer} (related : Related validKey validReply firstGood first second)
    (nextFirst nextSecond : Answer → Program Key Reply Other)
    (later : ∀ answer, firstGood answer →
      Related validKey validReply lastGood (nextFirst answer) (nextSecond answer)) :
    Related validKey validReply lastGood (bind first nextFirst) (bind second nextSecond) := by
  induction related with
  | pure good => exact later _ good
  | read keySafe children ih => exact .read keySafe ih

theorem map_related_of_agree (validKey : Key → Prop) (validReply : Reply → Prop)
    (firstGood : Answer → Prop) (lastGood : Other → Prop)
    {first second : Program Key Reply Answer} (related : Related validKey validReply firstGood first second)
    (convertFirst convertSecond : Answer → Other)
    (same : ∀ answer, firstGood answer → convertFirst answer = convertSecond answer)
    (preserves : ∀ answer, firstGood answer → lastGood (convertFirst answer)) :
    Related validKey validReply lastGood (map convertFirst first) (map convertSecond second) := by
  apply bind_related validKey validReply firstGood lastGood related
  intro answer good
  rw [← same answer good]
  exact .pure (preserves answer good)

theorem map_related (validKey : Key → Prop) (validReply : Reply → Prop)
    (firstGood : Answer → Prop) (lastGood : Other → Prop)
    {first second : Program Key Reply Answer} (related : Related validKey validReply firstGood first second)
    (convert : Answer → Other) (preserves : ∀ answer, firstGood answer → lastGood (convert answer)) :
    Related validKey validReply lastGood (map convert first) (map convert second) :=
  map_related_of_agree validKey validReply firstGood lastGood related convert convert (fun _ _ => rfl) preserves

/-- The entire observation agrees: answer, final private state and ordered
read occurrences. Missing observations stop without executing a continuation. -/
theorem demand_run_eq (validKey : Key → Prop) (validReply : Reply → Prop) (validAnswer : Answer → Prop)
    {first second : Program Key Reply Answer} (related : Related validKey validReply validAnswer first second)
    (firstService secondService : State → Key → Option Reply × State)
    (same : ∀ state key, validKey key → firstService state key = secondService state key)
    (valid : ∀ state key, validKey key → ∀ reply,
      (firstService state key).1 = some reply → validReply reply) (state : State) :
    QueryState.run firstService (demand first) state = QueryState.run secondService (demand second) state := by
  induction related generalizing state with
  | pure good => rfl
  | @read key left right keySafe children ih =>
      simp only [demand, QueryState.run, ← same state key keySafe]
      cases found : (firstService state key).1 with
      | none => rfl
      | some reply =>
          have tail := ih reply (valid state key keySafe reply found) (firstService state key).2
          simp only [tail]

/-- The existing one-program invariant remains sound under a stateful
available service, independently of a pairwise equivalence derivation. -/
theorem completed_sound (validKey : Key → Prop) (validReply : Reply → Prop) (validAnswer : Answer → Prop)
    (program : Program Key Reply Answer) (safe : Guarantees validKey validReply validAnswer program)
    (service : State → Key → Option Reply × State)
    (valid : ∀ state key, validKey key → ∀ reply,
      (service state key).1 = some reply → validReply reply)
    (state : State) (answer : Answer)
    (completed : (QueryState.run service (demand program) state).answer = some answer) : validAnswer answer := by
  induction safe generalizing state with
  | pure good => exact (Option.some.inj completed) ▸ good
  | @read key next keySafe children ih =>
      cases found : (service state key).1 with
      | none => simp [demand, QueryState.run, found] at completed
      | some reply =>
          exact ih reply (valid state key keySafe reply found) (service state key).2
            (by simpa only [demand, QueryState.run, found] using completed)

namespace Controls

def twice : Program Bool Nat (Nat × Nat) :=
  .read true fun first => .read true fun second => .pure (first, second)

def guardedTwice : Program Bool Nat (Nat × Nat) :=
  .read true fun first => if first < 100 then
    .read true fun second => .pure (first, second)
    else .pure (0, 0)

def service (state : Nat) (_ : Bool) : Option Nat × Nat := (some (state % 100), state + 1)

def alternate (state : Nat) (key : Bool) : Option Nat × Nat :=
  if key then service state key else (none, state + 7)

theorem guarded_related :
    Related (fun key : Bool => key = true) (fun reply : Nat => reply < 100)
      (fun answer : Nat × Nat => answer.1 < 100 ∧ answer.2 < 100) twice guardedTwice := by
  unfold twice guardedTwice
  refine .read rfl ?_
  intro first bounded
  simp only [if_pos bounded]
  exact .read rfl (fun second secondBounded => .pure ⟨bounded, secondBounded⟩)

theorem services_agree_on_valid_keys (state : Nat) (key : Bool) (validKey : key = true) :
    service state key = alternate state key := by simp [alternate, validKey]

theorem service_reply_valid (state : Nat) (key : Bool) (_ : key = true) (reply : Nat)
    (returned : (service state key).1 = some reply) : reply < 100 := by
  cases Option.some.inj returned
  exact Nat.mod_lt _ (by decide)

theorem adaptive_programs_agree (state : Nat) :
    QueryState.run service (demand twice) state = QueryState.run alternate (demand guardedTwice) state :=
  demand_run_eq _ _ _ guarded_related service alternate services_agree_on_valid_keys service_reply_valid state

/-- The same key returns two distinct fresh replies and advances twice. -/
theorem repeated_key_has_distinct_occurrences :
    QueryState.run alternate (demand guardedTwice) 4 =
      ⟨some (4, 5), 6, [(true, some 4), (true, some 5)]⟩ := by
  rw [← adaptive_programs_agree]
  simp [QueryState.run, demand, twice, service]

def missingSecond (state : Nat) (_ : Bool) : Option Nat × Nat :=
  if state = 5 then (none, state + 1) else (some state, state + 1)

/-- Missing is recorded at its occurrence and stops before a pure answer. -/
theorem missing_stops_at_second_occurrence :
    QueryState.run missingSecond (demand twice) 4 =
      ⟨none, 6, [(true, some 4), (true, none)]⟩ := by
  simp [QueryState.run, demand, twice, missingSecond]

def thirdRead : Program Bool Nat Nat :=
  .read true fun _ => .read true fun _ => .read false fun third => .pure third

theorem missing_does_not_run_suffix :
    (QueryState.run missingSecond (demand thirdRead) 4).reads =
      [(true, some 4), (true, none)] := by
  simp [QueryState.run, demand, thirdRead, missingSecond]

theorem missing_is_not_a_completed_zero :
    (QueryState.run missingSecond (demand twice) 4).answer ≠ some (4, 0) := by
  rw [missing_stops_at_second_occurrence]
  decide

theorem fixed_key_reuse_changes_answer :
    (QueryState.run service (demand twice) 4).answer ≠
      (QueryState.run (fun state (_ : Bool) => (some 4, state + 1)) (demand twice) 4).answer := by
  simp [QueryState.run, demand, twice, service]

end Controls

end Mettapedia.Machines.ReadOnlyQueryRelation
