import Mettapedia.Machines.ConstraintPropagation

/-!
# Registering conditional answers on the shared delayed-goal table

The source specifies an ordered batch: withdraw carried goals, append each
component once, then partition its fresh occurrence indices according to the
current binding store. The target withdraws incrementally and calls the existing
table's suspension operation for each component. Their equality preserves both
queues, duplicate occurrences and variable identities. Full payload decoding
precedes retained-owner materialization or any mutation.

This is an algorithm law. Native payload shape checks, retained-owner export,
allocation, trail barriers and C lifetimes remain implementation obligations.
Resource refusal below is modeled at component boundaries and preserves the
actual completed prefix. It does not assert that a C suspension is atomic under
allocation failure, rollback of foreign effects, or permission to replay a failed
registration.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.ConditionalRegistration

open ConstraintPropagation

variable {Var Val Goal : Type} [DecidableEq Var]

abbrev Component (Var Goal : Type) := Goal × List Var

/-- Indices selected from an authored component sequence, without deduplication. -/
def selected (test : Component Var Goal → Bool) : Nat → List (Component Var Goal) → List Nat
  | _, [] => []
  | n, c :: cs => if test c then n :: selected test (n + 1) cs
      else selected test (n + 1) cs

def isBound (value : Var → Option Val) (c : Component Var Goal) : Bool :=
  c.2.any (fun v => (value v).isSome)

/-- Source withdrawal: remove exactly the suspended goals touching a carried variable. -/
def withdrawBatch (s : TableState Var Val Goal) (carried : List Var) :
    TableState Var Val Goal :=
  { s with suspended := (s.suspended.filter
      (fun i => !(carried.any (fun v => s.waitsOn v i)))) }

/-- Target withdrawal follows the carried variables in their authored order. -/
def withdrawSteps : TableState Var Val Goal → List Var → TableState Var Val Goal
  | s, [] => s
  | s, v :: vs => withdrawSteps
      { s with suspended := s.suspended.filter (fun i => !s.waitsOn v i) } vs

/-- Source registration directly specifies the final table and ordered queues. -/
def registerBatch (s : TableState Var Val Goal) (cs : List (Component Var Goal)) :
    TableState Var Val Goal :=
  { value := s.value
    goals := s.goals ++ cs
    suspended := s.suspended ++ selected (fun c => !isBound s.value c) s.goals.length cs
    woken := s.woken ++ selected (isBound s.value) s.goals.length cs }

/-- Target uses the maintained multi-variable suspension table once per component. -/
def registerSteps : TableState Var Val Goal → List (Component Var Goal) →
    TableState Var Val Goal
  | s, [] => s
  | s, (g, vs) :: cs => registerSteps (s.suspend g vs) cs

@[simp] theorem withdrawSteps_value (s : TableState Var Val Goal) (vs : List Var) :
    (withdrawSteps s vs).value = s.value := by
  induction vs generalizing s with
  | nil => rfl
  | cons v vs ih => exact ih _

@[simp] theorem withdrawSteps_goals (s : TableState Var Val Goal) (vs : List Var) :
    (withdrawSteps s vs).goals = s.goals := by
  induction vs generalizing s with
  | nil => rfl
  | cons v vs ih => exact ih _

@[simp] theorem withdrawSteps_woken (s : TableState Var Val Goal) (vs : List Var) :
    (withdrawSteps s vs).woken = s.woken := by
  induction vs generalizing s with
  | nil => rfl
  | cons v vs ih => exact ih _

theorem withdraw_refines (s : TableState Var Val Goal) (vs : List Var) :
    withdrawSteps s vs = withdrawBatch s vs := by
  induction vs generalizing s with
  | nil => simp [withdrawSteps, withdrawBatch]
  | cons v vs ih =>
      rw [withdrawSteps, ih]
      simp [withdrawBatch, TableState.waitsOn, List.filter_filter,
        Bool.not_or, Bool.and_comm]

omit [DecidableEq Var] in
theorem registration_refines (s : TableState Var Val Goal)
    (cs : List (Component Var Goal)) : registerSteps s cs = registerBatch s cs := by
  induction cs generalizing s with
  | nil => simp [registerSteps, registerBatch, selected]
  | cons c cs ih =>
      rcases c with ⟨g, vs⟩
      rw [registerSteps, ih]
      cases hb : vs.any (fun v => (s.value v).isSome) <;>
        simp only [TableState.suspend, hb, Bool.false_eq_true, ↓reduceIte] <;>
        simp only [registerBatch, selected, isBound, hb, Bool.not_false,
          Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.length_append,
          List.length_singleton, List.append_assoc, List.cons_append,
          List.nil_append]

/-- Carried withdrawal never wakes a goal; only the answer's components can add work. -/
theorem conditional_registration_refines (s : TableState Var Val Goal)
    (vs : List Var) (cs : List (Component Var Goal)) :
    registerSteps (withdrawSteps s vs) cs = registerBatch (withdrawBatch s vs) cs := by
  rw [withdraw_refines, registration_refines]

omit [DecidableEq Var] in
/-- A component occurs once even when its term and variables equal another's. -/
theorem registration_preserves_occurrences (s : TableState Var Val Goal)
    (cs : List (Component Var Goal)) :
    (registerSteps s cs).goals = s.goals ++ cs ∧
    (registerSteps s cs).value = s.value := by
  rw [registration_refines]
  exact ⟨rfl, rfl⟩

omit [DecidableEq Var] in
/-- Retained component syntax and variable identities are unchanged, including
sharing within a component and distinct identities between components. -/
theorem registered_payload_is_exact (s : TableState Var Val Goal)
    (cs : List (Component Var Goal)) :
    (registerSteps s cs).goals.drop s.goals.length = cs := by
  rw [registration_refines]
  simp [registerBatch]

omit [DecidableEq Var] in
/-- Incremental registration preserves the same chronology as one batch. -/
theorem registration_split (s : TableState Var Val Goal)
    (left right : List (Component Var Goal)) :
    registerSteps s (left ++ right) = registerSteps (registerSteps s left) right := by
  induction left generalizing s with
  | nil => rfl
  | cons c cs ih => exact ih _

omit [DecidableEq Var] in
theorem registration_wf (s : TableState Var Val Goal)
    (cs : List (Component Var Goal)) (hs : s.Wf) : (registerSteps s cs).Wf := by
  induction cs generalizing s with
  | nil => exact hs
  | cons c cs ih => exact ih _ (table_suspend_wf s c.1 c.2 hs)

omit [DecidableEq Var] in
/-- Several watched variables, including repetitions, give one fresh queue entry. -/
theorem already_bound_component (s : TableState Var Val Goal)
    (g : Goal) (vs : List Var) (v : Var) (hv : v ∈ vs)
    (a : Val) (ha : s.value v = some a) :
    (registerSteps s [(g, vs)]).woken = s.woken ++ [s.goals.length] := by
  have hb : isBound s.value (g, vs) = true :=
    List.any_eq_true.mpr ⟨v, hv, by simp [ha]⟩
  rw [registration_refines]
  simp [registerBatch, selected, hb]

/-- Withdrawal removes no binding or old queued occurrence and keeps table validity. -/
theorem withdrawal_wf (s : TableState Var Val Goal) (vs : List Var) (hs : s.Wf) :
    (withdrawBatch s vs).Wf := by
  have hsub : List.Sublist
      ((withdrawBatch s vs).suspended ++ (withdrawBatch s vs).woken)
      (s.suspended ++ s.woken) :=
    List.Sublist.append (List.filter_sublist) (List.Sublist.refl _)
  exact ⟨hsub.nodup hs.1, fun id hid => hs.2 id (hsub.subset hid)⟩

theorem conditional_registration_wf (s : TableState Var Val Goal)
    (vs : List Var) (cs : List (Component Var Goal)) (hs : s.Wf) :
    (registerSteps (withdrawSteps s vs) cs).Wf := by
  rw [withdraw_refines]
  exact registration_wf _ _ (withdrawal_wf s vs hs)

structure RawComponent (Var Goal : Type) where
  goal : Option Goal
  vars : List (Option Var)

structure RawPayload (Var Goal : Type) where
  carried : List (Option Var)
  components : List (RawComponent Var Goal)

/-- A malformed node is represented by none. Native node kinds are not erased
until this complete preflight succeeds. -/
def decodeVars : List (Option Var) → Option (List Var)
  | [] => some []
  | none :: _ => none
  | some v :: rest => (decodeVars rest).map (v :: ·)

def decodeComponent (raw : RawComponent Var Goal) : Option (Component Var Goal) := do
  let goal ← raw.goal
  let vars ← decodeVars raw.vars
  return (goal, vars)

def decodeComponents : List (RawComponent Var Goal) → Option (List (Component Var Goal))
  | [] => some []
  | c :: cs => do
      let component ← decodeComponent c
      let rest ← decodeComponents cs
      return component :: rest

omit [DecidableEq Var] in
/-- Validation reaches the entire suffix before the caller may enter a hook. -/
theorem invalid_suffix_rejected (left right : List (RawComponent Var Goal))
    (bad : decodeComponents right = none) : decodeComponents (left ++ right) = none := by
  induction left with
  | nil => exact bad
  | cons c cs ih =>
      cases h : decodeComponent c <;> simp [decodeComponents, h, ih]

def decodePayload (raw : RawPayload Var Goal) : Option (List Var × List (Component Var Goal)) := do
  let carried ← decodeVars raw.carried
  let components ← decodeComponents raw.components
  return (carried, components)

/-- World and owner hooks are included so rejection is stronger than no answers. -/
structure Entry (Var Val Goal World Event : Type) where
  table : TableState Var Val Goal
  world : World
  hooks : List Event

inductive RegistrationResult (State : Type) where
  | accepted (state : State)
  | malformed (state : State)
  | exhausted (state : State)

variable {World Event : Type}

/-- The retained-owner boundary may change its world and trace. It is reached
only after complete validation; this model does not assume it is pure. -/
def install (materialize : Entry Var Val Goal World Event → Entry Var Val Goal World Event)
    (raw : RawPayload Var Goal) (entry : Entry Var Val Goal World Event) :
    RegistrationResult (Entry Var Val Goal World Event) :=
  match decodePayload raw with
  | none => .malformed entry
  | some (carried, components) =>
      let prepared := materialize entry
      .accepted { prepared with table := registerSteps (withdrawSteps prepared.table carried) components }

theorem malformed_preserves_entry
    (materialize : Entry Var Val Goal World Event → Entry Var Val Goal World Event)
    (raw : RawPayload Var Goal) (entry : Entry Var Val Goal World Event)
    (bad : decodePayload raw = none) :
    install materialize raw entry = .malformed entry := by simp [install, bad]

/-- This exact result includes bindings, old goals, world and owner-hook trace. -/
theorem valid_install_batch
    (materialize : Entry Var Val Goal World Event → Entry Var Val Goal World Event)
    (raw : RawPayload Var Goal) (entry : Entry Var Val Goal World Event)
    (carried : List Var) (cs : List (Component Var Goal))
    (good : decodePayload raw = some (carried, cs)) :
    install materialize raw entry = .accepted
      { (materialize entry) with table := (registerBatch
          (withdrawBatch (materialize entry).table carried) cs) } := by
  simp [install, good, conditional_registration_refines]

/-- A failure terminal retains the precise successful prefix and remaining
components, so observing it again never reruns materialization or registration. -/
structure Residual (Var Val Goal : Type) where
  table : TableState Var Val Goal
  remaining : List (Component Var Goal)
  terminal : Bool

def advance (allow : Bool) (r : Residual Var Val Goal) : Residual Var Val Goal :=
  if r.terminal then r else
  match r.remaining with
  | [] => r
  | (g, vs) :: cs => if allow then
      ⟨r.table.suspend g vs, cs, false⟩
    else { r with terminal := true }

omit [DecidableEq Var] in
theorem failed_registration_is_terminal (r : Residual Var Val Goal)
    (g : Goal) (vs : List Var) (cs : List (Component Var Goal))
    (active : r.terminal = false) (pending : r.remaining = (g, vs) :: cs)
    (allow : Bool) : advance allow (advance false r) = advance false r := by
  simp [advance, active, pending]

def runAllows : List Bool → Residual Var Val Goal → Residual Var Val Goal
  | [], r => r
  | allow :: rest, r => runAllows rest (advance allow r)

omit [DecidableEq Var] in
theorem runAllows_append (left right : List Bool) (r : Residual Var Val Goal) :
    runAllows (left ++ right) r = runAllows right (runAllows left r) := by
  induction left generalizing r with
  | nil => rfl
  | cons b bs ih => exact ih _

omit [DecidableEq Var] in
theorem terminal_run_stutters (allows : List Bool) (r : Residual Var Val Goal)
    (terminal : r.terminal = true) : runAllows allows r = r := by
  induction allows with
  | nil => rfl
  | cons b bs ih => simpa [runAllows, advance, terminal] using ih

omit [DecidableEq Var] in
/-- An allowed prefix consumes precisely its own components and no suffix. -/
theorem allowed_prefix (s : TableState Var Val Goal)
    (left right : List (Component Var Goal)) :
    runAllows (List.replicate left.length true) ⟨s, left ++ right, false⟩ =
      ⟨registerSteps s left, right, false⟩ := by
  induction left generalizing s with
  | nil => rfl
  | cons c cs ih =>
      simpa [runAllows, advance, registerSteps, List.replicate_succ] using
        ih (s.suspend c.1 c.2)

omit [DecidableEq Var] in
/-- Resource refusal before the next component retains the committed table
prefix and every unregistered component. Further attempted execution is inert,
rather than a retry. Internal allocation failures within a component are not
represented by this boundary-level model. -/
theorem resource_failure_keeps_prefix (s : TableState Var Val Goal)
    (left right : List (Component Var Goal)) (next : Component Var Goal)
    (later : List Bool) :
    runAllows (List.replicate left.length true ++ false :: later)
        ⟨s, left ++ next :: right, false⟩ =
      ⟨registerSteps s left, next :: right, true⟩ := by
  rw [runAllows_append, allowed_prefix]
  simp only [runAllows, advance, Bool.false_eq_true, ↓reduceIte]
  exact terminal_run_stutters later _ rfl

/-- Positive control: equal components remain two occurrences, each queued once. -/
def boundExample : TableState Nat Nat Nat := ⟨fun _ => some 7, [], [], []⟩

theorem duplicate_components_are_not_collapsed :
    (registerSteps boundExample [(9, [1, 1]), (9, [1, 1])]).woken = [0, 1] := by decide

/-- A streaming validator demonstrates the bug: an invalid suffix is found
only after the valid prefix has already altered the branch. -/
def streamingInstall : TableState Var Val Goal → List (RawComponent Var Goal) →
    TableState Var Val Goal
  | s, [] => s
  | s, c :: cs => match decodeComponent c with
    | none => s
    | some (g, vs) => streamingInstall (s.suspend g vs) cs

def goodRaw : RawComponent Nat Nat := ⟨some 9, [some 1]⟩
def badRaw : RawComponent Nat Nat := ⟨some 10, [none]⟩

theorem invalid_suffix_preflight_rejects :
    decodeComponents [goodRaw, badRaw] = none := by decide

theorem streaming_invalid_suffix_changes_branch :
    (streamingInstall boundExample [goodRaw, badRaw]).woken ≠ boundExample.woken := by decide

/-! ## Unique watch entries preserve exact residual components

The stored goal keeps its original variable sequence. The watch index records
one slot per variable per goal, by checking the slots already built for that
goal. Its membership agrees with source-list membership, including repeated
variables, without collapsing distinct goals that happen to share a payload.
-/

/-- A projection of the current component's already-created watch records.
These slots are separate from the exact variable array stored with its goal. -/
def buildWatchSlots : List Var → List Var → List Var
  | [], slots => slots
  | v :: rest, slots => if v ∈ slots then buildWatchSlots rest slots
      else buildWatchSlots rest (v :: slots)

/-- Incremental index construction has the same membership as the authored
variable sequence, regardless of repetitions or the existing prefix. -/
theorem buildWatchSlots_mem (vars slots : List Var) (v : Var) :
    v ∈ buildWatchSlots vars slots ↔ v ∈ slots ∨ v ∈ vars := by
  induction vars generalizing slots with
  | nil => simp [buildWatchSlots]
  | cons w vars ih =>
      by_cases h : w ∈ slots
      · simp only [buildWatchSlots, h, ↓reduceIte, ih, List.mem_cons]
        constructor
        · tauto
        · rintro (hv | rfl | hv)
          · exact Or.inl hv
          · exact Or.inl h
          · exact Or.inr hv
      · simp only [buildWatchSlots, h, ↓reduceIte, ih, List.mem_cons]
        tauto

/-- A native goal has at most one index slot for each watched variable. -/
theorem buildWatchSlots_nodup (vars slots : List Var) (unique : slots.Nodup) :
    (buildWatchSlots vars slots).Nodup := by
  induction vars generalizing slots with
  | nil => exact unique
  | cons w vars ih =>
      by_cases h : w ∈ slots
      · simpa [buildWatchSlots, h] using ih slots unique
      · simpa [buildWatchSlots, h] using ih (w :: slots) (List.nodup_cons.mpr ⟨h, unique⟩)

omit [DecidableEq Var] in
/-- Looking only in the queried variable's bucket loses no matching current
component slot, even when unrelated variables collide in that bucket. -/
theorem current_bucket_membership (bucket : Var → Nat) (slots : List Var) (v : Var) :
    v ∈ slots.filter (fun w => decide (bucket w = bucket v)) ↔ v ∈ slots := by
  simp

/-- Bucket-local form of the native loop; slots contain only the current
goal's watch prefix, never records belonging to an older goal. -/
def buildBucketSlots (bucket : Var → Nat) : List Var → List Var → List Var
  | [], slots => slots
  | v :: rest, slots =>
      if v ∈ slots.filter (fun w => decide (bucket w = bucket v)) then
        buildBucketSlots bucket rest slots
      else buildBucketSlots bucket rest (v :: slots)

/-- Bucket lookup implements the goal-local unique index for every bucket
function, including the constant function that makes every variable collide. -/
theorem bucket_index_refines (bucket : Var → Nat) (vars slots : List Var) :
    buildBucketSlots bucket vars slots = buildWatchSlots vars slots := by
  induction vars generalizing slots with
  | nil => rfl
  | cons v vars ih =>
      simp only [buildBucketSlots, current_bucket_membership]
      split <;> simp_all [buildWatchSlots]

/-- The fresh goal-local index is duplicate-free and has precisely the source
variables. No constraint or variable occurrence is removed from the goal itself. -/
theorem fresh_watch_index_exact (vars : List Var) :
    (buildWatchSlots vars []).Nodup ∧
    ∀ v, v ∈ buildWatchSlots vars [] ↔ v ∈ vars := by
  exact ⟨buildWatchSlots_nodup vars [] (by simp), fun v => by
    simpa using buildWatchSlots_mem vars [] v⟩

def indexedWaitsOn (s : TableState Var Val Goal) (v : Var) (i : Nat) : Bool :=
  match s.goals[i]? with
  | none => false
  | some (_, vars) => decide (v ∈ buildWatchSlots vars [])

/-- An index built from goal-local unique slots implements the existing table
predicate, which asks whether the variable occurs at all. -/
theorem indexed_waitsOn_refines (s : TableState Var Val Goal) (v : Var) (i : Nat) :
    indexedWaitsOn s v i = s.waitsOn v i := by
  cases hgoal : s.goals[i]? with
  | none => simp [indexedWaitsOn, TableState.waitsOn, hgoal]
  | some pair => simp [indexedWaitsOn, TableState.waitsOn, hgoal, buildWatchSlots_mem]

/-- Native lookup enumerates distinct goal IDs in the source suspension order.
Equal payloads at different IDs remain distinct occurrences. -/
theorem indexed_candidates_refine (s : TableState Var Val Goal) (v : Var) :
    s.suspended.filter (indexedWaitsOn s v) = s.watching v := by
  have h : indexedWaitsOn s v = s.waitsOn v := funext (indexed_waitsOn_refines s v)
  rw [h]
  rfl

/-- This same candidate list is safe for waking, withdrawal and observation:
no repeated watch can cause the same goal ID to be processed twice. -/
theorem indexed_candidates_nodup (s : TableState Var Val Goal) (v : Var)
    (wf : s.Wf) : (s.suspended.filter (indexedWaitsOn s v)).Nodup := by
  exact ((List.nodup_append.mp wf.1).1).filter _

/-- Source binding queues precisely the goal IDs returned by the unique index. -/
theorem indexed_wake_matches_table (s : TableState Var Val Goal) (v : Var) (a : Val) :
    s.woken ++ s.suspended.filter (indexedWaitsOn s v) = (s.bind v a).woken := by
  rw [indexed_candidates_refine]
  rfl

/-- Two equal residual components retain separate IDs, while every repeated
variable inside either component has one index entry. -/
def repeatedVariableTable : TableState Nat Nat Nat :=
  ⟨fun _ => none, [(9, [1, 1, 1]), (9, [1, 1, 1])], [0, 1], []⟩

theorem repeated_variables_preserve_goal_multiplicity :
    repeatedVariableTable.suspended.filter (indexedWaitsOn repeatedVariableTable 1) = [0, 1] ∧
    buildWatchSlots [1, 1, 1] [] = [1] := by decide

/-- Indexing once per occurrence instead of once per (goal,variable) is
observably wrong even though the stored residual terms are unchanged. -/
theorem occurrence_watch_index_duplicates_goal :
    [(0, 1), (0, 1), (1, 1), (1, 1)].filterMap
        (fun entry => if entry.2 = 1 then some entry.1 else none) ≠
      repeatedVariableTable.watching 1 := by decide

end Mettapedia.Machines.ConditionalRegistration
