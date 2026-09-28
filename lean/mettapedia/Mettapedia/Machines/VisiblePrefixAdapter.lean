import Mettapedia.GSLT.Dynamics.CollapseObservationContract

/-!
# Bounded observation after occurrence adaptation

An answer allowance counts visible occurrences, rather than raw producer
events. `step` implements that counter over a finite raw frontier; its
independent specification is `filterMap` followed by `take`. The retained
state supports arbitrary partitions of the inspection budget and stops
before inspecting any suffix after the requested visible answer.

The projection is supplied by the observation boundary. It may retain a
value together with its environment, quotation authority and provenance.
No value comparison, variable freshening, deduplication or evaluation occurs
here. Those operations need separate dialect-specific refinement proofs.

In particular, success-priority error suppression is not generally a
pointwise projection: a later success can invalidate a provisional error.
The final controls prove that obstruction. This module does not assign one
universal error policy to HE, PeTTa or their enclosing handlers.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.VisiblePrefixAdapter

universe u v

variable {Raw : Type u} {Visible : Type v}

/-- Private adapter state. `inspected` counts raw rows actually inspected.
`reversed` retains occurrences, including repeated values and environments. -/
structure State (Raw : Type u) (Visible : Type v) where
  remaining : Nat
  source : List Raw
  reversed : List Visible
  inspected : Nat
deriving DecidableEq, Repr

def start (allowance : Nat) (source : List Raw) : State Raw Visible :=
  ⟨allowance, source, [], 0⟩

def answers (state : State Raw Visible) : List Visible :=
  state.reversed.reverse

/-- One raw row is inspected only when a visible answer is still demanded.
A hidden row consumes inspection budget but leaves the answer allowance. -/
def step (project : Raw → Option Visible) (state : State Raw Visible) :
    State Raw Visible :=
  match state.remaining, state.source with
  | 0, _ => state
  | _, [] => state
  | count + 1, row :: rest =>
      match project row with
      | none => ⟨count + 1, rest, state.reversed, state.inspected + 1⟩
      | some value => ⟨count, rest, value :: state.reversed, state.inspected + 1⟩

/-- A finite scheduler slice. Terminal states are stable, so unused scheduler
budget does not trigger extra producer work. -/
def run (project : Raw → Option Visible) : Nat → State Raw Visible → State Raw Visible
  | 0, state => state
  | budget + 1, state => run project budget (step project state)

/-- Specification of the remaining work, independent of `step` and `run`. -/
def meaning (project : Raw → Option Visible) (state : State Raw Visible) :
    List Visible :=
  answers state ++ (state.source.filterMap project).take state.remaining

def Terminal (state : State Raw Visible) : Prop :=
  state.remaining = 0 ∨ state.source = []

theorem step_meaning (project : Raw → Option Visible) (state : State Raw Visible) :
    meaning project (step project state) = meaning project state := by
  rcases state with ⟨remaining, source, reversed, inspected⟩
  cases remaining with
  | zero => rfl
  | succ count =>
      cases source with
      | nil => rfl
      | cons row rest =>
          cases projected : project row <;>
            simp [step, meaning, answers, projected, List.append_assoc]

theorem run_meaning (project : Raw → Option Visible) (budget : Nat)
    (state : State Raw Visible) :
    meaning project (run project budget state) = meaning project state := by
  induction budget generalizing state with
  | zero => rfl
  | succ budget ih =>
      exact (ih (step project state)).trans (step_meaning project state)

theorem run_add (project : Raw → Option Visible) (first second : Nat)
    (state : State Raw Visible) :
    run project (first + second) state =
      run project second (run project first state) := by
  induction first generalizing state with
  | zero => simp [run]
  | succ first ih =>
      simpa [Nat.succ_add, run] using ih (step project state)

theorem step_terminal (project : Raw → Option Visible)
    (state : State Raw Visible) (terminal : Terminal state) :
    step project state = state := by
  rcases state with ⟨remaining, source, reversed, inspected⟩
  rcases terminal with zero | empty
  · simp_all [step]
  · cases remaining <;> simp_all [step]

theorem run_terminal (project : Raw → Option Visible) (budget : Nat)
    (state : State Raw Visible) (terminal : Terminal state) :
    run project budget state = state := by
  induction budget with
  | zero => rfl
  | succ budget ih => simpa [run, step_terminal project state terminal] using ih

theorem zero_demand_no_inspection (project : Raw → Option Visible)
    (budget : Nat) (source : List Raw) :
    run project budget (start 0 source) = start 0 source :=
  run_terminal project budget _ (Or.inl rfl)

theorem terminal_after_length (project : Raw → Option Visible)
    (source : List Raw) (remaining : Nat) (reversed : List Visible) (inspected : Nat) :
    Terminal (run project source.length ⟨remaining, source, reversed, inspected⟩) := by
  induction source generalizing remaining reversed inspected with
  | nil => exact Or.inr rfl
  | cons row rest ih =>
      cases remaining with
      | zero =>
          rw [run_terminal project _ _ (Or.inl rfl)]
          exact Or.inl rfl
      | succ count =>
          cases projected : project row with
          | none => simpa [run, step, projected] using ih (count + 1) reversed (inspected + 1)
          | some value =>
              simpa [run, step, projected] using ih count (value :: reversed) (inspected + 1)

theorem meaning_terminal (project : Raw → Option Visible)
    (state : State Raw Visible) (terminal : Terminal state) :
    meaning project state = answers state := by
  rcases terminal with zero | empty
  · simp [meaning, zero]
  · simp [meaning, empty]

/-- Exact adapter refinement: completion of the finite frontier gives the
requested prefix of visible occurrences, with order and multiplicity intact. -/
theorem run_exact (project : Raw → Option Visible) (allowance : Nat)
    (source : List Raw) :
    answers (run project source.length (start allowance source)) =
      (source.filterMap project).take allowance := by
  calc
    _ = meaning project (run project source.length (start allowance source)) :=
      (meaning_terminal project _
        (terminal_after_length project source allowance [] 0)).symm
    _ = meaning project (start allowance source) := run_meaning project _ _
    _ = _ := by simp [meaning, start, answers]

/-- The exact-occurrence finite-prefix contract is applied to the already
adapted occurrence stream, never to an unqualified raw frontier. -/
theorem completion_permits {Observation : Type}
    (project : Raw → Option Observation) (allowance : Nat)
    (source : List Raw) :
    Mettapedia.GSLT.Dynamics.CollapseObservationContract.CompletionPermits
      (.finitePrefix allowance) (source.filterMap project)
      (answers (run project source.length (start allowance source))) :=
  run_exact project allowance source

/-- Returning the final demanded answer leaves the uninspected raw suffix
intact, even if a caller gives this scheduler slice excess fuel. -/
theorem first_visible_stops (project : Raw → Option Visible)
    (row : Raw) (value : Visible) (rest : List Raw) (budget : Nat)
    (visible : project row = some value) :
    run project (budget + 1) (start 1 (row :: rest)) =
      ⟨0, rest, [value], 1⟩ := by
  simp only [run, start, step, visible]
  exact run_terminal project budget _ (Or.inl rfl)

theorem step_inspections (project : Raw → Option Visible) (state : State Raw Visible) :
    (step project state).inspected ≤ state.inspected + 1 := by
  rcases state with ⟨remaining, source, reversed, inspected⟩
  cases remaining <;> cases source <;> simp [step]
  split <;> simp

/-- Budget is charged to hidden and visible raw rows alike. -/
theorem run_inspections (project : Raw → Option Visible) (budget : Nat)
    (state : State Raw Visible) :
    (run project budget state).inspected ≤ state.inspected + budget := by
  induction budget generalizing state with
  | zero => simp [run]
  | succ budget ih =>
      have total := ih (step project state)
      have one := step_inspections project state
      change (run project budget (step project state)).inspected ≤ _
      omega

/-! ## Controls and a scope-sensitive error-policy obstruction -/

theorem hidden_rows_do_not_spend_allowance :
    run (id : Option Nat → Option Nat) 4
      (start 2 [none, some 7, some 7, some 8]) =
      ⟨0, [some 8], [7, 7], 3⟩ := by rfl

theorem filtering_after_raw_take_loses_answer :
    ([none, some 7, some 8].take 2).filterMap id ≠
      ([none, some 7, some 8].filterMap id).take 2 := by decide

theorem environments_are_occurrences :
    answers (run (id : Option (Nat × Nat) → Option (Nat × Nat)) 3
      (start 3 [some (7, 1), some (7, 2), some (7, 1)])) =
      [(7, 1), (7, 2), (7, 1)] := by rfl

theorem paused_state_retains_allowance_and_suffix :
    run (id : Option Nat → Option Nat) 1
      (start 2 [none, some 7, some 8]) =
      ⟨2, [some 7, some 8], [], 1⟩ := by rfl

theorem fewer_answers_preserve_unspent_allowance :
    run (id : Option Nat → Option Nat) 3
      (start 5 [some 7, none, some 7]) =
      ⟨3, [], [7, 7], 3⟩ := by rfl

/-- A wide request over a tiny source requires no correspondingly large
allocation and still retains every available occurrence. -/
theorem wide_allowance_retains_three :
    answers (run (some : Nat → Option Nat) 3
      (start 4294967298 [1, 2, 3])) = [1, 2, 3] := by rfl

/-- Narrowing the allowance modulo a 32-bit word changes the observation,
even though this source contains only three rows. -/
theorem word_truncation_changes_observation :
    answers (run (some : Nat → Option Nat) 3
      (start (4294967298 % 4294967296) [1, 2, 3])) ≠
      answers (run (some : Nat → Option Nat) 3
        (start 4294967298 [1, 2, 3])) := by decide

inductive Classified where
  | preferred : Nat → Classified
  | fallback : Nat → Classified
deriving DecidableEq, Repr

def preferredValue : Classified → Option Nat
  | .preferred value => some value
  | .fallback _ => none

def fallbackValue : Classified → Option Nat
  | .preferred _ => none
  | .fallback value => some value

/-- A complete scope prefers its successes; only a scope with no success
exposes its fallback occurrences. This is a separate observer. -/
def preferSuccess (source : List Classified) : List Nat :=
  let successes := source.filterMap preferredValue
  if successes.isEmpty then source.filterMap fallbackValue else successes

theorem a_late_success_invalidates_fallback :
    preferSuccess [.fallback 7] = [7] ∧
      preferSuccess [.fallback 7, .preferred 9] = [9] := by decide

/-- A pointwise adapter cannot implement complete-scope success priority.
It would have to emit a lone fallback, and also erase that same occurrence
when a later preferred answer appears. -/
theorem success_priority_not_pointwise :
    ¬ ∃ project : Classified → Option Nat,
      ∀ source, source.filterMap project = preferSuccess source := by
  rintro ⟨project, correct⟩
  have fallback := correct [.fallback 7]
  have success := correct [.preferred 9]
  have together := correct [.fallback 7, .preferred 9]
  clear correct
  cases hf : project (.fallback 7) <;>
    cases hs : project (.preferred 9) <;>
    simp_all [preferSuccess, preferredValue, fallbackValue]
  have impossible : (2 : Nat) = 1 := congrArg List.length together
  omega

end Mettapedia.Machines.VisiblePrefixAdapter
