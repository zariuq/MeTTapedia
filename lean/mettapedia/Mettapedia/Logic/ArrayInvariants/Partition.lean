import Mettapedia.Logic.ArrayInvariants.UpdateTrace

/-!
# Quantified invariants for array partitioning

Public source: Laura Kovacs and Andrei Voronkov, *Finding Loop Invariants for
Programs over Arrays Using a Theorem Prover*, FASE 2009, Figure 1 and Section 2,
https://doi.org/10.1007/978-3-642-00593-0_33.

This reconstruction executes the published body and proves all six listed
array properties, together with a = b + c. Natural counters represent the
nonnegative counters reachable from initialization. Array indices and values
are integers, and arrays are total functions as in Section 3 of the paper.
`run n` denotes n body iterations, independent of the loop guard, matching the
paper's iteration semantics. It is not a bounded-memory or machine-integer model.
The invariants are verified here; the paper's automatic discovery algorithm is
not implemented in this module.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ArrayInvariants.Partition

structure OutputInvariant (input initial : Int -> Int) (selected : Int -> Prop)
    (processed used : Nat) (output : Int -> Int) : Prop where
  bounded : used <= processed
  sound : forall position : Int, 0 <= position -> position < (used : Int) ->
    selected (output position) /\
      exists i : Nat, i < processed /\ output position = input (i : Int)
  complete : forall i : Nat, i < processed -> selected (input (i : Int)) ->
    exists position : Int, 0 <= position /\ position < (used : Int) /\
      output position = input (i : Int)
  frame : forall position : Int, (used : Int) <= position ->
    output position = initial position

theorem output_initial (input initial : Int -> Int) (selected : Int -> Prop) :
    OutputInvariant input initial selected 0 0 initial where
  bounded := le_rfl
  sound position lower upper := by omega
  complete i before _ := by omega
  frame _ _ := rfl

theorem output_write {input initial : Int -> Int} {selected : Int -> Prop}
    {processed used : Nat} {output : Int -> Int}
    (inv : OutputInvariant input initial selected processed used output)
    (accept : selected (input (processed : Int))) :
    OutputInvariant input initial selected (processed + 1) (used + 1)
      (Function.update output (used : Int) (input (processed : Int))) where
  bounded := Nat.add_le_add_right inv.bounded 1
  sound position lower upper := by
    by_cases atWrite : position = (used : Int)
    · subst position
      simp only [Function.update_self]
      exact ⟨accept, processed, by omega, rfl⟩
    · rw [Function.update_of_ne atWrite]
      obtain ⟨accept, i, before, equal⟩ := inv.sound position lower (by omega)
      exact ⟨accept, i, by omega, equal⟩
  complete i before acceptInput := by
    by_cases newest : i = processed
    · subst i
      exact ⟨(used : Int), by omega, by omega, by simp⟩
    · obtain ⟨position, lower, upper, equal⟩ :=
        inv.complete i (by omega) acceptInput
      have different : position ≠ (used : Int) := by omega
      exact ⟨position, lower, by omega, by simpa [Function.update_of_ne different] using equal⟩
  frame position after := by
    have different : position ≠ (used : Int) := by omega
    rw [Function.update_of_ne different]
    exact inv.frame position (by omega)

theorem output_skip {input initial : Int -> Int} {selected : Int -> Prop}
    {processed used : Nat} {output : Int -> Int}
    (inv : OutputInvariant input initial selected processed used output)
    (reject : ¬selected (input (processed : Int))) :
    OutputInvariant input initial selected (processed + 1) used output where
  bounded := by have bound := inv.bounded; omega
  sound position lower upper := by
    obtain ⟨accept, i, before, equal⟩ := inv.sound position lower upper
    exact ⟨accept, i, by omega, equal⟩
  complete i before acceptInput := by
    have earlier : i < processed := by
      by_contra notEarlier
      have newest : i = processed := by omega
      subst i
      exact reject acceptInput
    exact inv.complete i earlier acceptInput
  frame := inv.frame

structure State where
  a : Nat
  b : Nat
  c : Nat
  B : Int -> Int
  C : Int -> Int

def initial (B0 C0 : Int -> Int) : State := ⟨0, 0, 0, B0, C0⟩

/-- The loop body of Figure 1, including both array writes and both counters. -/
def step (input : Int -> Int) (state : State) : State :=
  if 0 <= input (state.a : Int) then
    ⟨state.a + 1, state.b + 1, state.c,
      Function.update state.B (state.b : Int) (input (state.a : Int)), state.C⟩
  else
    ⟨state.a + 1, state.b, state.c + 1, state.B,
      Function.update state.C (state.c : Int) (input (state.a : Int))⟩

def run (input B0 C0 : Int -> Int) : Nat -> State
  | 0 => initial B0 C0
  | n + 1 => step input (run input B0 C0 n)

/-- The B update events extracted from the published body, as in Section 4. -/
def writesB (input B0 C0 : Int -> Int) (n : Nat) : Option (UpdateTrace.Write Int Int) :=
  let state := run input B0 C0 n
  if 0 <= input (state.a : Int) then
    some ⟨(state.b : Int), input (state.a : Int)⟩
  else none

/-- The C update events extracted from the same body. -/
def writesC (input B0 C0 : Int -> Int) (n : Nat) : Option (UpdateTrace.Write Int Int) :=
  let state := run input B0 C0 n
  if 0 <= input (state.a : Int) then none
  else some ⟨(state.c : Int), input (state.a : Int)⟩

theorem B_eq_trace (input B0 C0 : Int -> Int) (n : Nat) :
    (run input B0 C0 n).B = UpdateTrace.trace B0 (writesB input B0 C0) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases accept : 0 <= input ((run input B0 C0 n).a : Int)
    · simp only [run, step, writesB, accept, if_true, UpdateTrace.trace,
        UpdateTrace.applyWrite, ih]
    · simp only [run, step, writesB, accept, if_false, UpdateTrace.trace,
        UpdateTrace.applyWrite, ih]

theorem C_eq_trace (input B0 C0 : Int -> Int) (n : Nat) :
    (run input B0 C0 n).C = UpdateTrace.trace C0 (writesC input B0 C0) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases accept : 0 <= input ((run input B0 C0 n).a : Int)
    · simp only [run, step, writesC, accept, if_true, UpdateTrace.trace,
        UpdateTrace.applyWrite, ih]
    · simp only [run, step, writesC, accept, if_false, UpdateTrace.trace,
        UpdateTrace.applyWrite, ih]

structure Invariant (input B0 C0 : Int -> Int) (state : State) : Prop where
  conservation : state.a = state.b + state.c
  nonnegative : OutputInvariant input B0 (fun value => 0 <= value)
    state.a state.b state.B
  negative : OutputInvariant input C0 (fun value => value < 0)
    state.a state.c state.C

theorem invariant_initial (input B0 C0 : Int -> Int) :
    Invariant input B0 C0 (initial B0 C0) :=
  ⟨rfl, output_initial input B0 _, output_initial input C0 _⟩

theorem invariant_step (input B0 C0 : Int -> Int) (state : State)
    (inv : Invariant input B0 C0 state) :
    Invariant input B0 C0 (step input state) := by
  have conservation := inv.conservation
  by_cases accept : 0 <= input (state.a : Int)
  · simp only [step, accept, if_true]
    refine ⟨by dsimp; omega, output_write inv.nonnegative accept, ?_⟩
    exact output_skip inv.negative (by omega)
  · simp only [step, accept, if_false]
    refine ⟨by dsimp; omega, output_skip inv.nonnegative accept, ?_⟩
    exact output_write inv.negative (by omega)

/-- All six array properties and counter conservation hold after every iteration. -/
theorem invariant_run (input B0 C0 : Int -> Int) :
    forall n, Invariant input B0 C0 (run input B0 C0 n) := by
  intro n
  induction n with
  | zero => exact invariant_initial input B0 C0
  | succ n ih => exact invariant_step input B0 C0 _ ih

theorem step_a (input : Int -> Int) (state : State) :
    (step input state).a = state.a + 1 := by
  unfold step
  split <;> rfl

theorem iterations (input B0 C0 : Int -> Int) (n : Nat) :
    (run input B0 C0 n).a = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [run, step_a, ih]

theorem conservation (input B0 C0 : Int -> Int) (n : Nat) :
    (run input B0 C0 n).b + (run input B0 C0 n).c = n := by
  rw [← (invariant_run input B0 C0 n).conservation, iterations]

/-- Property 1: all populated B positions contain a nonnegative input value. -/
theorem nonnegative_sound (input B0 C0 : Int -> Int) (n : Nat) (position : Int)
    (lower : 0 <= position) (upper : position < ((run input B0 C0 n).b : Int)) :
    0 <= (run input B0 C0 n).B position /\
      exists i : Nat, i < n /\ (run input B0 C0 n).B position = input (i : Int) := by
  simpa only [iterations] using (invariant_run input B0 C0 n).nonnegative.sound position lower upper

/-- Property 2: all populated C positions contain a negative input value. -/
theorem negative_sound (input B0 C0 : Int -> Int) (n : Nat) (position : Int)
    (lower : 0 <= position) (upper : position < ((run input B0 C0 n).c : Int)) :
    (run input B0 C0 n).C position < 0 /\
      exists i : Nat, i < n /\ (run input B0 C0 n).C position = input (i : Int) := by
  simpa only [iterations] using (invariant_run input B0 C0 n).negative.sound position lower upper

/-- Property 3: each processed nonnegative input occurs in populated B. -/
theorem nonnegative_complete (input B0 C0 : Int -> Int) (n i : Nat)
    (before : i < n) (accept : 0 <= input (i : Int)) :
    exists position : Int, 0 <= position /\ position < ((run input B0 C0 n).b : Int) /\
      (run input B0 C0 n).B position = input (i : Int) :=
  (invariant_run input B0 C0 n).nonnegative.complete i
    (by simpa only [iterations] using before) accept

/-- Property 4: each processed negative input occurs in populated C. -/
theorem negative_complete (input B0 C0 : Int -> Int) (n i : Nat)
    (before : i < n) (accept : input (i : Int) < 0) :
    exists position : Int, 0 <= position /\ position < ((run input B0 C0 n).c : Int) /\
      (run input B0 C0 n).C position = input (i : Int) :=
  (invariant_run input B0 C0 n).negative.complete i
    (by simpa only [iterations] using before) accept

/-- Property 5: B positions at and above its counter retain their initial value. -/
theorem nonnegative_frame (input B0 C0 : Int -> Int) (n : Nat) (position : Int)
    (after : ((run input B0 C0 n).b : Int) <= position) :
    (run input B0 C0 n).B position = B0 position :=
  (invariant_run input B0 C0 n).nonnegative.frame position after

/-- Property 6: C positions at and above its counter retain their initial value. -/
theorem negative_frame (input B0 C0 : Int -> Int) (n : Nat) (position : Int)
    (after : ((run input B0 C0 n).c : Int) <= position) :
    (run input B0 C0 n).C position = C0 position :=
  (invariant_run input B0 C0 n).negative.frame position after

namespace Examples

def input (position : Int) : Int :=
  if position = 0 then -2 else if position = 1 then 5 else if position = 2 then -1 else 0

theorem partition_values :
    let state := run input (fun _ => 17) (fun _ => 23) 3
    (state.a, state.b, state.c, state.B 0, state.C 0, state.C 1, state.B 1, state.C 2) =
      (3, 1, 2, 5, -2, -1, 17, 23) := by
  norm_num [run, step, initial, input, Function.update_apply]

/-- The sign property concerns populated positions, not the entire output array. -/
theorem unused_position_can_be_negative :
    (run input (fun _ => -7) (fun _ => 23) 3).B 1 < 0 := by
  decide

end Examples

end Mettapedia.Logic.ArrayInvariants.Partition
