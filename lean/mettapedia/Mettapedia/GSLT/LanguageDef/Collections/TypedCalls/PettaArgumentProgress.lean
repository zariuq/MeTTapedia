import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaOccurrenceBinding

/-!
# Argument indices earned by the actual typed-call phases

A frame's ready prefix and remaining formals describe one traversal of its
declared parameters. An argument currently being produced occupies one pending
position; it enters the ready prefix only after its guard reply. Body entry
therefore earns the existence of every in-range ready argument.

These are metadata and operand-position facts. They do not assert that a
typing observation remains valid after later bindings or world changes.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaArgumentProgress

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open EagerDFS.Destination
open PettaOccurrenceOverlay

def pending : Phase → Nat
  | .argument _ _ => 1
  | .nextArgument | .body => 0

structure Aligned (frame : CallFrame) : Prop where
  ready_count : frame.ready.length = frame.index
  balance : frame.index + frame.remaining.length + pending frame.phase = frame.row.parameters.length
  formals : frame.remaining.map Prod.fst = frame.row.parameters.drop (frame.index + pending frame.phase)
  argument_formal : ∀ formal slot, frame.phase = .argument formal slot →
    frame.row.parameters[frame.index]? = some formal
  body_complete : frame.phase = .body → frame.remaining = []

def Calls {User : Type} (context : Context User) : Prop :=
  ∀ frame ∈ context.calls, Aligned frame

theorem Calls.empty {User : Type} (user : User) : Calls (⟨user, []⟩ : Context User) := by
  intro frame member
  cases member

theorem Calls.push {User : Type} {context : Context User} (good : Calls context)
    (frame : CallFrame) (aligned : Aligned frame) : Calls {context with calls := frame :: context.calls} := by
  intro other member
  rcases List.mem_cons.mp member with rfl | old
  · exact aligned
  · exact good other old

theorem Calls.update {User : Type} {context : Context User} {frame : CallFrame} {outside : List CallFrame}
    (good : Calls context) (calls : context.calls = frame :: outside) (updated : CallFrame)
    (aligned : Aligned updated) : Calls {context with calls := updated :: outside} := by
  intro other member
  rcases List.mem_cons.mp member with rfl | old
  · exact aligned
  · exact good other (calls ▸ List.mem_cons_of_mem _ old)

theorem Calls.pop {User : Type} {context : Context User} {frame : CallFrame} {outside : List CallFrame}
    (good : Calls context) (calls : context.calls = frame :: outside) : Calls {context with calls := outside} := by
  intro other member
  exact good other (calls ▸ List.mem_cons_of_mem _ member)

theorem row_work_aligned {User : Type} (control : DControl) (context : Context User) (origins : List Nat)
    (depth : Nat) (head : String) (arguments : List Atom) (destination : Atom)
    (older : List EagerDFS.Destination.Goal) (row : Row) (occurrence : Nat)
    (arity : row.parameters.length = arguments.length) :
    ∀ frame, (rowWork control context origins depth head arguments destination older row occurrence).2.1.calls.head? =
      some frame → Aligned frame := by
  intro frame atHead
  cases Option.some.inj atHead
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · simp [pending, List.length_zip, arity]
  · simpa only [pending, Nat.zero_add, List.drop_zero] using List.map_fst_zip (Nat.le_of_eq arity)
  · intro formal slot impossible
    cases impossible
  · intro impossible
    cases impossible

theorem row_work_calls {User : Type} (control : DControl) (context : Context User) (origins : List Nat)
    (depth : Nat) (head : String) (arguments : List Atom) (destination : Atom)
    (older : List EagerDFS.Destination.Goal) (row : Row) (occurrence : Nat)
    (arity : row.parameters.length = arguments.length) (good : Calls context) :
    Calls (rowWork control context origins depth head arguments destination older row occurrence).2.1 := by
  intro frame member
  simp only [rowWork, List.mem_cons] at member
  rcases member with rfl | old
  · exact row_work_aligned control context origins depth head arguments destination older row occurrence arity _ rfl
  · exact good frame old

theorem next_formal {frame : CallFrame} (good : Aligned frame) (phase : frame.phase = .nextArgument)
    (formal : Ty String) (argument : Atom) (rest : List (Ty String × Atom))
    (remaining : frame.remaining = (formal, argument) :: rest) :
    frame.row.parameters[frame.index]? = some formal ∧
      rest.map Prod.fst = frame.row.parameters.drop (frame.index + 1) := by
  have columns : frame.row.parameters.drop frame.index = formal :: rest.map Prod.fst := by
    simpa only [phase, pending, Nat.add_zero, remaining, List.map_cons] using good.formals.symm
  constructor
  · have head := congrArg (fun values : List (Ty String) => values[0]?) columns
    simpa only [List.getElem?_drop, Nat.add_zero, List.getElem?_cons_zero] using head
  · have tail := congrArg (List.drop 1) columns
    simpa only [List.drop_drop, List.drop_succ_cons, List.drop_zero] using tail.symm

theorem raw_advance {frame : CallFrame} (good : Aligned frame) (phase : frame.phase = .nextArgument)
    (formal : Ty String) (argument : Atom) (rest : List (Ty String × Atom))
    (remaining : frame.remaining = (formal, argument) :: rest) :
    Aligned {frame with
      remaining := rest
      ready := frame.ready ++ [argument]
      index := frame.index + 1
      phase := .nextArgument} := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, good.ready_count]
  · have balance := good.balance
    simp only [phase, pending, remaining, List.length_cons] at balance
    change frame.index + 1 + rest.length + 0 = frame.row.parameters.length
    omega
  · simpa only [pending, Nat.add_zero] using (next_formal good phase formal argument rest remaining).2
  · intro other slot impossible
    cases impossible
  · intro impossible
    cases impossible

theorem begin_argument {frame : CallFrame} (good : Aligned frame) (phase : frame.phase = .nextArgument)
    (formal : Ty String) (argument slot : Atom) (rest : List (Ty String × Atom))
    (remaining : frame.remaining = (formal, argument) :: rest) :
    Aligned {frame with remaining := rest, phase := .argument formal slot} := by
  refine ⟨good.ready_count, ?_, ?_, ?_, ?_⟩
  · have balance := good.balance
    simp only [phase, pending, remaining, List.length_cons] at balance
    change frame.index + rest.length + 1 = frame.row.parameters.length
    omega
  · exact (next_formal good phase formal argument rest remaining).2
  · intro other otherSlot same
    have named := (Phase.argument.inj same).1
    rw [← named]
    exact (next_formal good phase formal argument rest remaining).1
  · intro impossible
    cases impossible

theorem guarded_advance {frame : CallFrame} (good : Aligned frame) (formal : Ty String) (slot : Atom)
    (phase : frame.phase = .argument formal slot) (store : Store) :
    Aligned {frame with
      ready := frame.ready ++ [slot]
      store := store
      index := frame.index + 1
      phase := .nextArgument} := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, good.ready_count]
  · have balance := good.balance
    simp only [phase, pending] at balance
    change frame.index + 1 + frame.remaining.length + 0 = frame.row.parameters.length
    omega
  · simpa only [phase, pending, Nat.add_zero] using good.formals
  · intro other otherSlot impossible
    cases impossible
  · intro impossible
    cases impossible

theorem body_ready {frame : CallFrame} (good : Aligned frame) (phase : frame.phase = .nextArgument)
    (finished : frame.remaining = []) : Aligned {frame with phase := .body} := by
  refine ⟨good.ready_count, ?_, ?_, ?_, fun _ => finished⟩
  · simpa only [phase, pending] using good.balance
  · simpa only [phase, pending] using good.formals
  · intro formal slot impossible
    cases impossible

theorem body_ready_count {frame : CallFrame} (good : Aligned frame) (phase : frame.phase = .body) :
    frame.ready.length = frame.row.parameters.length := by
  have balance := good.balance
  simp only [phase, pending, good.body_complete phase, List.length_nil, Nat.add_zero] at balance
  exact good.ready_count.trans balance

theorem ready_index_available {frame : CallFrame} (good : Aligned frame) (phase : frame.phase = .body)
    (index : Nat) (within : index < frame.row.parameters.length) :
    ∃ argument, frame.ready[index]? = some argument := by
  have bound : index < frame.ready.length := by rw [body_ready_count good phase]; exact within
  exact ⟨frame.ready[index], List.getElem?_eq_getElem bound⟩

theorem argument_index_in_bounds {frame : CallFrame} (good : Aligned frame) (formal : Ty String) (slot : Atom)
    (phase : frame.phase = .argument formal slot) : frame.index < frame.row.parameters.length := by
  obtain ⟨within, _⟩ := List.getElem?_eq_some_iff.mp (good.argument_formal formal slot phase)
  exact within

theorem body_index {frame : CallFrame} (good : Aligned frame) (phase : frame.phase = .body) :
    frame.index = frame.row.parameters.length :=
  good.ready_count.symm.trans (body_ready_count good phase)

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaArgumentProgress
