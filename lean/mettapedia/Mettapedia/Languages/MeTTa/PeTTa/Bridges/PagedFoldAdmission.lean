import Mettapedia.Languages.MeTTa.PeTTa.PagedFoldCompletion
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FoldCallbackExtraction
import Mettapedia.Machines.ResumableFinality

/-!
# Source-certified admission before a paged fold starts

Preparation elaborates callbacks without executing source effects. Unsupported
callbacks retain the original request. Once admitted, a session stores the
actual program, callback, entrance and residual as data and advances only its
current residual. Finite source derivations prove completion and exclude the
diagnostic boundary from every admitted terminal page.

The program is the retained immutable profile throughout a session. Native
program mutation and concurrent use require separate live-admission evidence.
This reference envelope intentionally keeps its source witness data; it is
not a claim of minimal physical retention or native root completeness.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.PagedFoldAdmission

open Mettapedia.Machines
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics PagedFold

structure Request where
  program : Program
  callback : FoldSource.Callback
  world : Effects.State
  items : List Atom
  initial : Atom

def Request.start (request : Request) : PagedFold.State :=
  ⟨.ready request.world request.items request.initial, [], 0, 0⟩

def Request.Admitted (request : Request) : Prop :=
  ∃ result, FoldSource.Evaluates request.program request.callback request.world request.items request.initial result

structure Session where
  request : Request
  current : PagedFold.State
  admitted : request.Admitted
  reached : ∃ allowance, (PagedFold.run request.program request.callback allowance request.start).1 = current

def begin (request : Request) (admitted : request.Admitted) : Session :=
  ⟨request, request.start, admitted, ⟨0, rfl⟩⟩

def advance (allowance : Nat) (session : Session) : Session × Nat :=
  let page := PagedFold.run session.request.program session.request.callback allowance session.current
  (⟨session.request, page.1, session.admitted, by
    obtain ⟨before, reached⟩ := session.reached
    refine ⟨before + allowance, ?_⟩
    rw [PagedFold.split_pages]
    dsimp only
    rw [reached]⟩, page.2)

theorem advance_keeps_source (allowance : Nat) (session : Session) :
    (advance allowance session).1.request = session.request := rfl

theorem current_is_the_actual_page (allowance : Nat) (session : Session) :
    (advance allowance session).1.current =
      (PagedFold.run session.request.program session.request.callback allowance session.current).1 := rfl

theorem source_completion (session : Session) :
    ∃ result ticks values,
      FoldSource.Evaluates session.request.program session.request.callback session.request.world
        session.request.items session.request.initial result ∧
      PagedFold.run session.request.program session.request.callback
        (ticks + 2 * session.request.items.length + 1) session.request.start =
          (⟨.done session.request.world result, values, ticks, 2 * session.request.items.length + 1⟩,
            ticks + 2 * session.request.items.length + 1) := by
  obtain ⟨result, source⟩ := session.admitted
  obtain ⟨ticks, values, _, complete⟩ := completes_evaluation source
  exact ⟨result, ticks, values, source, complete⟩

theorem terminal_page_is_source_completion (session : Session)
    (terminal : PagedFold.step session.request.program session.request.callback session.current = none) :
    ∃ result ticks values,
      FoldSource.Evaluates session.request.program session.request.callback session.request.world
        session.request.items session.request.initial result ∧
      session.current = ⟨.done session.request.world result, values, ticks, 2 * session.request.items.length + 1⟩ := by
  obtain ⟨result, ticks, values, source, complete⟩ := source_completion session
  obtain ⟨earlierBudget, reached⟩ := session.reached
  have final : PagedFold.step session.request.program session.request.callback
      (PagedFold.run session.request.program session.request.callback
        (ticks + 2 * session.request.items.length + 1) session.request.start).1 = none := by rw [complete]; rfl
  have same := MachineCore.runSlice_terminal_unique (core session.request.program session.request.callback)
    earlierBudget (ticks + 2 * session.request.items.length + 1) session.request.start
    (by simpa [reached] using terminal) final
  refine ⟨result, ticks, values, source, ?_⟩
  have states := congrArg Prod.fst same
  simpa [reached, complete] using states

theorem completed_page_is_source_value (session : Session) (world : Effects.State) (value : Atom)
    (completed : session.current.phase = .done world value) :
    world = session.request.world ∧
      FoldSource.Evaluates session.request.program session.request.callback session.request.world
        session.request.items session.request.initial value := by
  have stopped : PagedFold.step session.request.program session.request.callback session.current = none := by
    simp [PagedFold.step, completed]
  obtain ⟨result, ticks, values, source, same⟩ := terminal_page_is_source_completion session stopped
  have phase := congrArg PagedFold.State.phase same
  rw [completed] at phase
  obtain ⟨rfl, rfl⟩ := Phase.done.inj phase
  exact ⟨rfl, source⟩

theorem admitted_session_cannot_hit_boundary (session : Session) (call : Call) (outcome : Eval.Outcome) :
    session.current.phase ≠ .boundary call outcome := by
  intro boundary
  have stopped : PagedFold.step session.request.program session.request.callback session.current = none := by
    simp [PagedFold.step, boundary]
  obtain ⟨result, ticks, values, _, same⟩ := terminal_page_is_source_completion session stopped
  have phase := congrArg PagedFold.State.phase same
  rw [boundary] at phase
  cases phase

theorem every_retained_page_can_finish (session : Session) :
    ∃ allowance value, (advance allowance session).1.current.phase = .done session.request.world value := by
  obtain ⟨value, ticks, values, _, complete⟩ := source_completion session
  obtain ⟨earlierBudget, reached⟩ := session.reached
  let allowance := ticks + 2 * session.request.items.length + 1
  have stopped : PagedFold.step session.request.program session.request.callback
      (PagedFold.run session.request.program session.request.callback allowance session.request.start).1 = none := by
    rw [complete]; rfl
  have residual := (MachineCore.runSlice_residual_completes (core session.request.program session.request.callback)
    allowance earlierBudget session.request.start stopped).1
  refine ⟨allowance, value, ?_⟩
  change (PagedFold.run session.request.program session.request.callback allowance session.current).1.phase = _
  rw [← reached, residual]
  exact congrArg (fun page : PagedFold.State × Nat => page.1.phase) complete

def pages (quantum : Nat) : Nat → Session → Session
  | 0, session => session
  | count + 1, session => pages quantum count (advance quantum session).1

theorem pages_keep_source (quantum count : Nat) (session : Session) :
    (pages quantum count session).request = session.request := by
  induction count generalizing session with
  | zero => rfl
  | succ count ih => rw [pages, ih, advance_keeps_source]

theorem pages_are_one_slice (quantum count : Nat) (session : Session) :
    (pages quantum count session).current =
      (PagedFold.run session.request.program session.request.callback (count * quantum) session.current).1 := by
  induction count generalizing session with
  | zero => simp [pages, PagedFold.run, MachineCore.runSlice]
  | succ count ih =>
      rw [pages, ih, advance_keeps_source, current_is_the_actual_page]
      rw [show (count + 1) * quantum = quantum + count * quantum by simp [Nat.add_mul, Nat.add_comm]]
      exact (congrArg Prod.fst (PagedFold.split_pages session.request.program session.request.callback
        quantum (count * quantum) session.current)).symm

theorem positive_quantum_completes (quantum : Nat) (positive : 0 < quantum) (session : Session) :
    ∃ count value, (pages quantum count session).current.phase = .done session.request.world value := by
  obtain ⟨allowance, value, completed⟩ := every_retained_page_can_finish session
  have done : (PagedFold.run session.request.program session.request.callback allowance session.current).1.phase =
      .done session.request.world value := completed
  have stopped : PagedFold.step session.request.program session.request.callback
      (PagedFold.run session.request.program session.request.callback allowance session.current).1 = none := by
    simp [PagedFold.step, done]
  have enough : allowance ≤ allowance * quantum := by
    simpa using Nat.mul_le_mul_left allowance (show 1 ≤ quantum by omega)
  have same := MachineCore.runSlice_larger_final (core session.request.program session.request.callback)
    allowance (allowance * quantum) session.current stopped enough
  refine ⟨allowance, value, ?_⟩
  rw [pages_are_one_slice]
  exact (congrArg (fun page : PagedFold.State × Nat => page.1.phase) same).trans done

theorem zero_quantum_keeps_pending_state (count : Nat) (session : Session) :
    (pages 0 count session).current = session.current := by rw [pages_are_one_slice]; simp [run, MachineCore.runSlice]

inductive Entry where
  | reference (request : Request)
  | admitted (session : Session)

def prepare (budget : Nat) (request : Request) : Entry :=
  match FoldCallbackExtraction.prepare budget request.program request.callback request.items request.initial with
  | none => .reference request
  | some prepared => .admitted (begin request ⟨prepared.result, prepared.returns request.world⟩)

theorem refusal_does_not_run_source (budget : Nat) (request : Request)
    (refused : FoldCallbackExtraction.prepare budget request.program request.callback request.items request.initial = none) :
    prepare budget request = .reference request := by simp [prepare, refused]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.PagedFoldAdmission
