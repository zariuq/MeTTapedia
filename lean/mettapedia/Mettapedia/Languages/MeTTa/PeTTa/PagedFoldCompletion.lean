import Mettapedia.Languages.MeTTa.PeTTa.PagedFold

/-!
# Completion and exact callback accounting for admitted folds

Finite source callback derivations supply exact evaluator slices. Composing
those slices with host entry/return steps yields a completed fold, its exact
accumulator trace, and separate source/host debits. The callback debit is
derived from the actual evaluator, never supplied by a profitability estimate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.PagedFold

open Mettapedia.Machines
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Eval SpaceSemantics

theorem one_callback (program : Program) (callback : FoldSource.Callback) (world : Effects.State)
    (item : Atom) (rest prefixes : List Atom) (accumulator next : Atom) (sourceDebit hostDebit : Nat)
    (invoked : FoldSource.Invokes program callback world accumulator item next) :
    ∃ ticks, run program callback (ticks + 2)
      ⟨.ready world (item :: rest) accumulator, prefixes, sourceDebit, hostDebit⟩ =
        (⟨.ready world rest next, prefixes ++ [next], sourceDebit + ticks, hostDebit + 2⟩, ticks + 2) := by
  obtain ⟨ticks, source⟩ := EvaluatorAccounting.pure_return_has_exact_slice program
    (FoldSource.bindings callback accumulator item) world world (FoldSource.expression callback) next invoked
  let call : Call := ⟨accumulator, item, rest, callStart callback world accumulator item,
    callStart callback world accumulator item⟩
  let entrance : State := ⟨.ready world (item :: rest) accumulator, prefixes, sourceDebit, hostDebit⟩
  have entered : run program callback 1 entrance = (running call prefixes sourceDebit (hostDebit + 1), 1) := rfl
  have body := exact_callback_slice program callback ticks call prefixes sourceDebit (hostDebit + 1)
    (finished world [next] [] []) source
  have returned : run program callback 1
      (running {call with current := finished world [next] [] []} prefixes (sourceDebit + ticks) (hostDebit + 1)) =
        (⟨.ready world rest next, prefixes ++ [next], sourceDebit + ticks, hostDebit + 2⟩, 1) := by
    simp only [run, MachineCore.runSlice, core,
      return_callback program callback {call with current := finished world [next] [] []}
        prefixes (sourceDebit + ticks) (hostDebit + 1) world next rfl]
    rfl
  refine ⟨ticks, ?_⟩
  change run program callback (ticks + 2) entrance = _
  rw [show ticks + 2 = 1 + (ticks + 1) by omega, split_pages, entered]
  dsimp only
  rw [split_pages program callback ticks 1, body]
  dsimp only
  rw [returned]

theorem completes_trace {program : Program} {callback : FoldSource.Callback} {world : Effects.State}
    {items : List Atom} {initial : Atom} {values : List Atom}
    (source : FoldSource.Trace program callback world items initial values)
    (prefixes : List Atom) (sourceDebit hostDebit : Nat) :
    ∃ ticks, run program callback (ticks + 2 * items.length + 1)
      ⟨.ready world items initial, prefixes, sourceDebit, hostDebit⟩ =
        (⟨.done world (values.getLast?.getD initial), prefixes ++ values,
          sourceDebit + ticks, hostDebit + 2 * items.length + 1⟩, ticks + 2 * items.length + 1) := by
  induction source generalizing prefixes sourceDebit hostDebit with
  | nil accumulator =>
      refine ⟨0, ?_⟩
      simp [run, MachineCore.runSlice, core, step]
  | @cons item rest accumulator next values invoked tail ih =>
      obtain ⟨firstTicks, first⟩ := one_callback program callback world item rest prefixes accumulator next
        sourceDebit hostDebit invoked
      obtain ⟨laterTicks, later⟩ := ih (prefixes ++ [next]) (sourceDebit + firstTicks) (hostDebit + 2)
      refine ⟨firstTicks + laterTicks, ?_⟩
      have budget : firstTicks + laterTicks + 2 * (item :: rest).length + 1 =
          (firstTicks + 2) + (laterTicks + 2 * rest.length + 1) := by simp; omega
      rw [budget, split_pages, first]
      dsimp only
      rw [later]
      simp [List.getLast?_cons, List.append_assoc, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem trace_of_evaluation {program : Program} {callback : FoldSource.Callback} {world : Effects.State}
    {items : List Atom} {initial result : Atom} (source : FoldSource.Evaluates program callback world items initial result) :
    ∃ values, FoldSource.Trace program callback world items initial values ∧ values.getLast?.getD initial = result := by
  induction source with
  | nil accumulator => exact ⟨[], .nil accumulator, rfl⟩
  | @cons item rest accumulator next result invoked tail ih =>
      obtain ⟨values, trace, last⟩ := ih
      exact ⟨next :: values, .cons invoked trace, by simpa [List.getLast?_cons] using last⟩

theorem completes_evaluation {program : Program} {callback : FoldSource.Callback} {world : Effects.State}
    {items : List Atom} {initial result : Atom}
    (source : FoldSource.Evaluates program callback world items initial result) :
    ∃ ticks values, FoldSource.Trace program callback world items initial values ∧
      run program callback (ticks + 2 * items.length + 1) ⟨.ready world items initial, [], 0, 0⟩ =
        (⟨.done world result, values, ticks, 2 * items.length + 1⟩, ticks + 2 * items.length + 1) := by
  obtain ⟨values, trace, last⟩ := trace_of_evaluation source
  obtain ⟨ticks, complete⟩ := completes_trace trace [] 0 0
  refine ⟨ticks, values, trace, ?_⟩
  simpa [last] using complete

end Mettapedia.Languages.MeTTa.PeTTa.PagedFold
