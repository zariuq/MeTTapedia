import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQueryBinding
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedAtomicCallOperands
import Mettapedia.Languages.MeTTa.PeTTa.DestinationProtectedSlots
import Mettapedia.Languages.MeTTa.PeTTa.DestinationMatchSource

/-!
# Protected source-template delivery from the actual query frontier

A query selects occurrence-fresh records, then runs the original template.
For a variable-return template the existing source unifier determines the
next two steps: either a real return equation, or refusal of that occurrence.
The reached world and saved siblings are retained in both cases. No returned
value, successful body run, or native metadata classification is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQueryReturn

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS (World)
open EagerDFS.Destination
open ProtectedSlots RefinementTransport
open ClosedOnceQueryFrame (placed)

theorem refinement_fixes_destination {before after : Equations} {slot destination value : Atom}
    (fixed : Fixed before slot value) (returned : Refinement before slot destination (some after)) :
    Fixed after destination value := by
  intro environment solved
  cases returned with
  | accepted witness old same =>
      have observations := (solves_append_equation _ _ _ _).mp solved
      exact observations.2.symm.trans (fixed environment observations.1)

theorem selected_keeps_protected_slot {control : Control} {pattern template destination : Atom}
    {older : List Goal} {rows : List Atom} {start : Nat} {selected : List (Nat × Control)}
    (source : QueryFrontier control pattern template destination older start rows selected)
    (slot value : Atom) (fixed : Fixed control.bindings slot value) :
    ∀ chosen ∈ selected, Fixed chosen.2.bindings slot value := by
  intro chosen present
  exact fixed.extends (query_frontier_good source chosen present)

theorem variable_body_two_steps {Context : Type} (policy : Policy)
    (program : SpaceSemantics.Program) (allocator : Allocator) (world : World)
    (scope : CollectionScope Context) (parents : List (CollectionScope Context))
    (caller : Control) (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (name : String) (destination : Atom) (older : List Goal) (bindings : Equations)
    (accepted : refine caller.bindings (.var name) destination = some bindings) :
    (ScopedQuerySource.ownedMachine policy program).run 2
      (placed allocator world scope parents
        {caller with goals := [.evaluate (.var name) destination] ++ older} context origins pending) =
      ([], .exhausted (placed allocator world scope parents
        {caller with bindings, goals := older} context origins pending)) := by
  simp [Machine.run, ScopedQuerySource.ownedMachine, ScopedQuerySource.ownedStep,
    ScopedCaseSource.entryStep, ScopedCaseSource.readyStep,
    ScopedQuerySource.ownershipStep, ScopedQuerySource.step, ScopedQuerySource.syntaxStep,
    ScopedQuerySource.constrainedCall, ScopedQuerySource.mutationCall, ScopedQuerySource.queryStep,
    placed, scopeStep, enterCollapse?, enterSuperpose?, EagerDFS.Destination.machine,
    prepare, replace, installChild, retainChild, accepted]

theorem variable_body_refuses_only_current {Context : Type} (policy : Policy)
    (program : SpaceSemantics.Program) (allocator : Allocator) (world : World)
    (scope : CollectionScope Context) (parents : List (CollectionScope Context))
    (caller : Control) (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (name : String) (destination : Atom) (older : List Goal)
    (refused : refine caller.bindings (.var name) destination = none) :
    (ScopedQuerySource.ownedMachine policy program).run 2
      (placed allocator world scope parents
        {caller with goals := [.evaluate (.var name) destination] ++ older} context origins pending) =
      ([], .exhausted (allocator, ⟨world, {scope with frontier := pending} :: parents⟩)) := by
  simp [Machine.run, ScopedQuerySource.ownedMachine, ScopedQuerySource.ownedStep,
    ScopedCaseSource.entryStep, ScopedCaseSource.readyStep,
    ScopedQuerySource.ownershipStep, ScopedQuerySource.step, ScopedQuerySource.syntaxStep,
    ScopedQuerySource.constrainedCall, ScopedQuerySource.mutationCall, ScopedQuerySource.queryStep,
    placed, scopeStep, enterCollapse?, enterSuperpose?, EagerDFS.Destination.machine,
    prepare, replace, installChild, retainChild, refused]

/-- Total classification of each actual selected occurrence. The successful
branch earns both the next source state and its fixed output; the refused
branch earns the exact saved frontier, not an empty successful record. -/
theorem selected_variable_delivery {Context : Type} (policy : Policy)
    (program : SpaceSemantics.Program) (allocator : Allocator) (world : World)
    (scope : CollectionScope Context) (parents : List (CollectionScope Context))
    (control : Control) (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (name : String) (pattern destination value : Atom) (older : List Goal)
    (rows : List Atom) (start : Nat) (selected : List (Nat × Control))
    (source : QueryFrontier control pattern (.var name) destination older start rows selected)
    (fixed : Fixed control.bindings (.var name) value)
    (chosen : Nat × Control) (present : chosen ∈ selected) :
    match refine chosen.2.bindings (.var name) destination with
    | none =>
        (ScopedQuerySource.ownedMachine policy program).run 2
          (placed allocator world scope parents chosen.2 context (origins ++ [chosen.1]) pending) =
          ([], .exhausted (allocator, ⟨world, {scope with frontier := pending} :: parents⟩))
    | some bindings =>
        (ScopedQuerySource.ownedMachine policy program).run 2
          (placed allocator world scope parents chosen.2 context (origins ++ [chosen.1]) pending) =
          ([], .exhausted (placed allocator world scope parents
            {chosen.2 with bindings, goals := older} context (origins ++ [chosen.1]) pending)) ∧
        Fixed bindings destination value ∧ Extends chosen.2.bindings bindings := by
  have recipe := MatchSource.selected_template_is_original_recipe source chosen present
  have protectedValue := selected_keeps_protected_slot source (.var name) value fixed chosen present
  have restored : {chosen.2 with goals := [.evaluate (.var name) destination] ++ older} = chosen.2 := by
    simp only [List.singleton_append, ← recipe]
  cases returned : refine chosen.2.bindings (.var name) destination with
  | none =>
      simpa only [restored] using variable_body_refuses_only_current policy program allocator world scope parents
        chosen.2 context (origins ++ [chosen.1]) pending name destination older returned
  | some bindings =>
      have returnSource := (refinement_iff _ _ _ _).mpr returned
      refine ⟨?_, refinement_fixes_destination protectedValue returnSource, ?_⟩
      · simpa only [restored] using variable_body_two_steps policy program allocator world scope parents
          chosen.2 context (origins ++ [chosen.1]) pending name destination older bindings returned
      · exact accepted_extends returnSource

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQueryReturn
