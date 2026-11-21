import Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedQueryCollection

/-!
# Copied Boolean tuples return their actual source count

The collected tuple carries the actual Boolean values. Its size is the
number of collected producers, whatever their values; an all-`True` tuple
of ready packets is the special case indexed by its count.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedCountReturn

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS (World)
open EagerDFS.Destination
open ClosedOnceQueryFrame (FreshFor placed)
open GuardedQueryCollection (tuple flagTuple tuple_eq_flagTuple)

def value (count : Nat) : Atom := .grounded (.int count)

theorem flagTuple_literal (flags : List Bool) : SpaceSemantics.Literal (flagTuple flags) := by
  apply SpaceSemantics.Literal.expression
  · intro first rest same
    match flags, same with
    | [_, _, _], same => simp [Effects.boolean] at same
  · intro item member
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp member
    exact .grounded _

theorem flagTuple_closed (flags : List Bool) (environment : Environment) :
    read environment (flagTuple flags) = flagTuple flags :=
  LiteralQuerySource.read_literal _ (flagTuple_literal flags) environment

theorem tuple_literal (count : Nat) : SpaceSemantics.Literal (tuple count) := by
  rw [tuple_eq_flagTuple]
  exact flagTuple_literal _

theorem tuple_closed (count : Nat) (environment : Environment) : read environment (tuple count) = tuple count :=
  LiteralQuerySource.read_literal _ (tuple_literal count) environment

def waiting (caller : Control) (slot : String) (destination : Atom) : Control :=
  {caller with goals := .invoke "size-atom" [.var slot] destination :: caller.goals}

def tupleReturnedFlags (caller : Control) (slot : String) (destination : Atom) (flags : List Bool) : Control :=
  {waiting caller slot destination with
    goals := .equate (flagTuple flags) (.var slot) :: (waiting caller slot destination).goals}

def readyFlags (caller : Control) (slot : String) (destination : Atom) (flags : List Bool) : Control :=
  {waiting caller slot destination with bindings := caller.bindings ++ [(flagTuple flags, .var slot)]}

def countedFlags (caller : Control) (slot : String) (destination : Atom) (flags : List Bool) : Control :=
  {caller with bindings := (readyFlags caller slot destination flags).bindings ++ [(value flags.length, destination)]}

def tupleReturned (caller : Control) (slot : String) (destination : Atom) (count : Nat) : Control :=
  {waiting caller slot destination with
    goals := .equate (tuple count) (.var slot) :: (waiting caller slot destination).goals}

def ready (caller : Control) (slot : String) (destination : Atom) (count : Nat) : Control :=
  {waiting caller slot destination with bindings := caller.bindings ++ [(tuple count, .var slot)]}

def counted (caller : Control) (slot : String) (destination : Atom) (count : Nat) : Control :=
  {caller with bindings := (ready caller slot destination count).bindings ++ [(value count, destination)]}

theorem tupleReturned_eq (caller : Control) (slot : String) (destination : Atom) (count : Nat) :
    tupleReturned caller slot destination count = tupleReturnedFlags caller slot destination (List.replicate count true) := by
  simp only [tupleReturned, tupleReturnedFlags, tuple_eq_flagTuple]

theorem ready_eq (caller : Control) (slot : String) (destination : Atom) (count : Nat) :
    ready caller slot destination count = readyFlags caller slot destination (List.replicate count true) := by
  simp only [ready, readyFlags, tuple_eq_flagTuple]

theorem counted_eq (caller : Control) (slot : String) (destination : Atom) (count : Nat) :
    counted caller slot destination count = countedFlags caller slot destination (List.replicate count true) := by
  simp only [counted, countedFlags, ready_eq, List.length_replicate]

theorem flags_refined (caller : Control) (slot : String) (destination : Atom) (flags : List Bool)
    (fresh : FreshFor slot caller.bindings) (consistent : ∃ environment, Solves environment caller.bindings) :
    refine caller.bindings (flagTuple flags) (.var slot) = some (readyFlags caller slot destination flags).bindings :=
  ClosedOnceQueryFrame.refine_fresh_closed _ _ _ fresh consistent (flagTuple_closed flags)

theorem tuple_refined (caller : Control) (slot : String) (destination : Atom) (count : Nat)
    (fresh : FreshFor slot caller.bindings) (consistent : ∃ environment, Solves environment caller.bindings) :
    refine caller.bindings (tuple count) (.var slot) = some (ready caller slot destination count).bindings := by
  rw [ready_eq, tuple_eq_flagTuple]
  exact flags_refined caller slot destination _ fresh consistent

theorem flags_prefix {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context) (parents : List (CollectionScope Context))
    (caller : Control) (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (slot : String) (destination : Atom) (flags : List Bool)
    (fresh : FreshFor slot caller.bindings) (consistent : ∃ environment, Solves environment caller.bindings) :
    (ScopedQuerySource.machine .relational program).run 1
      (placed allocator world scope parents (tupleReturnedFlags caller slot destination flags) context origins pending) =
      ([], .exhausted (placed allocator world scope parents (readyFlags caller slot destination flags)
        context origins pending)) := by
  have refined := flags_refined caller slot destination flags fresh consistent
  simp only [readyFlags, waiting] at refined
  simp [Machine.run, ScopedQuerySource.machine, ScopedQuerySource.step, ScopedQuerySource.syntaxStep,
    ScopedQuerySource.constrainedCall, ScopedQuerySource.mutationCall, ScopedQuerySource.queryStep,
    placed, tupleReturnedFlags, readyFlags, waiting, scopeStep, enterCollapse?, enterSuperpose?,
    EagerDFS.Destination.machine, installChild, retainChild, refined]

theorem tuple_prefix {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context) (parents : List (CollectionScope Context))
    (caller : Control) (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (slot : String) (destination : Atom) (count : Nat)
    (fresh : FreshFor slot caller.bindings) (consistent : ∃ environment, Solves environment caller.bindings) :
    (ScopedQuerySource.machine .relational program).run 1
      (placed allocator world scope parents (tupleReturned caller slot destination count) context origins pending) =
      ([], .exhausted (placed allocator world scope parents (ready caller slot destination count) context origins pending)) := by
  rw [tupleReturned_eq, ready_eq]
  exact flags_prefix program allocator world scope parents caller context origins pending slot destination _ fresh consistent

theorem flags_read (caller : Control) (slot : String) (destination : Atom) (flags : List Bool) (principal : Environment)
    (resolved : resolve (readyFlags caller slot destination flags).bindings = some principal) :
    read principal (.var slot) = flagTuple flags := by
  have equation := resolve_sound resolved (flagTuple flags, .var slot) (List.mem_append_right _ (by simp))
  rw [flagTuple_closed] at equation
  exact equation.symm

theorem tuple_read (caller : Control) (slot : String) (destination : Atom) (count : Nat) (principal : Environment)
    (resolved : resolve (ready caller slot destination count).bindings = some principal) :
    read principal (.var slot) = tuple count := by
  rw [ready_eq] at resolved
  rw [tuple_eq_flagTuple]
  exact flags_read caller slot destination _ principal resolved

/-- One tuple refinement and two ordinary primitive-return steps. The output
need not be syntactically fresh; an unbound principal representative suffices.
The count is the number of collected values, whatever they are. -/
theorem count_prefix_flags {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context) (parents : List (CollectionScope Context))
    (caller : Control) (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (slot : String) (destination : Atom) (flags : List Bool) (principal : Environment) (representative : String)
    (resolved : resolve caller.bindings = some principal) (unbound : read principal destination = .var representative)
    (fresh : FreshFor slot caller.bindings) (apart : slot ∉ (encode destination).freeVars) :
    (ScopedQuerySource.machine .relational program).run 3
      (placed allocator world scope parents (tupleReturnedFlags caller slot destination flags) context origins pending) =
      ([], .exhausted (placed allocator world scope parents (countedFlags caller slot destination flags)
        context (origins ++ [0]) pending)) := by
  obtain ⟨after, resultName, afterResolved, stillUnbound⟩ := ScopedMutationSource.unbound_after_fresh_operand
    caller.bindings principal destination (flagTuple flags) representative slot resolved unbound fresh apart
    (by rw [CapturedPatternSupport.literal_names_empty _ (flagTuple_literal flags)]; simp)
  have reading := flags_read caller slot destination flags after afterResolved
  have applied : StdLib.apply world.state "size-atom" ([.var slot].map (read after)) =
      .ok (world.state, [value flags.length]) := by
    simp only [List.map_cons, List.map_nil, reading]
    change (Except.ok (world.state, [.grounded (.int (flags.map Effects.boolean).length)]) :
      Except Effects.Fault (Effects.State × List Atom)) = _
    simp only [List.length_map, value]
  have numeric := ScopedMutationSource.primitive_prefix .relational program allocator world
    {scope with frontier := (readyFlags caller slot destination flags, context, origins) :: pending}
    parents (readyFlags caller slot destination flags) context origins pending "size-atom" [.var slot] destination
    resultName caller.goals after world.state (value flags.length) rfl rfl afterResolved stillUnbound
    (fun environment => ConstantQuerySource.Scalar.read (.grounded _) environment)
    (by decide) (by decide) (by decide) (by intro impossible; simp at impossible) applied
  have first := flags_prefix program allocator world scope parents caller context origins pending slot destination flags
    fresh ⟨principal, resolve_sound resolved⟩
  change (ScopedQuerySource.machine .relational program).run 2
    (placed allocator world scope parents (readyFlags caller slot destination flags) context origins pending) =
    ([], .exhausted (placed allocator world scope parents (countedFlags caller slot destination flags)
      context (origins ++ [0]) pending)) at numeric
  have joined := (ScopedQuerySource.machine .relational program).established_and_pending 1 2 _ _ [] first
  rw [numeric] at joined
  simpa only [List.nil_append, countedFlags, readyFlags, waiting, placed] using joined

theorem count_prefix {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context) (parents : List (CollectionScope Context))
    (caller : Control) (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (slot : String) (destination : Atom) (count : Nat) (principal : Environment) (representative : String)
    (resolved : resolve caller.bindings = some principal) (unbound : read principal destination = .var representative)
    (fresh : FreshFor slot caller.bindings) (apart : slot ∉ (encode destination).freeVars) :
    (ScopedQuerySource.machine .relational program).run 3
      (placed allocator world scope parents (tupleReturned caller slot destination count) context origins pending) =
      ([], .exhausted (placed allocator world scope parents (counted caller slot destination count)
        context (origins ++ [0]) pending)) := by
  rw [tupleReturned_eq, counted_eq]
  exact count_prefix_flags program allocator world scope parents caller context origins pending slot destination _
    principal representative resolved unbound fresh apart

/-- A constrained result is handed to reference service after tuple return.
The query's effects and copy allocation are already in the reached cursor. -/
theorem constrained_prefix_flags {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context) (parents : List (CollectionScope Context))
    (caller : Control) (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (slot : String) (destination : Atom) (flags : List Bool) (principal : Environment)
    (fresh : FreshFor slot caller.bindings)
    (resolved : resolve (readyFlags caller slot destination flags).bindings = some principal)
    (constrained : ∀ name, read principal destination ≠ .var name) :
    (ScopedQuerySource.machine .relational program).run 2
      (placed allocator world scope parents (tupleReturnedFlags caller slot destination flags) context origins pending) =
      ([], .suspended (.branch (.invoke "size-atom" [.var slot] destination))
        (placed allocator world scope parents (readyFlags caller slot destination flags) context origins pending)) := by
  have consistent : ∃ environment, Solves environment caller.bindings := by
    refine ⟨principal, ?_⟩
    intro pair member
    exact resolve_sound resolved pair (List.mem_append_left _ member)
  have first := flags_prefix program allocator world scope parents caller context origins pending slot destination flags
    fresh consistent
  have requested := ScopedQuerySource.constrained_result_retains_reference_entry .relational program allocator world
    {scope with frontier := (readyFlags caller slot destination flags, context, origins) :: pending} parents
    (readyFlags caller slot destination flags) context origins pending "size-atom" [.var slot] destination caller.goals
    principal rfl rfl (by decide) resolved constrained
  change (ScopedQuerySource.machine .relational program).step
    (placed allocator world scope parents (readyFlags caller slot destination flags) context origins pending) = _ at requested
  have last : (ScopedQuerySource.machine .relational program).run 1
      (placed allocator world scope parents (readyFlags caller slot destination flags) context origins pending) =
      ([], .suspended (.branch (.invoke "size-atom" [.var slot] destination))
        (placed allocator world scope parents (readyFlags caller slot destination flags) context origins pending)) := by
    simp only [Machine.run, requested]
    rfl
  have joined := (ScopedQuerySource.machine .relational program).established_and_pending 1 1 _ _ [] first
  rw [last] at joined
  simpa only [List.nil_append] using joined

theorem constrained_prefix {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context) (parents : List (CollectionScope Context))
    (caller : Control) (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (slot : String) (destination : Atom) (count : Nat) (principal : Environment)
    (fresh : FreshFor slot caller.bindings)
    (resolved : resolve (ready caller slot destination count).bindings = some principal)
    (constrained : ∀ name, read principal destination ≠ .var name) :
    (ScopedQuerySource.machine .relational program).run 2
      (placed allocator world scope parents (tupleReturned caller slot destination count) context origins pending) =
      ([], .suspended (.branch (.invoke "size-atom" [.var slot] destination))
        (placed allocator world scope parents (ready caller slot destination count) context origins pending)) := by
  rw [ready_eq] at resolved
  rw [tupleReturned_eq, ready_eq]
  exact constrained_prefix_flags program allocator world scope parents caller context origins pending slot destination _
    principal fresh resolved constrained

theorem countedFlags_value (caller : Control) (slot : String) (destination : Atom) (flags : List Bool)
    (environment : Environment) (solved : Solves environment (countedFlags caller slot destination flags).bindings) :
    read environment destination = value flags.length := by
  have equation := solved (value flags.length, destination) (List.mem_append_right _ (by simp))
  have closed : read environment (value flags.length) = value flags.length :=
    ConstantQuerySource.Scalar.read (.grounded _) environment
  rw [closed] at equation
  exact equation.symm

theorem counted_value (caller : Control) (slot : String) (destination : Atom) (count : Nat)
    (environment : Environment) (solved : Solves environment (counted caller slot destination count).bindings) :
    read environment destination = value count := by
  rw [counted_eq] at solved
  simpa only [List.length_replicate] using countedFlags_value caller slot destination _ environment solved

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedCountReturn
