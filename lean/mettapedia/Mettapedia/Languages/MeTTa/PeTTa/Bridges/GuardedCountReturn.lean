import Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedQueryCollection

/-!
# Copied Boolean tuples return their actual source count

Tuple refinement preserves the saved caller's equations and goals. The
ordinary numeric route uses an actually unbound destination, including an
alias. A constrained output retains the reached invocation instead.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedCountReturn

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS (World)
open EagerDFS.Destination
open ClosedOnceQueryFrame (FreshFor placed)
open GuardedQueryCollection (tuple)

def value (count : Nat) : Atom := .grounded (.int count)

theorem tuple_literal (count : Nat) : SpaceSemantics.Literal (tuple count) := by
  apply SpaceSemantics.Literal.expression
  · intro first rest same
    cases count <;> simp [List.replicate_succ, Effects.boolean] at same
  · intro item member
    obtain ⟨_, rfl⟩ := List.mem_replicate.mp member
    exact .grounded _

theorem tuple_closed (count : Nat) (environment : Environment) : read environment (tuple count) = tuple count :=
  LiteralQuerySource.read_literal _ (tuple_literal count) environment

def waiting (caller : Control) (slot : String) (destination : Atom) : Control :=
  {caller with goals := .invoke "size-atom" [.var slot] destination :: caller.goals}

def tupleReturned (caller : Control) (slot : String) (destination : Atom) (count : Nat) : Control :=
  {waiting caller slot destination with
    goals := .equate (tuple count) (.var slot) :: (waiting caller slot destination).goals}

def ready (caller : Control) (slot : String) (destination : Atom) (count : Nat) : Control :=
  {waiting caller slot destination with bindings := caller.bindings ++ [(tuple count, .var slot)]}

def counted (caller : Control) (slot : String) (destination : Atom) (count : Nat) : Control :=
  {caller with bindings := (ready caller slot destination count).bindings ++ [(value count, destination)]}

theorem tuple_refined (caller : Control) (slot : String) (destination : Atom) (count : Nat)
    (fresh : FreshFor slot caller.bindings) (consistent : ∃ environment, Solves environment caller.bindings) :
    refine caller.bindings (tuple count) (.var slot) = some (ready caller slot destination count).bindings :=
  ClosedOnceQueryFrame.refine_fresh_closed _ _ _ fresh consistent (tuple_closed count)

theorem tuple_prefix {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context) (parents : List (CollectionScope Context))
    (caller : Control) (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (slot : String) (destination : Atom) (count : Nat)
    (fresh : FreshFor slot caller.bindings) (consistent : ∃ environment, Solves environment caller.bindings) :
    (ScopedQuerySource.machine .relational program).run 1
      (placed allocator world scope parents (tupleReturned caller slot destination count) context origins pending) =
      ([], .exhausted (placed allocator world scope parents (ready caller slot destination count) context origins pending)) := by
  have refined := tuple_refined caller slot destination count fresh consistent
  simp only [ready, waiting] at refined
  simp [Machine.run, ScopedQuerySource.machine, ScopedQuerySource.step, ScopedQuerySource.syntaxStep,
    ScopedQuerySource.constrainedCall, ScopedQuerySource.mutationCall, ScopedQuerySource.queryStep,
    placed, tupleReturned, ready, waiting, scopeStep, enterCollapse?, enterSuperpose?,
    EagerDFS.Destination.machine, installChild, retainChild, refined]

theorem tuple_read (caller : Control) (slot : String) (destination : Atom) (count : Nat) (principal : Environment)
    (resolved : resolve (ready caller slot destination count).bindings = some principal) :
    read principal (.var slot) = tuple count := by
  have equation := resolve_sound resolved (tuple count, .var slot) (List.mem_append_right _ (by simp))
  rw [tuple_closed] at equation
  exact equation.symm

/-- One tuple refinement and two ordinary primitive-return steps. The output
need not be syntactically fresh; an unbound principal representative suffices. -/
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
  obtain ⟨after, resultName, afterResolved, stillUnbound⟩ := ScopedMutationSource.unbound_after_fresh_operand
    caller.bindings principal destination (tuple count) representative slot resolved unbound fresh apart
    (by rw [CapturedPatternSupport.literal_names_empty _ (tuple_literal count)]; simp)
  have reading := tuple_read caller slot destination count after afterResolved
  have applied : StdLib.apply world.state "size-atom" ([.var slot].map (read after)) = .ok (world.state, [value count]) := by
    simp only [List.map_cons, List.map_nil, reading]
    change (Except.ok (world.state, [.grounded (.int (List.replicate count (Effects.boolean true)).length)]) :
      Except Effects.Fault (Effects.State × List Atom)) = _
    simp only [List.length_replicate, value]
  have numeric := ScopedMutationSource.primitive_prefix .relational program allocator world
    {scope with frontier := (ready caller slot destination count, context, origins) :: pending}
    parents (ready caller slot destination count) context origins pending "size-atom" [.var slot] destination resultName
    caller.goals after world.state (value count) rfl rfl afterResolved stillUnbound
    (fun environment => ConstantQuerySource.Scalar.read (.grounded _) environment)
    (by decide) (by decide) (by decide) (by intro impossible; simp at impossible) applied
  have first := tuple_prefix program allocator world scope parents caller context origins pending slot destination count fresh
    ⟨principal, resolve_sound resolved⟩
  change (ScopedQuerySource.machine .relational program).run 2
    (placed allocator world scope parents (ready caller slot destination count) context origins pending) =
    ([], .exhausted (placed allocator world scope parents (counted caller slot destination count)
      context (origins ++ [0]) pending)) at numeric
  have joined := (ScopedQuerySource.machine .relational program).established_and_pending 1 2 _ _ [] first
  rw [numeric] at joined
  simpa only [List.nil_append, counted, ready, waiting, placed] using joined

/-- A constrained result is handed to reference service after tuple return.
The query's effects and copy allocation are already in the reached cursor. -/
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
  have consistent : ∃ environment, Solves environment caller.bindings := by
    refine ⟨principal, ?_⟩
    intro pair member
    exact resolve_sound resolved pair (List.mem_append_left _ member)
  have first := tuple_prefix program allocator world scope parents caller context origins pending slot destination count fresh consistent
  have requested := ScopedQuerySource.constrained_result_retains_reference_entry .relational program allocator world
    {scope with frontier := (ready caller slot destination count, context, origins) :: pending} parents
    (ready caller slot destination count) context origins pending "size-atom" [.var slot] destination caller.goals principal
    rfl rfl (by decide) resolved constrained
  change (ScopedQuerySource.machine .relational program).step
    (placed allocator world scope parents (ready caller slot destination count) context origins pending) = _ at requested
  have last : (ScopedQuerySource.machine .relational program).run 1
      (placed allocator world scope parents (ready caller slot destination count) context origins pending) =
      ([], .suspended (.branch (.invoke "size-atom" [.var slot] destination))
        (placed allocator world scope parents (ready caller slot destination count) context origins pending)) := by
    simp only [Machine.run, requested]
    rfl
  have joined := (ScopedQuerySource.machine .relational program).established_and_pending 1 1 _ _ [] first
  rw [last] at joined
  simpa only [List.nil_append] using joined

theorem counted_value (caller : Control) (slot : String) (destination : Atom) (count : Nat)
    (environment : Environment) (solved : Solves environment (counted caller slot destination count).bindings) :
    read environment destination = value count := by
  have equation := solved (value count, destination) (List.mem_append_right _ (by simp))
  have closed : read environment (value count) = value count := ConstantQuerySource.Scalar.read (.grounded _) environment
  rw [closed] at equation
  exact equation.symm

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedCountReturn
