import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedGuardSource

/-!
# Primitive results through unconstrained aliased destinations

The written result may already occur in equations. What matters is that the
actual solved presentation still reads it as a variable. A closed primitive
result then always refines those equations, without replaying its effect.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedMutationSource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS (World)
open EagerDFS.Destination

theorem read_comp (later first : Environment) (atom : Atom) :
    read (Mettapedia.Logic.LP.Subst.comp later first) atom = read later (read first atom) := by
  simp only [EagerDFS.Destination.read, Mettapedia.Logic.LP.Subst.applyTerm_comp, encode_decode]

theorem solves_comp (later first : Environment) (bindings : Equations) (solved : Solves first bindings) :
    Solves (Mettapedia.Logic.LP.Subst.comp later first) bindings := by
  intro pair member
  rw [read_comp, read_comp, solved pair member]

/-- Refining an unbound representative is valid even when the written
destination is an alias already mentioned by the caller's equations. -/
theorem refine_unbound (bindings : Equations) (principal : Environment) (destination value : Atom) (name : String)
    (resolved : resolve bindings = some principal) (unbound : read principal destination = .var name)
    (closed : ∀ environment, read environment value = value) :
    refine bindings value destination = some (bindings ++ [(value, destination)]) := by
  let later : Environment := Mettapedia.Logic.LP.Subst.single name (encode value)
  apply (refine_iff _ _ _ _).mpr
  refine ⟨rfl, Mettapedia.Logic.LP.Subst.comp later principal,
    solves_comp later principal bindings (resolve_sound resolved), ?_⟩
  rw [closed, read_comp, unbound]
  simp [later, EagerDFS.Destination.read, encode,
    Mettapedia.Logic.LP.Subst.single]

theorem refine_fresh_operand (bindings : Equations) (slot : String) (operand : Atom)
    (fresh : ClosedOnceQueryFrame.FreshFor slot bindings) (apart : slot ∉ (encode operand).freeVars)
    (consistent : ∃ environment, Solves environment bindings) :
    refine bindings operand (.var slot) = some (bindings ++ [(operand, .var slot)]) := by
  obtain ⟨environment, solved⟩ := consistent
  apply (refine_iff _ _ _ _).mpr
  refine ⟨rfl, Function.update environment slot (encode (read environment operand)),
    ClosedOnceQueryFrame.solves_update environment bindings slot (read environment operand) fresh solved, ?_⟩
  rw [ClosedOnceQueryFrame.read_update environment slot (read environment operand) operand apart]
  simp only [EagerDFS.Destination.read, encode, Mettapedia.Logic.LP.Subst.applyTerm]
  exact ((congrArg decode (Function.update_self slot (encode (read environment operand)) environment)).trans
    (decode_encode (read environment operand))).symm

/-- A term admitting both Boolean instances cannot have a rigid constructor
in the principal solved presentation. This tests logical freedom, not whether
the written destination has previously occurred in an equation. -/
theorem unbound_of_boolean_models (bindings : Equations) (principal : Environment) (destination : Atom)
    (resolved : resolve bindings = some principal)
    (models : ∀ value : Bool, ∃ environment, Solves environment bindings ∧
      read environment destination = Effects.boolean value) :
    ∃ name, read principal destination = .var name := by
  obtain ⟨yes, yesSolved, yesRead⟩ := models true
  obtain ⟨no, noSolved, noRead⟩ := models false
  have yesValue := (resolve_read_preserves resolved yes yesSolved destination).trans yesRead
  have noValue := (resolve_read_preserves resolved no noSolved destination).trans noRead
  cases current : read principal destination with
  | var name => exact ⟨name, rfl⟩
  | symbol name =>
      rw [current] at yesValue
      simp [EagerDFS.Destination.read, encode, decode, Effects.boolean] at yesValue
  | grounded value =>
      rw [current] at yesValue noValue
      simp [EagerDFS.Destination.read, encode, decode, Effects.boolean] at yesValue noValue
      exact (by decide : OSLFCore.GroundedValue.bool true ≠ OSLFCore.GroundedValue.bool false)
        (yesValue.symm.trans noValue) |>.elim
  | expression children =>
      rw [current] at yesValue
      simp [read_eq_applyTypeValuation,
        HE.Spec.Type.RuntimeRefinement.applyTypeValuation, Effects.boolean] at yesValue

/-- Preparing an independent operand cannot constrain an older unbound
destination. The new principal solver may choose a different representative;
the theorem preserves its variable character without requiring a name oracle. -/
theorem unbound_after_fresh_operand (bindings : Equations) (principal : Environment)
    (destination operand : Atom) (representative slot : String)
    (resolved : resolve bindings = some principal) (unbound : read principal destination = .var representative)
    (fresh : ClosedOnceQueryFrame.FreshFor slot bindings) (apart : slot ∉ (encode destination).freeVars)
    (operandApart : slot ∉ (encode operand).freeVars) :
    ∃ next name, resolve (bindings ++ [(operand, .var slot)]) = some next ∧ read next destination = .var name := by
  have refined := refine_fresh_operand bindings slot operand fresh operandApart ⟨principal, resolve_sound resolved⟩
  obtain ⟨next, nextResolved⟩ := resolve_complete (ClosedOnceQueryFrame.refined_consistent _ _ _ refined)
  have freedom : ∀ value : Bool, ∃ environment, Solves environment (bindings ++ [(operand, .var slot)]) ∧
      read environment destination = Effects.boolean value := by
    intro value
    let later : Environment := Mettapedia.Logic.LP.Subst.single representative (encode (Effects.boolean value))
    let before : Environment := Mettapedia.Logic.LP.Subst.comp later principal
    let after : Environment := Function.update before slot (encode (read before operand))
    have beforeSolved : Solves before bindings := solves_comp later principal bindings (resolve_sound resolved)
    have afterSolved : Solves after bindings :=
      ClosedOnceQueryFrame.solves_update before bindings slot (read before operand) fresh beforeSolved
    refine ⟨after, ?_, ?_⟩
    · intro pair member
      rcases List.mem_append.mp member with old | added
      · exact afterSolved pair old
      · have same := List.mem_singleton.mp added
        subst pair
        rw [show read after operand = read before operand from
          ClosedOnceQueryFrame.read_update before slot (read before operand) operand operandApart]
        simp only [after, EagerDFS.Destination.read, encode, Mettapedia.Logic.LP.Subst.applyTerm]
        exact ((congrArg decode (Function.update_self slot (encode (read before operand)) before)).trans
          (decode_encode (read before operand))).symm
    · rw [show read after destination = read before destination from
        ClosedOnceQueryFrame.read_update before slot (read before operand) destination apart, read_comp, unbound]
      simp [later, EagerDFS.Destination.read, encode, Mettapedia.Logic.LP.Subst.single, Effects.boolean, decode]
  obtain ⟨name, reading⟩ := unbound_of_boolean_models _ next destination nextResolved freedom
  exact ⟨next, name, nextResolved, reading⟩

/-- The source commits a single primitive result and resumes its actual
continuation with the new equation. Unsupported or constrained entries do not
obtain this prefix merely because a primitive would have returned a value. -/
theorem primitive_prefix {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (head : String) (arguments : List Atom) (destination : Atom) (result : String) (older : List Goal)
    (environment : Environment) (state : Effects.State) (value : Atom)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke head arguments destination :: older)
    (resolved : resolve control.bindings = some environment) (unbound : read environment destination = .var result)
    (closedValue : ∀ environment, read environment value = value)
    (known : StdLib.known head = true) (ordinary : head ≠ "parse") (notQuery : head ≠ "match")
    (mutation : head = "add-atom" ∨ head = "remove-atom" →
      ScopedQuerySource.mutationReady world head (arguments.map (read environment)) = true)
    (applied : StdLib.apply world.state head (arguments.map (read environment)) = .ok (state, [value])) :
    (ScopedQuerySource.machine policy program).run 2 (allocator, ⟨world, scope :: parents⟩) =
      ([], .exhausted (allocator, ⟨{world with state}, {scope with frontier :=
        ({control with bindings := control.bindings ++ [(value, destination)], goals := older},
          context, origins ++ [0]) :: pending} :: parents⟩)) := by
  let returned : Control := {control with goals := .equate value destination :: older}
  let nextScope : CollectionScope Context := {scope with frontier := (returned, context, origins ++ [0]) :: pending}
  have invoked := ScopedQuerySource.Caller.primitive_step policy program allocator world scope parents control context origins pending
    head arguments destination older environment state [value] result frontier atCall resolved unbound known ordinary notQuery mutation applied
  have first : (ScopedQuerySource.machine policy program).step (allocator, ⟨world, scope :: parents⟩) =
      some (.silent (allocator, ⟨{world with state}, nextScope :: parents⟩)) := by
    simpa [nextScope, returned, primitiveWork] using invoked
  have refined := refine_unbound control.bindings environment destination value result resolved unbound closedValue
  have second : (ScopedQuerySource.machine policy program).step (allocator, ⟨{world with state}, nextScope :: parents⟩) =
      some (.silent (allocator, ⟨{world with state}, {scope with frontier :=
        ({control with bindings := control.bindings ++ [(value, destination)], goals := older},
          context, origins ++ [0]) :: pending} :: parents⟩)) := by
    rw [ScopedQuerySource.Guards.ordinary_step policy program allocator {world with state} nextScope parents returned context
      (origins ++ [0]) pending (.equate value destination) older rfl rfl rfl]
    simp [nextScope, returned, scopeStep, enterCollapse?, enterSuperpose?, EagerDFS.Destination.machine,
      refined, installChild, retainChild]
  rw [Machine.run_succ_silent _ first, Machine.run_succ_silent _ second]
  rfl

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedMutationSource
