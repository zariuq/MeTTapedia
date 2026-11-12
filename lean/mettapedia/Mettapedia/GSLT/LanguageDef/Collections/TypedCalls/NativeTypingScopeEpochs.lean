import Mettapedia.Machines.IssuedEpochDirectory
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeEntryScope

/-!
# Chronological compression of source typing-scope certificates

This executable publication-level model follows the existing mixed source,
import and overlay actions. The local declaration counter protects the root
coordinates. For layered views, two globally issued epochs protect the inherited
own-prefix and ordered import coordinates. Their maximum replaces the explicit
pair in the retained token. No hash injectivity or whole-query equality is
assumed. Initialization and publication derive the coordinate invariant.

The interface publishes changed source coordinates, not inference answers.
Connecting C's notification branches and compressed owner/profile words to this
interface is a separate realization obligation. In particular, this file does
not infer that comparison of arbitrary maxima is sufficient, or that native
counters can wrap. The native cache payload and heap representation retain
their existing independent contracts.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypingScopeEpochs

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open NativeTypeSourcePorts (Source)
open RetainedTypePayloads (ExternalView)

namespace Directory
export Mettapedia.Machines.IssuedEpochDirectory
  (State Valid initial initial_valid publish execute execute_append execute_valid
    latest execute_same_latest_value)
end Directory

namespace Scope
export NativeTypingScopeOverlays
  (State Token token Action step execute check CeilingValid packet validated_packet)
end Scope

abbrev Value (size : Nat) := Nat ⊕ List (Fin size × Nat)

/-- Plain scopes keep their whole source certificate in the local revision.
Layered scopes leave inherited prefix/import coordinates to the epoch issuer. -/
def rootCoordinate {size : Nat} (scope : Scope.State size) : Scope.Token size :=
  if scope.layers.isEmpty then Scope.token scope
  else { Scope.token scope with own := 0, imports := [] }

def part {size : Nat} (scope : Scope.State size) (which : Bool) : Value size :=
  match which with
  | false => .inl (if scope.layers.isEmpty then 0 else (Scope.token scope).own)
  | true => .inr (if scope.layers.isEmpty then [] else (Scope.token scope).imports)

def assemble {size : Nat} (root : Scope.Token size) : Value size → Value size → Option (Scope.Token size)
  | .inl own, .inr imports => some { root with own := root.own + own, imports := root.imports ++ imports }
  | _, _ => none

theorem assemble_current {size : Nat} (scope : Scope.State size) :
    assemble (rootCoordinate scope) (part scope false) (part scope true) = some (Scope.token scope) := by
  cases empty : scope.layers.isEmpty <;> simp [assemble, rootCoordinate, part, empty]

structure State (size : Nat) where
  scope : Scope.State size
  declarations : Nat
  epochs : Directory.State Bool (Value size)

def Valid {size : Nat} (state : State size) : Prop :=
  Directory.Valid state.epochs ∧ ∀ which, (state.epochs.cells which).value = part state.scope which

def initial {size : Nat} (scope : Scope.State size) : State size :=
  ⟨scope, 0, Directory.initial (part scope)⟩

theorem initial_valid {size : Nat} (scope : Scope.State size) : Valid (initial scope) :=
  ⟨Directory.initial_valid _, fun _ => rfl⟩

def updates {size : Nat} (epochs : Directory.State Bool (Value size)) (scope : Scope.State size) :
    List (Bool × Value size) :=
  (if (epochs.cells false).value = part scope false then [] else [(false, part scope false)]) ++
  (if (epochs.cells true).value = part scope true then [] else [(true, part scope true)])

theorem updates_value {size : Nat} (epochs : Directory.State Bool (Value size))
    (scope : Scope.State size) (which : Bool) :
    ((Directory.execute epochs (updates epochs scope)).cells which).value = part scope which := by
  cases which <;>
    by_cases own : (epochs.cells false).value = part scope false <;>
    by_cases imports : (epochs.cells true).value = part scope true <;>
    simp [updates, own, imports, Directory.execute, Directory.publish]

def commands {size : Nat} (state : State size) (action : Scope.Action size) : List (Bool × Value size) :=
  updates state.epochs (Scope.step state.scope action)

def step {size : Nat} (state : State size) (action : Scope.Action size) : State size :=
  let after := Scope.step state.scope action
  ⟨after, state.declarations + if rootCoordinate after = rootCoordinate state.scope then 0 else 1,
    Directory.execute state.epochs (commands state action)⟩

theorem step_valid {size : Nat} (state : State size) (valid : Valid state) (action : Scope.Action size) :
    Valid (step state action) :=
  ⟨Directory.execute_valid state.epochs valid.1 _, updates_value state.epochs _⟩

theorem step_declarations_mono {size : Nat} (state : State size) (action : Scope.Action size) :
    state.declarations ≤ (step state action).declarations := by simp [step]

theorem step_same_declarations_root {size : Nat} (state : State size) (action : Scope.Action size)
    (same : (step state action).declarations = state.declarations) :
    rootCoordinate (step state action).scope = rootCoordinate state.scope := by
  by_cases unchanged : rootCoordinate (Scope.step state.scope action) = rootCoordinate state.scope
  · exact unchanged
  · simp [step, unchanged] at same

def execute {size : Nat} (state : State size) : List (Scope.Action size) → State size
  | [] => state
  | action :: rest => execute (step state action) rest

def trace {size : Nat} (state : State size) : List (Scope.Action size) → List (Bool × Value size)
  | [] => []
  | action :: rest => commands state action ++ trace (step state action) rest

theorem execute_scope {size : Nat} (state : State size) (actions : List (Scope.Action size)) :
    (execute state actions).scope = Scope.execute state.scope actions := by
  induction actions generalizing state with
  | nil => rfl
  | cons action rest ih => exact ih _

theorem execute_epochs {size : Nat} (state : State size) (actions : List (Scope.Action size)) :
    (execute state actions).epochs = Directory.execute state.epochs (trace state actions) := by
  induction actions generalizing state with
  | nil => rfl
  | cons action rest ih => simpa [execute, trace, Directory.execute_append, step] using ih (step state action)

theorem execute_valid {size : Nat} (state : State size) (valid : Valid state)
    (actions : List (Scope.Action size)) : Valid (execute state actions) := by
  induction actions generalizing state with
  | nil => exact valid
  | cons action rest ih => exact ih _ (step_valid state valid action)

theorem execute_declarations_mono {size : Nat} (state : State size) (actions : List (Scope.Action size)) :
    state.declarations ≤ (execute state actions).declarations := by
  induction actions generalizing state with
  | nil => exact Nat.le_refl _
  | cons action rest ih => exact (step_declarations_mono state action).trans (ih _)

theorem execute_same_declarations_root {size : Nat} (state : State size) (actions : List (Scope.Action size))
    (same : (execute state actions).declarations = state.declarations) :
    rootCoordinate (execute state actions).scope = rootCoordinate state.scope := by
  induction actions generalizing state with
  | nil => rfl
  | cons action rest ih =>
      have first := step_declarations_mono state action
      have later := execute_declarations_mono (step state action) rest
      have firstEq : (step state action).declarations = state.declarations := by
        change (execute (step state action) rest).declarations = state.declarations at same
        omega
      exact (ih _ (by simpa [execute, firstEq] using same)).trans
        (step_same_declarations_root state action firstEq)

structure Token (size : Nat) where
  identity : Nat
  generation : Nat
  reader : Fin size
  declarations : Nat
  dependency : Nat
  deriving DecidableEq

def token {size : Nat} (state : State size) : Token size :=
  ⟨state.scope.identity, state.scope.generation, state.scope.reader, state.declarations,
    Directory.latest state.epochs [false, true]⟩

def check {size : Nat} (state : State size) (saved : Token size) : Bool := decide (token state = saved)

/-- The compressed check earns equality of the full source certificate over
the actual publication history; it is not a collision-free-hash assumption. -/
theorem validated_source_token {size : Nat} (state : State size) (valid : Valid state)
    (actions : List (Scope.Action size))
    (accepted : check (execute state actions) (token state) = true) :
    Scope.token (execute state actions).scope = Scope.token state.scope := by
  have equal : token (execute state actions) = token state := of_decide_eq_true accepted
  have root := execute_same_declarations_root state actions (congrArg Token.declarations equal)
  have latest := congrArg Token.dependency equal
  change Directory.latest (execute state actions).epochs [false, true] =
    Directory.latest state.epochs [false, true] at latest
  rw [execute_epochs] at latest
  have aligned := execute_valid state valid actions
  have parts (which : Bool) : part (execute state actions).scope which = part state.scope which := by
    have retained := Directory.execute_same_latest_value state.epochs valid.1 (trace state actions)
      [false, true] latest which (by cases which <;> simp)
    rw [← execute_epochs] at retained
    simpa only [aligned.2 which, valid.2 which] using retained
  apply Option.some.inj
  calc
    some (Scope.token (execute state actions).scope) =
        assemble (rootCoordinate (execute state actions).scope)
          (part (execute state actions).scope false) (part (execute state actions).scope true) :=
      (assemble_current _).symm
    _ = assemble (rootCoordinate state.scope) (part state.scope false) (part state.scope true) := by
      rw [root, parts false, parts true]
    _ = some (Scope.token state.scope) := assemble_current _

theorem validated_source_check {size : Nat} (state : State size) (valid : Valid state)
    (actions : List (Scope.Action size))
    (accepted : check (execute state actions) (token state) = true) :
    Scope.check (Scope.execute state.scope actions) (Scope.token state.scope) = true := by
  have same := validated_source_token state valid actions accepted
  rw [execute_scope] at same
  simp [Scope.check, same]

theorem validated_packet {size : Nat} (state : State size) (valid : Valid state)
    (actions : List (Scope.Action size)) (bounded : Scope.CeilingValid state.scope.source state.scope.reader state.scope.layers)
    (accepted : check (execute state actions) (token state) = true) :
    Scope.packet (execute state actions).scope = Scope.packet state.scope := by
  rw [execute_scope]
  exact Scope.validated_packet state.scope actions bounded (validated_source_check state valid actions accepted)

theorem validated_snapshot {size : Nat} (configuration : Source) (state : State size) (valid : Valid state)
    (actions : List (Scope.Action size)) (bounded : Scope.CeilingValid state.scope.source state.scope.reader state.scope.layers)
    (accepted : check (execute state actions) (token state) = true) :
    TypeReadScopeMemo.snapshot configuration (execute state actions).scope =
      TypeReadScopeMemo.snapshot configuration state.scope := by
  rw [execute_scope]
  exact TypeReadScopeMemo.snapshot_validated configuration state.scope actions bounded
    (validated_source_check state valid actions accepted)

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypingScopeEpochs
