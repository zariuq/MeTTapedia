import Mettapedia.GSLT.Dynamics.StoreReachability
import Mathlib.Data.List.Basic

/-!
# Host callback ownership across native weak records

The reference is the ordinary host strong-reference graph. The bridge adds
native records, externally rooted native lifetimes and strongly retained weakref
boxes. Weak targets are real metadata edges, but not strong traversal edges.
Host-to-native and native-to-native ownership are permitted. Strong reachability
of host objects is proved unchanged, without requiring host cycles to be
acyclic. Active calls instead install explicit scoped strong roots.

The cleanup model independently compares recursive first-error handling with a
saved-error accumulator. It preserves actual cleanup worlds and ordered effects,
including cleanup errors, while keeping an invocation's own primary error.

The graph is a tracing semantics, not a proof of CPython collection, refcounts,
GIL behavior, native pointer lifetimes or finalizer termination/resurrection.
The bridge requires no hidden strong backedge or weakref callback into the host.
Weakref wrappers are separate logical nodes; physical wrapper freshness or
sharing is not asserted. Host reachability here concerns callback graph objects.
Faults represent primary exception identity; mutations of messages, tracebacks
and notes are ordinary world/diagnostic effects, not rolled back here.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.HostCallbackOwners

open Mettapedia.GSLT.Dynamics.StoreReachability

variable {Host Native : Type}

inductive Node (Host Native : Type) where
  | host (object : Host)
  | native (record : Native)
  | weakBox (record : Native)
  deriving DecidableEq, Repr

structure Bridge (Host Native : Type) where
  host : Store Host
  nativeRoot : Native → Prop
  hostNative : Host → Native → Prop
  nativeNative : Native → Native → Prop
  target : Native → Option Host

/-- Embedding the existing host graph introduces no adapter references. -/
def liftHost (host : Store Host) : Store (Node Host Native) where
  pointsTo source target := match source, target with
    | .host a, .host b => host.pointsTo a b
    | _, _ => False
  root node := match node with
    | .host object => host.root object
    | _ => False

/-- The implementation graph contains actual strong native→weakref-object
edges. Its non-null weak targets are recorded separately below. -/
def nativeStore (bridge : Bridge Host Native) : Store (Node Host Native) where
  pointsTo source target := match source, target with
    | .host a, .host b => bridge.host.pointsTo a b
    | .host object, .native record => bridge.hostNative object record
    | .native a, .native b => bridge.nativeNative a b
    | .native record, .weakBox box => record = box
    | _, _ => False
  root node := match node with
    | .host object => bridge.host.root object
    | .native record => bridge.nativeRoot record
    | .weakBox _ => False

def weakTarget (bridge : Bridge Host Native) : Node Host Native → Node Host Native → Prop
  | .weakBox record, .host object => bridge.target record = some object
  | _, _ => False

/-- The new strong context owns only native records and weakref boxes. Its
edges never require a new live host interface. -/
def weakDeployment (bridge : Bridge Host Native) : Deployment (liftHost (Native := Native) bridge.host) where
  ctxPointsTo source target := match source, target with
    | .host object, .native record => bridge.hostNative object record
    | .native a, .native b => bridge.nativeNative a b
    | .native record, .weakBox box => record = box
    | _, _ => False
  ctxRoot node := match node with
    | .native record => bridge.nativeRoot record
    | _ => False
  owns node := match node with | .host _ => False | _ => True
  interface _ := False
  roots_owned := by intro node rooted; cases node <;> simp_all
  edges_closed := by intro source target edge; cases source <;> cases target <;> simp_all
  interface_live := by intro _ impossible; exact impossible.elim
  ownership_disjoint := by intro source target edge; cases source <;> cases target <;> simp_all [liftHost]

theorem native_store_is_weak_deployment (bridge : Bridge Host Native) :
    nativeStore bridge = compose (liftHost bridge.host) (weakDeployment bridge) := by
  apply congrArg₂ Store.mk
  · funext source target
    cases source <;> cases target <;> simp [liftHost, weakDeployment]
  · funext node
    cases node <;> simp [liftHost, weakDeployment]

theorem lifted_host_reach_iff (host : Store Host) (object : Host) :
    Reach (liftHost (Native := Native) host) (.host object) ↔ Reach host object := by
  constructor
  · intro reached
    have reflected := Reach.reflect (source := host) (target := liftHost host) Node.host
      (by
        intro node rooted
        cases node with
        | host value => exact ⟨value, rooted, rfl⟩
        | native record => cases rooted
        | weakBox record => cases rooted)
      (by
        intro parent node edge
        cases node with
        | host value => exact ⟨value, edge, rfl⟩
        | native record => cases edge
        | weakBox record => cases edge)
      reached
    obtain ⟨original, live, same⟩ := reflected
    cases same
    exact live
  · intro reached
    exact reached.map Node.host (fun _ rooted => rooted) (fun _ _ edge => edge)

/-- Adding arbitrary externally rooted weak records cannot make any new
host object strongly reachable. The additional wrapper objects are real
reachable cells; this result projects precisely the host component. -/
theorem weak_records_preserve_host_reach (bridge : Bridge Host Native) (object : Host) :
    Reach (nativeStore bridge) (.host object) ↔ Reach bridge.host object := by
  rw [native_store_is_weak_deployment]
  constructor
  · intro reached
    rcases compose_reach_cases (liftHost bridge.host) (weakDeployment bridge) (.host object) reached with
      original | owned
    · exact (lifted_host_reach_iff bridge.host object).mp original
    · cases owned
  · intro reached
    exact ((lifted_host_reach_iff bridge.host object).mpr reached).map id
      (fun _ rooted => Or.inl rooted) (fun _ _ edge => Or.inl edge)

theorem externally_rooted_weak_box_is_live (bridge : Bridge Host Native) (record : Native)
    (rooted : bridge.nativeRoot record) : Reach (nativeStore bridge) (.weakBox record) := by
  have start : Reach (nativeStore bridge) (.native record) := .root rooted
  exact .step start rfl

theorem weak_records_preserve_host_garbage (bridge : Bridge Host Native)
    (object : Host) (unreachable : garbage bridge.host object) : garbage (nativeStore bridge) (.host object) := by
  intro reached
  exact unreachable ((weak_records_preserve_host_reach bridge object).mp reached)

def Reference.withRoots (host : Store Host) (active : Host → Prop) : Store Host where
  pointsTo := host.pointsTo
  root object := host.root object ∨ active object

/-- A successful weakref promotion holds the returned object as an actual
strong root until the corresponding scoped reference is released. -/
def scopedStore (bridge : Bridge Host Native) (active : Host → Prop) : Store (Node Host Native) where
  pointsTo := (nativeStore bridge).pointsTo
  root node := (nativeStore bridge).root node ∨ ∃ object, active object ∧ node = .host object

theorem scoped_store_is_host_root_extension (bridge : Bridge Host Native) (active : Host → Prop) :
    scopedStore bridge active = nativeStore {bridge with host := Reference.withRoots bridge.host active} := by
  apply congrArg₂ Store.mk
  · funext source target
    cases source <;> cases target <;> rfl
  · funext node
    cases node <;> simp [nativeStore, Reference.withRoots]

theorem active_scope_reach_refines (bridge : Bridge Host Native) (active : Host → Prop) (object : Host) :
    Reach (scopedStore bridge active) (.host object) ↔ Reach (Reference.withRoots bridge.host active) object := by
  rw [scoped_store_is_host_root_extension]
  exact weak_records_preserve_host_reach _ object

theorem active_strong_root_protects_call (bridge : Bridge Host Native) (active : Host → Prop)
    (object : Host) (held : active object) : Reach (scopedStore bridge active) (.host object) :=
  .root (Or.inr ⟨object, held, rfl⟩)

theorem active_scope_protects_reachable_fields (bridge : Bridge Host Native) (active : Host → Prop)
    (owner object : Host) (held : active owner)
    (path : Relation.ReflTransGen bridge.host.pointsTo owner object) :
    Reach (scopedStore bridge active) (.host object) := by
  apply (active_scope_reach_refines bridge active object).mpr
  have start : Reach (Reference.withRoots bridge.host active) owner := .root (Or.inr held)
  induction path with
  | refl => exact start
  | tail _ edge ih => exact .step ih edge

theorem removing_active_roots_restores_garbage (bridge : Bridge Host Native) (object : Host)
    (unreachable : garbage bridge.host object) :
    garbage (scopedStore bridge (fun _ => False)) (.host object) := by
  intro reached
  have hostReach := (active_scope_reach_refines bridge (fun _ => False) object).mp reached
  apply unreachable
  exact Reach.map (source := Reference.withRoots bridge.host (fun _ => False))
    (target := bridge.host) id
    (fun object rooted => by
      change bridge.host.root object ∨ False at rooted
      exact rooted.elim id False.elim)
    (fun _ _ edge => edge) hostReach

/-- The mutant adds a native strong hold of the weak target. It does not
alter the host program's own graph, but defeats collection of its cycle. -/
def strongTargetMutant (bridge : Bridge Host Native) : Store (Node Host Native) where
  pointsTo source target := (nativeStore bridge).pointsTo source target ∨
    ∃ record object, source = .native record ∧ target = .host object ∧ bridge.target record = some object
  root := (nativeStore bridge).root

theorem rooted_strong_target_is_live (bridge : Bridge Host Native) (record : Native) (object : Host)
    (rooted : bridge.nativeRoot record) (target : bridge.target record = some object) :
    Reach (strongTargetMutant bridge) (.host object) := by
  have start : Reach (strongTargetMutant bridge) (.native record) := .root rooted
  exact .step start (Or.inr ⟨record, object, rfl, rfl, target⟩)

theorem rootless_host_graph_is_garbage (host : Store Host)
    (noRoots : ∀ object, ¬host.root object) (object : Host) : garbage host object := by
  intro reached
  induction reached with
  | root rooted => exact noRoots _ rooted
  | step _ _ ih => exact ih

namespace Cleanup

variable {World Fault Effect : Type}

structure Reply (World Fault Effect : Type) where
  world : World
  fault : Option Fault
  effects : List Effect

abbrev Operation (World Fault Effect : Type) := World → Reply World Fault Effect

structure Result (World Fault Effect : Type) where
  world : World
  reported : Option Fault
  effects : List Effect
  /-- A semantic suppression trace, not a runtime strong-reference registry. -/
  suppressed : List Fault

/-- Independent recursive reference: the first error belongs to the original
pull when supplied, otherwise to the first failing cleanup. Later cleanup
still executes, including operations that themselves report another error. -/
def reference : List (Operation World Fault Effect) → Option Fault → World → Result World Fault Effect
  | [], primary, world => ⟨world, primary, [], []⟩
  | operation :: rest, primary, world =>
      let actual := operation world
      let selected := match primary with | some fault => some fault | none => actual.fault
      let later := reference rest selected actual.world
      ⟨later.world, later.reported, actual.effects ++ later.effects,
        (if primary.isSome then actual.fault.toList else []) ++ later.suppressed⟩

/-- The native client saves its own pending error across each effectful
operation. An absent own error does not acquire an unrelated handled error
from an outer caller. Diagnostic faults use the same protected boundary. -/
def step (state : Result World Fault Effect) (operation : Operation World Fault Effect) :
    Result World Fault Effect :=
  let saved := state.reported
  let actual := operation state.world
  match saved with
  | none => ⟨actual.world, actual.fault, state.effects ++ actual.effects, state.suppressed⟩
  | some primary =>
      ⟨actual.world, some primary, state.effects ++ actual.effects,
        state.suppressed ++ actual.fault.toList⟩

def native (operations : List (Operation World Fault Effect)) (primary : Option Fault) (world : World) :
    Result World Fault Effect := operations.foldl step ⟨world, primary, [], []⟩

theorem fold_refines (operations : List (Operation World Fault Effect))
    (before : Result World Fault Effect) :
    operations.foldl step before =
      let expected := reference operations before.reported before.world
      ⟨expected.world, expected.reported, before.effects ++ expected.effects,
        before.suppressed ++ expected.suppressed⟩ := by
  induction operations generalizing before with
  | nil => simp [reference]
  | cons operation rest ih =>
      rw [List.foldl_cons, ih]
      cases primary : before.reported <;>
        simp [reference, step, primary, List.append_assoc]

/-- Complete worlds, ordered effect occurrences and suppressed-error traces
agree, not only the selected primary identity. -/
theorem native_refines (operations : List (Operation World Fault Effect))
    (primary : Option Fault) (world : World) :
    native operations primary world = reference operations primary world := by
  simpa [native] using fold_refines operations (⟨world, primary, [], []⟩ : Result World Fault Effect)

theorem reference_preserves_own_primary (operations : List (Operation World Fault Effect))
    (primary : Fault) (world : World) :
    (reference operations (some primary) world).reported = some primary := by
  induction operations generalizing world with
  | nil => rfl
  | cons operation rest ih => exact ih (operation world).world

theorem cleanup_cannot_replace_own_primary (operations : List (Operation World Fault Effect))
    (primary : Fault) (world : World) :
    (native operations (some primary) world).reported = some primary := by
  rw [native_refines]
  exact reference_preserves_own_primary operations primary world

/-- Error protection does not skip or roll back cleanup. Every operation
sees the actual world left by its predecessor, independently of which error
will eventually be reported. -/
theorem reference_effects_independent_of_primary
    (operations : List (Operation World Fault Effect)) (first second : Option Fault) (world : World) :
    (reference operations first world).world = (reference operations second world).world ∧
      (reference operations first world).effects = (reference operations second world).effects := by
  induction operations generalizing first second world with
  | nil => exact ⟨rfl, rfl⟩
  | cons operation rest ih =>
      have later := ih
        (match first with | some fault => some fault | none => (operation world).fault)
        (match second with | some fault => some fault | none => (operation world).fault)
        (operation world).world
      exact ⟨later.1, congrArg (List.append (operation world).effects) later.2⟩

theorem native_cleanup_effects_do_not_depend_on_primary
    (operations : List (Operation World Fault Effect)) (first second : Option Fault) (world : World) :
    (native operations first world).world = (native operations second world).world ∧
      (native operations first world).effects = (native operations second world).effects := by
  rw [native_refines, native_refines]
  exact reference_effects_independent_of_primary operations first second world

end Cleanup

namespace Controls

inductive HostObject where
  | engine | registration | function | invocation | iterator
  deriving DecidableEq, Repr

inductive NativeRecord where
  | registration | invocation
  deriving DecidableEq, Repr

/-- Registration.engine is weak; the function closes over its engine.
Invocation.engine and the ordinary engine invocation table are strong. -/
def callbackGraph : Store HostObject where
  pointsTo source target := match source, target with
    | .engine, .registration | .registration, .function | .function, .engine => True
    | .engine, .invocation | .invocation, .engine | .invocation, .iterator | .iterator, .engine => True
    | _, _ => False
  root _ := False

def bridge : Bridge HostObject NativeRecord where
  host := callbackGraph
  nativeRoot _ := True
  hostNative object _ := object = .engine
  nativeNative _ _ := True
  target record := some (match record with | .registration => .registration | .invocation => .invocation)

theorem callback_function_really_forms_a_host_cycle :
    Relation.TransGen callbackGraph.pointsTo .engine .engine := by
  have first : Relation.TransGen callbackGraph.pointsTo .engine .registration := .single trivial
  have second : Relation.TransGen callbackGraph.pointsTo .engine .function := .tail first trivial
  exact .tail second trivial

theorem rootless_cycles_remain_garbage (object : HostObject) :
    garbage (nativeStore bridge) (.host object) :=
  weak_records_preserve_host_garbage bridge object
    (rootless_host_graph_is_garbage callbackGraph (fun _ impossible => impossible) object)

theorem rooted_weak_record_keeps_box_but_not_its_engine :
    Reach (nativeStore bridge) (.weakBox .registration) ∧
      weakTarget bridge (.weakBox .registration) (.host .registration) ∧
      garbage (nativeStore bridge) (.host .engine) := by
  exact ⟨externally_rooted_weak_box_is_live bridge .registration trivial, rfl,
    rootless_cycles_remain_garbage .engine⟩

theorem collection_removes_unreachable_cycle_edges :
    ¬(collect (nativeStore bridge)).pointsTo (.host .engine) (.host .registration) := by
  intro present
  exact rootless_cycles_remain_garbage .engine present.1

theorem active_invocation_protects_the_engine_and_iterator :
    Reach (scopedStore bridge (fun object => object = .invocation)) (.host .engine) ∧
      Reach (scopedStore bridge (fun object => object = .invocation)) (.host .iterator) := by
  have live := active_strong_root_protects_call bridge
    (fun object => object = .invocation) .invocation rfl
  exact ⟨.step live trivial, .step live trivial⟩

theorem releasing_active_roots_exposes_the_rootless_cycle_again :
    garbage (scopedStore bridge (fun _ => False)) (.host .engine) :=
  removing_active_roots_restores_garbage bridge .engine
    (rootless_host_graph_is_garbage callbackGraph (fun _ impossible => impossible) .engine)

/-- An externally rooted native strong hold would leak the actual callback
closure cycle, even though the host graph has no ordinary external roots. -/
theorem strong_reference_mutant_leaks_the_callback_cycle :
    Reach (strongTargetMutant bridge) (.host .engine) := by
  have registration := rooted_strong_target_is_live bridge .registration .registration trivial rfl
  have functionLive : Reach (strongTargetMutant bridge) (.host .function) :=
    .step registration (Or.inl trivial)
  exact .step functionLive (Or.inl trivial)

theorem strongly_retained_target_violates_host_projection :
    garbage bridge.host .engine ∧ Reach (strongTargetMutant bridge) (.host .engine) :=
  ⟨rootless_host_graph_is_garbage callbackGraph (fun _ impossible => impossible) .engine,
    strong_reference_mutant_leaks_the_callback_cycle⟩

def cleanup (effect : Nat) (fault : Option String) : Cleanup.Operation (List Nat) String Nat :=
  fun world => ⟨world ++ [effect], fault, [effect]⟩

theorem primary_survives_close_and_diagnostic_failures :
    let result := Cleanup.native [cleanup 1 (some "close"), cleanup 2 (some "note")]
      (some "pull") []
    result.reported = some "pull" ∧ result.world = [1, 2] ∧ result.effects = [1, 2] ∧
      result.suppressed = ["close", "note"] := by decide

theorem no_own_primary_reports_the_first_cleanup_error :
    let result := Cleanup.native [cleanup 1 (some "close"), cleanup 2 (some "later")]
      none []
    result.reported = some "close" ∧ result.world = [1, 2] ∧ result.suppressed = ["later"] := by decide

theorem successful_cleanup_preserves_primary_and_duplicate_effects :
    let result := Cleanup.native [cleanup 7 none, cleanup 7 none] (some "pull") []
    result.reported = some "pull" ∧ result.world = [7, 7] ∧ result.effects = [7, 7] := by decide

def overwritePrimary (state : Cleanup.Result (List Nat) String Nat)
    (operation : Cleanup.Operation (List Nat) String Nat) : Cleanup.Result (List Nat) String Nat :=
  let actual := operation state.world
  ⟨actual.world, actual.fault, state.effects ++ actual.effects, state.suppressed⟩

theorem replacing_primary_with_cleanup_error_is_detected :
    let initial : Cleanup.Result (List Nat) String Nat := ⟨[], some "pull", [], []⟩
    let correct := Cleanup.step initial (cleanup 1 (some "close"))
    let faulty := overwritePrimary initial (cleanup 1 (some "close"))
    correct.world = faulty.world ∧ correct.effects = faulty.effects ∧
      correct.reported = some "pull" ∧ faulty.reported = some "close" := by decide

theorem sampling_unrelated_caller_error_is_detected :
    (Cleanup.native [cleanup 1 (some "close")] none []).reported = some "close" ∧
      (Cleanup.native [cleanup 1 (some "close")] (some "unrelated caller") []).reported =
        some "unrelated caller" := by decide

/-- Returning the primary immediately would preserve error identity while
silently skipping the cleanup's actual effects. -/
theorem skipping_cleanup_to_preserve_primary_is_detected :
    let result := Cleanup.native [cleanup 1 (some "close")] (some "pull") []
    result.reported = some "pull" ∧ result.world ≠ [] ∧ result.effects = [1] := by decide

end Controls

end Mettapedia.Machines.HostCallbackOwners
