import Mettapedia.Machines.OrderedDependencyStore

/-!
# Nested ordered dependency overlays

Each overlay holds a bounded prefix of its parent's own storage, hides selected
parent positions, and appends its own ordered entries. Nested overlays transform
only own storage. The root module's flattened dependencies are read live once,
after the outermost own layer. Whole-store notifications and overlay publication
clocks jointly certify this view.

Clocks are unbounded natural numbers. A concrete finite-width implementation
must refuse rollover or advance a lifetime identity before reusing a stamp.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OrderedDependencyOverlay

open OrderedDependencyStore

universe u

structure Layer (Entry : Type u) where
  ceiling : Nat
  hidden : Finset Nat
  own : List Entry

variable {Entry : Type u} {size : Nat}

def Layer.view (layer : Layer Entry) (parent : List Entry) : List Entry :=
  (parent.take layer.ceiling).zipIdx.filterMap
    (fun row => if row.2 ∈ layer.hidden then none else some row.1) ++ layer.own

def collectVisible (layer : Layer Entry) : List (Entry × Nat) → List Entry → List Entry
  | [], accumulated => accumulated
  | row :: rest, accumulated => collectVisible layer rest
      (if row.2 ∈ layer.hidden then accumulated else accumulated ++ [row.1])

theorem collectVisible_eq (layer : Layer Entry) (rows : List (Entry × Nat))
    (accumulated : List Entry) : collectVisible layer rows accumulated =
      accumulated ++ rows.filterMap
        (fun row => if row.2 ∈ layer.hidden then none else some row.1) := by
  induction rows generalizing accumulated with
  | nil => simp [collectVisible]
  | cons row rest ih =>
      by_cases hidden : row.2 ∈ layer.hidden <;>
        simp [collectVisible, hidden, ih, List.append_assoc]

def Layer.execute (layer : Layer Entry) (parent : List Entry) : List Entry :=
  collectVisible layer (parent.take layer.ceiling).zipIdx [] ++ layer.own

theorem Layer.execute_eq_view (layer : Layer Entry) (parent : List Entry) :
    layer.execute parent = layer.view parent := by
  simp [Layer.execute, Layer.view, collectVisible_eq]

def collectLayers : List (Layer Entry) → List Entry → List Entry
  | [], parent => parent
  | layer :: rest, parent => collectLayers rest (layer.execute parent)

theorem collectLayers_eq (layers : List (Layer Entry)) (parent : List Entry) :
    collectLayers layers parent = layers.foldl (fun own layer => layer.view own) parent := by
  induction layers generalizing parent with
  | nil => rfl
  | cons layer rest ih => simp [collectLayers, ih, Layer.execute_eq_view]

structure State (Entry : Type u) (size : Nat) where
  identity : Nat
  generation : Nat
  store : Store Entry size
  reader : Fin size
  layers : List (Layer Entry)
  revision : Nat

/-- Independent layer and source-segment observation. -/
def observe (layers : List (Layer Entry))
    (parts : List Entry × List (Fin size × List Entry)) : List Entry :=
  layers.foldl (fun own layer => layer.view own) parts.1 ++ parts.2.flatMap Prod.snd

def view (s : State Entry size) : List Entry := observe s.layers (segments s.store s.reader)

/-- Apply local layers first, then run the module source collection loop once. -/
def query (s : State Entry size) : List Entry :=
  collect s.store (s.store.members s.reader).deps
    (collectLayers s.layers (s.store.members s.reader).own)

theorem query_eq_view (s : State Entry size) : query s = view s := by
  simp [query, view, observe, segments, collect_eq, collectLayers_eq,
    List.flatMap_map]

def clock (s : State Entry size) : Nat := s.revision + (s.store.members s.reader).revision

inductive Action (Entry : Type u) (size : Nat) where
  | storeUpdate (action : OrderedDependencyStore.Action Entry size)
  | publish (layers : List (Layer Entry))
  | retire

/-- Layer publication advances the overlay clock even if its new answer happens
to equal the old answer. Retirement also advances its lifetime generation. -/
def step (s : State Entry size) : Action Entry size → State Entry size
  | .storeUpdate action => { s with store := OrderedDependencyStore.step s.store action }
  | .publish layers => { s with layers := layers, revision := s.revision + 1 }
  | .retire =>
      { s with layers := [], generation := s.generation + 1, revision := s.revision + 1 }

theorem step_observers (s : State Entry size) (h : ObserverInvariant s.store)
    (action : Action Entry size) : ObserverInvariant (step s action).store := by
  cases action with
  | storeUpdate action => exact OrderedDependencyStore.step_observers s.store h action
  | publish layers => exact h
  | retire => exact h

theorem step_clock_mono (s : State Entry size) (action : Action Entry size) :
    clock s ≤ clock (step s action) := by
  cases action with
  | storeUpdate action =>
      exact Nat.add_le_add_left
        (OrderedDependencyStore.step_revision_mono s.store action s.reader) s.revision
  | publish layers => simp only [clock, step]; omega
  | retire => simp only [clock, step]; omega

theorem step_view_of_clock_eq (s : State Entry size) (h : ObserverInvariant s.store)
    (action : Action Entry size) (same : clock (step s action) = clock s) :
    view (step s action) = view s := by
  cases action with
  | storeUpdate action =>
      have unchanged : ((OrderedDependencyStore.step s.store action).members s.reader).revision =
          (s.store.members s.reader).revision := by
        simp only [clock, step] at same
        omega
      unfold view
      exact congrArg (observe s.layers)
        (OrderedDependencyStore.step_segments_of_revision_eq s.store h action s.reader unchanged)
  | publish layers => simp only [clock, step] at same; omega
  | retire => simp only [clock, step] at same; omega

def execute (s : State Entry size) : List (Action Entry size) → State Entry size
  | [] => s
  | action :: rest => execute (step s action) rest

theorem execute_observers (s : State Entry size) (h : ObserverInvariant s.store)
    (actions : List (Action Entry size)) : ObserverInvariant (execute s actions).store := by
  induction actions generalizing s with
  | nil => exact h
  | cons action rest ih => exact ih (step s action) (step_observers s h action)

theorem execute_clock_mono (s : State Entry size) (actions : List (Action Entry size)) :
    clock s ≤ clock (execute s actions) := by
  induction actions generalizing s with
  | nil => exact Nat.le_refl _
  | cons action rest ih => exact (step_clock_mono s action).trans (ih _)

theorem execute_view_of_clock_eq (s : State Entry size) (h : ObserverInvariant s.store)
    (actions : List (Action Entry size)) (same : clock (execute s actions) = clock s) :
    view (execute s actions) = view s := by
  induction actions generalizing s with
  | nil => rfl
  | cons action rest ih =>
      have first := step_clock_mono s action
      have later := execute_clock_mono (step s action) rest
      have unchanged : clock (step s action) = clock s := by
        simp only [execute] at same
        omega
      have tail : clock (execute (step s action) rest) = clock (step s action) := by
        simpa [execute, unchanged] using same
      exact (ih (step s action) (step_observers s h action) tail).trans
        (step_view_of_clock_eq s h action unchanged)

structure Stamp (size : Nat) where
  identity : Nat
  generation : Nat
  root : ReadStamp size
  clock : Nat
  deriving DecidableEq

def stamp (s : State Entry size) : Stamp size :=
  ⟨s.identity, s.generation, readStamp s.store s.reader, clock s⟩

def checkStamp (s : State Entry size) (certificate : Stamp size) : Bool :=
  decide (certificate = stamp s)

theorem validated_query (s : State Entry size) (h : ObserverInvariant s.store)
    (actions : List (Action Entry size))
    (valid : checkStamp (execute s actions) (stamp s) = true) :
    query (execute s actions) = query s := by
  have same := congrArg Stamp.clock (of_decide_eq_true valid)
  simp only [stamp] at same
  rw [query_eq_view, query_eq_view]
  exact execute_view_of_clock_eq s h actions same.symm

namespace Controls

def nested : State Nat 3 :=
  ⟨903, 0, OrderedDependencyStore.Controls.imported, 0,
    [⟨1, ∅, [99, 99]⟩, ⟨3, {0}, [77]⟩], 0⟩

theorem nested_masks_do_not_mask_or_duplicate_dependencies :
    query nested = [99, 99, 77, 7, 7] := by decide

theorem dependency_mutation_expires_nested_view :
    query (step nested (.storeUpdate (.append 2 [8]))) = [99, 99, 77, 7, 7, 8] ∧
    checkStamp (step nested (.storeUpdate (.append 2 [8]))) (stamp nested) = false := by
  decide

theorem masked_parent_append_keeps_answer_not_full_stamp :
    query (step nested (.storeUpdate (.append 0 [88]))) = query nested ∧
    checkStamp (step nested (.storeUpdate (.append 0 [88]))) (stamp nested) = false := by
  decide

theorem unrelated_member_update_keeps_nested_stamp :
    checkStamp (step nested (.storeUpdate (.append 1 [88]))) (stamp nested) = true ∧
    query (step nested (.storeUpdate (.append 1 [88]))) = query nested := by
  decide

def missingParentNotification : State Nat 3 :=
  { nested with store := OrderedDependencyStore.Controls.omittedNotification }

theorem missing_parent_notification_accepts_changed_nested_answer :
    checkStamp missingParentNotification (stamp nested) = true ∧
    query missingParentNotification ≠ query nested := by
  decide

theorem restored_layers_do_not_revive_a_retired_overlay_stamp :
    let restored := step (step nested .retire) (.publish nested.layers)
    query restored = query nested ∧ checkStamp restored (stamp nested) = false := by
  decide

theorem layer_removal_expires_nested_stamp :
    query (step nested (.publish [⟨1, ∅, [99, 99]⟩])) = [42, 99, 99, 7, 7] ∧
    checkStamp (step nested (.publish [⟨1, ∅, [99, 99]⟩])) (stamp nested) = false := by
  decide

def doubleComposed : List Nat :=
  query nested ++ (nested.store.members nested.reader).deps.flatMap
    fun source => (nested.store.members source).own

theorem double_composition_changes_duplicate_occurrences :
    doubleComposed = [99, 99, 77, 7, 7, 7, 7] ∧ doubleComposed ≠ query nested := by
  decide

end Controls

end Mettapedia.Machines.OrderedDependencyOverlay
