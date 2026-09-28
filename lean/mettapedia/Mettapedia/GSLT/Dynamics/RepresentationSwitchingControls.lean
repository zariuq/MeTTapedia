import Mettapedia.GSLT.Dynamics.ContextIndexedSwitching
import Mettapedia.GSLT.Dynamics.CertifiedRepresentationPlanning

/-!
# Controls for scoped switching and supported work plans

These controls do not use rho, MeTTa, a benchmark name, or a search heuristic.
They exercise the generic contract with two-slot contexts. A separate rho
instance certifies a recursive syntax compiler.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.RepresentationSwitchingControls

open RegionHolePlan RepresentationSwitching ContextIndexedSwitching
open CertifiedRepresentationPlanning
open Mettapedia.GraphTheory.Representation

/-- The prepared evaluator changes the arithmetic evaluation order; equality
is proved rather than defining the source through the prepared evaluator. -/
def contextKernel : Kernel Bool Nat where
  Code := Nat
  source index env := env false + env true + index
  prepared index := index
  execute code env := code + env true + env false
  correct index env := by omega

def firstKey : ActivationKey := ⟨7, 1⟩
def recycledKey : ActivationKey := ⟨7, 2⟩

def originalStore : Store Bool Nat := fun key coordinate =>
  if key = firstKey then (if coordinate then 20 else 10)
  else (if coordinate then 200 else 100)

def refineFirst (store : Store Bool Nat) : Store Bool Nat := fun key coordinate =>
  if key = firstKey ∧ coordinate = false then 7 else store key coordinate

def initial : TreeState Bool Nat :=
  ⟨originalStore, [⟨firstKey, 0, 41⟩, ⟨firstKey, 0, 42⟩, ⟨recycledKey, 0, 43⟩], []⟩

/-- A -> B -> A -> B -> A with a write, a rollback and cancellation.
The first two jobs have equal templates/values but distinct occurrences. -/
def route : Execution (family contextKernel) .tree () .tree () :=
  .region (Y := ()) 1
    (.switch (enter contextKernel { time := 2, allocated := 3 })
      (.hole (Y := ()) (.environment refineFirst)
        (.region (Y := ()) 1
          (.switch (leave contextKernel { time := 1 })
            (.hole (Y := ()) (.environment (fun _ => originalStore))
              (.region (Y := ()) 1
                (.switch (enter contextKernel { time := 2 })
                  (.hole (Y := ()) .cancel
                    (.switch (leave contextKernel { time := 1 }) (.done Engine.tree ()))))))))))

theorem repeated_switches_exact : route.denote initial =
    Plan.denote (treeRealization contextKernel) route.erase initial :=
  mixed_execution_exact contextKernel route initial

theorem scoped_trace : (route.denote initial).published =
    [⟨firstKey, 41, 30⟩, ⟨firstKey, 42, 27⟩, ⟨recycledKey, 43, 300⟩] := by
  decide

theorem rollback_and_cancellation : (route.denote initial).store = originalStore ∧
    (route.denote initial).pending = [] := by
  constructor <;> rfl

theorem conversion_receipt :
    (route.resources (fun _ {_ _} _ => Resources.zero)
      (fun _ {_ _} _ => Resources.zero)).time = 6 := by decide

/-- Re-encoding the decoded cursor compacts it, rather than resurrecting its
consumed prefix. A return switch need not restore identical storage. -/
theorem compacted_cursor_receipt :
    let cursor := indexedStep contextKernel (encode initial)
    (compact cursor).frontier.size = 2 ∧
    compactPeak cursor 0 = 5 ∧
    decode (compact cursor) = decode cursor := by
  exact ⟨by decide, by decide, decode_compact _⟩

def advanced : IndexedState Bool Nat := indexedStep contextKernel (encode initial)

/-- Losing the cursor position repeats an already published occurrence. -/
theorem restarting_replays :
    (decode (indexedStep contextKernel { advanced with cursor := 0 })).published ≠
      (decode (indexedStep contextKernel advanced)).published := by decide

/-- A published value is not enough to reconstruct the pending computation. -/
theorem equal_latest_answer_not_equal_residual :
    advanced.published = ({ advanced with cursor := 0 } : IndexedState Bool Nat).published ∧
      (decode advanced).pending ≠
        (decode ({ advanced with cursor := 0 } : IndexedState Bool Nat)).pending := by
  exact ⟨rfl, by decide⟩

/-- A cached value from the old environment misses a later refinement. -/
theorem freezing_values_misses_refinement :
    contextKernel.source 0 (originalStore firstKey) ≠
      contextKernel.source 0 (refineFirst originalStore firstKey) := by decide

/-- Sharing a handle across generations does not license environment sharing. -/
theorem recycled_handle_is_not_same_context :
    firstKey.handle = recycledKey.handle ∧
      contextKernel.source 0 (originalStore firstKey) ≠
        contextKernel.source 0 (originalStore recycledKey) := by decide

/-- Preserving all reference answers by inclusion is weaker than preserving
the ordered occurrence stream: an extra copy is an invented behavior. -/
theorem forward_inclusion_allows_extra_answer :
    (∀ answer ∈ ([30] : List Nat), answer ∈ ([30, 30] : List Nat)) ∧
      ([30] : List Nat) ≠ [30, 30] := by simp

/-! ## Program-supported route choice -/

def treeChoice (authored : Plan Unit (fun _ _ => Nat) (fun _ _ => Boundary Bool Nat) () ()) :
    CertifiedRoute (family contextKernel) .tree authored where
  finish := .tree
  execution := Execution.stay (family := family contextKernel) Engine.tree authored
  source_exact := Execution.erase_stay _ _

def indexedChoice (authored : Plan Unit (fun _ _ => Nat) (fun _ _ => Boundary Bool Nat) () ()) :
    CertifiedRoute (family contextKernel) .tree authored where
  finish := .tree
  execution := .switch (enter contextKernel { time := 2 })
    ((Execution.stay (family := family contextKernel) Engine.indexed authored).append
      (.switch (leave contextKernel { time := 1 }) (.done Engine.tree ())))
  source_exact := by
    simp [Execution.erase, Execution.erase_append, Plan.append_nil]

/-- Only this implementation declaration chooses the route. Current logical
values are not members of the dependency cone. -/
def choosePlan (authored : Plan Unit (fun _ _ => Nat) (fun _ _ => Boundary Bool Nat) () ()) :
    Mettapedia.GSLT.FinitelySupportedPlan Bool Bool
      (CertifiedRoute (family contextKernel) .tree authored) :=
  (Mettapedia.GSLT.FinitelySupportedPlan.read true).map
    (fun enabled => if enabled then indexedChoice authored else treeChoice authored)

def planned := supportedRealization choosePlan

theorem both_work_plans_preserve_residuals (enabled : Bool) :
    observeResult (((planned.freeze (fun _ => enabled)).compile () (route.erase, initial))) =
      Plan.denote (treeRealization contextKernel) route.erase initial :=
  (planned.freeze (fun _ => enabled)).adequate () (route.erase, initial)

theorem irrelevant_declaration_does_not_invalidate :
    (choosePlan route.erase).run (fun _ => true) =
      (choosePlan route.erase).run (fun coordinate => coordinate) := by
  apply (choosePlan route.erase).stable
  intro coordinate member
  have : coordinate = true := by simpa [choosePlan,
    Mettapedia.GSLT.FinitelySupportedPlan.map,
    Mettapedia.GSLT.FinitelySupportedPlan.read] using member
  subst coordinate
  rfl

theorem relevant_declaration_changes_work_plan :
    (((choosePlan route.erase).run (fun _ => true)).execution.resources
      (fun _ {_ _} _ => Resources.zero) (fun _ {_ _} _ => Resources.zero)).time = 3 ∧
    (((choosePlan route.erase).run (fun _ => false)).execution.resources
      (fun _ {_ _} _ => Resources.zero) (fun _ {_ _} _ => Resources.zero)).time = 0 := by
  decide

def onePublication : Plan Unit (fun _ _ => Nat) (fun _ _ => Boundary Bool Nat) () () :=
  .region (Y := ()) 1 (.nil ())

theorem same_plan_reads_current_branch_image :
    ((observeResult ((planned.freeze (fun _ => true)).compile ()
      (onePublication, initial))).published.map Published.value) = [30] ∧
    ((observeResult ((planned.freeze (fun _ => true)).compile ()
      (onePublication, { initial with store := refineFirst originalStore }))).published.map
        Published.value) = [27] := by decide

/-! ## Higher-order values require no change to the switching law -/

def functionKernel : Kernel Bool (Nat → Nat) where
  Code := Nat
  source index env := fun input => env false (index + input)
  prepared := id
  execute index env := fun input => env false (input + index)
  correct index env := by funext input; simp [Nat.add_comm]

def functionState : TreeState Bool (Nat → Nat) :=
  ⟨(fun key _ input => key.generation + input), [⟨recycledKey, 3, 4⟩], []⟩

theorem higher_order_value_survives_switch :
    ((decode (indexedStep functionKernel (encode functionState))).published.map
      (fun answer => answer.value 10)) = [15] := by decide

/-! ## Failed admission does not consume the residual -/

def admittedEnter (compiledRevision liveRevision : Nat) :
    GuardedTransfer (fun state : TreeState Bool Nat => state) decode where
  attempt state := if compiledRevision = liveRevision then some (encode state) else none
  correct state converted accepted := by
    split at accepted
    · cases accepted
      exact decode_encode state
    · contradiction

theorem stale_admission_keeps_frontier :
    (admittedEnter 4 5).choose initial = .inl initial := rfl

theorem fresh_admission_preserves_frontier :
    (admittedEnter 4 4).attempt initial = some (encode initial) ∧
      decode (encode initial) = initial := ⟨rfl, decode_encode _⟩

#print axioms repeated_switches_exact
#print axioms scoped_trace
#print axioms restarting_replays
#print axioms both_work_plans_preserve_residuals
#print axioms irrelevant_declaration_does_not_invalidate

end Mettapedia.GSLT.Dynamics.RepresentationSwitchingControls
