import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeNormalizationScope

/-!
# Explicit postorder normalization and retained continuations

The worklist evaluates every child, including a computed operator, before
dispatching the rebuilt node. Expressions shorter than two are opaque and
primitive results are returned without a second normalization pass. These
are the source traversal conditions of the native type normalizer.

The recursive specification and the one-step worklist are independent.
The proof keeps arbitrary pending parent frames and proves termination by
unvisited input work, not by the size of values returned by primitives.
Partial execution retains the exact remaining normalization. The transition
count is administrative; allocator failure, pointer reuse, array capacity,
and the primitive implementations are not identified with this model.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeNormalizationWorklist

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open InertTypeDependencies (normalize normalizeList normalizeHead)
open TypeNormalizationScope (Primitive)

structure Frame where
  doneRev : List Atom
  todo : List Atom
  deriving DecidableEq

inductive State where
  | visit (atom : Atom) (parents : List Frame)
  | deliver (value : Atom) (parents : List Frame)
  | finished (value : Atom)
  deriving DecidableEq

def step (active : String → Bool) (primitive : Primitive) : State → State
  | .visit (.expression (first :: second :: rest)) parents =>
      .visit first (⟨[], second :: rest⟩ :: parents)
  | .visit atom parents => .deliver atom parents
  | .deliver value (⟨doneRev, next :: todo⟩ :: parents) =>
      .visit next (⟨value :: doneRev, todo⟩ :: parents)
  | .deliver value (⟨doneRev, []⟩ :: parents) =>
      .deliver (normalizeHead active primitive (.expression (value :: doneRev).reverse)) parents
  | .deliver value [] => .finished value
  | .finished value => .finished value

def run (active : String → Bool) (primitive : Primitive) : Nat → State → State
  | 0, state => state
  | fuel + 1, state => run active primitive fuel (step active primitive state)

/-- Interpret pending parents without executing the stack machine. -/
def finish (active : String → Bool) (primitive : Primitive) (value : Atom) : List Frame → Atom
  | [] => value
  | frame :: parents =>
      finish active primitive
        (normalizeHead active primitive (.expression
          (frame.doneRev.reverse ++ value :: normalizeList active primitive frame.todo))) parents

def observation (active : String → Bool) (primitive : Primitive) : State → Atom
  | .visit atom parents => finish active primitive (normalize active primitive atom) parents
  | .deliver value parents => finish active primitive value parents
  | .finished value => value

theorem step_observation (active : String → Bool) (primitive : Primitive) (state : State) :
    observation active primitive (step active primitive state) =
      observation active primitive state := by
  cases state with
  | visit atom parents =>
      cases atom with
      | symbol _ | var _ | grounded _ => rfl
      | expression children =>
          cases children with
          | nil => rfl
          | cons first rest =>
              cases rest with
              | nil => rfl
              | cons second rest =>
                  simp [step, observation, finish, InertTypeDependencies.normalize, normalizeList]
  | deliver value parents =>
      cases parents with
      | nil => rfl
      | cons frame parents =>
          cases frame with
          | mk doneRev todo =>
              cases todo <;>
                simp [step, observation, finish, normalizeList, List.reverse_cons,
                  List.append_assoc]
  | finished _ => rfl

theorem run_observation (active : String → Bool) (primitive : Primitive)
    (fuel : Nat) (state : State) :
    observation active primitive (run active primitive fuel state) =
      observation active primitive state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih => rw [run, ih, step_observation]

theorem run_add (active : String → Bool) (primitive : Primitive)
    (first second : Nat) (state : State) :
    run active primitive (first + second) state =
      run active primitive second (run active primitive first state) := by
  induction first generalizing state with
  | zero => simp [run]
  | succ first ih => simpa only [Nat.succ_add, run] using ih (step active primitive state)

mutual
def work : Atom → Nat
  | .expression (first :: second :: rest) => 1 + workList (first :: second :: rest)
  | _ => 1
def workList : List Atom → Nat
  | [] => 0
  | atom :: atoms => work atom + 1 + workList atoms
end

def parentWork : List Frame → Nat
  | [] => 1
  | frame :: parents => 1 + workList frame.todo + parentWork parents

def remaining : State → Nat
  | .visit atom parents => work atom + parentWork parents
  | .deliver _ parents => parentWork parents
  | .finished _ => 0

theorem parentWork_pos (parents : List Frame) : 0 < parentWork parents := by
  cases parents <;> simp [parentWork]

theorem remaining_zero (state : State) : remaining state = 0 ↔ ∃ value, state = .finished value := by
  cases state with
  | visit atom parents =>
      have positive := parentWork_pos parents
      constructor
      · intro zero
        simp only [remaining] at zero
        omega
      · rintro ⟨value, impossible⟩
        cases impossible
  | deliver value parents =>
      have positive := parentWork_pos parents
      constructor
      · intro zero
        simp only [remaining] at zero
        omega
      · rintro ⟨value, impossible⟩
        cases impossible
  | finished value => simp [remaining]

theorem step_remaining (active : String → Bool) (primitive : Primitive)
    (state : State) (unfinished : remaining state ≠ 0) :
    remaining (step active primitive state) + 1 = remaining state := by
  cases state with
  | visit atom parents =>
      cases atom with
      | symbol _ | var _ | grounded _ => simp [step, remaining, work, Nat.add_comm]
      | expression children =>
          cases children with
          | nil => simp [step, remaining, work, Nat.add_comm]
          | cons first rest =>
              cases rest with
              | nil => simp [step, remaining, work, Nat.add_comm]
              | cons second rest =>
                  simp [step, remaining, work, workList, parentWork]
                  omega
  | deliver value parents =>
      cases parents with
      | nil => rfl
      | cons frame parents =>
          cases frame with
          | mk doneRev todo =>
              cases todo <;> simp [step, remaining, parentWork, workList] <;> omega
  | finished value => exact False.elim (unfinished rfl)

theorem finished_run (active : String → Bool) (primitive : Primitive)
    (fuel : Nat) (value : Atom) :
    run active primitive fuel (.finished value) = .finished value := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => exact ih

theorem run_remaining (active : String → Bool) (primitive : Primitive)
    (fuel : Nat) (state : State) :
    remaining (run active primitive fuel state) = remaining state - fuel := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      by_cases done : remaining state = 0
      · obtain ⟨value, rfl⟩ := (remaining_zero state).mp done
        simp [finished_run, remaining]
      · have reduced := step_remaining active primitive state done
        rw [run, ih]
        omega

theorem run_finishes (active : String → Bool) (primitive : Primitive)
    (fuel : Nat) (state : State) (enough : remaining state ≤ fuel) :
    ∃ value, run active primitive fuel state = .finished value := by
  induction fuel generalizing state with
  | zero =>
      obtain ⟨value, rfl⟩ := (remaining_zero state).mp (by omega)
      exact ⟨value, rfl⟩
  | succ fuel ih =>
      by_cases done : remaining state = 0
      · obtain ⟨value, rfl⟩ := (remaining_zero state).mp done
        exact ⟨value, finished_run active primitive _ value⟩
      · have reduced := step_remaining active primitive state done
        exact ih (step active primitive state) (by omega)

/-- The worklist implements the recursive specification with an explicit
input-dependent bound, for arbitrary primitive result sizes. -/
theorem run_exact (active : String → Bool) (primitive : Primitive)
    (fuel : Nat) (state : State) (enough : remaining state ≤ fuel) :
    run active primitive fuel state = .finished (observation active primitive state) := by
  obtain ⟨value, done⟩ := run_finishes active primitive fuel state enough
  have sound := run_observation active primitive fuel state
  rw [done] at sound
  change value = observation active primitive state at sound
  simpa [sound] using done

theorem normalize_worklist (active : String → Bool) (primitive : Primitive) (atom : Atom) :
    run active primitive (work atom + 1) (.visit atom []) =
      .finished (normalize active primitive atom) :=
  run_exact active primitive _ _ (Nat.le_refl _)

/-- Stopping a run retains the same result obligation. Resuming its saved
state, rather than restarting its input, finishes the remaining work. -/
theorem residual_exact (active : String → Bool) (primitive : Primitive)
    (budget : Nat) (state : State) :
    let saved := run active primitive budget state
    run active primitive (remaining saved) saved =
      .finished (observation active primitive state) := by
  dsimp only
  rw [run_exact active primitive _ _ (Nat.le_refl _), run_observation]

/-- An insufficient administrative budget is an unfinished state, not an
empty or failed normalization result. -/
theorem incomplete_iff (active : String → Bool) (primitive : Primitive)
    (fuel : Nat) (state : State) :
    (¬ ∃ value, run active primitive fuel state = .finished value) ↔ fuel < remaining state := by
  rw [← remaining_zero, run_remaining]
  omega

mutual
def visitedNodes : Atom → Nat
  | .expression (first :: second :: rest) => 1 + visitedNodesList (first :: second :: rest)
  | _ => 1
def visitedNodesList : List Atom → Nat
  | [] => 0
  | atom :: atoms => visitedNodes atom + visitedNodesList atoms
end

mutual
theorem work_eq_nodes : ∀ atom, work atom + 1 = 2 * visitedNodes atom
  | .symbol _ => rfl
  | .var _ => rfl
  | .grounded _ => rfl
  | .expression [] => rfl
  | .expression [_] => rfl
  | .expression (first :: second :: rest) => by
      rw [work, visitedNodes, workList_eq_nodes]
      omega
theorem workList_eq_nodes : ∀ atoms, workList atoms = 2 * visitedNodesList atoms
  | [] => rfl
  | atom :: atoms => by
      rw [workList, visitedNodesList, work_eq_nodes, workList_eq_nodes]
      omega
end

/-- Exactly two administrative transitions per visited occurrence. Opaque
singleton expressions count as one node; primitive-internal work is absent. -/
theorem source_cost_exact (active : String → Bool) (primitive : Primitive)
    (atom : Atom) (fuel : Nat) :
    remaining (run active primitive fuel (.visit atom [])) = 2 * visitedNodes atom - fuel := by
  rw [run_remaining]
  simp only [remaining, parentWork, work_eq_nodes]

theorem resource_free_worklist (active : String → Bool) (primitive : Primitive)
    (closed : TypeNormalizationScope.ResultsClosed active primitive)
    (first second : RetainedTypePayloads.ExternalView) (atom : Atom)
    (safe : TypeDependencyAdmission.resourceFree atom = true) :
    run active (TypeNormalizationScope.observed first primitive) (work atom + 1) (.visit atom []) =
      run active (TypeNormalizationScope.observed second primitive) (work atom + 1) (.visit atom []) := by
  rw [normalize_worklist, normalize_worklist,
    TypeNormalizationScope.normalize_world active first second primitive closed atom safe]

open TypeDependencyAdmission (resourceFree resourceFreeList)

def safeParents : List Frame → Prop
  | [] => True
  | frame :: parents => resourceFreeList frame.doneRev = true ∧
      resourceFreeList frame.todo = true ∧ safeParents parents

def Safe : State → Prop
  | .visit atom parents | .deliver atom parents => resourceFree atom = true ∧ safeParents parents
  | .finished atom => resourceFree atom = true

theorem safe_rebuilt (value : Atom) (doneRev : List Atom)
    (valueSafe : resourceFree value = true) (doneSafe : resourceFreeList doneRev = true) :
    resourceFree (.expression (value :: doneRev).reverse) = true := by
  apply (TypeDependencyAdmission.resourceFreeList_iff _).mpr
  intro atom member
  have before := List.mem_reverse.mp member
  rcases List.mem_cons.mp before with rfl | later
  · exact valueSafe
  · exact (TypeDependencyAdmission.resourceFreeList_iff _).mp doneSafe atom later

theorem step_safe (active : String → Bool) (primitive : Primitive)
    (closed : TypeNormalizationScope.ResultsClosed active primitive)
    (state : State) (safe : Safe state) : Safe (step active primitive state) := by
  cases state with
  | visit atom parents =>
      cases atom with
      | symbol _ | var _ | grounded _ => exact safe
      | expression children =>
          cases children with
          | nil => exact safe
          | cons first rest =>
              cases rest with
              | nil => exact safe
              | cons second rest =>
                  simpa [step, Safe, safeParents, resourceFree, resourceFreeList,
                    and_assoc] using safe
  | deliver value parents =>
      cases parents with
      | nil => exact safe.1
      | cons frame parents =>
          cases frame with
          | mk doneRev todo =>
              rcases safe with ⟨valueSafe, doneSafe, todoSafe, parentsSafe⟩
              cases todo with
              | nil =>
                  exact ⟨TypeNormalizationScope.head_preserves active primitive closed _
                    (safe_rebuilt value doneRev valueSafe doneSafe), parentsSafe⟩
              | cons next todo =>
                  simp only [resourceFreeList, Bool.and_eq_true] at todoSafe
                  exact ⟨todoSafe.1, Bool.and_eq_true_iff.mpr ⟨valueSafe, doneSafe⟩,
                    todoSafe.2, parentsSafe⟩
  | finished _ => exact safe

theorem step_world (active : String → Bool) (primitive : Primitive)
    (first second : RetainedTypePayloads.ExternalView) (state : State) (safe : Safe state) :
    step active (TypeNormalizationScope.observed first primitive) state =
      step active (TypeNormalizationScope.observed second primitive) state := by
  cases state with
  | visit atom parents =>
      cases atom with
      | symbol _ | var _ | grounded _ => rfl
      | expression children => cases children with
          | nil => rfl
          | cons first rest => cases rest <;> rfl
  | deliver value parents =>
      cases parents with
      | nil => rfl
      | cons frame parents =>
          cases frame with
          | mk doneRev todo =>
              cases todo with
              | nil =>
                  rw [step, step, TypeNormalizationScope.head_world active first second primitive _
                    (safe_rebuilt value doneRev safe.1 safe.2.1)]
              | cons _ _ => rfl
  | finished _ => rfl

/-- External state may change between administrative steps. The pending
operand packet is retained; type dependencies are not reread as fresh input. -/
def runWorlds (active : String → Bool) (primitive : Primitive) :
    List RetainedTypePayloads.ExternalView → State → State
  | [], state => state
  | world :: worlds, state =>
      runWorlds active primitive worlds (step active (TypeNormalizationScope.observed world primitive) state)

theorem changing_worlds_exact (active : String → Bool) (primitive : Primitive)
    (closed : TypeNormalizationScope.ResultsClosed active primitive)
    (fixed : RetainedTypePayloads.ExternalView) (worlds : List RetainedTypePayloads.ExternalView)
    (state : State) (safe : Safe state) :
    runWorlds active primitive worlds state =
      run active (TypeNormalizationScope.observed fixed primitive) worlds.length state := by
  induction worlds generalizing state with
  | nil => rfl
  | cons world worlds ih =>
      rw [runWorlds, step_world active primitive world fixed state safe,
        ih _ (step_safe active _
          (TypeNormalizationScope.observed_closed active fixed primitive closed) state safe)]
      rfl

namespace Controls

def subtract : Primitive
  | "-", [.grounded (.int left), .grounded (.int right)] => some (.grounded (.int (left - right)))
  | _, _ => none

def ordered : Atom := .expression [.symbol "-", .grounded (.int 10),
  .expression [.symbol "-", .grounded (.int 4), .grounded (.int 1)]]

theorem postorder_preserves_argument_order :
    run (fun head => head == "-") subtract (work ordered + 1) (.visit ordered []) =
      .finished (.grounded (.int 7)) := by decide

theorem reversed_operands_change_result :
    normalize (fun head => head == "-") subtract ordered ≠
      normalize (fun head => head == "-") subtract
        (.expression [.symbol "-", .expression [.symbol "-", .grounded (.int 4), .grounded (.int 1)],
          .grounded (.int 10)]) := by decide

theorem short_expression_is_opaque :
    run (fun head => head == "-") subtract 2 (.visit (.expression [ordered]) []) =
      .finished (.expression [ordered]) := by decide

def produces_code : Primitive := fun _ _ => some ordered

theorem primitive_result_is_not_reentered :
    run (fun _ => true) produces_code (work ordered + 1) (.visit ordered []) =
      .finished ordered := by decide

def computedOperator : Primitive
  | "pick", [_, _] => some (.symbol "-")
  | head, args => subtract head args

theorem operator_is_normalized_before_dispatch :
    let input := Atom.expression
      [.expression [.symbol "pick", .symbol "left", .symbol "right"],
        .grounded (.int 10), .grounded (.int 3)]
    run (fun _ => true) computedOperator (work input + 1) (.visit input []) =
      .finished (.grounded (.int 7)) := by decide

theorem incomplete_run_is_not_a_result :
    (∃ value, run (fun head => head == "-") subtract 1 (.visit ordered []) = .finished value) = False := by
  simp [run, step, ordered]

theorem resource_world_changes_can_change_normalization :
    let input := TypeNormalizationScope.Controls.mutableExpression
    let initial := RetainedTypePayloads.Controls.initial
    let changed := RetainedTypePayloads.Controls.changed
    let active := fun head => head == "=="
    let primitive := TypeNormalizationScope.Controls.equalOnly
    runWorlds active primitive (List.replicate (work input + 1) initial) (.visit input []) =
        .finished (.grounded (.bool true)) ∧
    runWorlds active primitive (List.replicate (work input + 1) changed) (.visit input []) =
        .finished (.grounded (.bool false)) ∧
    ¬ Safe (.visit input []) := by
  dsimp only
  refine ⟨by decide, by decide, ?_⟩
  simp [Safe, TypeNormalizationScope.Controls.mutableExpression,
    RetainedTypePayloads.Controls.state, resourceFree, resourceFreeList]

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeNormalizationWorklist
