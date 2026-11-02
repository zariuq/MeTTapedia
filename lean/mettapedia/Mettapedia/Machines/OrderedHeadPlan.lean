import Mettapedia.Machines.UnificationWorklist
import Mettapedia.Languages.MeTTa.OSLFCore.Atom

/-!
# Ordered structural head plans

The source inspects ordinary atoms. The target compiles the right operand
into immutable dispatch nodes and traverses their children in source order.
Depth exhaustion retains a direct source node, representing conservative
fallback rather than a failed match. Variable binding and rigid comparison
are opaque services that may change the store, reject, or fault.

The refinement preserves every inspection prefix, the direction of binding,
the ordered residual, and the actual store on failure. It does not license
speculative refutation or evaluate code-shaped data. Alias dereferencing,
occurs checks, native schema coordinates, allocation and pointer lifetime
remain separate correspondence obligations of the service and implementation.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OrderedHeadPlan

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open UnificationWorklist

inductive Plan where
  | direct (source : Atom)
  | symbol (name : String)
  | var (name : String)
  | grounded (value : GroundedValue)
  | expression (children : List Plan)

def compile : Nat → Atom → Plan
  | 0, source => .direct source
  | _ + 1, .symbol name => .symbol name
  | _ + 1, .var name => .var name
  | _ + 1, .grounded value => .grounded value
  | depth + 1, .expression children => .expression (children.map (compile depth))

def decode : Plan → Atom
  | .direct source => source
  | .symbol name => .symbol name
  | .var name => .var name
  | .grounded value => .grounded value
  | .expression children => .expression (children.map decode)

theorem compile_readback (depth : Nat) (source : Atom) :
    decode (compile depth source) = source := by
  induction depth generalizing source with
  | zero => simp [compile, decode]
  | succ depth ih =>
      cases source <;> simp [compile, decode, List.map_map, Function.comp_def, ih]

abbrev Pair := Atom × Atom
abbrev PlannedPair := Atom × Plan

def project (pair : PlannedPair) : Pair := (pair.1, decode pair.2)

inductive Request where
  | bindLeft (name : String) (right : Atom)
  | bindRight (left : Atom) (name : String)
  | rigid (left right : Atom)
  deriving DecidableEq

inductive Action (Store Fault : Type) where
  | accepted (store : Store)
  | rejected (store : Store)
  | fault (error : Fault) (store : Store)

def action {Pair Store Fault : Type} : Action Store Fault → Inspection Pair Store Fault
  | .accepted store => .next store []
  | .rejected store => .failed store
  | .fault error store => .fault error store

variable {Store Fault : Type}

def sourceInspect (service : Request → Store → Action Store Fault)
    (store : Store) (pair : Pair) : Inspection Pair Store Fault :=
  match pair with
  | (.var name, right) => action (service (.bindLeft name right) store)
  | (left, .var name) => action (service (.bindRight left name) store)
  | (.expression left, .expression right) =>
      if left.length = right.length then .next store (left.zip right) else .failed store
  | (left, right) => action (service (.rigid left right) store)

def targetInspect (service : Request → Store → Action Store Fault)
    (store : Store) (pair : PlannedPair) : Inspection PlannedPair Store Fault :=
  match pair with
  | (left, .direct right) =>
      match sourceInspect service store (left, right) with
      | .next later children => .next later (children.map fun (l, r) => (l, .direct r))
      | .failed later => .failed later
      | .fault error later => .fault error later
  | (.var name, right) => action (service (.bindLeft name (decode right)) store)
  | (left, .var name) => action (service (.bindRight left name) store)
  | (.expression left, .expression right) =>
      if left.length = right.length then .next store (left.zip right) else .failed store
  | (left, right) => action (service (.rigid left (decode right)) store)

def projectInspection : Inspection PlannedPair Store Fault → Inspection Pair Store Fault
  | .next store children => .next store (children.map project)
  | .failed store => .failed store
  | .fault error store => .fault error store

theorem zip_readback (left : List Atom) (right : List Plan) :
    (left.zip right).map project = left.zip (right.map decode) := by
  induction left generalizing right with
  | nil => simp
  | cons head tail ih =>
      cases right <;> simp [project, ih]

theorem action_readback (result : Action Store Fault) :
    projectInspection (action result) = action (Pair := Pair) result := by
  cases result <;> rfl

theorem inspect_readback (service : Request → Store → Action Store Fault)
    (store : Store) (pair : PlannedPair) :
    projectInspection (targetInspect service store pair) =
      sourceInspect service store (project pair) := by
  rcases pair with ⟨left, right⟩
  cases right with
  | direct right =>
      simp only [targetInspect, project, decode]
      cases sourceInspect service store (left, right) <;>
        simp [projectInspection, project, decode, List.map_map, Function.comp_def]
  | symbol name => cases left <;> simp [targetInspect, sourceInspect, project,
      decode, action_readback]
  | var name => cases left <;> simp [targetInspect, sourceInspect, project,
      decode, action_readback]
  | grounded value => cases left <;> simp [targetInspect, sourceInspect, project,
      decode, action_readback]
  | expression children =>
      cases left with
      | symbol name => simp [targetInspect, sourceInspect, project, decode, action_readback]
      | var name => simp [targetInspect, sourceInspect, project, decode, action_readback]
      | grounded value => simp [targetInspect, sourceInspect, project, decode, action_readback]
      | expression left =>
          simp only [targetInspect, project, decode, sourceInspect, List.length_map]
          split <;> simp_all [projectInspection, zip_readback]

def projectOutcome : Outcome PlannedPair Store Fault → Outcome Pair Store Fault
  | .complete store => .complete store
  | .failed store => .failed store
  | .fault error store => .fault error store
  | .paused pending store => .paused (pending.map project) store

def projectReceipt (receipt : Receipt PlannedPair Store Fault) : Receipt Pair Store Fault :=
  ⟨projectOutcome receipt.outcome, receipt.inspected.map project,
    receipt.pushes, receipt.pops⟩

theorem run_readback (service : Request → Store → Action Store Fault)
    (allowance : Nat) (pending : List PlannedPair) (store : Store) :
    projectReceipt (stackRun (targetInspect service) allowance pending store) =
      stackRun (sourceInspect service) allowance (pending.map project) store := by
  induction allowance generalizing pending store with
  | zero => cases pending <;> rfl
  | succ allowance ih =>
      cases pending with
      | nil => rfl
      | cons pair pending =>
          have step := inspect_readback service store pair
          cases result : targetInspect service store pair with
          | failed later =>
              simp only [result, projectInspection] at step
              simp [stackRun, result, ← step, projectReceipt, projectOutcome, record, terminal]
          | fault error later =>
              simp only [result, projectInspection] at step
              simp [stackRun, result, ← step, projectReceipt, projectOutcome, record, terminal]
          | next later children =>
              simp only [result, projectInspection] at step
              have recurse := ih (children ++ pending) later
              simp only [projectReceipt] at recurse ⊢
              simp only [stackRun, result, List.map_cons, ← step, record,
                List.map_append, List.length_map] at recurse ⊢
              cases first : stackRun (targetInspect service) allowance (children ++ pending) later
              cases second : stackRun (sourceInspect service) allowance
                  (children.map project ++ pending.map project) later
              simp_all

theorem compiled_run (service : Request → Store → Action Store Fault)
    (depth allowance : Nat) (pending : List Pair) (store : Store) :
    projectReceipt (stackRun (targetInspect service) allowance
      (pending.map fun (left, right) => (left, compile depth right)) store) =
      stackRun (sourceInspect service) allowance pending store := by
  rw [run_readback]
  simp [List.map_map, Function.comp_def, project, compile_readback]

namespace Controls

def service : Request → List Request → Action (List Request) Unit
  | request@(.rigid (.grounded (.int 1)) (.grounded (.int 3))), trace =>
      .rejected (trace ++ [request])
  | request, trace => .accepted (trace ++ [request])

def query : Atom := .expression [.var "probe", .grounded (.int 1)]
def pattern : Atom := .expression [.grounded (.int 2), .grounded (.int 3)]

theorem failure_retains_prefix :
    (stackRun (sourceInspect service) 3 [(query, pattern)] []).outcome =
      .failed [.bindLeft "probe" (.grounded (.int 2)),
        .rigid (.grounded (.int 1)) (.grounded (.int 3))] := by
  rfl

theorem source_direction :
    sourceInspect service [] (.var "query", .var "rule") =
      .next [.bindLeft "query" (.var "rule")] [] := by
  rfl

theorem depth_exhaustion_is_not_failure :
    projectReceipt (stackRun (targetInspect service) 3 [(query, compile 0 pattern)] []) =
      stackRun (sourceInspect service) 3 [(query, pattern)] [] := by
  exact compiled_run service 0 3 [(query, pattern)] []

def reverseInspect (trace : List Request) (pair : Pair) :
    Inspection Pair (List Request) Unit :=
  match sourceInspect service trace pair with
  | .next later children => .next later children.reverse
  | .failed later => .failed later
  | .fault error later => .fault error later

theorem reordered_failure_loses_prefix :
    (stackRun reverseInspect 3 [(query, pattern)] []).outcome =
      .failed [.rigid (.grounded (.int 1)) (.grounded (.int 3))] := by
  rfl

theorem failed_prefix_is_observable :
    (stackRun reverseInspect 3 [(query, pattern)] []).outcome ≠
      (stackRun (sourceInspect service) 3 [(query, pattern)] []).outcome := by
  rw [reordered_failure_loses_prefix, failure_retains_prefix]
  decide

theorem duplicate_requests_are_retained :
    (stackRun (sourceInspect service) 2
      [(.var "query", .grounded (.int 7)), (.var "query", .grounded (.int 7))] []).outcome =
      .complete [.bindLeft "query" (.grounded (.int 7)),
        .bindLeft "query" (.grounded (.int 7))] := by
  rfl

end Controls
end Mettapedia.Machines.OrderedHeadPlan
