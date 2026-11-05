import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CollectedOnceQuerySource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ConstantQuerySource

/-!
# Presence guards at retained source continuations

The authored guard is not (equal (collapse (once query)) empty). Preparation
uses the existing source argument-demand rules and fresh-name allocator.
The intermediate collection is still subject to its generative return
boundary. Boolean readout is justified independently from query search.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.PresenceGuardSource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS (World)
open EagerDFS.Destination
open LiteralQuerySource (Request)
open ClosedOnceQueryFrame (FreshFor placed)

def equality (request : Request) : Atom :=
  .expression [.symbol "==", CollectedOnceQuerySource.source request, .expression []]

def source (request : Request) : Atom := .expression [.symbol "not", equality request]

def start (caller : Control) (destination : Atom) (request : Request) : Control :=
  {caller with goals := .evaluate (source request) destination :: caller.goals}

def notSlot (caller : Control) (destination : Atom) (request : Request) : String :=
  freshName (start caller destination request) 0

def equalityControl (caller : Control) (destination : Atom) (request : Request) : Control :=
  {caller with goals := [
    .evaluate (equality request) (.var (notSlot caller destination request)),
    .invoke "not" [.var (notSlot caller destination request)] destination] ++ caller.goals}

def leftSlot (caller : Control) (destination : Atom) (request : Request) : String :=
  freshName (equalityControl caller destination request) 0

def rightSlot (caller : Control) (destination : Atom) (request : Request) : String :=
  freshName (equalityControl caller destination request) 1

def suffix (caller : Control) (destination : Atom) (request : Request) : List Goal :=
  [.evaluate (.expression []) (.var (rightSlot caller destination request)),
   .invoke "==" [.var (leftSlot caller destination request), .var (rightSlot caller destination request)]
     (.var (notSlot caller destination request)),
   .invoke "not" [.var (notSlot caller destination request)] destination] ++ caller.goals

def collecting (caller : Control) (destination : Atom) (request : Request) : Control :=
  {caller with goals := (.evaluate (CollectedOnceQuerySource.source request)
    (.var (leftSlot caller destination request)) :: suffix caller destination request)}

theorem not_fresh (caller : Control) (destination : Atom) (request : Request) :
    FreshFor (notSlot caller destination request) caller.bindings :=
  ClosedOnceQueryFrame.fresh_for_bindings (start caller destination request) _ (freshName_not_mem _ _)

theorem left_fresh (caller : Control) (destination : Atom) (request : Request) :
    FreshFor (leftSlot caller destination request) caller.bindings :=
  ClosedOnceQueryFrame.fresh_for_bindings (equalityControl caller destination request) _ (freshName_not_mem _ _)

theorem right_fresh (caller : Control) (destination : Atom) (request : Request) :
    FreshFor (rightSlot caller destination request) caller.bindings :=
  ClosedOnceQueryFrame.fresh_for_bindings (equalityControl caller destination request) _ (freshName_not_mem _ _)

theorem not_in_equality_support (caller : Control) (destination : Atom) (request : Request) :
    notSlot caller destination request ∈ (equalityControl caller destination request).support := by
  apply Finset.mem_union_right
  apply (ClosedOnceQueryFrame.fold_support_iff _ _ _).mpr
  right
  refine ⟨.var (notSlot caller destination request), ?_, ?_⟩
  · simp [equalityControl, Goal.atoms]
  · simp [encode, Mettapedia.Logic.LP.Term.freeVars]

theorem not_ne_left (caller : Control) (destination : Atom) (request : Request) :
    notSlot caller destination request ≠ leftSlot caller destination request := by
  intro same
  have present := not_in_equality_support caller destination request
  rw [same] at present
  exact freshName_not_mem (equalityControl caller destination request) 0 present

theorem not_ne_right (caller : Control) (destination : Atom) (request : Request) :
    notSlot caller destination request ≠ rightSlot caller destination request := by
  intro same
  have present := not_in_equality_support caller destination request
  rw [same] at present
  exact freshName_not_mem (equalityControl caller destination request) 1 present

theorem left_ne_right (caller : Control) (destination : Atom) (request : Request) :
    leftSlot caller destination request ≠ rightSlot caller destination request := by
  intro same
  have impossible := freshName_injective (equalityControl caller destination request) same
  contradiction

set_option maxHeartbeats 1000000 in
theorem source_to_collection {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (caller : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (destination : Atom) (request : Request) :
    (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).run 2
      (placed allocator world scope parents (start caller destination request) context origins pending) =
      ([], .exhausted (placed allocator world scope parents (collecting caller destination request) context origins pending)) := by
  simp [Machine.run, EagerDFSStreaming.machine, placed, start, source, equality,
    scopeStep, enterCollapse?, enterSuperpose?, EagerDFS.Destination.machine, prepare, replace,
    installChild, retainChild, callable, StdLib.known, Eval.ioHead,
    callArguments, freshSlots, List.range_succ, Eval.argumentIsRaw, StdLib.rawArgument,
    collecting, suffix, notSlot, leftSlot, rightSlot, equalityControl]

def tuple (request : Request) (present : Bool) : Atom := .expression (if present then [request.payload] else [])

theorem tuple_read (request : Request) (present : Bool) (environment : Environment) :
    EagerDFS.Destination.read environment (tuple request present) = tuple request present := by
  rcases request with ⟨handle, pattern, literal, payload, scalar, ordinary⟩
  cases scalar <;> cases present <;> simp [tuple, EagerDFS.Destination.read, encode, decode, List.ofFn_succ]

theorem tuple_freeVars (request : Request) (present : Bool) : (encode (tuple request present)).freeVars = ∅ := by
  cases present <;> simp [tuple, encode, Mettapedia.Logic.LP.Term.freeVars, request.scalar.freeVars]

theorem empty_read (environment : Environment) :
    EagerDFS.Destination.read environment (.expression []) = .expression [] := by
  simp [EagerDFS.Destination.read, encode, decode]

theorem equality_readout (state : Effects.State) (request : Request) (present : Bool) :
    StdLib.apply state "==" [tuple request present, .expression []] = .ok (state, [Effects.boolean (!present)]) := by
  cases present <;> rfl

theorem negation_readout (state : Effects.State) (present : Bool) :
    StdLib.apply state "not" [Effects.boolean (!present)] = .ok (state, [Effects.boolean present]) := by
  cases present <;> rfl

theorem read_boolean (value : Bool) (environment : Environment) :
    EagerDFS.Destination.read environment (Effects.boolean value) = Effects.boolean value := by
  simp [EagerDFS.Destination.read, Effects.boolean, encode, decode]

theorem fresh_append_closed (bindings : Equations) (name bound : String) (value : Atom)
    (fresh : FreshFor name bindings) (different : name ≠ bound)
    (closed : (encode value).freeVars = ∅) :
    FreshFor name (bindings ++ [(value, .var bound)]) := by
  intro pair member
  rcases List.mem_append.mp member with old | added
  · exact fresh pair old
  · have same := List.mem_singleton.mp added
    subst pair
    simpa [closed, encode, Mettapedia.Logic.LP.Term.freeVars] using different

def tupleBindings (caller : Control) (destination : Atom) (request : Request) (present : Bool) : Equations :=
  caller.bindings ++ [(tuple request present, .var (leftSlot caller destination request))]

def emptyBindings (caller : Control) (destination : Atom) (request : Request) (present : Bool) : Equations :=
  tupleBindings caller destination request present ++ [(.expression [], .var (rightSlot caller destination request))]

def comparisonBindings (caller : Control) (destination : Atom) (request : Request) (present : Bool) : Equations :=
  emptyBindings caller destination request present ++ [(Effects.boolean (!present), .var (notSlot caller destination request))]

/-- Guard-local slots avoid the retained result destination. An actually
fresh result therefore stays fresh through either Boolean readout case. -/
theorem comparison_fresh (caller : Control) (result : String) (request : Request) (present : Bool)
    (fresh : FreshFor result caller.bindings) :
    FreshFor result (comparisonBindings caller (.var result) request present) := by
  have supported (control : Control) (used : .var result ∈ control.goals.flatMap Goal.atoms) :
      result ∈ control.support := by
    apply Finset.mem_union_right
    apply (ClosedOnceQueryFrame.fold_support_iff _ _ result).mpr
    exact Or.inr ⟨.var result, List.mem_cons_of_mem _ (List.mem_append_right _ used),
      by simp [encode, Mettapedia.Logic.LP.Term.freeVars]⟩
  have apart (control : Control) (index : Nat) (used : result ∈ control.support) :
      result ≠ freshName control index := by
    intro same
    apply freshName_not_mem control index
    rw [← same]
    exact used
  have first := supported (start caller (.var result) request) (by simp [start, Goal.atoms])
  have later := supported (equalityControl caller (.var result) request) (by simp [equalityControl, Goal.atoms])
  apply fresh_append_closed
  · apply fresh_append_closed
    · apply fresh_append_closed
      · exact fresh
      · exact apart _ 0 later
      · exact tuple_freeVars request present
    · exact apart _ 1 later
    · simp [encode, Mettapedia.Logic.LP.Term.freeVars]
  · exact apart _ 0 first
  · simp [Effects.boolean, encode, Mettapedia.Logic.LP.Term.freeVars]

theorem tuple_refined (caller : Control) (destination : Atom) (request : Request) (present : Bool)
    (consistent : ∃ environment, Solves environment caller.bindings) :
    refine caller.bindings (tuple request present) (.var (leftSlot caller destination request)) =
      some (tupleBindings caller destination request present) :=
  ClosedOnceQueryFrame.refine_fresh_closed _ _ _ (left_fresh caller destination request)
    consistent (tuple_read request present)

theorem empty_refined (caller : Control) (destination : Atom) (request : Request) (present : Bool)
    (consistent : ∃ environment, Solves environment caller.bindings) :
    refine (tupleBindings caller destination request present) (.expression []) (.var (rightSlot caller destination request)) =
      some (emptyBindings caller destination request present) := by
  apply ClosedOnceQueryFrame.refine_fresh_closed
  · exact fresh_append_closed _ _ _ _ (right_fresh caller destination request)
      (left_ne_right caller destination request).symm (tuple_freeVars request present)
  · exact ClosedOnceQueryFrame.refined_consistent _ _ _ (tuple_refined caller destination request present consistent)
  · exact empty_read

theorem comparison_refined (caller : Control) (destination : Atom) (request : Request) (present : Bool)
    (consistent : ∃ environment, Solves environment caller.bindings) :
    refine (emptyBindings caller destination request present) (Effects.boolean (!present)) (.var (notSlot caller destination request)) =
      some (comparisonBindings caller destination request present) := by
  apply ClosedOnceQueryFrame.refine_fresh_closed
  · apply fresh_append_closed
    · exact fresh_append_closed _ _ _ _ (not_fresh caller destination request)
        (not_ne_left caller destination request) (tuple_freeVars request present)
    · exact not_ne_right caller destination request
    · decide +kernel
  · exact ClosedOnceQueryFrame.refined_consistent _ _ _ (empty_refined caller destination request present consistent)
  · exact read_boolean _

theorem bound_closed_value (bindings : Equations) (value : Atom) (name : String)
    (environment : Environment) (resolved : resolve bindings = some environment)
    (member : (value, .var name) ∈ bindings)
    (closed : EagerDFS.Destination.read environment value = value) :
    EagerDFS.Destination.read environment (.var name) = value := by
  rw [← resolve_sound resolved (value, .var name) member, closed]

theorem comparison_arguments (caller : Control) (destination : Atom) (request : Request) (present : Bool)
    (environment : Environment) (resolved : resolve (emptyBindings caller destination request present) = some environment) :
    [.var (leftSlot caller destination request), .var (rightSlot caller destination request)].map
      (EagerDFS.Destination.read environment) = [tuple request present, .expression []] := by
  have left := bound_closed_value _ (tuple request present) (leftSlot caller destination request) environment resolved
    (by simp [emptyBindings, tupleBindings]) (tuple_read request present environment)
  have right := bound_closed_value _ (.expression []) (rightSlot caller destination request) environment resolved
    (by simp [emptyBindings]) (empty_read environment)
  simp only [List.map_cons, List.map_nil, left, right]

theorem negation_argument (caller : Control) (destination : Atom) (request : Request) (present : Bool)
    (environment : Environment) (resolved : resolve (comparisonBindings caller destination request present) = some environment) :
    [.var (notSlot caller destination request)].map (EagerDFS.Destination.read environment) =
      [Effects.boolean (!present)] := by
  have value := bound_closed_value _ (Effects.boolean (!present)) (notSlot caller destination request) environment resolved
    (by simp [comparisonBindings]) (read_boolean _ environment)
  simp only [List.map_cons, List.map_nil, value]

def afterCopy (caller : Control) (destination : Atom) (request : Request) (present : Bool) : Control :=
  {caller with goals := .equate (tuple request present) (.var (leftSlot caller destination request)) :: suffix caller destination request}

def afterTuple (caller : Control) (destination : Atom) (request : Request) (present : Bool) : Control :=
  {caller with
    bindings := tupleBindings caller destination request present
    goals := suffix caller destination request}

def emptyPrepared (caller : Control) (destination : Atom) (request : Request) (present : Bool) : Control :=
  {caller with
    bindings := tupleBindings caller destination request present
    goals := [.equate (.expression []) (.var (rightSlot caller destination request)),
      .invoke "==" [.var (leftSlot caller destination request), .var (rightSlot caller destination request)]
        (.var (notSlot caller destination request)),
      .invoke "not" [.var (notSlot caller destination request)] destination] ++ caller.goals}

def beforeEquality (caller : Control) (destination : Atom) (request : Request) (present : Bool) : Control :=
  {caller with
    bindings := emptyBindings caller destination request present
    goals := [.invoke "==" [.var (leftSlot caller destination request), .var (rightSlot caller destination request)]
      (.var (notSlot caller destination request)), .invoke "not" [.var (notSlot caller destination request)] destination] ++ caller.goals}

def equalityReturned (caller : Control) (destination : Atom) (request : Request) (present : Bool) : Control :=
  {caller with
    bindings := emptyBindings caller destination request present
    goals := [.equate (Effects.boolean (!present)) (.var (notSlot caller destination request)),
      .invoke "not" [.var (notSlot caller destination request)] destination] ++ caller.goals}

def beforeNegation (caller : Control) (destination : Atom) (request : Request) (present : Bool) : Control :=
  {caller with
    bindings := comparisonBindings caller destination request present
    goals := .invoke "not" [.var (notSlot caller destination request)] destination :: caller.goals}

def delivered (caller : Control) (destination : Atom) (request : Request) (present : Bool) : Control :=
  {caller with
    bindings := comparisonBindings caller destination request present
    goals := .equate (Effects.boolean present) destination :: caller.goals}

set_option maxHeartbeats 1200000 in
theorem readout_prefix {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (caller : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (destination : Atom) (request : Request)
    (present : Bool) (consistent : ∃ environment, Solves environment caller.bindings) :
    (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).run 6
      (placed allocator world scope parents (afterCopy caller destination request present) context origins pending) =
      ([], .exhausted (placed allocator world scope parents (delivered caller destination request present)
        context (origins ++ [0, 0]) pending)) := by
  obtain ⟨equalEnvironment, equalResolved⟩ := resolve_complete
    (ClosedOnceQueryFrame.refined_consistent _ _ _ (empty_refined caller destination request present consistent))
  obtain ⟨notEnvironment, notResolved⟩ := resolve_complete
    (ClosedOnceQueryFrame.refined_consistent _ _ _ (comparison_refined caller destination request present consistent))
  let s0 := placed allocator world scope parents (afterCopy caller destination request present) context origins pending
  let s1 := placed allocator world scope parents (afterTuple caller destination request present) context origins pending
  let s2 := placed allocator world scope parents (emptyPrepared caller destination request present) context origins pending
  let s3 := placed allocator world scope parents (beforeEquality caller destination request present) context origins pending
  let s4 := placed allocator world scope parents (equalityReturned caller destination request present) context (origins ++ [0]) pending
  let s5 := placed allocator world scope parents (beforeNegation caller destination request present) context (origins ++ [0]) pending
  let s6 := placed allocator world scope parents (delivered caller destination request present) context (origins ++ [0, 0]) pending
  have step1 : scopeStep .relational program s0 = .silent s1 := by
    simp [s0, s1, placed, afterCopy, afterTuple, scopeStep, enterCollapse?, enterSuperpose?,
      EagerDFS.Destination.machine, tuple_refined caller destination request present consistent,
      installChild, retainChild]
  have step2 : scopeStep .relational program s1 = .silent s2 := by
    simp [s1, s2, placed, afterTuple, emptyPrepared, suffix, scopeStep, enterCollapse?, enterSuperpose?,
      EagerDFS.Destination.machine, prepare, replace, dataGoals, freshSlots, installChild, retainChild]
  have step3 : scopeStep .relational program s2 = .silent s3 := by
    simp [s2, s3, placed, emptyPrepared, beforeEquality, scopeStep, enterCollapse?, enterSuperpose?,
      EagerDFS.Destination.machine, empty_refined caller destination request present consistent,
      installChild, retainChild]
  have equalityApplied : StdLib.apply world.state "=="
      ([.var (leftSlot caller destination request), .var (rightSlot caller destination request)].map
        (EagerDFS.Destination.read equalEnvironment)) = .ok (world.state, [Effects.boolean (!present)]) := by
    rw [comparison_arguments caller destination request present equalEnvironment equalResolved,
      equality_readout]
  have step4 : scopeStep .relational program s3 = .silent s4 := by
    have actual := scope_primitive_success .relational program allocator world
      {scope with frontier := (beforeEquality caller destination request present, context, origins) :: pending}
      parents (beforeEquality caller destination request present) context origins pending "=="
      [.var (leftSlot caller destination request), .var (rightSlot caller destination request)]
      (.var (notSlot caller destination request))
      (.invoke "not" [.var (notSlot caller destination request)] destination :: caller.goals)
      equalEnvironment world.state [Effects.boolean (!present)] rfl rfl equalResolved (by decide) (by decide) equalityApplied
    simpa [s3, s4, placed, beforeEquality, equalityReturned, primitiveWork] using actual
  have step5 : scopeStep .relational program s4 = .silent s5 := by
    simp [s4, s5, placed, equalityReturned, beforeNegation, scopeStep, enterCollapse?, enterSuperpose?,
      EagerDFS.Destination.machine, comparison_refined caller destination request present consistent,
      installChild, retainChild]
  have negationApplied : StdLib.apply world.state "not"
      ([.var (notSlot caller destination request)].map (EagerDFS.Destination.read notEnvironment)) =
      .ok (world.state, [Effects.boolean present]) := by
    rw [negation_argument caller destination request present notEnvironment notResolved, negation_readout]
  have step6 : scopeStep .relational program s5 = .silent s6 := by
    have actual := scope_primitive_success .relational program allocator world
      {scope with frontier := (beforeNegation caller destination request present, context, origins ++ [0]) :: pending}
      parents (beforeNegation caller destination request present) context (origins ++ [0]) pending "not"
      [.var (notSlot caller destination request)] destination caller.goals
      notEnvironment world.state [Effects.boolean present] rfl rfl notResolved (by decide) (by decide) negationApplied
    simpa [s5, s6, placed, beforeNegation, delivered, primitiveWork, List.append_assoc] using actual
  have machine1 : (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).step s0 = some (.silent s1) := by
    rw [EagerDFSStreaming.Scoped.step_scope, step1]
  have machine2 : (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).step s1 = some (.silent s2) := by
    rw [EagerDFSStreaming.Scoped.step_scope, step2]
  have machine3 : (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).step s2 = some (.silent s3) := by
    rw [EagerDFSStreaming.Scoped.step_scope, step3]
  have machine4 : (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).step s3 = some (.silent s4) := by
    rw [EagerDFSStreaming.Scoped.step_scope, step4]
  have machine5 : (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).step s4 = some (.silent s5) := by
    rw [EagerDFSStreaming.Scoped.step_scope, step5]
  have machine6 : (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).step s5 = some (.silent s6) := by
    rw [EagerDFSStreaming.Scoped.step_scope, step6]
  change (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).run 6 s0 = ([], .exhausted s6)
  rw [Machine.run_succ_silent _ machine1, Machine.run_succ_silent _ machine2,
    Machine.run_succ_silent _ machine3, Machine.run_succ_silent _ machine4,
    Machine.run_succ_silent _ machine5, Machine.run_succ_silent _ machine6]
  rfl

def collectionScope {Context : Type} (scope : CollectionScope Context) (caller : Control)
    (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (destination : Atom) (request : Request) : CollectionScope Context :=
  {scope with frontier := (collecting caller destination request, context, origins) :: pending}

def collectionEnd {Context : Type} (allocator : Allocator) (world : World)
    (scope : CollectionScope Context) (parents : List (CollectionScope Context)) (caller : Control)
    (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (destination : Atom) (request : Request) (present : Bool) : ScopedCursor Context :=
  CollectedOnceQuerySource.completed allocator world
    (collectionScope scope caller context origins pending destination request) parents
    (collecting caller destination request) context origins pending
    (.var (leftSlot caller destination request)) (suffix caller destination request) request present

def copyAllocator (allocator : Allocator) (present : Bool) : Option Allocator :=
  if present then (EagerDFS.Collection.allocateAnswer? allocator).map Prod.fst else some allocator

set_option maxHeartbeats 1000000 in
theorem finish_collectionEnd {Context : Type} (allocator : Allocator) (world : World)
    (scope : CollectionScope Context) (parents : List (CollectionScope Context)) (caller : Control)
    (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (destination : Atom) (request : Request) (present : Bool) :
    finishAllocated? (collectionEnd allocator world scope parents caller context origins pending destination request present) =
      (copyAllocator allocator present).map (fun next =>
        placed next world scope parents (afterCopy caller destination request present) context origins pending) := by
  cases present with
  | false => rfl
  | true =>
      have allocation := request.scalar.allocateCopy allocator
      have copiedValue := request.scalar.copy
      cases allocated : EagerDFS.Collection.allocateAnswer? allocator with
      | none =>
          simp [collectionEnd, CollectedOnceQuerySource.completed, finishAllocated?, ClosedOnceQueryFrame.answer,
            EagerDFS.Collection.copyOwnedAnswers?, allocation, allocated, copyAllocator]
      | some result =>
          rcases result with ⟨next, token⟩
          simp [collectionEnd, CollectedOnceQuerySource.completed, finishAllocated?, ClosedOnceQueryFrame.answer,
            EagerDFS.Collection.copyOwnedAnswers?, allocation, allocated, copyAllocator,
            copiedValue, allocatedWork, CollectedOnceQuerySource.caller, collectionScope,
            placed, collecting, afterCopy, tuple]

theorem source_to_return_boundary {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (caller : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (destination : Atom) (request : Request)
    (consistent : ∃ environment, Solves environment caller.bindings)
    (rows : List Atom) (snapshot : world.state.read request.handle = some rows) :
    let present := decide (request.pattern ∈ rows)
    (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).run
      (CollectedOnceQuerySource.childBudget present + 4)
      (placed allocator world scope parents (start caller destination request) context origins pending) =
      ([], match copyAllocator allocator present with
        | some next => .exhausted (placed next world scope parents (afterCopy caller destination request present) context origins pending)
        | none => .suspended .allocation
            (collectionEnd allocator world scope parents caller context origins pending destination request present)) := by
  dsimp only
  have queried := CollectedOnceQuerySource.source_return_boundary program allocator world
    (collectionScope scope caller context origins pending destination request) parents
    (collecting caller destination request) context origins pending (.var (leftSlot caller destination request))
    (suffix caller destination request) request rfl rfl consistent rows snapshot
  have composed := (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).established_and_pending
    2 (CollectedOnceQuerySource.childBudget (decide (request.pattern ∈ rows)) + 2) _ _ []
    (source_to_collection program allocator world scope parents caller context origins pending destination request)
  change (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).run _ _ = _ at queried
  change (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).run
    (CollectedOnceQuerySource.childBudget (decide (request.pattern ∈ rows)) + 2)
    (placed allocator world scope parents (collecting caller destination request) context origins pending) =
    ([], match finishAllocated? (collectionEnd allocator world scope parents caller context origins pending
      destination request (decide (request.pattern ∈ rows))) with
      | some next => .exhausted next
      | none => .suspended .allocation _) at queried
  rw [queried] at composed
  rw [finish_collectionEnd] at composed
  have cost : 2 + (CollectedOnceQuerySource.childBudget (decide (request.pattern ∈ rows)) + 2) =
      CollectedOnceQuerySource.childBudget (decide (request.pattern ∈ rows)) + 4 := by omega
  rw [cost] at composed
  cases copied : copyAllocator allocator (decide (request.pattern ∈ rows)) <;>
    simpa [copied, collectionEnd] using composed

theorem source_guard_prefix {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (caller : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (destination : Atom) (request : Request)
    (consistent : ∃ environment, Solves environment caller.bindings)
    (rows : List Atom) (snapshot : world.state.read request.handle = some rows) :
    let present := decide (request.pattern ∈ rows)
    (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).run
      (CollectedOnceQuerySource.childBudget present + 10)
      (placed allocator world scope parents (start caller destination request) context origins pending) =
      ([], match copyAllocator allocator present with
        | some next => .exhausted (placed next world scope parents (delivered caller destination request present)
            context (origins ++ [0, 0]) pending)
        | none => .suspended .allocation
            (collectionEnd allocator world scope parents caller context origins pending destination request present)) := by
  dsimp only
  have returned := source_to_return_boundary program allocator world scope parents caller context origins pending
    destination request consistent rows snapshot
  dsimp only at returned
  cases copied : copyAllocator allocator (decide (request.pattern ∈ rows)) with
  | some next =>
      rw [copied] at returned
      have composed := (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).established_and_pending
        (CollectedOnceQuerySource.childBudget (decide (request.pattern ∈ rows)) + 4) 6 _ _ [] returned
      rw [readout_prefix program next world scope parents caller context origins pending destination request _ consistent] at composed
      simpa only [List.nil_append, Nat.add_assoc] using composed
  | none =>
      rw [copied] at returned
      have stable := (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).run_stable
        (CollectedOnceQuerySource.childBudget (decide (request.pattern ∈ rows)) + 4) 6
        (placed allocator world scope parents (start caller destination request) context origins pending)
        (fun residual => by rw [returned]; simp)
      rw [returned] at stable
      simpa only [Nat.add_assoc] using stable

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.PresenceGuardSource
