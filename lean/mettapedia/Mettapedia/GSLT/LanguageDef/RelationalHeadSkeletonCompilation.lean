import Mettapedia.Languages.MeTTa.OSLFCore.Atom
import Mettapedia.GSLT.LanguageDef.UnificationEliminationTraceCompilation
import Mathlib.Data.List.Range

/-!
# Structural input heads with ordered relational occurrences

An admitted relational occurrence is replaced by its own fresh output hole.
The surrounding structural head is retained, including shared source
variables. The compiler emits an ordered call plan without identifying equal
call payloads. Filling the holes reconstructs an independently interpreted
source shape for every source-variable environment and every family of
occurrence results; no relation is assumed total or pure by that statement.

The input is an annotated head, not raw MeTTa. Deciding its structural and
relational roles belongs to the lane classifier. A relational payload is
opaque to this pass: its own argument evaluation is not head elaboration.
Logical cons is a separate structural constructor, not an application whose
symbol happens to be `cons`. Its physical list encoding is outside this file.
Whole clauses, static output heads, mutable authority, source freshening, and
C storage/lifetime refinement are also outside the claim.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RelationalHeadSkeletonCompilation

open Mettapedia.Logic.LP
open UnificationEliminationTraceCompilation

mutual

/-- Classification has already separated a structural node from a relational
call occurrence. A generated structural role therefore cannot be reclassified
from its spelling by this pass. -/
inductive Head (Var Call : Type) where
  | variable (name : Var)
  | atom (name : String)
  | node (name : String) (fields : Heads Var Call)
  | logicalCons (first rest : Head Var Call)
  | relational (payload : Call)
  deriving Repr, DecidableEq

inductive Heads (Var Call : Type) where
  | nil
  | cons (first : Head Var Call) (rest : Heads Var Call)
  deriving Repr, DecidableEq

end

variable {Var Call : Type}

abbrev Skeleton (Var : Type) := Head (Var ⊕ Nat) Empty
abbrev Skeletons (Var : Type) := Heads (Var ⊕ Nat) Empty

mutual

/-- Independent authored order, with one entry for every admitted occurrence. -/
def Head.calls : Head Var Call → List Call
  | .variable _ | .atom _ => []
  | .node _ fields => fields.calls
  | .logicalCons first rest => first.calls ++ rest.calls
  | .relational payload => [payload]

def Heads.calls : Heads Var Call → List Call
  | .nil => []
  | .cons first rest => first.calls ++ rest.calls

end

mutual

/-- Source-variable occurrences in the structural portion. Variables inside
opaque call payloads remain in the unchanged payloads of `Head.calls`. -/
def Head.variables : Head Var Call → List Var
  | .variable name => [name]
  | .atom _ | .relational _ => []
  | .node _ fields => fields.variables
  | .logicalCons first rest => first.variables ++ rest.variables

def Heads.variables : Heads Var Call → List Var
  | .nil => []
  | .cons first rest => first.variables ++ rest.variables

end

structure Compiled (Var Call : Type) where
  skeleton : Skeleton Var
  plan : List (Nat × Call)
  next : Nat
  deriving Repr

structure CompiledFields (Var Call : Type) where
  skeleton : Skeletons Var
  plan : List (Nat × Call)
  next : Nat
  deriving Repr

mutual

/-- Stateful compilation allocates fresh occurrence holes while traversing the
head. Its counter comes from recursive compiler results, not a reference map. -/
def lower (start : Nat) : Head Var Call → Compiled Var Call
  | .variable name => ⟨.variable (.inl name), [], start⟩
  | .atom name => ⟨.atom name, [], start⟩
  | .node name fields =>
      let compiled := lowerFields start fields
      ⟨.node name compiled.skeleton, compiled.plan, compiled.next⟩
  | .logicalCons first rest =>
      let left := lower start first
      let right := lower left.next rest
      ⟨.logicalCons left.skeleton right.skeleton,
        left.plan ++ right.plan, right.next⟩
  | .relational payload =>
      ⟨.variable (.inr start), [(start, payload)], start + 1⟩

def lowerFields (start : Nat) : Heads Var Call → CompiledFields Var Call
  | .nil => ⟨.nil, [], start⟩
  | .cons first rest =>
      let left := lower start first
      let right := lowerFields left.next rest
      ⟨.cons left.skeleton right.skeleton,
        left.plan ++ right.plan, right.next⟩

end

mutual

theorem lower_next (start : Nat) (source : Head Var Call) :
    (lower start source).next = start + source.calls.length := by
  cases source with
  | «variable» name => simp [lower, Head.calls]
  | atom name => simp [lower, Head.calls]
  | node name fields =>
      simpa [lower, Head.calls] using lowerFields_next start fields
  | logicalCons first rest =>
      simp [lower, Head.calls, lower_next start first,
        lower_next (start + first.calls.length) rest, Nat.add_assoc]
  | relational payload => simp [lower, Head.calls]

theorem lowerFields_next (start : Nat) (source : Heads Var Call) :
    (lowerFields start source).next = start + source.calls.length := by
  cases source with
  | nil => simp [lowerFields, Heads.calls]
  | cons first rest =>
      simp [lowerFields, Heads.calls, lower_next start first,
        lowerFields_next (start + first.calls.length) rest, Nat.add_assoc]

end

/-- Independent numbering of an already enumerated occurrence list. -/
def numberFrom (start : Nat) : List Call → List (Nat × Call)
  | [] => []
  | payload :: rest => (start, payload) :: numberFrom (start + 1) rest

theorem numberFrom_append (start : Nat) (first rest : List Call) :
    numberFrom start (first ++ rest) =
      numberFrom start first ++ numberFrom (start + first.length) rest := by
  induction first generalizing start with
  | nil => simp [numberFrom]
  | cons payload first ih =>
      simp [numberFrom, ih, Nat.add_comm, Nat.add_left_comm]

theorem numberFrom_payloads (start : Nat) (payloads : List Call) :
    (numberFrom start payloads).map Prod.snd = payloads := by
  induction payloads generalizing start with
  | nil => rfl
  | cons payload rest ih => simp [numberFrom, ih]

theorem numberFrom_holes (start : Nat) (payloads : List Call) :
    (numberFrom start payloads).map Prod.fst =
      List.range' start payloads.length := by
  induction payloads generalizing start with
  | nil => rfl
  | cons payload rest ih => simp [numberFrom, ih, List.range']

mutual

/-- The actual stateful compiler has the independently enumerated source
occurrences, in exactly their source order, with consecutive fresh IDs. -/
theorem lower_plan (start : Nat) (source : Head Var Call) :
    (lower start source).plan = numberFrom start source.calls := by
  cases source with
  | «variable» name => rfl
  | atom name => rfl
  | node name fields =>
      simpa [lower, Head.calls] using lowerFields_plan start fields
  | logicalCons first rest =>
      simp [lower, Head.calls, lower_plan start first,
        lower_plan (start + first.calls.length) rest,
        lower_next, numberFrom_append]
  | relational payload => rfl

theorem lowerFields_plan (start : Nat) (source : Heads Var Call) :
    (lowerFields start source).plan = numberFrom start source.calls := by
  cases source with
  | nil => rfl
  | cons first rest =>
      simp [lowerFields, Heads.calls, lower_plan start first,
        lowerFields_plan (start + first.calls.length) rest,
        lower_next, numberFrom_append]

end

theorem exact_call_order (start : Nat) (source : Head Var Call) :
    (lower start source).plan.map Prod.snd = source.calls := by
  rw [lower_plan, numberFrom_payloads]

theorem exact_call_count (start : Nat) (source : Head Var Call) :
    (lower start source).plan.length = source.calls.length := by
  have same := congrArg List.length (exact_call_order start source)
  simpa using same

theorem exact_call_multiplicity [DecidableEq Call]
    (start : Nat) (source : Head Var Call) (payload : Call) :
    ((lower start source).plan.map Prod.snd).count payload =
      source.calls.count payload := by
  rw [exact_call_order]

def original? : Var ⊕ Nat → Option Var
  | .inl name => some name
  | .inr _ => none

def hole? : Var ⊕ Nat → Option Nat
  | .inl _ => none
  | .inr index => some index

mutual

/-- Structural source names and their repeated occurrences survive lowering. -/
theorem lower_original_variables (start : Nat) (source : Head Var Call) :
    ((lower start source).skeleton.variables.filterMap original?) =
      source.variables := by
  cases source with
  | «variable» name => rfl
  | atom name => rfl
  | node name fields =>
      simpa [lower, Head.variables] using
        lowerFields_original_variables start fields
  | logicalCons first rest =>
      simp [lower, Head.variables, lower_original_variables start first,
        lower_original_variables (lower start first).next rest]
  | relational payload => rfl

theorem lowerFields_original_variables (start : Nat)
    (source : Heads Var Call) :
    ((lowerFields start source).skeleton.variables.filterMap original?) =
      source.variables := by
  cases source with
  | nil => rfl
  | cons first rest =>
      simp [lowerFields, Heads.variables,
        lower_original_variables start first,
        lowerFields_original_variables (lower start first).next rest]

end

mutual

/-- Every planned hole occurs exactly where the compiler placed its call
occurrence. No call plan is silently missing from the structural skeleton. -/
theorem lower_skeleton_holes (start : Nat) (source : Head Var Call) :
    ((lower start source).skeleton.variables.filterMap hole?) =
      (lower start source).plan.map Prod.fst := by
  cases source with
  | «variable» name => rfl
  | atom name => rfl
  | node name fields =>
      simpa [lower, Head.variables] using lowerFields_skeleton_holes start fields
  | logicalCons first rest =>
      simp [lower, Head.variables, lower_skeleton_holes start first,
        lower_skeleton_holes (lower start first).next rest]
  | relational payload => rfl

theorem lowerFields_skeleton_holes (start : Nat) (source : Heads Var Call) :
    ((lowerFields start source).skeleton.variables.filterMap hole?) =
      (lowerFields start source).plan.map Prod.fst := by
  cases source with
  | nil => rfl
  | cons first rest =>
      simp [lowerFields, Heads.variables, lower_skeleton_holes start first,
        lowerFields_skeleton_holes (lower start first).next rest]

end

theorem fresh_consecutive_holes (start : Nat) (source : Head Var Call) :
    ((lower start source).skeleton.variables.filterMap hole?) =
      List.range' start source.calls.length := by
  rw [lower_skeleton_holes, lower_plan, numberFrom_holes]

private theorem consecutive_unique (start count : Nat) :
    (List.range' start count).Nodup := by
  induction count generalizing start with
  | zero => simp
  | succ count ih =>
      change (start :: List.range' (start + 1) count).Nodup
      apply List.nodup_cons.mpr
      constructor
      · intro present
        rw [List.mem_range'] at present
        obtain ⟨offset, _, same⟩ := present
        omega
      · exact ih (start + 1)

theorem fresh_holes_unique (start : Nat) (source : Head Var Call) :
    ((lower start source).skeleton.variables.filterMap hole?).Nodup := by
  rw [fresh_consecutive_holes]
  exact consecutive_unique start source.calls.length

theorem planned_holes_unique (start : Nat) (source : Head Var Call) :
    ((lower start source).plan.map Prod.fst).Nodup := by
  rw [← lower_skeleton_holes]
  exact fresh_holes_unique start source

theorem planned_hole_interval (start : Nat) (source : Head Var Call) (index : Nat)
    (present : index ∈ (lower start source).plan.map Prod.fst) :
    start ≤ index ∧ index < (lower start source).next := by
  rw [lower_plan, numberFrom_holes, List.mem_range'] at present
  obtain ⟨offset, bound, same⟩ := present
  rw [lower_next]
  omega

theorem original_ne_hole (name : Var) (index : Nat) :
    (Sum.inl name : Var ⊕ Nat) ≠ Sum.inr index := by
  intro impossible
  cases impossible

/-- A structural interpretation is independent of the compiler. It may
reconstruct syntax, build an LP term, or give another constructor algebra. -/
structure Algebra (Value : Type) where
  atom : String → Value
  node : String → List Value → Value
  logicalCons : Value → Value → Value

mutual

/-- Interpret the annotated source directly, assigning results by source
occurrence position. Nested calls inside an opaque payload remain opaque. -/
def interpret {Value : Type} (algebra : Algebra Value)
    (environment : Var → Value) (results : Nat → Value) (start : Nat) :
    Head Var Call → Value
  | .variable name => environment name
  | .atom name => algebra.atom name
  | .node name fields =>
      algebra.node name (interpretFields algebra environment results start fields)
  | .logicalCons first rest =>
      algebra.logicalCons
        (interpret algebra environment results start first)
        (interpret algebra environment results (start + first.calls.length) rest)
  | .relational _ => results start

def interpretFields {Value : Type} (algebra : Algebra Value)
    (environment : Var → Value) (results : Nat → Value) (start : Nat) :
    Heads Var Call → List Value
  | .nil => []
  | .cons first rest =>
      interpret algebra environment results start first ::
        interpretFields algebra environment results (start + first.calls.length) rest

end

mutual

/-- Ordinary structural filling of a compiled skeleton. The sum namespace
prevents a generated hole from capturing a source variable. -/
def fill {Value : Type} (algebra : Algebra Value)
    (environment : Var → Value) (results : Nat → Value) : Skeleton Var → Value
  | .variable (.inl name) => environment name
  | .variable (.inr index) => results index
  | .atom name => algebra.atom name
  | .node name fields => algebra.node name (fillFields algebra environment results fields)
  | .logicalCons first rest =>
      algebra.logicalCons (fill algebra environment results first)
        (fill algebra environment results rest)
  | .relational impossible => nomatch impossible

def fillFields {Value : Type} (algebra : Algebra Value)
    (environment : Var → Value) (results : Nat → Value) : Skeletons Var → List Value
  | .nil => []
  | .cons first rest =>
      fill algebra environment results first :: fillFields algebra environment results rest

end

mutual

/-- Fresh-hole reconstruction for arbitrary source bindings and occurrence
results. In particular, a repeated source variable uses one environment entry,
while equal relational payloads still have independently supplied results. -/
theorem fill_lower {Value : Type} (algebra : Algebra Value)
    (environment : Var → Value) (results : Nat → Value)
    (start : Nat) (source : Head Var Call) :
    fill algebra environment results (lower start source).skeleton =
      interpret algebra environment results start source := by
  cases source with
  | «variable» name => rfl
  | atom name => rfl
  | node name fields =>
      simp [lower, fill, interpret, fillFields_lower algebra environment results start fields]
  | logicalCons first rest =>
      simp [lower, fill, interpret, fill_lower algebra environment results start first,
        fill_lower algebra environment results (start + first.calls.length) rest, lower_next]
  | relational payload => rfl

theorem fillFields_lower {Value : Type} (algebra : Algebra Value)
    (environment : Var → Value) (results : Nat → Value)
    (start : Nat) (source : Heads Var Call) :
    fillFields algebra environment results (lowerFields start source).skeleton =
      interpretFields algebra environment results start source := by
  cases source with
  | nil => rfl
  | cons first rest =>
      simp [lowerFields, fillFields, interpretFields,
        fill_lower algebra environment results start first,
        fillFields_lower algebra environment results (start + first.calls.length) rest, lower_next]

end

/-! ## The structural gate precedes the ordered prefix

This is a small input-head phase semantics. It uses the existing independent
LP unifier, with explicit failure/fuel reasons. The supplied prefix dispatcher
models one sequential execution and can stop on control, exception, or physical
decline. It is not a semantics of branching relational calls or a claim about
all PeTTa effects. The dispatcher receives the checked head substitution.
-/

inductive Constructor where
  | node (name : String) (arity : Nat)
  | logicalCons
  deriving DecidableEq, Repr

/-- Source names, generated holes, and caller variables have disjoint logical
namespaces. Freshening a concrete runtime's names into them is a separate bridge. -/
abbrev headSignature (Var : Type) : LPSignature where
  constants := String
  vars := (Var ⊕ Nat) ⊕ Nat
  relationSymbols := Empty
  relationArity := Empty.elim
  functionSymbols := Constructor
  functionArity
    | .node _ arity => arity
    | .logicalCons => 2

abbrev LogicalTerm (Var : Type) := Term (headSignature Var)

def nodeTerm (name : String) (fields : List (LogicalTerm Var)) : LogicalTerm Var :=
  .app (.node name fields.length) fields.get

def logicalAlgebra : Algebra (LogicalTerm Var) where
  atom name := .const name
  node := nodeTerm
  logicalCons first rest :=
    .app .logicalCons (fun index => if index.val = 0 then first else rest)

def sourceVariable (name : Var) : LogicalTerm Var := .var (.inl (.inl name))
def occurrenceHole (index : Nat) : LogicalTerm Var := .var (.inl (.inr index))
def callerVariable (index : Nat) : LogicalTerm Var := .var (.inr index)

def encode (skeleton : Skeleton Var) : LogicalTerm Var :=
  fill logicalAlgebra sourceVariable occurrenceHole skeleton

theorem encode_lower (start : Nat) (source : Head Var Call) :
    encode (lower start source).skeleton =
      interpret logicalAlgebra sourceVariable occurrenceHole start source :=
  fill_lower logicalAlgebra sourceVariable occurrenceHole start source

inductive Interruption where
  | cut
  | exception
  | decline
  deriving DecidableEq, Repr

inductive Reply (State : Type) where
  | continueWith (state : State)
  | interrupt (reason : Interruption) (state : State)

inductive PhaseStop where
  | complete
  | interrupted (reason : Interruption)
  | headStopped (reason : StopReason)
  deriving DecidableEq, Repr

structure PhaseRun (Call State : Type) where
  attempted : List Call
  state : State
  stop : PhaseStop
  deriving DecidableEq, Repr

/-- An ordered prefix retains repeated occurrences and does not execute the
suffix after interruption. State carries whatever this supplied dispatcher
observes; no commutation of effects is used. -/
def runPrefix {State : Type} (dispatch : Call → State → Reply State) :
    List Call → State → PhaseRun Call State
  | [], state => ⟨[], state, .complete⟩
  | payload :: rest, state =>
      match dispatch payload state with
      | .continueWith next =>
          let tail := runPrefix dispatch rest next
          ⟨payload :: tail.attempted, tail.state, tail.stop⟩
      | .interrupt reason next =>
          ⟨[payload], next, .interrupted reason⟩

def runInputHead [DecidableEq Var] {State : Type}
    (fuel start : Nat) (source : Head Var Call) (query : LogicalTerm Var)
    (dispatch : Subst (headSignature Var) → Call → State → Reply State)
    (state : State) : PhaseRun Call State :=
  let compiled := lower start source
  let trace := runTrace fuel [(encode compiled.skeleton, query)]
  match trace.stop with
  | .success =>
      runPrefix (dispatch (traceSubst trace.updates))
        (compiled.plan.map Prod.snd) state
  | reason => ⟨[], state, .headStopped reason⟩

/-- Compilation preserves every observation of the supplied ordered prefix
dispatcher, including its state and interruption point. -/
theorem ordered_prefix_exact {State : Type}
    (dispatch : Call → State → Reply State) (state : State)
    (start : Nat) (source : Head Var Call) :
    runPrefix dispatch ((lower start source).plan.map Prod.snd) state =
      runPrefix dispatch source.calls state := by
  rw [exact_call_order]

/-- A failed structural gate cannot enter its relational prefix. Fuel
exhaustion is an explicit stop reason, not a proof of logical impossibility. -/
theorem stopped_head_has_no_prefix [DecidableEq Var] {State : Type}
    (fuel start : Nat) (source : Head Var Call) (query : LogicalTerm Var)
    (dispatch : Subst (headSignature Var) → Call → State → Reply State)
    (state : State)
    (stopped : (runTrace fuel [(encode (lower start source).skeleton, query)]).stop ≠
      .success) :
    (runInputHead fuel start source query dispatch state).attempted = [] ∧
      (runInputHead fuel start source query dispatch state).state = state := by
  unfold runInputHead
  cases reason : (runTrace fuel [(encode (lower start source).skeleton, query)]).stop <;>
    simp_all

/-- Entering the prefix requires a substitution established by the actual
independent unifier. Reconstruction identifies the unified skeleton with the
source's independently interpreted input shape. -/
theorem successful_gate_reconstructs [DecidableEq Var]
    (fuel start : Nat) (source : Head Var Call) (query : LogicalTerm Var)
    (substitution : Subst (headSignature Var))
    (accepted : observe
        (runTrace fuel [(encode (lower start source).skeleton, query)]) =
      some substitution) :
    substitution.applyTerm
        (interpret logicalAlgebra sourceVariable occurrenceHole start source) =
      substitution.applyTerm query := by
  rw [observe_runTrace_exact] at accepted
  have sound := unifyFuel_sound fuel
    [(encode (lower start source).skeleton, query)] substitution accepted
  have pair := sound (encode (lower start source).skeleton, query) (by simp)
  simpa [encode_lower] using pair

/-! ## Executable positive and negative boundaries -/

private abbrev Payload := Mettapedia.Languages.MeTTa.OSLFCore.Atom

private def touchX : Payload :=
  .expression [.symbol "touch", .var "x"]

private def sharedHead : Head String Payload :=
  .node "before" (.cons (.relational touchX)
    (.cons (.variable "x") (.cons (.variable "x") .nil)))

theorem shared_names_and_call_payload_survive :
    (lower 4 sharedHead).skeleton =
      .node "before" (.cons (.variable (.inr 4))
        (.cons (.variable (.inl "x")) (.cons (.variable (.inl "x")) .nil))) ∧
    (lower 4 sharedHead).plan = [(4, touchX)] := by decide

private def duplicatedCalls : Head String Payload :=
  .node "pair" (.cons (.relational touchX)
    (.cons (.relational touchX) .nil))

theorem equal_calls_have_distinct_occurrence_holes :
    (lower 7 duplicatedCalls).plan = [(7, touchX), (8, touchX)] ∧
    (lower 7 duplicatedCalls).skeleton.variables = [.inr 7, .inr 8] := by decide

theorem deduplicating_the_plan_changes_the_observation :
    (lower 7 duplicatedCalls).plan.map Prod.snd ≠ [touchX] := by decide

private def headsOfList : List (Head Var Call) → Heads Var Call
  | [] => .nil
  | first :: rest => .cons first (headsOfList rest)

private def syntaxAlgebra : Algebra (Head String Empty) where
  atom := .atom
  node name fields := .node name (headsOfList fields)
  logicalCons := .logicalCons

theorem duplicate_calls_can_fill_distinct_results :
    fill syntaxAlgebra (fun _ => .atom "bound")
        (fun index => if index = 7 then .atom "left-result" else .atom "right-result")
        (lower 7 duplicatedCalls).skeleton =
      .node "pair" (.cons (.atom "left-result") (.cons (.atom "right-result") .nil)) := by
  decide

private def countDispatch {Signature : LPSignature} :
    Subst Signature → Payload → Nat → Reply Nat :=
  fun _ _ count => .continueWith (count + 1)

private def nestedCall : Head String Payload :=
  .node "box" (.cons (.relational touchX) .nil)

/-- An open enclosing query is unified with the skeleton first. It does not
hide the nested callable occurrence from the source-directed compiler. -/
theorem open_enclosing_query_enters_the_nested_prefix :
    runInputHead 8 0 nestedCall (callerVariable 0) countDispatch 0 =
      ⟨[touchX], 1, .complete⟩ := by decide

private def conflictingQuery : LogicalTerm String :=
  nodeTerm "before" [.const "value",
    nodeTerm "rigid-f" [callerVariable 0],
    nodeTerm "rigid-g" [callerVariable 1]]

theorem partial_structural_conflict_precedes_the_effect :
    runInputHead 32 0 sharedHead conflictingQuery countDispatch 0 =
      ⟨[], 0, .headStopped .constructorConflict⟩ := by decide

private def compatibleQuery : LogicalTerm String :=
  nodeTerm "before" [.const "value",
    nodeTerm "rigid-f" [callerVariable 0],
    nodeTerm "rigid-f" [callerVariable 1]]

theorem compatible_open_aliases_enter_the_prefix_once :
    runInputHead 32 0 sharedHead compatibleQuery countDispatch 0 =
      ⟨[touchX], 1, .complete⟩ := by decide

private def reportSourceBinding :
    Subst (headSignature String) → Payload → List String → Reply (List String) :=
  fun substitution _ state =>
    match substitution.applyTerm (sourceVariable "x") with
    | .const value => .continueWith (state ++ [value])
    | _ => .continueWith (state ++ ["unresolved"])

theorem structural_binding_is_visible_to_the_first_prefix_call :
    runInputHead 24 0 sharedHead
        (nodeTerm "before" [.const "fixed-result", .const "payload", .const "payload"])
        reportSourceBinding [] =
      ⟨[touchX], ["payload"], .complete⟩ := by decide

private def cyclicHead : Head String Payload :=
  .node "cycle" (.cons (.variable "x")
    (.cons (.node "wrap" (.cons (.variable "x") .nil))
      (.cons (.relational touchX) .nil)))

theorem cross_coordinate_occurs_failure_precedes_the_prefix :
    runInputHead 32 0 cyclicHead
        (nodeTerm "cycle" [callerVariable 0, callerVariable 0, .const "value"])
        countDispatch 0 =
      ⟨[], 0, .headStopped .occursCheck⟩ := by decide

theorem exhausted_head_fuel_is_a_distinct_stop :
    runInputHead 0 0 sharedHead compatibleQuery countDispatch 0 =
      ⟨[], 0, .headStopped .fuelExhausted⟩ := by decide

private def generatedStructural : Head String Payload :=
  .node "touch" (.cons (.variable "x") .nil)

theorem structural_role_does_not_create_a_call :
    (lower 0 generatedStructural).plan = [] ∧
      (lower 0 (.relational touchX : Head String Payload)).plan = [(0, touchX)] := by
  decide

private def logicalConsHead : Head String Payload :=
  .logicalCons (.relational touchX) (.atom "nil")

private def consSpellingQuery : LogicalTerm String :=
  nodeTerm "cons" [.const "value", .const "nil"]

theorem logical_cons_is_not_an_application_spelling :
    runInputHead 8 0 logicalConsHead consSpellingQuery countDispatch 0 =
      ⟨[], 0, .headStopped .constructorConflict⟩ := by decide

private def interruptSecond (reason : Interruption) :
    Subst (headSignature String) → Payload → Nat → Reply Nat :=
  fun _ _ count =>
    if count = 1 then .interrupt reason (count + 1)
    else .continueWith (count + 1)

private def threeCalls : Head String Payload :=
  .node "triple" (.cons (.relational touchX)
    (.cons (.relational touchX) (.cons (.relational touchX) .nil)))

theorem interrupted_prefix_does_not_run_its_suffix (reason : Interruption) :
    runInputHead 8 0 threeCalls (callerVariable 0) (interruptSecond reason) 0 =
      ⟨[touchX, touchX], 2, .interrupted reason⟩ := by
  cases reason <;> decide

#print axioms lower_plan
#print axioms lower_original_variables
#print axioms fresh_holes_unique
#print axioms fill_lower
#print axioms exact_call_multiplicity
#print axioms stopped_head_has_no_prefix
#print axioms successful_gate_reconstructs
#print axioms partial_structural_conflict_precedes_the_effect
#print axioms structural_binding_is_visible_to_the_first_prefix_call
#print axioms cross_coordinate_occurs_failure_precedes_the_prefix
#print axioms interrupted_prefix_does_not_run_its_suffix

end Mettapedia.GSLT.LanguageDef.RelationalHeadSkeletonCompilation
