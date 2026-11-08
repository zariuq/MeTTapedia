import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEStructuralIf
import Mettapedia.Languages.MeTTa.HE.RecursiveCorrectness
import Mettapedia.Machines.HEProducerCompletion

/-!
# Retained HE condition and argument continuations

The existing recursive machine already represents the boundary after an
argument producer has returned: its results, binding records, remaining
operands and expected types are retained in `argumentHeads`. A conditional
uses that same boundary, followed by rebuilding the call, invoking the actual
`if` implementation and selecting the completed result frontier.

The source theorem permits arbitrary condition results and records. It does
not evaluate the condition again and does not replace a reached invocation
by a new evaluation of the whole conditional. No standard-if equation set is
assumed: the actual space/dispatch decides its meaning, including overrides.

This is the existing read-only, finite, all-candidate HE evaluator profile.
It is not an identification with first-success native selection or effects.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERetainedConditional

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.CompletedDelivery
open Mettapedia.Languages.MeTTa.HE.BindingComposition
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open HEReturns

/-- Any non-leaf argument producer can finish before its saved argument
continuation runs. Its result stream is consumed once, with every record. -/
theorem arguments_from_reached (space : Space) (dispatch : GroundedDispatch)
    (original type : Atom) (remaining types : List Atom) (bindings : Bindings)
    (fuel : Nat) (live : List Atom) :
    interpretArgs space dispatch (original :: remaining) (type :: types) bindings
      (fuel + 1) live =
      (Frame.argumentHeads original remaining types fuel live).denote space dispatch
        (evalAtom space dispatch original type bindings fuel (remaining ++ types ++ live)) := rfl

/-- The machine schedules the reached argument continuation, not a second
producer request. Retained alternatives and published history are unchanged. -/
theorem reached_argument_step (space : Space) (dispatch : GroundedDispatch)
    (original : Atom) (remaining types : List Atom) (fuel : Nat) (live : List Atom)
    (results emitted : ResultSet) (stack : List Frame) :
    RecursiveMachine.next dispatch
      ⟨space, .returning results, .argumentHeads original remaining types fuel live :: stack, emitted⟩ =
      some ⟨space, .work (.argumentHeads original remaining types fuel results live), stack, emitted⟩ := rfl

def conditionLive (chosen other : Atom) (name : String) (live : List Atom) : List Atom :=
  [chosen, other, Atom.atomType, Atom.atomType, .symbol "if", .var name] ++ live

def frames (original chosen other : Atom) (name : String) (fuel : Nat) (live : List Atom) : List Frame :=
  [.argumentHeads original [chosen, other] [Atom.atomType, Atom.atomType]
      fuel (.symbol "if" :: .var name :: live),
   .functionTail (.symbol "if"), .calls (.var name) (fuel + 2) live, .filter]

def reached (space : Space) (original chosen other : Atom) (name : String)
    (fuel : Nat) (live : List Atom) (conditions : ResultSet) : Configuration :=
  ⟨space, .returning conditions, frames original chosen other name fuel live, []⟩

def resume (space : Space) (dispatch : GroundedDispatch) (original chosen other : Atom)
    (name : String) (fuel : Nat) (live : List Atom) (conditions : ResultSet) : ResultSet :=
  (reached space original chosen other name fuel live conditions).denote dispatch

/-- One reached alternative, before whole-frontier success selection. -/
def rowContinuation (space : Space) (dispatch : GroundedDispatch) (original chosen other : Atom)
    (name : String) (fuel : Nat) (live : List Atom) (condition : ResultPair) : ResultSet :=
  (Frame.calls (.var name) (fuel + 2) live).denote space dispatch
    (RecursiveTasks.functionTail (.symbol "if")
      ((Frame.argumentHeads original [chosen, other] [Atom.atomType, Atom.atomType]
        fuel (.symbol "if" :: .var name :: live)).denote space dispatch [condition]))

/-- Alternatives keep their authored order and individual records. Selection
is performed on the complete resulting frontier, not on each row separately. -/
theorem resume_rows (space : Space) (dispatch : GroundedDispatch) (original chosen other : Atom)
    (name : String) (fuel : Nat) (live : List Atom) (conditions : ResultSet) :
    resume space dispatch original chosen other name fuel live conditions =
      keep (conditions.flatMap (rowContinuation space dispatch original chosen other name fuel live)) := by
  change keep ((Frame.calls (.var name) (fuel + 2) live).denote space dispatch
    (RecursiveTasks.functionTail (.symbol "if")
      ((Frame.argumentHeads original [chosen, other] [Atom.atomType, Atom.atomType]
        fuel (.symbol "if" :: .var name :: live)).denote space dispatch conditions))) = _
  apply congrArg keep
  unfold rowContinuation
  simp [Frame.denote, Task.denote, RecursiveTasks.functionTail,
    List.map_flatMap, List.flatMap_assoc, List.flatMap_map]

/-- A Boolean result invokes the actual if implementation with held branch
syntax and its reached record. No condition producer or type check is rerun. -/
theorem rowContinuation_bool (space : Space) (dispatch : GroundedDispatch)
    (original chosen other : Atom) (name : String) (fuel : Nat) (live : List Atom)
    (truth : Bool) (record : Bindings) :
    rowContinuation space dispatch original chosen other name (fuel + 3) live
      (.grounded (.bool truth), record) =
      invoke space dispatch (.ordinary (.var name))
        (.expression [.symbol "if", .grounded (.bool truth), chosen, other]) record
        (fuel + 5) live := by
  have held : ∀ retained, interpretArgs space dispatch [chosen, other]
      [Atom.atomType, Atom.atomType] record (fuel + 3) retained =
        [(argumentPacket [chosen, other], record)] := by
    intro retained
    exact interpretArgs_cons_self
      (fun live => HECorrespondence.he_atom_demand space dispatch chosen record (fuel + 1) live)
      (fun live => interpretArgs_cons_self
        (fun live => HECorrespondence.he_atom_demand space dispatch other record fuel live)
        (fun live => interpretArgs_nil_self record fuel live) live) retained
  simp [rowContinuation, Frame.denote, Task.denote, held, RecursiveTasks.argumentTail,
    RecursiveTasks.functionTail, argumentsSucceeded_packet, argumentValues_packet,
    isEmptyOrError, isEmptyAtom, isErrorAtom, Atom.empty, mettaCall]

theorem resume_boolean_stream (space : Space) (dispatch : GroundedDispatch)
    (original chosen other : Atom) (name : String) (fuel : Nat) (live : List Atom)
    (conditions : List (Bool × Bindings)) :
    resume space dispatch original chosen other name (fuel + 3) live
      (conditions.map fun row => (.grounded (.bool row.1), row.2)) =
      keep (conditions.flatMap fun row => invoke space dispatch (.ordinary (.var name))
        (.expression [.symbol "if", .grounded (.bool row.1), chosen, other]) row.2
        (fuel + 5) live) := by
  rw [resume_rows, List.flatMap_map]
  congr 1
  apply List.flatMap_congr
  intro row _
  exact rowContinuation_bool space dispatch original chosen other name fuel live row.1 row.2

private theorem single_applicable_stream {space : Space} {dispatch : GroundedDispatch}
    {head : String} {params args : List Atom} {range expected : Atom}
    {bindings selected : Bindings} {fuel : Nat} {live : List Atom}
    (declared : getAtomTypes space (.symbol head) = [arrowType params range])
    (applicable : checkIfFunctionTypeIsApplicable (.expression (.symbol head :: args))
      (arrowType params range) expected space bindings fuel = .inr [selected]) :
    interpretExpression space dispatch (.expression (.symbol head :: args)) expected bindings
      (fuel + 1) live =
      (interpretFunction space dispatch (.expression (.symbol head :: args))
        (arrowType params range) selected fuel (callReturnType range :: live)).flatMap
          fun result => invoke space dispatch (.ordinary (callReturnType range)) result.1 result.2 fuel live := by
  rw [interpretExpression]
  simp only [declared, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    isFunctionType_arrowType, if_true, applicable,
    callReturnType_arrowType]
  have nonFunction : ([arrowType params range].any fun type =>
      !isFunctionType type || type == Atom.undefinedType) = false := by
    simp [isFunctionType_arrowType, arrowType_beq_symbol, Atom.undefinedType]
  simp only [nonFunction, Bool.false_eq_true, if_false, List.append_nil,
    Bool.not_false, if_true, List.all_cons, List.all_nil, Bool.and_true,
    isFunctionType_arrowType, applicable]
  generalize (interpretFunction space dispatch (.expression (.symbol head :: args))
      (arrowType params range) selected fuel (callReturnType range :: live)).flatMap
        (fun result => invoke space dispatch (.ordinary (callReturnType range))
          result.1 result.2 fuel live) = results
  cases results <;> simp

/-- The argument/range checks produce the retained conditional record before
the condition producer starts. Neither condition evaluation nor its answers
are hypotheses of this header theorem. -/
theorem conditional_header {space : Space} {dispatch : GroundedDispatch} {name : String}
    {condition chosen other expected : Atom}
    (declared : getAtomTypes space (.symbol "if") = [ifArrow name])
    (expectedGround : atomVariables expected = [])
    (notUndefined : expected ≠ Atom.undefinedType) (notAtom : expected ≠ Atom.atomType)
    (conditionChecked : ArgumentChecked space (.symbol "Bool") condition)
    (chosenChecked : ArgumentChecked space Atom.atomType chosen)
    (otherChecked : ArgumentChecked space Atom.atomType other)
    {bindings : Bindings} (unbound : bindings.lookup name = none)
    (noEqualities : bindings.equalities = []) {fuel : Nat} (enough : 9 ≤ fuel) :
    checkIfFunctionTypeIsApplicable (.expression [.symbol "if", condition, chosen, other])
      (ifArrow name) expected space bindings (fuel + 2) = .inr [bindings.assign name expected] ∧
    ∀ live, evalAtom space dispatch (.symbol "if") (ifArrow name)
      (bindings.assign name expected) (fuel + 1) live =
        [(.symbol "if", ifRecord bindings name expected)] := by
  obtain ⟨g, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
  have boolClass : ValueClass (.symbol "Bool") := Or.inr (Or.inr (Or.inl rfl))
  have atomGround : atomVariables Atom.atomType = [] := rfl
  have steps : CheckSteps space (g + 2) [.symbol "Bool", Atom.atomType, Atom.atomType]
      [condition, chosen, other] bindings bindings :=
    .cons (checkArgumentType_checked boolClass.ground conditionChecked bindings
        (by rw [boolClass.matchFuel_eq]; omega))
      (.cons (checkArgumentType_checked atomGround chosenChecked bindings
          (by simp [matchFuel, Atom.atomType]))
        (.cons (checkArgumentType_checked atomGround otherChecked bindings
            (by simp [matchFuel, Atom.atomType])) (.nil bindings)))
  have loop := checkArgLoop_steps (expr := .expression [.symbol "if", condition, chosen, other])
    steps [] 1
  constructor
  · rw [checkIfFunctionTypeIsApplicable]
    simp only [getFunctionArgTypes_arrowType, getFunctionRetType_arrowType]
    simp [loop, HEStructuralIf.matchTypes_ground_var expectedGround notUndefined notAtom name
      unbound noEqualities g]
  · intro live
    have bound : (bindings.assign name expected).lookup name = some expected :=
      lookup_assign_of_lookup_none bindings name expected unbound
    have self : SelfEqualities name (bindings.assign name expected) := by
      intro e member
      simp [Bindings.assign, noEqualities] at member
    have shapes : ∀ atom ∈ (.symbol "->" :: ([.symbol "Bool", Atom.atomType, Atom.atomType] ++
        [.var name]) : List Atom), (∃ label, atom = .symbol label) ∨ atom = .var name := by
      intro atom member
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl
      · exact Or.inl ⟨_, rfl⟩
      · exact Or.inl ⟨_, rfl⟩
      · exact Or.inl ⟨_, rfl⟩
      · exact Or.inl ⟨_, rfl⟩
      · exact Or.inr rfl
    rw [evalAtom_head_selfMatch declared shapes (by decide) self bound (by simp; omega) live]
    have count : (.symbol "->" :: ([.symbol "Bool", Atom.atomType, Atom.atomType] ++ [.var name]) :
        List Atom).count (.var name) = 1 := by simp [Atom.atomType]
    rw [count]
    rfl

/-- An arbitrary condition result stream is handed to the reached machine
continuation. The exact live roots and all result bindings are retained. -/
theorem source_if_from_condition_stream {space : Space} {dispatch : GroundedDispatch} {name : String}
    {condition chosen other expected : Atom}
    (declared : getAtomTypes space (.symbol "if") = [ifArrow name])
    (expectedGround : atomVariables expected = [])
    (notUndefined : expected ≠ Atom.undefinedType)
    (notAtom : expected ≠ Atom.atomType) (notExpression : expected ≠ Atom.expressionType)
    (conditionChecked : ArgumentChecked space (.symbol "Bool") condition)
    (chosenChecked : ArgumentChecked space Atom.atomType chosen)
    (otherChecked : ArgumentChecked space Atom.atomType other)
    {bindings : Bindings} (unbound : bindings.lookup name = none)
    (noEqualities : bindings.equalities = []) {fuel : Nat} (enough : 9 ≤ fuel)
    (live : List Atom) :
    evalAtom space dispatch (.expression [.symbol "if", condition, chosen, other]) expected
      bindings (fuel + 4) live =
      resume space dispatch condition chosen other name fuel live
        (evalAtom space dispatch condition (.symbol "Bool") (ifRecord bindings name expected)
          fuel (conditionLive chosen other name live)) := by
  obtain ⟨applicable, head⟩ := conditional_header (dispatch := dispatch) declared expectedGround
    notUndefined notAtom conditionChecked chosenChecked otherChecked unbound noEqualities enough
  have interpreted : interpretFunction space dispatch
      (.expression [.symbol "if", condition, chosen, other]) (ifArrow name)
      (bindings.assign name expected) (fuel + 2) (.var name :: live) =
      RecursiveTasks.functionTail (.symbol "if")
        (interpretArgs space dispatch [condition, chosen, other]
          [.symbol "Bool", Atom.atomType, Atom.atomType] (ifRecord bindings name expected)
          (fuel + 1) (.symbol "if" :: .var name :: live)) := by
    rw [interpretFunction, head]
    simp only [List.flatMap_singleton, getFunctionArgTypes_arrowType]
    rfl
  have resultType : callReturnType (.var name) = .var name := by
    simp [callReturnType, Atom.expressionType]
  rw [evalAtom_expression (isEmptyOrError_call (by decide) _) notAtom notExpression,
    single_applicable_stream declared applicable, resultType, interpreted, arguments_from_reached]
  rfl

/-- Completed-frontier normalization is the maintained producer-completion
adapter over whole result pairs, not over their payloads alone. -/
theorem completion_reference (results : ResultSet) :
    Mettapedia.Machines.HEProducerCompletion.reference (fun result => isErrorAtom result.1)
      true results = keep results := by
  cases successes : results.filter (fun result => !isErrorAtom result.1) with
  | nil =>
      have absent : results.any (fun result => !isErrorAtom result.1) = false := by
        apply List.any_eq_false.mpr
        exact List.filter_eq_nil_iff.mp successes
      have errors := (Mettapedia.Machines.HEProducerCompletion.no_success_filters
        (fun result : ResultPair => isErrorAtom result.1) results absent).2
      simp [Mettapedia.Machines.HEProducerCompletion.reference, absent, keep, successes, errors]
  | cons first rest =>
      have member : first ∈ results.filter (fun result => !isErrorAtom result.1) := by
        rw [successes]
        exact List.mem_cons_self
      have found : results.any (fun result => !isErrorAtom result.1) = true :=
        List.any_eq_true.mpr ⟨first, (List.mem_filter.mp member).1, (List.mem_filter.mp member).2⟩
      simp [Mettapedia.Machines.HEProducerCompletion.reference, found, keep, successes]

theorem bank_completion_exact (results : ResultSet) :
    Mettapedia.Machines.HEProducerCompletion.present (fun result => isErrorAtom result.1) true
      (Mettapedia.Machines.HEProducerCompletion.collect (fun result => isErrorAtom result.1)
        true results Mettapedia.Machines.HEProducerCompletion.empty) = keep results := by
  rw [Mettapedia.Machines.HEProducerCompletion.collection_refines, completion_reference]

namespace Controls

open HEStructuralIf.Controls

def original : Atom := .expression [.symbol "producer"]
def base : Bindings := ifRecord Bindings.empty "t" listNumbers
def bool (value : Bool) : Atom := .grounded (.bool value)
def num (value : Int) : Atom := .grounded (.int value)

theorem duplicate_boolean_results_survive :
    (resume space GroundedDispatch.none original numbers strings "t" 32 []
      [(bool true, base), (bool true, base)]).map Prod.fst = [numbers, numbers] := by decide

def tagged (value : Int) : Bindings := base.assign "tag" (num value)

theorem each_result_record_survives :
    (resume space GroundedDispatch.none original numbers strings "t" 32 []
      [(bool true, tagged 1), (bool true, tagged 2)]).map (fun result => result.2.lookup "tag") =
        [some (num 1), some (num 2)] := by decide

theorem branch_errors_are_suppressed_only_at_completion :
    (resume space GroundedDispatch.none original numbers strings "t" 32 []
      [(bool true, base), (bool false, base)]).map Prod.fst = [numbers] := by decide

def nonBooleanCall : Atom := .expression [.symbol "if", num 3, numbers, strings]

/-- A non-Boolean produced value reaches invocation, not a repeated argument
type check on a newly constructed source conditional. -/
theorem non_boolean_uses_reached_invocation :
    (resume space GroundedDispatch.none original numbers strings "t" 32 []
      [(num 3, base)]).map Prod.fst = [nonBooleanCall] := by decide

theorem restarting_whole_if_changes_answer :
    (resume space GroundedDispatch.none original numbers strings "t" 32 []
      [(num 3, base)]).map Prod.fst ≠
    (evalAtom space GroundedDispatch.none nonBooleanCall listNumbers base 36 []).map Prod.fst := by decide

def payloadRecord (value : Int) : Bindings :=
  (ifRecord Bindings.empty "t" (.symbol "Number")).assign "payload" (num value)

theorem reached_bindings_determine_branch_values :
    (resume space GroundedDispatch.none original (.var "payload") (num 0) "t" 32 []
      [(bool true, payloadRecord 1), (bool true, payloadRecord 2)]).map Prod.fst =
        [num 1, num 2] := by decide

theorem dropping_records_changes_branch_values :
    (resume space GroundedDispatch.none original (.var "payload") (num 0) "t" 32 []
      [(bool true, Bindings.empty), (bool true, Bindings.empty)]).map Prod.fst ≠
        [num 1, num 2] := by decide

def producerSpace : Space :=
  ((space.add (declaration (.symbol "producer") (arrowType [] (.symbol "Bool")))).add
    (equation original (bool true))).add (equation original (bool false))

theorem computed_condition_source_result :
    (evalAtom producerSpace GroundedDispatch.none
      (.expression [.symbol "if", original, numbers, strings]) listNumbers Bindings.empty 56 []).map
        Prod.fst = [numbers] := by decide

/-- Changing the if definition changes the reached continuation. A Boolean
value alone is not authority to hard-code branch selection. -/
def overrideSpace : Space :=
  (space.add (declaration (.symbol "Override") listNumbers)).add
    (equation (.expression [.symbol "if", bool true, .var "x", .var "y"]) (.symbol "Override"))

theorem actual_if_override_is_observed :
    (resume overrideSpace GroundedDispatch.none original numbers strings "t" 32 []
      [(bool true, base)]).map Prod.fst = [.symbol "Override", numbers] := by decide

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERetainedConditional
