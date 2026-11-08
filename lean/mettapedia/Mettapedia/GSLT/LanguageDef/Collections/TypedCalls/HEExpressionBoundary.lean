import Mettapedia.Machines.OrderedBoundary
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEReturns

/-!
# The full one-level HE expression boundary

Entry enumerates the actual applicable function-type rows and their binding
alternatives, then the optional tuple route. The body interprets the function
or tuple; the return boundary invokes the resulting call at the retained
range. Applicability diagnostics are emitted only when there is no tuple
route and every function-type check failed. An applicable route whose body
answers nothing does not restore diagnostics from a different failed row.

The factorization is unconditional for the existing finite all-candidate
`interpretExpression` profile. It assumes neither one type row nor closed
types, and preserves ordered duplicates. It is not a correspondence theorem
for native first-success selection or a whole evaluator implementation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEExpressionBoundary

open Mettapedia.Machines.OrderedBoundary
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

structure Request where
  atom : Atom
  expected : Atom
  bindings : Bindings
  fuel : Nat
  live : List Atom
  deriving DecidableEq

/-- A selected function or tuple interpretation and its exact return debt. -/
structure Frame where
  atom : Atom
  functionType : Option Atom
  range : Atom
  bindings : Bindings
  fuel : Nat
  live : List Atom
  deriving DecidableEq

def returnType (functionType : Atom) : Atom :=
  if getFunctionRetType functionType == some Atom.expressionType then Atom.undefinedType
  else (getFunctionRetType functionType).getD Atom.undefinedType

def functionFrame (q : Request) (fuel : Nat) (functionType : Atom) (bindings : Bindings) : Frame :=
  ⟨q.atom, some functionType, returnType functionType, bindings, fuel, q.live⟩

def tupleFrame (q : Request) (fuel : Nat) : Frame :=
  ⟨q.atom, none, q.expected, q.bindings, fuel, q.live⟩

def functionFrames (space : Space) (q : Request) (fuel : Nat) (types : List Atom) : List Frame :=
  types.flatMap fun functionType =>
    if isFunctionType functionType then
      match checkIfFunctionTypeIsApplicable q.atom functionType q.expected space q.bindings fuel with
      | .inl _ => []
      | .inr bindings => bindings.map (functionFrame q fuel functionType)
    else []

def hasNonFunction (types : List Atom) : Bool :=
  types.any fun t => !isFunctionType t || t == Atom.undefinedType

def checksFailed (space : Space) (q : Request) (fuel : Nat) (types : List Atom) : Bool :=
  types.all fun functionType =>
    if isFunctionType functionType then
      match checkIfFunctionTypeIsApplicable q.atom functionType q.expected space q.bindings fuel with
      | .inl _ => true
      | .inr _ => false
    else true

def checkErrors (space : Space) (q : Request) (fuel : Nat) (types : List Atom) : ResultSet :=
  types.flatMap fun functionType =>
    if isFunctionType functionType then
      match checkIfFunctionTypeIsApplicable q.atom functionType q.expected space q.bindings fuel with
      | .inl errors => errors.map fun error => (error, q.bindings)
      | .inr _ => []
    else []

def entries (space : Space) (q : Request) (fuel : Nat) (types : List Atom) : List Frame :=
  functionFrames space q fuel types ++ if hasNonFunction types then [tupleFrame q fuel] else []

def earlyFor (space : Space) (q : Request) (fuel : Nat) (types : List Atom) : ResultSet :=
  if !hasNonFunction types && checksFailed space q fuel types then checkErrors space q fuel types
  else []

/-- The boundary body performs argument interpretation, not the whole
expression evaluation and not final result selection. -/
def work (space : Space) (dispatch_ : GroundedDispatch) (frame : Frame) : ResultSet :=
  match frame.functionType with
  | some functionType => interpretFunction space dispatch_ frame.atom functionType frame.bindings
      frame.fuel (frame.range :: frame.live)
  | none => interpretTuple space dispatch_ frame.atom frame.bindings frame.fuel
      (frame.range :: frame.live)

def discharge (space : Space) (dispatch_ : GroundedDispatch) (frame : Frame)
    (reply : ResultPair) : ResultSet :=
  invoke space dispatch_ (.ordinary frame.range) reply.1 reply.2 frame.fuel frame.live

def expressionBoundary (space : Space) (dispatch_ : GroundedDispatch) :
    Boundary Request Frame ResultPair ResultPair where
  early := fun q => match q.fuel, q.atom with
    | n + 1, .expression (op :: _) => earlyFor space q n (getAtomTypes space op)
    | _, _ => []
  enter := fun q => match q.fuel, q.atom with
    | n + 1, .expression (op :: _) => entries space q n (getAtomTypes space op)
    | _, _ => []
  leave := discharge space dispatch_
  select := id

def selectedBoundary (space : Space) (dispatch_ : GroundedDispatch) :
    Boundary Request Frame ResultPair ResultPair :=
  { expressionBoundary space dispatch_ with select := HEReturns.keep }

theorem functionFrames_empty_of_failed (space : Space) (q : Request) (fuel : Nat)
    (types : List Atom) (failed : checksFailed space q fuel types = true) :
    functionFrames space q fuel types = [] := by
  induction types with
  | nil => rfl
  | cons functionType types ih =>
      simp only [checksFailed, List.all_cons, Bool.and_eq_true] at failed
      simp only [functionFrames, List.flatMap_cons]
      have tail := ih failed.2
      unfold functionFrames at tail
      rw [tail]
      cases functional : isFunctionType functionType with
      | false => simp
      | true =>
          cases checked : checkIfFunctionTypeIsApplicable q.atom functionType q.expected
              space q.bindings fuel with
          | inl errors => simp
          | inr bindings => simp [functional, checked] at failed

/-- The early-diagnostic gate admits no work frame. This remains true even
when individual errors happen to be represented by an empty error list. -/
theorem entries_empty_of_error_gate (space : Space) (q : Request) (fuel : Nat) (types : List Atom)
    (gate : (!hasNonFunction types && checksFailed space q fuel types) = true) :
    entries space q fuel types = [] := by
  have parts : !hasNonFunction types = true ∧ checksFailed space q fuel types = true := by
    simpa using gate
  have noTuple : hasNonFunction types = false := by simpa using parts.1
  simp [entries, noTuple, functionFrames_empty_of_failed space q fuel types parts.2]

theorem earlyFor_nonempty_no_work (space : Space) (q : Request) (fuel : Nat) (types : List Atom)
    (early : earlyFor space q fuel types ≠ []) : entries space q fuel types = [] := by
  unfold earlyFor at early
  split at early
  · exact entries_empty_of_error_gate space q fuel types ‹_›
  · exact False.elim (early rfl)

/-- Early applicability diagnostics cannot coexist with any body return. -/
theorem early_nonempty_no_returns (space : Space) (dispatch_ : GroundedDispatch) (q : Request)
    (early : (expressionBoundary space dispatch_).early q ≠ []) :
    ((expressionBoundary space dispatch_).enter q).flatMap
      (fun frame => (work space dispatch_ frame).flatMap (discharge space dispatch_ frame)) = [] := by
  rcases q with ⟨atom, expected, bindings, fuel, live⟩
  cases fuel with
  | zero => exact False.elim (early rfl)
  | succ fuel =>
      cases atom with
      | symbol _ => exact False.elim (early rfl)
      | var _ => exact False.elim (early rfl)
      | grounded _ => exact False.elim (early rfl)
      | expression atoms =>
          cases atoms with
          | nil => exact False.elim (early rfl)
          | cons op args =>
              change (entries space _ fuel (getAtomTypes space op)).flatMap _ = []
              rw [earlyFor_nonempty_no_work space _ fuel (getAtomTypes space op) early]
              rfl

def functionResults (space : Space) (dispatch_ : GroundedDispatch) (q : Request)
    (fuel : Nat) (types : List Atom) : ResultSet :=
  types.flatMap fun functionType =>
    if isFunctionType functionType then
      match checkIfFunctionTypeIsApplicable q.atom functionType q.expected space q.bindings fuel with
      | .inr bindings => bindings.flatMap fun b =>
          (interpretFunction space dispatch_ q.atom functionType b fuel
            (returnType functionType :: q.live)).flatMap fun reply =>
              invoke space dispatch_ (.ordinary (returnType functionType)) reply.1 reply.2 fuel q.live
      | .inl _ => []
    else []

def tupleResults (space : Space) (dispatch_ : GroundedDispatch) (q : Request)
    (fuel : Nat) (types : List Atom) : ResultSet :=
  if hasNonFunction types then
    (interpretTuple space dispatch_ q.atom q.bindings fuel (q.expected :: q.live)).flatMap fun reply =>
      invoke space dispatch_ (.ordinary q.expected) reply.1 reply.2 fuel q.live
  else []

theorem function_frames_run (space : Space) (dispatch_ : GroundedDispatch)
    (q : Request) (fuel : Nat) (types : List Atom) :
    (functionFrames space q fuel types).flatMap
      (fun frame => (work space dispatch_ frame).flatMap (discharge space dispatch_ frame)) =
      functionResults space dispatch_ q fuel types := by
  simp only [functionFrames, functionResults, List.flatMap_assoc]
  apply List.flatMap_congr
  intro functionType _
  cases functional : isFunctionType functionType with
  | false => simp
  | true =>
      cases checked : checkIfFunctionTypeIsApplicable q.atom functionType q.expected
          space q.bindings fuel with
      | inl errors => simp
      | inr bindings =>
          simp [List.flatMap_map, functionFrame, work]
          rfl

theorem entries_run (space : Space) (dispatch_ : GroundedDispatch)
    (q : Request) (fuel : Nat) (types : List Atom) :
    (entries space q fuel types).flatMap
      (fun frame => (work space dispatch_ frame).flatMap (discharge space dispatch_ frame)) =
      functionResults space dispatch_ q fuel types ++ tupleResults space dispatch_ q fuel types := by
  simp only [entries, List.flatMap_append, function_frames_run]
  cases h : hasNonFunction types with
  | false => simp [h, tupleResults]
  | true =>
      simp [h, tupleResults, tupleFrame, work]
      rfl

theorem nonempty_or_nil {α : Type} (xs : List α) : (if !xs.isEmpty then xs else []) = xs := by
  cases xs <;> rfl

/-- Error eligibility is decided at entry, not retroactively from an empty
batch of body answers. -/
theorem merge_early (space : Space) (dispatch_ : GroundedDispatch)
    (q : Request) (fuel : Nat) (types : List Atom) :
    earlyFor space q fuel types ++
        (functionResults space dispatch_ q fuel types ++ tupleResults space dispatch_ q fuel types) =
      let results := functionResults space dispatch_ q fuel types ++ tupleResults space dispatch_ q fuel types
      if !results.isEmpty then results
      else if !hasNonFunction types then
        if checksFailed space q fuel types then checkErrors space q fuel types else []
      else [] := by
  dsimp only
  cases nonFunction : hasNonFunction types with
  | true => simp only [earlyFor, nonFunction, Bool.not_true, Bool.false_and,
      Bool.false_eq_true, if_false, List.nil_append]; exact (nonempty_or_nil _).symm
  | false =>
      cases failed : checksFailed space q fuel types with
      | false => simp only [earlyFor, nonFunction, failed, Bool.not_false, Bool.true_and,
          Bool.false_eq_true, if_false, if_true, List.nil_append]
                 exact (nonempty_or_nil _).symm
      | true =>
          have absent := entries_empty_of_error_gate space q fuel types (by simp [nonFunction, failed])
          have outputs : functionResults space dispatch_ q fuel types ++
              tupleResults space dispatch_ q fuel types = [] := by
            rw [← entries_run, absent]
            rfl
          simp [earlyFor, nonFunction, failed, outputs]

/-- An unconditional factorization of the actual one-level all-candidate
interpreter. Each body stage is a proper constituent interpreter operation. -/
theorem run_eq_interpretExpression (space : Space) (dispatch_ : GroundedDispatch) (q : Request) :
    (expressionBoundary space dispatch_).run (work space dispatch_) q =
      interpretExpression space dispatch_ q.atom q.expected q.bindings q.fuel q.live := by
  rcases q with ⟨atom, expected, bindings, fuel, live⟩
  cases fuel with
  | zero => rfl
  | succ fuel =>
      cases atom with
      | symbol _ => rfl
      | var _ => rfl
      | grounded _ => rfl
      | expression atoms =>
          cases atoms with
          | nil => rfl
          | cons op args =>
              change earlyFor space _ fuel (getAtomTypes space op) ++
                (entries space _ fuel (getAtomTypes space op)).flatMap
                  (fun frame => (work space dispatch_ frame).flatMap (discharge space dispatch_ frame)) = _
              rw [entries_run, merge_early]
              rfl

theorem selected_eq_keep (space : Space) (dispatch_ : GroundedDispatch) (q : Request) :
    (selectedBoundary space dispatch_).run (work space dispatch_) q =
      HEReturns.keep (interpretExpression space dispatch_ q.atom q.expected q.bindings q.fuel q.live) := by
  change HEReturns.keep ((expressionBoundary space dispatch_).run (work space dispatch_) q) = _
  rw [run_eq_interpretExpression]

/-- The outer evaluator's exact case split is retained: held values and
leaf casts bypass expression entry, while its expression branch uses the
ordered selected boundary. -/
theorem evalAtom_boundary_step (space : Space) (dispatch_ : GroundedDispatch)
    (atom expected : Atom) (bindings : Bindings) (fuel : Nat) (live : List Atom) :
    evalAtom space dispatch_ atom expected bindings (fuel + 1) live =
      if isEmptyOrError atom then [(atom, bindings)]
      else if expected == Atom.atomType || expected == getMetaType atom ||
          getMetaType atom == Atom.variableType then [(atom, bindings)]
      else if getMetaType atom == Atom.symbolType || getMetaType atom == Atom.groundedType ||
          atom == Atom.unit then typeCast atom expected space bindings fuel
      else if getMetaType atom == Atom.expressionType then
        (selectedBoundary space dispatch_).run (work space dispatch_)
          ⟨atom, expected, bindings, fuel, live⟩
      else [(atom, bindings)] := by
  rw [evalAtom]
  simp only [selected_eq_keep, HEReturns.keep]

namespace Controls

def number : Atom := .symbol "Number"
def string : Atom := .symbol "String"
def nullaryNumber : Atom := .expression [.symbol "->", number]
def nullaryString : Atom := .expression [.symbol "->", string]
def unaryNumber : Atom := .expression [.symbol "->", number, number]
def annotate (type_ : Atom) : Atom := .expression [.symbol ":", .symbol "f", type_]

def call : Request := ⟨.expression [.symbol "f"], Atom.undefinedType, Bindings.empty, 2, []⟩

def mixedSpace : Space := Space.ofList [annotate unaryNumber, annotate nullaryNumber]

/-- The first row fails, the second is applicable, and its body has no
answer at this finite budget. Failed-row diagnostics must stay suppressed. -/
theorem failed_plus_applicable_empty :
    checkErrors mixedSpace call 1 (getAtomTypes mixedSpace (.symbol "f")) ≠ [] ∧
      functionFrames mixedSpace call 1 (getAtomTypes mixedSpace (.symbol "f")) ≠ [] ∧
      (expressionBoundary mixedSpace GroundedDispatch.none).run
        (work mixedSpace GroundedDispatch.none) call = [] := by
  cbv
  simp

/-- Emitting every failed check when body output is empty would change the
actual interpreter result. Entry applicability, not output existence, gates
the diagnostics. -/
theorem output_emptiness_does_not_license_errors :
    functionResults mixedSpace GroundedDispatch.none call 1
        (getAtomTypes mixedSpace (.symbol "f")) = [] ∧
      earlyFor mixedSpace call 1 (getAtomTypes mixedSpace (.symbol "f")) = [] ∧
      checkErrors mixedSpace call 1 (getAtomTypes mixedSpace (.symbol "f")) ≠ [] := by
  cbv
  simp

def failedSpace : Space := Space.ofList [annotate unaryNumber]

theorem all_failed_reports_actual_error :
    (expressionBoundary failedSpace GroundedDispatch.none).run
        (work failedSpace GroundedDispatch.none) call =
      [(mkError call.atom .incorrectNumberOfArguments, Bindings.empty)] := by
  cbv

def orderedSpace : Space := Space.ofList
  [annotate nullaryNumber, annotate nullaryNumber, annotate nullaryString]

/-- Actual declaration occurrences remain ordered entry frames, including
the duplicate Number candidate. No conversion to a set or bag occurs. -/
theorem ordered_duplicate_candidates :
    ((expressionBoundary orderedSpace GroundedDispatch.none).enter call).map Frame.range =
      [number, number, string] := by cbv

theorem no_first_candidate_collapse :
    ((expressionBoundary orderedSpace GroundedDispatch.none).enter call).length = 3 ∧
      ((expressionBoundary orderedSpace GroundedDispatch.none).enter call).length ≠ 1 := by
  cbv

def tupleRequest : Request :=
  ⟨.expression [.symbol "u", .grounded (.int 7)], Atom.undefinedType, Bindings.empty, 8, []⟩

theorem actual_tuple_entry :
    (expressionBoundary Space.empty GroundedDispatch.none).enter tupleRequest =
      [tupleFrame tupleRequest 7] := by cbv

theorem actual_tuple_answer :
    (expressionBoundary Space.empty GroundedDispatch.none).run
        (work Space.empty GroundedDispatch.none) tupleRequest =
      [(tupleRequest.atom, Bindings.empty)] := by cbv

/-- A tuple route suppresses failed function-type diagnostics even when its
own finite interpretation has no result. -/
def tupleAndFailure : Space := Space.ofList [annotate unaryNumber, annotate (.symbol "Data")]

theorem tuple_route_suppresses_check_errors :
    earlyFor tupleAndFailure call 1 (getAtomTypes tupleAndFailure (.symbol "f")) = [] ∧
      checkErrors tupleAndFailure call 1 (getAtomTypes tupleAndFailure (.symbol "f")) ≠ [] := by
  cbv
  simp

/-- Zero fuel yields no boundary work; it is not a completed type error. -/
theorem zero_fuel_no_early_error :
    (expressionBoundary failedSpace GroundedDispatch.none).run
        (work failedSpace GroundedDispatch.none) { call with fuel := 0 } = [] := rfl

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEExpressionBoundary
