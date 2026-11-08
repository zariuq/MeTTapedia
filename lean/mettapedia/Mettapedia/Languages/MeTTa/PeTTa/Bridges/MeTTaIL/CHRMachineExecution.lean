import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRMachineSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.StrictCallKit
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.IntegerWireExecution

/-! The CHR machine source executes as `Mettapedia.Languages.CHR.Machine`:
lists. Values are plain atoms; each function is called by value. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRMachineExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Mettapedia.Languages.MeTTa.PeTTa.Eval
open Mettapedia.Languages.MeTTa.PeTTa.BridgeKit
open WireKit StrictCallKit CHRMachineSource

/-! ## Native operations at evaluated arguments -/

abbrev Returns (caller : Subst) (state : State) (code value : Atom) : Prop :=
  PureReturns runtime caller state code state value

theorem equal_returns (caller : Subst) (state : State) (left right first second : Atom)
    (one : Returns caller state left first) (two : Returns caller state right second) :
    Returns caller state (apply "==" [left, right]) (Effects.boolean (decide (first = second))) := by
  apply native_binary_call_returns runtime caller state state state state "==" left right first second _
    (by decide) (by decide) (by rw [native_raw runtime "==" 0 (by decide)]; decide)
    (by rw [native_raw runtime "==" 1 (by decide)]; decide) one two _ (by decide)
  rw [StdLib.structural_equality]
  have same : (first == second) = decide (first = second) := Bool.eq_iff_iff.mpr (by simp)
  rw [same]

theorem integer_mul_returns (caller : Subst) (state : State) (left right : Atom) (first second : Int)
    (one : Returns caller state left (integer first)) (two : Returns caller state right (integer second)) :
    Returns caller state (apply "*" [left, right]) (integer (first * second)) :=
  native_binary_call_returns runtime caller state state state state "*" left right _ _ _
    (by decide) (by decide) (by rw [native_raw runtime "*" 0 (by decide)]; decide)
    (by rw [native_raw runtime "*" 1 (by decide)]; decide) one two rfl (by decide)

theorem integer_mod_returns (caller : Subst) (state : State) (left right : Atom) (first second : Int)
    (nonzero : second ≠ 0)
    (one : Returns caller state left (integer first)) (two : Returns caller state right (integer second)) :
    Returns caller state (apply "%" [left, right]) (integer (first.fmod second)) := by
  apply native_binary_call_returns runtime caller state state state state "%" left right _ _ _
    (by decide) (by decide) (by rw [native_raw runtime "%" 0 (by decide)]; decide)
    (by rw [native_raw runtime "%" 1 (by decide)]; decide) one two _ (by decide)
  show StdLib.apply state "%" [.grounded (.int first), .grounded (.int second)] =
    .ok (state, [.grounded (.int (first.fmod second))])
  have computed : StdLib.apply state "%" [.grounded (.int first), .grounded (.int second)] =
      (if second = 0 then .error .zeroDivisor else .ok (state, [.grounded (.int (first.fmod second))])) := rfl
  rw [computed, if_neg nonzero]

theorem integer_compare_returns (caller : Subst) (state : State) (head : String) (left right : Atom)
    (first second : Int) (holds : Bool)
    (notIO : ioHead head = false) (native : StdLib.known head = true)
    (leftRaw : StdLib.rawArgument head 0 = false) (rightRaw : StdLib.rawArgument head 1 = false)
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique"])
    (computed : StdLib.apply state head [integer first, integer second] = .ok (state, [Effects.boolean holds]))
    (one : Returns caller state left (integer first)) (two : Returns caller state right (integer second)) :
    Returns caller state (apply head [left, right]) (Effects.boolean holds) := by
  exact native_binary_call_returns runtime caller state state state state head left right _ _ _ notIO native
    (by rw [native_raw runtime head 0 native]; exact leftRaw)
    (by rw [native_raw runtime head 1 native]; exact rightRaw) one two computed ordinary

theorem integer_gt_returns (caller : Subst) (state : State) (left right : Atom) (first second : Int)
    (one : Returns caller state left (integer first)) (two : Returns caller state right (integer second)) :
    Returns caller state (apply ">" [left, right]) (Effects.boolean (decide (first > second))) :=
  integer_compare_returns caller state ">" left right first second _ (by decide) (by decide) (by decide)
    (by decide) (by decide) rfl one two

theorem integer_le_returns (caller : Subst) (state : State) (left right : Atom) (first second : Int)
    (one : Returns caller state left (integer first)) (two : Returns caller state right (integer second)) :
    Returns caller state (apply "<=" [left, right]) (Effects.boolean (decide (first ≤ second))) :=
  integer_compare_returns caller state "<=" left right first second _ (by decide) (by decide) (by decide)
    (by decide) (by decide) rfl one two

theorem integer_ge_returns (caller : Subst) (state : State) (left right : Atom) (first second : Int)
    (one : Returns caller state left (integer first)) (two : Returns caller state right (integer second)) :
    Returns caller state (apply ">=" [left, right]) (Effects.boolean (decide (first ≥ second))) :=
  integer_compare_returns caller state ">=" left right first second _ (by decide) (by decide) (by decide)
    (by decide) (by decide) rfl one two

theorem not_returns (caller : Subst) (state : State) (code : Atom) (value : Bool)
    (one : Returns caller state code (Effects.boolean value)) :
    Returns caller state (apply "not" [code]) (Effects.boolean (!value)) :=
  native_unary_call_returns runtime caller state state state "not" code _ _ (by decide) (by decide)
    (by rw [native_raw runtime "not" 0 (by decide)]; decide) one (StdLib.boolean_not state value) (by decide)

theorem and_returns (caller : Subst) (state : State) (left right : Atom) (first second : Bool)
    (one : Returns caller state left (Effects.boolean first)) (two : Returns caller state right (Effects.boolean second)) :
    Returns caller state (apply "and" [left, right]) (Effects.boolean (first && second)) :=
  native_binary_call_returns runtime caller state state state state "and" left right _ _ _
    (by decide) (by decide) (by rw [native_raw runtime "and" 0 (by decide)]; decide)
    (by rw [native_raw runtime "and" 1 (by decide)]; decide) one two (StdLib.boolean_and state first second)
    (by decide)

theorem or_returns (caller : Subst) (state : State) (left right : Atom) (first second : Bool)
    (one : Returns caller state left (Effects.boolean first)) (two : Returns caller state right (Effects.boolean second)) :
    Returns caller state (apply "or" [left, right]) (Effects.boolean (first || second)) :=
  native_binary_call_returns runtime caller state state state state "or" left right _ _ _
    (by decide) (by decide) (by rw [native_raw runtime "or" 0 (by decide)]; decide)
    (by rw [native_raw runtime "or" 1 (by decide)]; decide) one two (StdLib.boolean_or state first second)
    (by decide)

theorem number_type_returns (caller : Subst) (state : State) (code : Atom) (value : Int)
    (one : Returns caller state code (integer value)) :
    Returns caller state (apply "get-type" [code]) (.symbol "Number") :=
  native_unary_call_returns runtime caller state state state "get-type" code _ _ (by decide) (by decide)
    (by rw [native_raw runtime "get-type" 0 (by decide)]; decide) one (StdLib.integer_type_is_number state value)
    (by decide)

theorem string_type_returns (caller : Subst) (state : State) (code : Atom) (value : String)
    (one : Returns caller state code (.grounded (.string value))) :
    Returns caller state (apply "get-type" [code]) (.symbol "String") :=
  native_unary_call_returns runtime caller state state state "get-type" code _ _ (by decide) (by decide)
    (by rw [native_raw runtime "get-type" 0 (by decide)]; decide) one (StdLib.string_type_is_string state value)
    (by decide)

/-! ## Lists -/

def nil : Atom := .symbol "ChrNil"
def cons (first rest : Atom) : Atom := .expression [.symbol "ChrCons", first, rest]

def listAtom : List Atom → Atom
  | [] => nil
  | first :: rest => cons first (listAtom rest)

/-- The machine's heads. -/
def machineHeads : List String :=
  ["gslt:chr-machine:append", "gslt:chr-machine:member", "gslt:chr-machine:length", "gslt:chr-machine:drop", "gslt:chr-machine:reverse", "gslt:chr-machine:lookup", "gslt:chr-machine:match", "gslt:chr-machine:match-all", "gslt:chr-machine:instantiate", "gslt:chr-machine:instantiate-all", "gslt:chr-machine:magnitude", "gslt:chr-machine:divide", "gslt:chr-machine:truncate", "gslt:chr-machine:operate", "gslt:chr-machine:integer", "gslt:chr-machine:eval", "gslt:chr-machine:holds", "gslt:chr-machine:values", "gslt:chr-machine:guard", "gslt:chr-machine:guards", "gslt:chr-machine:slot", "gslt:chr-machine:put", "gslt:chr-machine:without", "gslt:chr-machine:alive", "gslt:chr-machine:remove-picks", "gslt:chr-machine:ids", "gslt:chr-machine:occurrences-of", "gslt:chr-machine:start", "gslt:chr-machine:with-status", "gslt:chr-machine:introduce", "gslt:chr-machine:goal", "gslt:chr-machine:candidates", "gslt:chr-machine:scan", "gslt:chr-machine:fire", "gslt:chr-machine:search", "gslt:chr-machine:complete", "gslt:chr-machine:tick", "gslt:chr-machine:advance", "gslt:chr-machine:begin", "gslt:chr-machine:unit", "gslt:chr-machine:outcome"]

/-! Each head is called by value; decided once per head. -/

theorem ready_append : strictReady library "gslt:chr-machine:append" = true := by decide +kernel
theorem ready_member : strictReady library "gslt:chr-machine:member" = true := by decide +kernel
theorem ready_length : strictReady library "gslt:chr-machine:length" = true := by decide +kernel
theorem ready_drop : strictReady library "gslt:chr-machine:drop" = true := by decide +kernel
theorem ready_reverse : strictReady library "gslt:chr-machine:reverse" = true := by decide +kernel
theorem ready_lookup : strictReady library "gslt:chr-machine:lookup" = true := by decide +kernel
theorem ready_match : strictReady library "gslt:chr-machine:match" = true := by decide +kernel
theorem ready_match_all : strictReady library "gslt:chr-machine:match-all" = true := by decide +kernel
theorem ready_instantiate : strictReady library "gslt:chr-machine:instantiate" = true := by decide +kernel
theorem ready_instantiate_all : strictReady library "gslt:chr-machine:instantiate-all" = true := by decide +kernel
theorem ready_magnitude : strictReady library "gslt:chr-machine:magnitude" = true := by decide +kernel
theorem ready_divide : strictReady library "gslt:chr-machine:divide" = true := by decide +kernel
theorem ready_truncate : strictReady library "gslt:chr-machine:truncate" = true := by decide +kernel
theorem ready_operate : strictReady library "gslt:chr-machine:operate" = true := by decide +kernel
theorem ready_integer : strictReady library "gslt:chr-machine:integer" = true := by decide +kernel
theorem ready_eval : strictReady library "gslt:chr-machine:eval" = true := by decide +kernel
theorem ready_holds : strictReady library "gslt:chr-machine:holds" = true := by decide +kernel
theorem ready_values : strictReady library "gslt:chr-machine:values" = true := by decide +kernel
theorem ready_guard : strictReady library "gslt:chr-machine:guard" = true := by decide +kernel
theorem ready_guards : strictReady library "gslt:chr-machine:guards" = true := by decide +kernel
theorem ready_slot : strictReady library "gslt:chr-machine:slot" = true := by decide +kernel
theorem ready_put : strictReady library "gslt:chr-machine:put" = true := by decide +kernel
theorem ready_without : strictReady library "gslt:chr-machine:without" = true := by decide +kernel
theorem ready_alive : strictReady library "gslt:chr-machine:alive" = true := by decide +kernel
theorem ready_remove_picks : strictReady library "gslt:chr-machine:remove-picks" = true := by decide +kernel
theorem ready_ids : strictReady library "gslt:chr-machine:ids" = true := by decide +kernel
theorem ready_occurrences_of : strictReady library "gslt:chr-machine:occurrences-of" = true := by decide +kernel
theorem ready_start : strictReady library "gslt:chr-machine:start" = true := by decide +kernel
theorem ready_with_status : strictReady library "gslt:chr-machine:with-status" = true := by decide +kernel
theorem ready_introduce : strictReady library "gslt:chr-machine:introduce" = true := by decide +kernel
theorem ready_goal : strictReady library "gslt:chr-machine:goal" = true := by decide +kernel
theorem ready_candidates : strictReady library "gslt:chr-machine:candidates" = true := by decide +kernel
theorem ready_scan : strictReady library "gslt:chr-machine:scan" = true := by decide +kernel
theorem ready_fire : strictReady library "gslt:chr-machine:fire" = true := by decide +kernel
theorem ready_search : strictReady library "gslt:chr-machine:search" = true := by decide +kernel
theorem ready_complete : strictReady library "gslt:chr-machine:complete" = true := by decide +kernel
theorem ready_tick : strictReady library "gslt:chr-machine:tick" = true := by decide +kernel
theorem ready_advance : strictReady library "gslt:chr-machine:advance" = true := by decide +kernel
theorem ready_begin : strictReady library "gslt:chr-machine:begin" = true := by decide +kernel
theorem ready_unit : strictReady library "gslt:chr-machine:unit" = true := by decide +kernel
theorem ready_outcome : strictReady library "gslt:chr-machine:outcome" = true := by decide +kernel

theorem ready_of_mem {head : String} (member : head ∈ machineHeads) : strictReady library head = true := by
  simp only [machineHeads, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ready_append
  · exact ready_member
  · exact ready_length
  · exact ready_drop
  · exact ready_reverse
  · exact ready_lookup
  · exact ready_match
  · exact ready_match_all
  · exact ready_instantiate
  · exact ready_instantiate_all
  · exact ready_magnitude
  · exact ready_divide
  · exact ready_truncate
  · exact ready_operate
  · exact ready_integer
  · exact ready_eval
  · exact ready_holds
  · exact ready_values
  · exact ready_guard
  · exact ready_guards
  · exact ready_slot
  · exact ready_put
  · exact ready_without
  · exact ready_alive
  · exact ready_remove_picks
  · exact ready_ids
  · exact ready_occurrences_of
  · exact ready_start
  · exact ready_with_status
  · exact ready_introduce
  · exact ready_goal
  · exact ready_candidates
  · exact ready_scan
  · exact ready_fire
  · exact ready_search
  · exact ready_complete
  · exact ready_tick
  · exact ready_advance
  · exact ready_begin
  · exact ready_unit
  · exact ready_outcome

/-- A machine head is called by value. -/
scoped macro "machine_ready" : term => `(ready_of_mem (by decide))

/-- The machine's data constructors. -/
def machineConstructors : List String :=
  ["ChrCons", "ChrSome", "ChrBind", "ChrTuple", "ChrPair", "ChrOk", "ChrFault", "ChrNonInteger", "ChrUnbound", "ChrUninstantiated", "ChrTupleTerm", "ChrValue", "ChrVar", "ChrHead", "ChrTell", "ChrAssign", "ChrLiteral", "ChrIndex", "ChrOperation", "ChrIdentical", "ChrDistinct", "ChrCompare", "ChrSlot", "ChrOcc", "ChrKey", "ChrPick", "ChrState", "ChrSeeds", "ChrGoals", "ChrScan", "ChrSearch", "ChrAt", "ChrRule", "ChrFrame", "ChrFaulted", "ChrFired", "ChrProgram", "ChrOccurrencesOf", "ChrRun", "LangPortDoneV1", "ChrMachineResult"]

/-! Each constructor is inert data; decided once per constructor. -/

theorem inert_ChrCons : BridgeKit.inertHead runtime "ChrCons" = true := by decide +kernel
theorem inert_ChrSome : BridgeKit.inertHead runtime "ChrSome" = true := by decide +kernel
theorem inert_ChrBind : BridgeKit.inertHead runtime "ChrBind" = true := by decide +kernel
theorem inert_ChrTuple : BridgeKit.inertHead runtime "ChrTuple" = true := by decide +kernel
theorem inert_ChrPair : BridgeKit.inertHead runtime "ChrPair" = true := by decide +kernel
theorem inert_ChrOk : BridgeKit.inertHead runtime "ChrOk" = true := by decide +kernel
theorem inert_ChrFault : BridgeKit.inertHead runtime "ChrFault" = true := by decide +kernel
theorem inert_ChrNonInteger : BridgeKit.inertHead runtime "ChrNonInteger" = true := by decide +kernel
theorem inert_ChrUnbound : BridgeKit.inertHead runtime "ChrUnbound" = true := by decide +kernel
theorem inert_ChrUninstantiated : BridgeKit.inertHead runtime "ChrUninstantiated" = true := by decide +kernel
theorem inert_ChrTupleTerm : BridgeKit.inertHead runtime "ChrTupleTerm" = true := by decide +kernel
theorem inert_ChrValue : BridgeKit.inertHead runtime "ChrValue" = true := by decide +kernel
theorem inert_ChrVar : BridgeKit.inertHead runtime "ChrVar" = true := by decide +kernel
theorem inert_ChrHead : BridgeKit.inertHead runtime "ChrHead" = true := by decide +kernel
theorem inert_ChrTell : BridgeKit.inertHead runtime "ChrTell" = true := by decide +kernel
theorem inert_ChrAssign : BridgeKit.inertHead runtime "ChrAssign" = true := by decide +kernel
theorem inert_ChrLiteral : BridgeKit.inertHead runtime "ChrLiteral" = true := by decide +kernel
theorem inert_ChrIndex : BridgeKit.inertHead runtime "ChrIndex" = true := by decide +kernel
theorem inert_ChrOperation : BridgeKit.inertHead runtime "ChrOperation" = true := by decide +kernel
theorem inert_ChrIdentical : BridgeKit.inertHead runtime "ChrIdentical" = true := by decide +kernel
theorem inert_ChrDistinct : BridgeKit.inertHead runtime "ChrDistinct" = true := by decide +kernel
theorem inert_ChrCompare : BridgeKit.inertHead runtime "ChrCompare" = true := by decide +kernel
theorem inert_ChrSlot : BridgeKit.inertHead runtime "ChrSlot" = true := by decide +kernel
theorem inert_ChrOcc : BridgeKit.inertHead runtime "ChrOcc" = true := by decide +kernel
theorem inert_ChrKey : BridgeKit.inertHead runtime "ChrKey" = true := by decide +kernel
theorem inert_ChrPick : BridgeKit.inertHead runtime "ChrPick" = true := by decide +kernel
theorem inert_ChrState : BridgeKit.inertHead runtime "ChrState" = true := by decide +kernel
theorem inert_ChrSeeds : BridgeKit.inertHead runtime "ChrSeeds" = true := by decide +kernel
theorem inert_ChrGoals : BridgeKit.inertHead runtime "ChrGoals" = true := by decide +kernel
theorem inert_ChrScan : BridgeKit.inertHead runtime "ChrScan" = true := by decide +kernel
theorem inert_ChrSearch : BridgeKit.inertHead runtime "ChrSearch" = true := by decide +kernel
theorem inert_ChrAt : BridgeKit.inertHead runtime "ChrAt" = true := by decide +kernel
theorem inert_ChrRule : BridgeKit.inertHead runtime "ChrRule" = true := by decide +kernel
theorem inert_ChrFrame : BridgeKit.inertHead runtime "ChrFrame" = true := by decide +kernel
theorem inert_ChrFaulted : BridgeKit.inertHead runtime "ChrFaulted" = true := by decide +kernel
theorem inert_ChrFired : BridgeKit.inertHead runtime "ChrFired" = true := by decide +kernel
theorem inert_ChrProgram : BridgeKit.inertHead runtime "ChrProgram" = true := by decide +kernel
theorem inert_ChrOccurrencesOf : BridgeKit.inertHead runtime "ChrOccurrencesOf" = true := by decide +kernel
theorem inert_ChrRun : BridgeKit.inertHead runtime "ChrRun" = true := by decide +kernel
theorem inert_LangPortDoneV1 : BridgeKit.inertHead runtime "LangPortDoneV1" = true := by decide +kernel
theorem inert_ChrMachineResult : BridgeKit.inertHead runtime "ChrMachineResult" = true := by decide +kernel

theorem inert_of_mem {head : String} (member : head ∈ machineConstructors) :
    BridgeKit.inertHead runtime head = true := by
  simp only [machineConstructors, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact inert_ChrCons
  · exact inert_ChrSome
  · exact inert_ChrBind
  · exact inert_ChrTuple
  · exact inert_ChrPair
  · exact inert_ChrOk
  · exact inert_ChrFault
  · exact inert_ChrNonInteger
  · exact inert_ChrUnbound
  · exact inert_ChrUninstantiated
  · exact inert_ChrTupleTerm
  · exact inert_ChrValue
  · exact inert_ChrVar
  · exact inert_ChrHead
  · exact inert_ChrTell
  · exact inert_ChrAssign
  · exact inert_ChrLiteral
  · exact inert_ChrIndex
  · exact inert_ChrOperation
  · exact inert_ChrIdentical
  · exact inert_ChrDistinct
  · exact inert_ChrCompare
  · exact inert_ChrSlot
  · exact inert_ChrOcc
  · exact inert_ChrKey
  · exact inert_ChrPick
  · exact inert_ChrState
  · exact inert_ChrSeeds
  · exact inert_ChrGoals
  · exact inert_ChrScan
  · exact inert_ChrSearch
  · exact inert_ChrAt
  · exact inert_ChrRule
  · exact inert_ChrFrame
  · exact inert_ChrFaulted
  · exact inert_ChrFired
  · exact inert_ChrProgram
  · exact inert_ChrOccurrencesOf
  · exact inert_ChrRun
  · exact inert_LangPortDoneV1
  · exact inert_ChrMachineResult

theorem cons_inert : (ioHead "ChrCons" || StdLib.known "ChrCons" ||
    runtime.equations.any (·.head == "ChrCons")) = false := by decide +kernel

theorem cons_returns (caller : Subst) (state : State) (first rest : Atom) (firstValue restValue : Atom)
    (one : Returns caller state first firstValue) (two : Returns caller state rest restValue) :
    Returns caller state (.expression [.symbol "ChrCons", first, rest]) (cons firstValue restValue) :=
  constructor_returns runtime caller state "ChrCons" [first, rest] [firstValue, restValue] cons_inert
    (by decide) (.cons one (.cons two .nil))

theorem append_returns (state : State) (second : List Atom) :
    ∀ (first : List Atom) (caller : Subst) (left right : Atom),
      Returns caller state left (listAtom first) → Returns caller state right (listAtom second) →
      Returns caller state (apply "gslt:chr-machine:append" [left, right]) (listAtom (first ++ second)) := by
  intro first
  induction first with
  | nil =>
    intro caller left right one two
    apply strict_call library checked machine_ready caller state [left, right] [listAtom [], listAtom second] _
      (.cons one (.cons two .nil)) (by metta_literal; rfl)
    metta_literal
    apply pure_case_returns _ _ _ _ (listAtom []) _ _ _ rfl (bound_returns _ _ _ (by rfl))
    · metta_select [listAtom, nil, cons]
    · intro selected body selection
      metta_select [listAtom, nil, cons] at selection
      obtain ⟨rfl, rfl⟩ := selection
      exact bound_returns _ _ _ (by rfl)
  | cons x rest ih =>
    intro caller left right one two
    apply strict_call library checked machine_ready caller state [left, right] [listAtom (x :: rest), listAtom second]
      _ (.cons one (.cons two .nil)) (by metta_literal; rfl)
    metta_literal
    apply pure_case_returns _ _ _ _ (listAtom (x :: rest)) _ _ _ rfl (bound_returns _ _ _ (by rfl))
    · metta_select [listAtom, nil, cons]
    · intro selected body selection
      metta_select [listAtom, nil, cons] at selection
      obtain ⟨rfl, rfl⟩ := selection
      exact cons_returns _ _ _ _ _ _ (bound_returns _ _ _ (by rfl))
        (ih _ _ _ (bound_returns _ _ _ (by rfl)) (bound_returns _ _ _ (by rfl)))

theorem member_returns (state : State) (item : Atom) :
    ∀ (items : List Atom) (caller : Subst) (left right : Atom),
      Returns caller state left item → Returns caller state right (listAtom items) →
      Returns caller state (apply "gslt:chr-machine:member" [left, right])
        (Effects.boolean (decide (item ∈ items))) := by
  intro items
  induction items with
  | nil =>
    intro caller left right one two
    apply strict_call library checked machine_ready caller state [left, right] [item, listAtom []] _
      (.cons one (.cons two .nil)) (by metta_literal; rfl)
    metta_literal
    apply pure_case_returns _ _ _ _ (listAtom []) _ _ _ rfl (bound_returns _ _ _ (by rfl))
    · metta_select [listAtom, nil, cons]
    · intro selected body selection
      metta_select [listAtom, nil, cons] at selection
      obtain ⟨rfl, rfl⟩ := selection
      exact grounded_returns runtime _ state (.bool false)
  | cons first rest ih =>
    intro caller left right one two
    apply strict_call library checked machine_ready caller state [left, right] [item, listAtom (first :: rest)] _
      (.cons one (.cons two .nil)) (by metta_literal; rfl)
    metta_literal
    apply pure_case_returns _ _ _ _ (listAtom (first :: rest)) _ _ _ rfl (bound_returns _ _ _ (by rfl))
    · metta_select [listAtom, nil, cons]
    · intro selected body selection
      metta_select [listAtom, nil, cons] at selection
      obtain ⟨rfl, rfl⟩ := selection
      apply pure_if_returns _ _ _ _ (decide (item = first)) _ _ _
        (equal_returns _ _ _ _ _ _ (bound_returns _ _ _ (by rfl)) (bound_returns _ _ _ (by rfl)))
      by_cases same : item = first
      · simp only [same, decide_true, ↓reduceIte, List.mem_cons_self]
        exact grounded_returns runtime _ state (.bool true)
      · simp only [same, decide_false, Bool.false_eq_true, ↓reduceIte, List.mem_cons, false_or]
        exact ih _ _ _ (bound_returns _ _ _ (by rfl)) (bound_returns _ _ _ (by rfl))

theorem length_returns (state : State) :
    ∀ (items : List Atom) (caller : Subst) (code : Atom), Returns caller state code (listAtom items) →
      Returns caller state (apply "gslt:chr-machine:length" [code]) (integer items.length) := by
  intro items
  induction items with
  | nil =>
    intro caller code one
    apply strict_call library checked machine_ready caller state [code] [listAtom []] _ (.cons one .nil)
      (by metta_literal; rfl)
    metta_literal
    apply pure_case_returns _ _ _ _ (listAtom []) _ _ _ rfl (bound_returns _ _ _ (by rfl))
    · metta_select [listAtom, nil, cons]
    · intro selected body selection
      metta_select [listAtom, nil, cons] at selection
      obtain ⟨rfl, rfl⟩ := selection
      exact integer_returns runtime _ state 0
  | cons first rest ih =>
    intro caller code one
    apply strict_call library checked machine_ready caller state [code] [listAtom (first :: rest)] _ (.cons one .nil)
      (by metta_literal; rfl)
    metta_literal
    apply pure_case_returns _ _ _ _ (listAtom (first :: rest)) _ _ _ rfl (bound_returns _ _ _ (by rfl))
    · metta_select [listAtom, nil, cons]
    · intro selected body selection
      metta_select [listAtom, nil, cons] at selection
      obtain ⟨rfl, rfl⟩ := selection
      have cast : ((first :: rest).length : Int) = (1 : Int) + (rest.length : Int) := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        omega
      rw [cast]
      exact integer_add_returns runtime _ state _ _ 1 rest.length (integer_returns runtime _ state 1)
        (ih _ _ (bound_returns _ _ _ (by rfl)))

theorem drop_returns (state : State) :
    ∀ (count : Nat) (items : List Atom) (caller : Subst) (left right : Atom),
      Returns caller state left (integer count) → Returns caller state right (listAtom items) →
      Returns caller state (apply "gslt:chr-machine:drop" [left, right]) (listAtom (items.drop count)) := by
  intro count
  induction count with
  | zero =>
    intro items caller left right one two
    apply strict_call library checked machine_ready caller state [left, right] [integer 0, listAtom items] _
      (.cons one (.cons two .nil)) (by metta_literal; rfl)
    metta_literal
    apply pure_if_returns _ _ _ _ (decide (integer ((0 : Nat) : Int) = integer 0)) _ _ _
      (equal_returns _ _ _ _ _ _ (bound_returns _ _ _ (by rfl)) (integer_returns runtime _ state 0))
    simp only [List.drop_zero]
    exact bound_returns _ _ _ (by rfl)
  | succ smaller ih =>
    intro items caller left right one two
    apply strict_call library checked machine_ready caller state [left, right]
      [integer (smaller + 1 : Nat), listAtom items] _ (.cons one (.cons two .nil)) (by metta_literal; rfl)
    metta_literal
    apply pure_if_returns _ _ _ _ (decide (integer ((smaller + 1 : Nat) : Int) = integer 0)) _ _ _
      (equal_returns _ _ _ _ _ _ (bound_returns _ _ _ (by rfl)) (integer_returns runtime _ state 0))
    have different : integer ((smaller + 1 : Nat) : Int) ≠ integer 0 := by
      simp only [integer, ne_eq, Atom.grounded.injEq, OSLFCore.GroundedValue.int.injEq]
      omega
    simp only [different, decide_false, Bool.false_eq_true, ↓reduceIte]
    cases items with
    | nil =>
      apply pure_case_returns _ _ _ _ (listAtom []) _ _ _ rfl (bound_returns _ _ _ (by rfl))
      · metta_select [listAtom, nil, cons]
      · intro selected body selection
        metta_select [listAtom, nil, cons] at selection
        obtain ⟨rfl, rfl⟩ := selection
        exact Eval.symbol_returns runtime _ state "ChrNil"
    | cons first rest =>
      apply pure_case_returns _ _ _ _ (listAtom (first :: rest)) _ _ _ rfl (bound_returns _ _ _ (by rfl))
      · metta_select [listAtom, nil, cons]
      · intro selected body selection
        metta_select [listAtom, nil, cons] at selection
        obtain ⟨rfl, rfl⟩ := selection
        simp only [List.drop_succ_cons]
        apply ih rest _ _ _ _ (bound_returns _ _ _ (by rfl))
        have cast : integer (smaller : Int) = integer (((smaller + 1 : Nat) : Int) - 1) := by
          simp only [integer, Atom.grounded.injEq, OSLFCore.GroundedValue.int.injEq]
          omega
        rw [cast]
        exact integer_sub_returns runtime _ state _ _ _ 1 (bound_returns _ _ _ (by rfl))
          (integer_returns runtime _ state 1)

theorem reverse_returns (state : State) :
    ∀ (items done : List Atom) (caller : Subst) (left right : Atom),
      Returns caller state left (listAtom items) → Returns caller state right (listAtom done) →
      Returns caller state (apply "gslt:chr-machine:reverse" [left, right]) (listAtom (items.reverse ++ done)) := by
  intro items
  induction items with
  | nil =>
    intro done caller left right one two
    apply strict_call library checked machine_ready caller state [left, right] [listAtom [], listAtom done] _
      (.cons one (.cons two .nil)) (by metta_literal; rfl)
    metta_literal
    apply pure_case_returns _ _ _ _ (listAtom []) _ _ _ rfl (bound_returns _ _ _ (by rfl))
    · metta_select [listAtom, nil, cons]
    · intro selected body selection
      metta_select [listAtom, nil, cons] at selection
      obtain ⟨rfl, rfl⟩ := selection
      exact bound_returns _ _ _ (by rfl)
  | cons first rest ih =>
    intro done caller left right one two
    apply strict_call library checked machine_ready caller state [left, right] [listAtom (first :: rest), listAtom done]
      _ (.cons one (.cons two .nil)) (by metta_literal; rfl)
    metta_literal
    apply pure_case_returns _ _ _ _ (listAtom (first :: rest)) _ _ _ rfl (bound_returns _ _ _ (by rfl))
    · metta_select [listAtom, nil, cons]
    · intro selected body selection
      metta_select [listAtom, nil, cons] at selection
      obtain ⟨rfl, rfl⟩ := selection
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
      exact ih (first :: done) _ _ _ (bound_returns _ _ _ (by rfl))
        (cons_returns _ _ _ _ _ _ (bound_returns _ _ _ (by rfl)) (bound_returns _ _ _ (by rfl)))

#print axioms append_returns
#print axioms member_returns
#print axioms length_returns
#print axioms drop_returns
#print axioms reverse_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRMachineExecution
