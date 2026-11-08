import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.FirstSuccessBoundary
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEReturns
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEOpenRangeTransport

/-!
# A constructed unique-record gate for instantiated HE call ranges

The gate threads the actual argument-check records before checking the
callee's declared range against its caller's expected type. It accepts any
arity and open structural formals; a typing list may contain failed
candidates, but exactly one successful record is required at each position.
Multiplicity is counted, so two equal successful records still decline.

Successful gating derives the real applicability result, the first-success
selection, and the retained entry with its selected record and callee return
policy. A materialized range is recorded as a witness; it is not permission
to discard that record or to replace the original return protocol.

This covers the all-positions-unique subcase of native range instantiation.
The native existential tests at private, non-range-sharing positions require
a separate argument-delivery and observation projection theorem. Inputs here
belong to the source applicability phase, not silently to a post-evaluation
value phase. Resource coverage is explicit when entering a checked worker.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEUniqueRangeGate

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.CompletedDelivery
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks
open Mettapedia.Languages.MeTTa.HE.Spec.Eval (SelectedTypePolicy)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

def sole {Value : Type} : List Value → Option Value
  | [value] => some value
  | _ => none

theorem sole_some_iff {Value : Type} (values : List Value) (value : Value) :
    sole values = some value ↔ values = [value] := by
  cases values with
  | nil => simp [sole]
  | cons first rest =>
      cases rest with
      | nil => simp [sole]
      | cons next rest => simp [sole]

def arguments (space : Space) (lookup : TypeLookup) (fuel : Nat) :
    List Atom → List Atom → Bindings → Option Bindings
  | [], [], incoming => some incoming
  | param :: params, arg :: args, incoming =>
      (sole (checkSuccesses (checkArgumentType space arg param incoming fuel lookup))).bind
        (arguments space lookup fuel params args)
  | _, _, _ => none

theorem arguments_length {space : Space} {lookup : TypeLookup} {fuel : Nat} :
    ∀ params args incoming selected,
      arguments space lookup fuel params args incoming = some selected → args.length = params.length
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp [arguments] at h
  | _ :: _, [], _, _, h => by simp [arguments] at h
  | param :: params, arg :: args, incoming, selected, h => by
      simp only [arguments, Option.bind_eq_some_iff] at h
      obtain ⟨middle, _, rest⟩ := h
      simp [arguments_length params args middle selected rest]

/-- The actual ordered argument loop has exactly the retained successful
record. Its diagnostic accumulator is not erased by this theorem. -/
theorem arguments_sound {space : Space} {lookup : TypeLookup} {fuel : Nat} :
    ∀ params args incoming selected,
      arguments space lookup fuel params args incoming = some selected →
      ∀ expression errors index,
        (checkIfFunctionTypeIsApplicable.checkArgLoop args params expression [incoming]
          errors space fuel index lookup).2 = [selected]
  | [], [], incoming, selected, h, _, _, _ => by
      cases Option.some.inj h
      rfl
  | [], _ :: _, _, _, h, _, _, _ => by simp [arguments] at h
  | _ :: _, [], _, _, h, _, _, _ => by simp [arguments] at h
  | param :: params, arg :: args, incoming, selected, h, expression, errors, index => by
      simp only [arguments, Option.bind_eq_some_iff] at h
      obtain ⟨middle, first, rest⟩ := h
      have step := (sole_some_iff _ middle).mp first
      rw [checkIfFunctionTypeIsApplicable.checkArgLoop]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [foldl_checks_snd _ (fun _ _ => rfl) (fun _ _ => rfl), step, List.nil_append]
      exact arguments_sound params args middle selected rest expression _ (index + 1)

structure Witness where
  record : Bindings
  rangeInstance : Atom
  deriving DecidableEq

/-- The caller's expectation is checked before the callee runs. The range
image is a witness beside, not instead of, its constraining record. -/
def prepare (space : Space) (lookup : TypeLookup) (params args : List Atom)
    (range expected : Atom) (incoming : Bindings) (fuel : Nat) : Option Witness :=
  (arguments space lookup fuel params args incoming).bind fun middle =>
    (sole (matchTypes expected range middle fuel)).map fun selected =>
      ⟨selected, selected.applyFull range fuel⟩

theorem prepare_witness {space : Space} {lookup : TypeLookup} {params args : List Atom}
    {range expected : Atom} {incoming : Bindings} {fuel : Nat} {witness : Witness}
    (ready : prepare space lookup params args range expected incoming fuel = some witness) :
    witness.rangeInstance = witness.record.applyFull range fuel := by
  simp only [prepare, Option.bind_eq_some_iff, Option.map_eq_some_iff] at ready
  obtain ⟨middle, _, selected, _, equal⟩ := ready
  cases equal
  rfl

/-- A successful source gate derives full applicability, including the
caller's expected range and the unique updated record. -/
theorem prepare_applicable {space : Space} {lookup : TypeLookup} {params args : List Atom}
    {range expected : Atom} {incoming : Bindings} {fuel : Nat} {witness : Witness}
    (ready : prepare space lookup params args range expected incoming fuel = some witness)
    (operator : Atom) :
    checkIfFunctionTypeIsApplicable (.expression (operator :: args)) (arrowType params range)
      expected space incoming (fuel + 1) lookup = .inr [witness.record] := by
  simp only [prepare, Option.bind_eq_some_iff, Option.map_eq_some_iff] at ready
  obtain ⟨middle, checked, selected, returned, equal⟩ := ready
  cases equal
  have loop := arguments_sound params args incoming middle checked (.expression (operator :: args)) [] 1
  have lengths := arguments_length params args incoming middle checked
  have returns := (sole_some_iff _ selected).mp returned
  rw [checkIfFunctionTypeIsApplicable]
  simp only [getFunctionArgTypes_arrowType, getFunctionRetType_arrowType, lengths,
    bne_self_eq_false, Bool.false_eq_true, if_false]
  rw [loop]
  simp [returns]

def policy (params : List Atom) (range : Atom) : SelectedTypePolicy :=
  ⟨arrowType params range, params, range, rfl⟩

theorem read_policy (params : List Atom) (range : Atom) :
    FirstSuccessRecursiveStrategy.readPolicy (arrowType params range) = some (policy params range) := by
  cases params with
  | nil => rfl
  | cons first rest =>
      simp [FirstSuccessRecursiveStrategy.readPolicy, arrowType, policy]
      change ((first :: rest) ++ [range]).dropLast = first :: rest
      exact List.dropLast_concat

/-- First-success selection retains the unique chosen record and does not
visit later arrow candidates. No all-candidate body equivalence is assumed. -/
theorem prepare_select {space : Space} {lookup : TypeLookup} {params args : List Atom}
    {range expected : Atom} {incoming : Bindings} {fuel : Nat} {witness : Witness}
    (ready : prepare space lookup params args range expected incoming fuel = some witness)
    (operator : Atom) (later : List Atom) :
    FirstSuccessRecursiveStrategy.select space (.expression (operator :: args)) expected incoming
      (fuel + 1) (arrowType params range :: later) lookup =
        .selected (policy params range) [witness.record] := by
  simp [FirstSuccessRecursiveStrategy.select, read_policy, prepare_applicable ready operator]

/-- The entered continuation owns the original callee range and the selected
record. In particular Undefined is not replaced by the caller's expectation. -/
theorem prepare_enter {space : Space} {lookup : TypeLookup} {params args : List Atom}
    {range expected : Atom} {incoming : Bindings} {fuel : Nat} {witness : Witness}
    (ready : prepare space lookup params args range expected incoming fuel = some witness)
    (dispatch : GroundedDispatch) (operator : Atom) (later live : List Atom) :
    FirstSuccessRecursiveStrategy.enter space dispatch
      (.functions (.expression (operator :: args)) expected incoming (fuel + 1)
        (arrowType params range :: later) live) lookup =
      (.work (.bindingAlternatives (.expression (operator :: args)) (arrowType params range)
        (callReturnType range) (fuel + 1) [witness.record] live), []) := by
  rw [FirstSuccessRecursiveStrategy.selected_enter _ _ _ _ _ _ _ _ _ _
    (prepare_select ready operator later)]
  simp [policy, callReturnType]
  rfl

theorem prepare_ready {space : Space} {lookup : TypeLookup} {params args : List Atom}
    {range expected : Atom} {incoming : Bindings} {fuel : Nat} {witness : Witness}
    (ready : prepare space lookup params args range expected incoming fuel = some witness)
    (operator : Atom) (later : List Atom)
    (covered : functionTypeCovered (.expression (operator :: args)) (arrowType params range)
      expected space incoming (fuel + 1) lookup = true) :
    FirstSuccessRecursiveStrategy.selectionReady space (.expression (operator :: args)) expected
      incoming (fuel + 1) (arrowType params range :: later) lookup = true :=
  FirstSuccessRecursiveStrategy.selectionReady_selected (read_policy params range) covered
    (prepare_applicable ready operator) later

namespace Controls

open HEOpenRangeTransport

def params : List Atom := [.symbol "Number", openList]
def args (value : Atom) : List Atom := [.grounded (.int 0), value]

theorem same_instantiated_tail_admitted :
    prepare typingSpace (rawTypeLookup typingSpace) params (args numberValue)
      openList numberList Bindings.empty 32 = some ⟨callerRecord, numberList⟩ := by decide

theorem replacement_tail_declines :
    prepare typingSpace (rawTypeLookup typingSpace) params (args stringValue)
      openList numberList Bindings.empty 32 = none := by decide

theorem caller_constraint_not_a_second_result_filter :
    prepare typingSpace (rawTypeLookup typingSpace) [] [] Atom.undefinedType
      numberList Bindings.empty 32 = some ⟨Bindings.empty, Atom.undefinedType⟩ := by decide

theorem undefined_callee_policy_retained (dispatch : GroundedDispatch) (live : List Atom) :
    FirstSuccessRecursiveStrategy.enter typingSpace dispatch
      (.functions (.expression [.symbol "opaque"]) numberList Bindings.empty 33
        [arrowType [] Atom.undefinedType] live) (rawTypeLookup typingSpace) =
      (.work (.bindingAlternatives (.expression [.symbol "opaque"])
        (arrowType [] Atom.undefinedType) Atom.undefinedType 33 [Bindings.empty] live), []) :=
  prepare_enter caller_constraint_not_a_second_result_filter dispatch (.symbol "opaque") [] live

/-- Repeated matching occurrences are not collapsed merely because their
records happen to be equal. -/
def duplicateLookup : TypeLookup := fun _ _ _ => [.symbol "Number", .symbol "Number"]

theorem duplicate_success_declines :
    prepare Space.empty duplicateLookup [.symbol "Number"] [.grounded (.int 1)]
      (.symbol "Number") Atom.undefinedType Bindings.empty 32 = none := by decide

/-- An earlier failed candidate is allowed; the single successful occurrence
is retained with its actual binding record. -/
def mixedLookup : TypeLookup := fun _ _ _ => [.symbol "String", .symbol "Number"]

theorem earlier_mismatch_does_not_block_unique_success :
    prepare Space.empty mixedLookup [.symbol "Number"] [.grounded (.int 1)]
      (.symbol "Number") Atom.undefinedType Bindings.empty 32 =
        some ⟨Bindings.empty, .symbol "Number"⟩ := by decide

theorem source_first_success_can_accept_declined_unique_gate :
    FirstSuccessRecursiveStrategy.select Space.empty
      (.expression [.symbol "f", .grounded (.int 1)]) Atom.undefinedType Bindings.empty 33
      [arrowType [.symbol "Number"] (.symbol "Number")] duplicateLookup =
        .selected (policy [.symbol "Number"] (.symbol "Number")) [Bindings.empty] := by rfl

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEUniqueRangeGate
