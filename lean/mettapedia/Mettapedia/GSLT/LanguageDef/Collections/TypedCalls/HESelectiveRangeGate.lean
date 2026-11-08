import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEUniqueRangeGate

/-!
# Selective uniqueness at an instantiated HE boundary

Range-sharing positions may require a unique successful typing, while private
positions need only a first successful typing. The constructed gate retains
the actual record selected at each position and checks the caller's range
under that record. Whenever this sequential path succeeds, it is the first
complete path of the actual argument/range checker. Later equal or distinct
private candidates do not duplicate first-success execution.

The gate does not equate a local failure with source rejection: a later
candidate may permit a complete source path. Such failures decline. Nor does
it erase a private record just because the formal is disjoint from the range;
argument delivery can still observe its instance. Native record projection
and source-to-delivered-value typing remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HESelectiveRangeGate

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.CompletedDelivery
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open HEUniqueRangeGate (Witness policy)

def choose (unique : Bool) (records : List Bindings) : Option Bindings :=
  if unique then HEUniqueRangeGate.sole records else records.head?

theorem choose_prefix {unique : Bool} {records : List Bindings} {record : Bindings}
    (selected : choose unique records = some record) : ∃ later, records = record :: later := by
  cases unique with
  | false => exact List.head?_eq_some_iff.mp selected
  | true => exact ⟨[], (HEUniqueRangeGate.sole_some_iff _ _).mp selected⟩

/-- This independent enumeration is the success projection of the existing
argument checker. It keeps every candidate before first-success selection. -/
def allArguments (space : Space) (lookup : TypeLookup) (fuel : Nat) :
    List Atom → List Atom → Bindings → List Bindings
  | param :: params, arg :: args, incoming =>
      (checkSuccesses (checkArgumentType space arg param incoming fuel lookup)).flatMap
        (allArguments space lookup fuel params args)
  | _, _, incoming => [incoming]

private def advance (space : Space) (lookup : TypeLookup) (fuel index : Nat)
    (expression param arg : Atom) (acc : List Atom × List Bindings) (record : Bindings) :
    List Atom × List Bindings :=
  (checkArgumentType space arg param record fuel lookup).foldl (fun state check =>
    match check with
    | .inl type => (state.1 ++ [mkError expression (.badArgType index param type)], state.2)
    | .inr next => (state.1, state.2 ++ [next])) acc

private theorem advance_snd (space : Space) (lookup : TypeLookup) (fuel index : Nat)
    (expression param arg : Atom) (acc : List Atom × List Bindings) (record : Bindings) :
    (advance space lookup fuel index expression param arg acc record).2 = acc.2 ++
      checkSuccesses (checkArgumentType space arg param record fuel lookup) :=
  foldl_checks_snd _ (fun _ _ => rfl) (fun _ _ => rfl) _ _

private theorem advance_fold (space : Space) (lookup : TypeLookup) (fuel index : Nat)
    (expression param arg : Atom) (records : List Bindings) (acc : List Atom × List Bindings) :
    (records.foldl (advance space lookup fuel index expression param arg) acc).2 =
      acc.2 ++ records.flatMap fun record =>
        checkSuccesses (checkArgumentType space arg param record fuel lookup) := by
  induction records generalizing acc with
  | nil => simp
  | cons record records ih =>
      rw [List.foldl_cons, ih, advance_snd]
      simp only [List.flatMap_cons, List.append_assoc]

theorem allArguments_loop (space : Space) (lookup : TypeLookup) (fuel : Nat) :
    ∀ params args expression records errors index,
      (checkIfFunctionTypeIsApplicable.checkArgLoop args params expression records errors
        space fuel index lookup).2 = records.flatMap (allArguments space lookup fuel params args)
  | [], [], _, _, _, _ => by simp [checkIfFunctionTypeIsApplicable.checkArgLoop, allArguments]
  | [], _ :: _, _, _, _, _ => by simp [checkIfFunctionTypeIsApplicable.checkArgLoop, allArguments]
  | _ :: _, [], _, _, _, _ => by simp [checkIfFunctionTypeIsApplicable.checkArgLoop, allArguments]
  | param :: params, arg :: args, expression, records, errors, index => by
      rw [checkIfFunctionTypeIsApplicable.checkArgLoop,
        allArguments_loop space lookup fuel params args expression]
      change ((records.foldl (advance space lookup fuel index expression param arg)
        (errors, [])).2).flatMap _ = _
      rw [advance_fold]
      simp only [List.nil_append, List.flatMap_assoc, allArguments]

def arguments (space : Space) (lookup : TypeLookup) (fuel : Nat) :
    List Bool → List Atom → List Atom → Bindings → Option Bindings
  | [], [], [], incoming => some incoming
  | unique :: modes, param :: params, arg :: args, incoming =>
      (choose unique (checkSuccesses (checkArgumentType space arg param incoming fuel lookup))).bind
        (arguments space lookup fuel modes params args)
  | _, _, _, _ => none

theorem arguments_length {space : Space} {lookup : TypeLookup} {fuel : Nat} :
    ∀ modes params args incoming selected,
      arguments space lookup fuel modes params args incoming = some selected →
        args.length = params.length
  | [], [], [], _, _, _ => rfl
  | unique :: modes, param :: params, arg :: args, incoming, selected, accepted => by
      simp only [arguments, Option.bind_eq_some_iff] at accepted
      obtain ⟨middle, _, rest⟩ := accepted
      simp [arguments_length modes params args middle selected rest]
  | [], [], _ :: _, _, _, accepted
  | [], _ :: _, _, _, _, accepted
  | _ :: _, [], _, _, _, accepted
  | _ :: _, _ :: _, [], _, _, accepted => by simp [arguments] at accepted

theorem arguments_prefix {space : Space} {lookup : TypeLookup} {fuel : Nat} :
    ∀ modes params args incoming selected,
      arguments space lookup fuel modes params args incoming = some selected →
        ∃ later, allArguments space lookup fuel params args incoming = selected :: later
  | [], [], [], incoming, selected, accepted => by
      cases Option.some.inj accepted
      exact ⟨[], rfl⟩
  | unique :: modes, param :: params, arg :: args, incoming, selected, accepted => by
      simp only [arguments, Option.bind_eq_some_iff] at accepted
      obtain ⟨middle, first, rest⟩ := accepted
      obtain ⟨laterChoices, choices⟩ := choose_prefix first
      obtain ⟨later, answers⟩ := arguments_prefix modes params args middle selected rest
      refine ⟨later ++ laterChoices.flatMap (allArguments space lookup fuel params args), ?_⟩
      simp only [allArguments, choices, List.flatMap_cons, answers, List.cons_append]
  | [], [], _ :: _, _, _, accepted
  | [], _ :: _, _, _, _, accepted
  | _ :: _, [], _, _, _, accepted
  | _ :: _, _ :: _, [], _, _, accepted => by simp [arguments] at accepted

def prepare (space : Space) (lookup : TypeLookup) (modes : List Bool) (params args : List Atom)
    (range expected : Atom) (incoming : Bindings) (fuel : Nat) : Option Witness :=
  (arguments space lookup fuel modes params args incoming).bind fun middle =>
    (matchTypes expected range middle fuel).head?.map fun selected =>
      ⟨selected, selected.applyFull range fuel⟩

/-- Positions contributing variables to the owed range require uniqueness;
other positions select their first successful local record. This is the
source-level counterpart of the native instance-formals mask. -/
def rangeModes (params : List Atom) (range : Atom) : List Bool :=
  params.map fun formal => (atomVariables formal).any (atomVariables range).contains

def prepareRange (space : Space) (lookup : TypeLookup) (params args : List Atom)
    (range expected : Atom) (incoming : Bindings) (fuel : Nat) : Option Witness :=
  prepare space lookup (rangeModes params range) params args range expected incoming fuel

private def returnAdvance (expected range expression : Atom) (fuel : Nat)
    (acc : List Atom × List Bindings) (record : Bindings) : List Atom × List Bindings :=
  let matching := matchTypes expected range record fuel
  if matching.isEmpty then
    (acc.1 ++ [mkError expression (.badType expected range)], acc.2)
  else (acc.1, acc.2 ++ matching)

private theorem returnAdvance_snd (expected range expression : Atom) (fuel : Nat)
    (acc : List Atom × List Bindings) (record : Bindings) :
    (returnAdvance expected range expression fuel acc record).2 =
      acc.2 ++ matchTypes expected range record fuel := by
  unfold returnAdvance
  dsimp only
  split
  next empty => simp [List.isEmpty_iff.mp empty]
  next nonempty => rfl

private theorem return_fold (expected range expression : Atom) (fuel : Nat)
    (records : List Bindings) (acc : List Atom × List Bindings) :
    (records.foldl (returnAdvance expected range expression fuel) acc).2 =
      acc.2 ++ records.flatMap (fun record => matchTypes expected range record fuel) := by
  induction records generalizing acc with
  | nil => simp
  | cons record records ih =>
      rw [List.foldl_cons, ih, returnAdvance_snd]
      simp only [List.flatMap_cons, List.append_assoc]

theorem prepare_applicable_prefix {space : Space} {lookup : TypeLookup}
    {modes : List Bool} {params args : List Atom} {range expected : Atom}
    {incoming : Bindings} {fuel : Nat} {witness : Witness}
    (ready : prepare space lookup modes params args range expected incoming fuel = some witness)
    (operator : Atom) :
    ∃ later, checkIfFunctionTypeIsApplicable (.expression (operator :: args)) (arrowType params range)
      expected space incoming (fuel + 1) lookup = .inr (witness.record :: later) := by
  simp only [prepare, Option.bind_eq_some_iff, Option.map_eq_some_iff] at ready
  obtain ⟨middle, accepted, selected, returned, equality⟩ := ready
  cases equality
  obtain ⟨tail, answers⟩ := arguments_prefix modes params args incoming middle accepted
  obtain ⟨tailReturn, firstReturn⟩ := List.head?_eq_some_iff.mp returned
  have lengths := arguments_length modes params args incoming middle accepted
  have loop := allArguments_loop space lookup fuel params args (.expression (operator :: args))
    [incoming] [] 1
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, answers] at loop
  rw [checkIfFunctionTypeIsApplicable]
  simp only [getFunctionArgTypes_arrowType, getFunctionRetType_arrowType, lengths,
    bne_self_eq_false, Bool.false_eq_true, if_false, loop, List.isEmpty_cons, if_false]
  change ∃ later, (if ((middle :: tail).foldl
      (returnAdvance expected range (.expression (operator :: args)) fuel) (_, [])).2.isEmpty
    then _ else Sum.inr ((middle :: tail).foldl
      (returnAdvance expected range (.expression (operator :: args)) fuel) (_, [])).2) = _
  rw [return_fold]
  simp only [List.nil_append, List.flatMap_cons, firstReturn, List.cons_append,
    List.isEmpty_cons, Bool.false_eq_true, if_false]
  exact ⟨_, rfl⟩

theorem prepare_select {space : Space} {lookup : TypeLookup}
    {modes : List Bool} {params args : List Atom} {range expected : Atom}
    {incoming : Bindings} {fuel : Nat} {witness : Witness}
    (ready : prepare space lookup modes params args range expected incoming fuel = some witness)
    (operator : Atom) (later : List Atom) :
    FirstSuccessRecursiveStrategy.select space (.expression (operator :: args)) expected incoming
      (fuel + 1) (arrowType params range :: later) lookup =
        .selected (policy params range) [witness.record] := by
  obtain ⟨rest, applicable⟩ := prepare_applicable_prefix ready operator
  simp [FirstSuccessRecursiveStrategy.select, HEUniqueRangeGate.read_policy, applicable]

/-- Selective source admission derives the actual selected HE activation.
The formal/range sharing mask is computed from the syntax, not supplied as a
claim that the entire source call already behaves like a prepared run. -/
theorem prepareRange_select {space : Space} {lookup : TypeLookup}
    {params args : List Atom} {range expected : Atom}
    {incoming : Bindings} {fuel : Nat} {witness : Witness}
    (ready : prepareRange space lookup params args range expected incoming fuel = some witness)
    (operator : Atom) (later : List Atom) :
    FirstSuccessRecursiveStrategy.select space (.expression (operator :: args)) expected incoming
      (fuel + 1) (arrowType params range :: later) lookup =
        .selected (policy params range) [witness.record] :=
  prepare_select ready operator later

theorem prepare_witness {space : Space} {lookup : TypeLookup}
    {modes : List Bool} {params args : List Atom} {range expected : Atom}
    {incoming : Bindings} {fuel : Nat} {witness : Witness}
    (ready : prepare space lookup modes params args range expected incoming fuel = some witness) :
    witness.rangeInstance = witness.record.applyFull range fuel := by
  simp only [prepare, Option.bind_eq_some_iff, Option.map_eq_some_iff] at ready
  obtain ⟨_, _, _, _, equality⟩ := ready
  cases equality
  rfl

theorem prepare_enter {space : Space} {lookup : TypeLookup}
    {modes : List Bool} {params args : List Atom} {range expected : Atom}
    {incoming : Bindings} {fuel : Nat} {witness : Witness}
    (ready : prepare space lookup modes params args range expected incoming fuel = some witness)
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

theorem prepare_ready {space : Space} {lookup : TypeLookup}
    {modes : List Bool} {params args : List Atom} {range expected : Atom}
    {incoming : Bindings} {fuel : Nat} {witness : Witness}
    (ready : prepare space lookup modes params args range expected incoming fuel = some witness)
    (operator : Atom) (later : List Atom)
    (covered : functionTypeCovered (.expression (operator :: args)) (arrowType params range)
      expected space incoming (fuel + 1) lookup = true) :
    FirstSuccessRecursiveStrategy.selectionReady space (.expression (operator :: args)) expected
      incoming (fuel + 1) (arrowType params range :: later) lookup = true := by
  obtain ⟨rest, applicable⟩ := prepare_applicable_prefix ready operator
  exact FirstSuccessRecursiveStrategy.selectionReady_selected
    (HEUniqueRangeGate.read_policy params range) covered applicable later

/-- The concrete gate earns the existing scoped worker transition. All
caller frames and emitted results remain in place; only the reached control
changes to the selected callee/range record. -/
theorem prepare_scoped_step (dispatch : GroundedDispatch) (site : FirstSuccessBoundary.Site)
    (operator : Atom) (params args : List Atom) (range : Atom) (later : List Atom)
    (fuel : Nat) (modes : List Bool) (witness : Witness)
    (source : site.expression = .expression (operator :: args))
    (depth : site.depth = fuel + 1)
    (candidates : site.candidates = arrowType params range :: later)
    (accepted : prepare site.space site.lookup modes params args range site.expected
      site.incoming fuel = some witness)
    (covered : functionTypeCovered site.expression (arrowType params range) site.expected
      site.space site.incoming site.depth site.lookup = true) :
    (FirstSuccessRecursiveExecution.Checked.machine dispatch FirstSuccessRecursiveExecution.scopedTypes).step
      site.state = some (.silent {site.state with control := (.work (.bindingAlternatives
        site.expression (arrowType params range) (callReturnType range)
        site.depth [witness.record] site.live))}) := by
  have ready : site.ready := by
    unfold FirstSuccessBoundary.Site.ready
    rw [source, depth, candidates]
    apply prepare_ready accepted operator later
    simpa [source, depth] using covered
  rw [FirstSuccessBoundary.checked_entry_step dispatch site ready]
  have entered := prepare_enter accepted dispatch operator later site.live
  unfold FirstSuccessBoundary.expanded
  rw [source, depth, candidates, entered]
  rfl

namespace Controls

def number : Atom := .symbol "Number"
def string : Atom := .symbol "String"
def num : Atom := .grounded (.int 1)
def box (inner : Atom) : Atom := .expression [.symbol "Box", inner]
def typeVariable : Atom := .var "a"

def duplicateLookup : TypeLookup := HEUniqueRangeGate.Controls.duplicateLookup

theorem private_duplicates_are_admitted :
    prepare Space.empty duplicateLookup [false] [number] [num] number Atom.undefinedType
      Bindings.empty 32 = some ⟨Bindings.empty, number⟩ := by decide +kernel

theorem shared_duplicates_decline :
    prepare Space.empty duplicateLookup [true] [number] [num] number Atom.undefinedType
      Bindings.empty 32 = none := by decide +kernel

theorem private_duplicates_select_once :
    FirstSuccessRecursiveStrategy.select Space.empty (.expression [.symbol "f", num])
      Atom.undefinedType Bindings.empty 33 [arrowType [number] number] duplicateLookup =
        .selected (policy [number] number) [Bindings.empty] :=
  prepare_select private_duplicates_are_admitted (.symbol "f") []

def privateLookup : TypeLookup := fun _ _ _ => [box number, box string]
def privateRecord : Bindings := Bindings.empty.assign "a" number

theorem open_private_formal_keeps_its_first_instance :
    prepare Space.empty privateLookup [false] [box typeVariable] [.symbol "value"] number
      Atom.undefinedType Bindings.empty 32 = some ⟨privateRecord, number⟩ := by decide +kernel

theorem private_instance_is_not_erased :
    privateRecord.applyFull (box typeVariable) 32 = box number ∧
      Bindings.empty.applyFull (box typeVariable) 32 ≠ box number := by decide +kernel

theorem open_private_source_selection :
    FirstSuccessRecursiveStrategy.select Space.empty (.expression [.symbol "f", .symbol "value"])
      Atom.undefinedType Bindings.empty 33 [arrowType [box typeVariable] number] privateLookup =
        .selected (policy [box typeVariable] number) [privateRecord] :=
  prepare_select open_private_formal_keeps_its_first_instance (.symbol "f") []

def rangeVariable : Atom := .var "range"
def pairLookup : TypeLookup := fun _ value _ =>
  if value == .symbol "private" then [box number, box string] else [box number]
def pairRecord : Bindings := (Bindings.empty.assign "a" number).assign "range" number

theorem range_mask_distinguishes_private_formal :
    rangeModes [box typeVariable, box rangeVariable] (box rangeVariable) = [false, true] := by
  decide +kernel

theorem mixed_unique_private_instance :
    prepareRange Space.empty pairLookup [box typeVariable, box rangeVariable]
      [.symbol "private", .symbol "shared"] (box rangeVariable) Atom.undefinedType
      Bindings.empty 32 = some ⟨pairRecord, box number⟩ := by decide +kernel

def coupledLookup : TypeLookup := fun _ value _ =>
  if value == .symbol "left" then [number, string] else [string]

def coupledArgs : List Atom := [.symbol "left", .symbol "right"]
def stringRecord : Bindings := Bindings.empty.assign "a" string

/-- Choosing locally without backtracking is a safe offer, not a complete
decision procedure. A later argument can invalidate the first local choice. -/
theorem coupled_local_choice_declines :
    prepare Space.empty coupledLookup [false, false] [typeVariable, typeVariable] coupledArgs
      Atom.undefinedType Atom.undefinedType Bindings.empty 32 = none := by decide +kernel

theorem coupled_source_later_path_succeeds :
    FirstSuccessRecursiveStrategy.select Space.empty (.expression (.symbol "f" :: coupledArgs))
      Atom.undefinedType Bindings.empty 33 [arrowType [typeVariable, typeVariable] Atom.undefinedType]
      coupledLookup = .selected (policy [typeVariable, typeVariable] Atom.undefinedType) [stringRecord] := by
  rfl

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HESelectiveRangeGate
