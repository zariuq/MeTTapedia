import Mettapedia.GSLT.LanguageDef.OwnershipPlans

/-!
# Typed resource contracts at native call boundaries

Arguments identify the actual loans and consumed owners, not just a callee
name. Transfer receipts cannot be duplicated or silently lost at return.
Parameter extents are minimum required footprints; the caller may lend a
larger allocation. Returned views are relative to a named input footprint.
Allocation policy and native implementation obligations remain separate.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Ownership

open Mettapedia.Machines.CMemory.Borrowing

inductive Parameter where
  | value
  | borrowed (count : Nat) (writing : Bool)
  | optionalBorrowed (count : Nat) (writing : Bool)
  | optionalOwned (count family : Nat)
  | static (nullable : Bool)
  | viewed (writing : Bool)
  | owned (count family : Nat)
  | released (family : Nat)
  deriving DecidableEq, Repr, BEq, ReflBEq, LawfulBEq

inductive ReturnShape where
  | value
  | static (nullable : Bool)
  | borrowed (input offset count : Nat) (writing nullable : Bool)
  | viewed (input offset count : Nat) (writing : Bool)
  /-- A complete dynamic input span. Function admission uses its abstract unit;
  OwnershipViewExtents interprets that unit at every caller byte extent. -/
  | wholeViewed (input : Nat) (writing : Bool)
  | owned (family : Nat) (nullable : Bool)
  deriving DecidableEq, Repr, BEq, ReflBEq, LawfulBEq

structure Signature where
  parameters : List Parameter
  variadicRead : Bool
  result : ReturnShape
  fields : List (Nat × ReturnShape) := []
  records : List (Nat × ReturnShape) := []
  deriving DecidableEq, Repr, BEq, ReflBEq, LawfulBEq

structure Callable where
  name : String
  signature : Signature
  deriving DecidableEq, Repr

def receipt (s : State) (holder family : Nat) (kind : TransferKind) (count : Nat) : Option State := do
  let t ← s.transfers.find? fun t => t.holder == holder
  require (t.family == family && t.kind == kind && count ≤ t.region.count)
  pure { s with transfers := s.transfers.filter fun t => t.holder != holder }

def passBorrow (s : State) (count : Nat) (writing : Bool) (id : Nat) : Option State := do
      let l ← findLoan s id
      require (count ≤ l.region.count)
      require (decide (Access s.loans id l.region writing))
      pure s

def passArgument (s : State) : Parameter → Argument → Option State
  | .value, .value => some s
  | .borrowed count writing, .loan id => passBorrow s count writing id
  | .optionalBorrowed count writing, .loan id
  | .optionalBorrowed count writing, .maybe id => passBorrow s count writing id
  | .optionalBorrowed _ _, .null => some s
  | .optionalOwned count family, .owned holder => receipt s holder family .owned count
  | .optionalOwned _ _, .null => some s
  | .static _, .loan id => do
      require (id == 0)
      pure s
  | .static nullable, .maybe id => do
      require (nullable && id == 0)
      pure s
  | .static nullable, .null => do
      require nullable
      pure s
  | .viewed writing, .loan id => passBorrow s 0 writing id
  | .owned count family, .owned holder => receipt s holder family .owned count
  | .released family, .released holder => receipt s holder family .released 0
  | .released _, .null => some s
  | _, _ => none

def passArguments : State → List Parameter → List Argument → Option State
  | s, [], [] => some s
  | s, p :: ps, a :: args => (passArgument s p a).bind fun after => passArguments after ps args
  | _, _, _ => none

def passVariadic : State → List Argument → Option State
  | s, [] => some s
  | s, .value :: rest => passVariadic s rest
  | s, .loan id :: rest => (passArgument s (.borrowed 0 false) (.loan id)).bind fun after => passVariadic after rest
  | _, _ => none

def invoke (signature : Signature) (s : State) (arguments : List Argument) : Option State := do
  require (signature.parameters.length ≤ arguments.length)
  let after ← passArguments s signature.parameters (arguments.take signature.parameters.length)
  let extra := arguments.drop signature.parameters.length
  if signature.variadicRead then passVariadic after extra
  else do
    require (extra.all (fun argument => argument == .value))
    pure after

theorem valid_change_transfers (s : State) (transfers : List Transfer) :
    Valid { s with transfers := transfers } ↔ Valid s := Iff.rfl

theorem receipt_preserves_valid {s after : State} {holder family count : Nat} {kind : TransferKind}
    (step : receipt s holder family kind count = some after) (valid : Valid s) : Valid after := by
  obtain ⟨t, _, rest⟩ := Option.bind_eq_some_iff.mp step
  obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp rest
  cases Option.some.inj same
  exact valid

theorem passArgument_preserves_valid {s after : State} {parameter : Parameter} {argument : Argument}
    (step : passArgument s parameter argument = some after) (valid : Valid s) : Valid after := by
  cases parameter <;> cases argument <;> simp only [passArgument] at step <;> try contradiction
  all_goals try exact receipt_preserves_valid step valid
  all_goals try { cases Option.some.inj step; exact valid }
  all_goals try {
    obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp step
    cases Option.some.inj same
    exact valid }
  all_goals
    obtain ⟨l, _, rest⟩ := Option.bind_eq_some_iff.mp step
    obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp rest
    obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp rest
    cases Option.some.inj same
    exact valid

theorem passArguments_preserves_valid {s after : State} {parameters : List Parameter}
    {arguments : List Argument} (step : passArguments s parameters arguments = some after)
    (valid : Valid s) : Valid after := by
  induction parameters generalizing s arguments with
  | nil =>
      cases arguments with
      | nil => cases Option.some.inj step; exact valid
      | cons => contradiction
  | cons p ps ih =>
      cases arguments with
      | nil => contradiction
      | cons a args =>
          obtain ⟨middle, first, rest⟩ := Option.bind_eq_some_iff.mp step
          exact ih rest (passArgument_preserves_valid first valid)

theorem passVariadic_preserves_valid {s after : State} {arguments : List Argument}
    (step : passVariadic s arguments = some after) (valid : Valid s) : Valid after := by
  induction arguments generalizing s with
  | nil => cases Option.some.inj step; exact valid
  | cons a args ih =>
      cases a <;> simp only [passVariadic] at step <;> try contradiction
      · exact ih step valid
      · obtain ⟨middle, first, rest⟩ := Option.bind_eq_some_iff.mp step
        exact ih rest (passArgument_preserves_valid first valid)

theorem invoke_preserves_valid {signature : Signature} {s after : State} {arguments : List Argument}
    (step : invoke signature s arguments = some after) (valid : Valid s) : Valid after := by
  obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp step
  obtain ⟨middle, first, rest⟩ := Option.bind_eq_some_iff.mp rest
  have middleValid := passArguments_preserves_valid first valid
  split at rest
  · exact passVariadic_preserves_valid rest middleValid
  · obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp rest
    cases Option.some.inj same
    exact middleValid

/-- A typed borrowed argument supplies actual, simultaneously usable access,
including its minimum extent. Merely possessing a loan name is insufficient. -/
theorem passed_borrow_has_access {s after : State} {count id : Nat} {writing : Bool}
    (passed : passArgument s (.borrowed count writing) (.loan id) = some after) :
    ∃ l ∈ s.loans, l.id = id ∧ count ≤ l.region.count ∧ Access s.loans id l.region writing := by
  obtain ⟨l, found, rest⟩ := Option.bind_eq_some_iff.mp passed
  obtain ⟨_, extent, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨_, access, _⟩ := Option.bind_eq_some_iff.mp rest
  have mem := List.mem_of_find?_eq_some found
  have id := List.find?_some found
  exact ⟨l, mem, by simpa using id, of_decide_eq_true (require_some extent),
    of_decide_eq_true (require_some access)⟩

/-- A bounded-view call lends the actual dynamic footprint. Zero here is a
minimum-size requirement, not a fabricated allocation extent. -/
theorem passed_view_has_access {s after : State} {id : Nat} {writing : Bool}
    (passed : passArgument s (.viewed writing) (.loan id) = some after) :
    ∃ l ∈ s.loans, l.id = id ∧ Access s.loans id l.region writing := by
  have borrowed : passArgument s (.borrowed 0 writing) (.loan id) = some after := passed
  obtain ⟨l, present, identity, _, access⟩ := passed_borrow_has_access borrowed
  exact ⟨l, present, identity, access⟩

/-- Instantiate a callee's relative field/slice in the caller's allocation.
The arithmetic is over logical offsets; lowering finite-width additions must
separately establish that their bounds exclude overflow. -/
def instantiateView (input : Region) (offset count : Nat) : Region :=
  ⟨input.root, input.first + offset, count⟩

theorem instantiateView_contained {input : Region} {extent offset count : Nat}
    (parameterExtent : extent ≤ input.count) (withinParameter : offset + count ≤ extent) :
    input.Contains (instantiateView input offset count) := by
  refine ⟨rfl, ?_, ?_⟩ <;> dsimp [instantiateView, Region.finish] <;> omega

/-- Caller–callee spatial composition: every subaccess within the typed
parameter footprint is authorized in the original caller loan context. This
accounts for other live caller loans rather than assuming an empty frame. -/
theorem typed_call_access_composition {s after : State} {extent id offset count : Nat}
    {writing : Bool}
    (passed : passArgument s (.borrowed extent writing) (.loan id) = some after)
    (withinParameter : offset + count ≤ extent) :
    ∃ l ∈ s.loans, l.id = id ∧
      Access s.loans id (instantiateView l.region offset count) writing := by
  obtain ⟨l, present, identity, extentFits, allowed⟩ := passed_borrow_has_access passed
  exact ⟨l, present, identity,
    access_subfootprint regionGeometry allowed (instantiateView_contained extentFits withinParameter)⟩

/-- A mutable subaccess admitted at a call cannot overlap another usable
caller reference, including one outside the passed arguments. -/
theorem typed_call_excludes_caller_alias {s after : State} {extent id other offset count : Nat}
    {region : Region} {writing : Bool} (valid : Valid s)
    (passed : passArgument s (.borrowed extent true) (.loan id) = some after)
    (withinParameter : offset + count ≤ extent) (different : id ≠ other)
    (reader : Access s.loans other region writing) :
    ∃ l ∈ s.loans, l.id = id ∧ (instantiateView l.region offset count).Disjoint region := by
  obtain ⟨l, present, identity, allowed⟩ := typed_call_access_composition passed withinParameter
  exact ⟨l, present, identity,
    exclusive_access_disjoint valid.2.2.2.1 different allowed reader⟩

theorem consumed_receipt_cannot_be_reused {s after : State} {holder family count : Nat}
    {kind : TransferKind} (passed : receipt s holder family kind count = some after) :
    receipt after holder family kind count = none := by
  obtain ⟨t, _, rest⟩ := Option.bind_eq_some_iff.mp passed
  obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp rest
  cases Option.some.inj same
  have absent : (s.transfers.filter fun t => t.holder != holder).find?
      (fun t => t.holder == holder) = none := by
    rw [List.find?_eq_none]
    intro t mem
    have different := (List.mem_filter.mp mem).2
    simpa using different
  simp only [receipt, absent]
  rfl

/-- Substituting a callee's returned subview into the caller's input cannot
enlarge the footprint. This composes repeated calls, field paths and slices. -/
theorem returned_view_composes {caller parameter returned : Region}
    (argument : caller.Contains parameter) (result : parameter.Contains returned) :
    caller.Contains returned := Region.contains_trans argument result

namespace CallControls

def borrowedState : State :=
  { loans := [⟨1, ⟨7, 0, 16⟩, .shared, []⟩]
    allocations := [⟨7, 16, .input⟩] }

theorem read_call_admitted : passArgument borrowedState (.borrowed 8 false) (.loan 1) = some borrowedState := by decide
theorem wrong_rights_call_refused : passArgument borrowedState (.borrowed 8 true) (.loan 1) = none := by decide
theorem short_argument_refused : passArgument borrowedState (.borrowed 17 false) (.loan 1) = none := by decide
theorem wrong_argument_kind_refused : passArgument borrowedState (.borrowed 8 false) .value = none := by decide

theorem scalar_variadic_arguments_admitted :
    invoke ⟨[], false, .value, [], []⟩ initial [.value, .value] = some initial := by decide

theorem pointer_variadic_requires_read_contract :
    invoke ⟨[], false, .value, [], []⟩ borrowedState [.loan 1] = none := by decide

def transferred : State := { initial with transfers := [⟨3, 9, ⟨7, 0, 16⟩, .owned⟩] }
theorem one_owner_one_call : (passArguments transferred [.owned 8 9] [.owned 3]).isSome = true := by decide
theorem duplicated_owner_refused : passArguments transferred [.owned 8 9, .owned 8 9] [.owned 3, .owned 3] = none := by decide
theorem wrong_family_refused : passArguments transferred [.owned 8 10] [.owned 3] = none := by decide

end CallControls

end Mettapedia.GSLT.LanguageDef.Ownership
