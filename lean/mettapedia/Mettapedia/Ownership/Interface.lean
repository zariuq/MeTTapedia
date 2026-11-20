import Mettapedia.Ownership.Step

/-!
# Typed resource contracts at native call boundaries

Arguments identify the actual loans and consumed owners, not just a callee
name. Transfer receipts cannot be duplicated or silently lost at return.
Parameter extents are minimum required footprints; the caller may lend a
larger allocation. Returned views are relative to a named input footprint.
Allocation policy and native implementation obligations remain separate.
-/

set_option autoImplicit false

namespace Mettapedia.Ownership

open Mettapedia.Machines.CMemory.Borrowing

inductive Parameter where
  | value
  | borrowed (count : Nat) (writing : Bool)
  | optionalBorrowed (count : Nat) (writing : Bool)
  | optionalOwned (count family : Nat)
  | static (nullable : Bool)
  | viewed (writing : Bool)
  | optionalViewed (writing : Bool)
  | owned (count family : Nat)
  | released (family : Nat)
  /-- A reallocation's source: the storage passed here moves to the call's
  owned result of `family`, unless that result is null, when nothing moved. -/
  | resized (family : Nat)
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

def receipt (s : State) (holder family : Nat) (kind : TransferKind) (count : Nat) : Option State :=
  (s.transfers.find? fun t => t.holder == holder).bind fun t =>
  (require (t.family == family && t.kind == kind && count ≤ t.region.count)).bind fun _ =>
  some { s with transfers := s.transfers.filter fun t => t.holder != holder }

/-- A reallocation takes released storage as a release does. Storage released
from an input stays suspended, now restorable: a null result moved nothing. -/
def resizeReceipt (s : State) (holder family : Nat) : Option State :=
  (s.transfers.find? fun t => t.holder == holder).bind fun t =>
  (receipt s holder family .released 0).bind fun after =>
  some { after with suspended := after.suspended.map fun x =>
    if x.root == t.region.root then { x with restorable := true } else x }

def passBorrow (s : State) (count : Nat) (writing : Bool) (id : Nat) : Option State :=
  (findLoan s id).bind fun l =>
  (require (count ≤ l.region.count)).bind fun _ =>
  (require (accessB s.loans id l.region writing)).bind fun _ =>
  some s

def passArgument (s : State) : Parameter → Argument → Option State
  | .value, .value => some s
  | .borrowed count writing, .loan id => passBorrow s count writing id
  | .optionalBorrowed count writing, .loan id
  | .optionalBorrowed count writing, .maybe id => passBorrow s count writing id
  | .optionalBorrowed _ _, .null => some s
  | .optionalOwned count family, .owned holder => receipt s holder family .owned count
  | .optionalOwned _ _, .null => some s
  | .static _, .loan id => (require (id == 0)).bind fun _ => some s
  | .static nullable, .maybe id => (require (nullable && id == 0)).bind fun _ => some s
  | .static nullable, .null => (require nullable).bind fun _ => some s
  | .viewed writing, .loan id => passBorrow s 0 writing id
  | .optionalViewed writing, .loan id
  | .optionalViewed writing, .maybe id => passBorrow s 0 writing id
  | .optionalViewed _, .null => some s
  | .owned count family, .owned holder => receipt s holder family .owned count
  | .released family, .released holder => receipt s holder family .released 0
  | .released _, .null => some s
  | .resized family, .released holder => resizeReceipt s holder family
  | .resized _, .null => some s
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

/-- The loan an argument lends, if it lends one. -/
def lentLoan : Argument → Option Nat
  | .loan id | .maybe id => some id
  | _ => none

/-- Whether a parameter receives its argument's storage for writing. -/
def lendsWriting : Parameter → Bool
  | .borrowed _ writing | .optionalBorrowed _ writing | .viewed writing
  | .optionalViewed writing => writing
  | _ => false

/-- A loan a call passes for writing is lent once: no other argument of the call,
fixed or variadic, lends the same loan. The callee was admitted with its inputs
as separate roots, so one caller storage behind two of its inputs, one of them
written, is outside its contract. Distinct loans need no such check: a valid
state already keeps an exclusive loan's storage disjoint from every other loan's. -/
def lentOnce (parameters : List Parameter) (arguments : List Argument) : Bool :=
  (parameters.zip arguments).all fun pa =>
    !lendsWriting pa.1 || match lentLoan pa.2 with
      | some id => (arguments.filterMap lentLoan).count id == 1
      | none => true

def invoke (signature : Signature) (s : State) (arguments : List Argument) : Option State :=
  (require (signature.parameters.length ≤ arguments.length)).bind fun _ =>
  (require (lentOnce signature.parameters arguments)).bind fun _ =>
  (passArguments s signature.parameters (arguments.take signature.parameters.length)).bind fun after =>
  let extra := arguments.drop signature.parameters.length
  if signature.variadicRead then passVariadic after extra
  else (require (extra.all (fun argument => argument == .value))).bind fun _ => some after

theorem valid_change_transfers (s : State) (transfers : List Transfer) :
    Valid { s with transfers := transfers } ↔ Valid s := valid_congr rfl rfl rfl

theorem valid_change_suspended (s : State) (suspended : List Suspension) :
    Valid { s with suspended := suspended } ↔ Valid s := valid_congr rfl rfl rfl

theorem receipt_preserves_valid {s after : State} {holder family count : Nat} {kind : TransferKind}
    (step : receipt s holder family kind count = some after) (valid : Valid s) : Valid after := by
  obtain ⟨t, _, rest⟩ := Option.bind_eq_some_iff.mp step
  obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp rest
  cases Option.some.inj same
  refine (valid_congr ?_ ?_ ?_).mp valid <;> rfl

theorem resizeReceipt_preserves_valid {s after : State} {holder family : Nat}
    (step : resizeReceipt s holder family = some after) (valid : Valid s) : Valid after := by
  obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp step
  obtain ⟨middle, received, same⟩ := Option.bind_eq_some_iff.mp rest
  cases Option.some.inj same
  exact (valid_change_suspended middle _).mpr (receipt_preserves_valid received valid)

theorem passArgument_preserves_valid {s after : State} {parameter : Parameter} {argument : Argument}
    (step : passArgument s parameter argument = some after) (valid : Valid s) : Valid after := by
  cases parameter <;> cases argument <;> simp only [passArgument] at step <;> try contradiction
  all_goals try exact receipt_preserves_valid step valid
  all_goals try exact resizeReceipt_preserves_valid step valid
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
  obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨middle, first, rest⟩ := Option.bind_eq_some_iff.mp rest
  have middleValid := passArguments_preserves_valid first valid
  split at rest
  · exact passVariadic_preserves_valid rest middleValid
  · obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp rest
    cases Option.some.inj same
    exact middleValid

/-- An admitted call lends each loan it passes for writing exactly once. -/
theorem invoke_lent_once {signature : Signature} {s after : State} {arguments : List Argument}
    (step : invoke signature s arguments = some after) :
    lentOnce signature.parameters arguments = true := by
  obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp step
  obtain ⟨_, once, _⟩ := Option.bind_eq_some_iff.mp rest
  exact require_some once

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
    require_access access⟩

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
    exclusive_access_disjoint valid.ordered different allowed reader⟩

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

end Mettapedia.Ownership
