import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEStructuralBoundary

/-!
# Open structural formals retain their caller's type constraints

A call whose range repeats an open formal cannot discharge that range merely
by rechecking the same written formal independently at its next activation.
The existing HE applicability checker distinguishes retained caller bindings
from an empty record. The controls below exercise that checker directly.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEOpenRangeTransport

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.CompletedDelivery
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

def listType (element : Atom) : Atom := .expression [.symbol "List", element]
def openList : Atom := listType (.var "a")
def numberList : Atom := listType (.symbol "Number")
def stringList : Atom := listType (.symbol "String")
def signature : Atom := arrowType [.symbol "Number", openList] openList
def numberValue : Atom := .symbol "NList"
def stringValue : Atom := .symbol "SList"
def selfCall (value : Atom) : Atom := .expression [.symbol "range-step", .grounded (.int 0), value]
def declaration (value type : Atom) : Atom := .expression [.symbol ":", value, type]

def typingSpace : Space := Space.ofList
  [declaration numberValue numberList,
   declaration stringValue stringList,
   declaration (.symbol "range-step") signature]

def callerRecord : Bindings := Bindings.empty.assign "a" (.symbol "Number")
def independentRecord : Bindings := Bindings.empty.assign "a" (.symbol "String")

/-- The caller's Number instance rejects replacement by a String instance.
The result is stable at every larger matching budget. -/
theorem retained_formal_rejects_replacement (extra : Nat) :
    checkIfFunctionTypeIsApplicable (selfCall stringValue) signature Atom.undefinedType
      typingSpace callerRecord (32 + extra) =
        .inl [mkError (selfCall stringValue) (.badArgType 2 openList stringList)] := by
  rw [functionTypeCovered_stable (selfCall stringValue) signature Atom.undefinedType
    typingSpace callerRecord 32 extra (lookup := rawTypeLookup typingSpace) (by decide +kernel)]
  decide

/-- Rechecking the same written formal from an empty record accepts the
replacement and changes the instantiation of the return range. -/
theorem independent_formal_accepts_replacement (extra : Nat) :
    checkIfFunctionTypeIsApplicable (selfCall stringValue) signature Atom.undefinedType
      typingSpace Bindings.empty (32 + extra) = .inr [independentRecord] := by
  rw [functionTypeCovered_stable (selfCall stringValue) signature Atom.undefinedType
    typingSpace Bindings.empty 32 extra (lookup := rawTypeLookup typingSpace) (by decide +kernel)]
  decide

/-- Forwarding the original structural value retains its Number instance. -/
theorem retained_formal_accepts_forwarding (extra : Nat) :
    checkIfFunctionTypeIsApplicable (selfCall numberValue) signature Atom.undefinedType
      typingSpace callerRecord (32 + extra) = .inr [callerRecord] := by
  rw [functionTypeCovered_stable (selfCall numberValue) signature Atom.undefinedType
    typingSpace callerRecord 32 extra (lookup := rawTypeLookup typingSpace) (by decide +kernel)]
  decide

theorem same_range_syntax_different_records :
    callerRecord.applyFull openList 32 = numberList ∧
    independentRecord.applyFull openList 32 = stringList ∧
    callerRecord.applyFull openList 32 ≠ independentRecord.applyFull openList 32 := by
  decide

/-- The discrepancy already occurs at the actual argument checker, before
equation evaluation, return marking, or native representation enters. -/
theorem argument_check_loses_constraint_when_reset :
    checkArgumentType typingSpace stringValue openList callerRecord 32 = [.inl stringList] ∧
    checkArgumentType typingSpace stringValue openList Bindings.empty 32 =
      [.inr independentRecord] := by decide

/-- Keeping the caller's instantiated expected range also detects the
replacement even when a fresh argument-check record was used. -/
theorem inherited_expected_range_rejects_replacement (extra : Nat) :
    checkIfFunctionTypeIsApplicable (selfCall stringValue) signature numberList
      typingSpace Bindings.empty (32 + extra) =
        .inl [mkError (selfCall stringValue) (.badType numberList openList)] := by
  rw [functionTypeCovered_stable (selfCall stringValue) signature numberList
    typingSpace Bindings.empty 32 extra (lookup := rawTypeLookup typingSpace) (by decide +kernel)]
  decide

/-- The return evaluation itself rejects the substituted String value under
the retained Number instance, uniformly beyond the verified matching bound. -/
theorem retained_return_rejects_replacement (extra : Nat) (live : List Atom) :
    evalAtom typingSpace GroundedDispatch.none stringValue openList callerRecord
      (32 + extra + 1) live =
        [(mkError stringValue (.badType openList stringList), callerRecord)] := by
  calc
    _ = typeCast stringValue openList typingSpace callerRecord (32 + extra) :=
      evalAtom_symbol (name := "SList") (param := openList)
        (by decide) (by decide) (by decide) callerRecord (32 + extra) live
    _ = typeCast stringValue openList typingSpace callerRecord 32 :=
      typeCastCovered_stable stringValue openList typingSpace callerRecord
        32 extra (lookup := rawTypeLookup typingSpace) (by decide +kernel)
    _ = _ := by decide

/-- Under the independent activation's String instance the same return
value is accepted. Equal written ranges therefore do not justify elision. -/
theorem independent_return_accepts_replacement (extra : Nat) (live : List Atom) :
    evalAtom typingSpace GroundedDispatch.none stringValue openList independentRecord
      (32 + extra + 1) live = [(stringValue, independentRecord)] := by
  calc
    _ = typeCast stringValue openList typingSpace independentRecord (32 + extra) :=
      evalAtom_symbol (name := "SList") (param := openList)
        (by decide) (by decide) (by decide) independentRecord (32 + extra) live
    _ = typeCast stringValue openList typingSpace independentRecord 32 :=
      typeCastCovered_stable stringValue openList typingSpace independentRecord
        32 extra (lookup := rawTypeLookup typingSpace) (by decide +kernel)
    _ = _ := by decide

def nilValue : Atom := .symbol "Nil"
def nilSpace : Space := typingSpace.add (declaration nilValue openList)

theorem nil_has_one_polymorphic_row : getAtomTypes nilSpace nilValue = [openList] := by decide

/-- The same Nil and the same single row can yield the Number instance. -/
theorem nil_number_instance (extra : Nat) :
    typeCast nilValue numberList nilSpace Bindings.empty (32 + extra) =
      [(nilValue, callerRecord)] := by
  rw [typeCastCovered_stable nilValue numberList nilSpace Bindings.empty
    32 extra (lookup := rawTypeLookup nilSpace) (by decide +kernel)]
  decide

/-- The very same Nil and row can yield the String instance instead.
Uniqueness of the uninstantiated row cannot authorize range transport. -/
theorem nil_string_instance (extra : Nat) :
    typeCast nilValue stringList nilSpace Bindings.empty (32 + extra) =
      [(nilValue, independentRecord)] := by
  rw [typeCastCovered_stable nilValue stringList nilSpace Bindings.empty
    32 extra (lookup := rawTypeLookup nilSpace) (by decide +kernel)]
  decide

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEOpenRangeTransport
