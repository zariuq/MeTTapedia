import Mettapedia.Ownership.Interface
import Mettapedia.Ownership.Controls.Step

/-!
# Controls: calls

Examples admitted and refused.
-/

set_option autoImplicit false

namespace Mettapedia.Ownership

open Mettapedia.Machines.CMemory.Borrowing

namespace CallControls

def borrowedState : State :=
  { loans := [⟨1, ⟨7, 0, 16⟩, .shared, []⟩]
    allocations := [⟨7, 16, .input⟩] }

theorem read_call_admitted : passArgument borrowedState (.borrowed 8 false) (.loan 1) = some borrowedState := by decide
theorem wrong_rights_call_refused : passArgument borrowedState (.borrowed 8 true) (.loan 1) = none := by decide
theorem short_argument_refused : passArgument borrowedState (.borrowed 17 false) (.loan 1) = none := by decide
theorem wrong_argument_kind_refused : passArgument borrowedState (.borrowed 8 false) .value = none := by decide

theorem optional_view_loan_admitted :
    passArgument borrowedState (.optionalViewed false) (.loan 1) = some borrowedState := by decide
theorem optional_view_null_admitted :
    passArgument borrowedState (.optionalViewed false) .null = some borrowedState := by decide
theorem optional_view_wrong_rights_refused :
    passArgument borrowedState (.optionalViewed true) (.loan 1) = none := by decide
theorem optional_view_value_refused :
    passArgument borrowedState (.optionalViewed false) .value = none := by decide

theorem scalar_variadic_arguments_admitted :
    invoke ⟨[], false, .value, [], []⟩ initial [.value, .value] = some initial := by decide

theorem pointer_variadic_requires_read_contract :
    invoke ⟨[], false, .value, [], []⟩ borrowedState [.loan 1] = none := by decide

def transferred : State := { initial with transfers := [⟨3, 9, ⟨7, 0, 16⟩, .owned⟩] }
theorem one_owner_one_call : (passArguments transferred [.owned 8 9] [.owned 3]).isSome = true := by decide
theorem duplicated_owner_refused : passArguments transferred [.owned 8 9, .owned 8 9] [.owned 3, .owned 3] = none := by decide
theorem wrong_family_refused : passArguments transferred [.owned 8 10] [.owned 3] = none := by decide

/-- An input whose storage was released to be replaced. -/
def vacated : State :=
  { loans := initial.loans ++ [⟨1, ⟨1, 0, 1⟩, .exclusive, []⟩]
    allocations := initial.allocations ++ [⟨1, 1, .input⟩]
    transfers := [⟨1, 9, ⟨1, 0, 1⟩, .released⟩]
    suspended := [⟨1, 9, false⟩] }

theorem reallocation_makes_storage_restorable :
    (passArgument vacated (.resized 9) (.released 1)).map (·.suspended) = some [⟨1, 9, true⟩] := by decide

theorem release_keeps_storage_released :
    (passArgument vacated (.released 9) (.released 1)).map (·.suspended) = some [⟨1, 9, false⟩] := by decide

theorem reallocation_of_other_family_refused :
    passArgument vacated (.resized 8) (.released 1) = none := by decide

/-- A caller holding one exclusive loan. -/
def writableState : State :=
  { loans := [⟨1, ⟨7, 0, 16⟩, .exclusive, []⟩]
    allocations := [⟨7, 16, .input⟩] }

def oneWriter : Signature := ⟨[.borrowed 8 true], false, .value, [], []⟩
def twoWriters : Signature := ⟨[.borrowed 8 true, .borrowed 8 true], false, .value, [], []⟩
def writerAndReader : Signature := ⟨[.borrowed 8 true, .borrowed 8 false], false, .value, [], []⟩
def writerAndVariadic : Signature := ⟨[.borrowed 8 true], true, .value, [], []⟩
def twoReaders : Signature := ⟨[.borrowed 8 false, .borrowed 8 false], false, .value, [], []⟩

theorem lent_once_for_writing_admitted :
    invoke oneWriter writableState [.loan 1] = some writableState := by decide
theorem lent_twice_for_writing_refused :
    invoke twoWriters writableState [.loan 1, .loan 1] = none := by decide
theorem lent_for_writing_and_reading_refused :
    invoke writerAndReader writableState [.loan 1, .loan 1] = none := by decide
theorem lent_for_writing_and_variadic_reading_refused :
    invoke writerAndVariadic writableState [.loan 1, .loan 1] = none := by decide
theorem lent_twice_for_reading_admitted :
    invoke twoReaders borrowedState [.loan 1, .loan 1] = some borrowedState := by decide

end CallControls

end Mettapedia.Ownership
