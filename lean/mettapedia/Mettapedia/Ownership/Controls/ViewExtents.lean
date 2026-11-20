import Mettapedia.Ownership.ViewExtents
import Mettapedia.Ownership.Controls.Admission

/-!
# Controls: whole views

Examples admitted and refused.
-/

set_option autoImplicit false

namespace Mettapedia.Ownership

open Mettapedia.Machines.CMemory
open Borrowing

namespace WholeViewControls

def reader : Function :=
  ⟨"reader", ⟨[.viewed false], false, .value, [], []⟩, [7], [], .value, .done⟩

def inputState : State :=
  { initial with loans := initial.loans ++ [⟨7, ⟨7, 0, 1⟩, .shared, []⟩]
                 allocations := initial.allocations ++ [⟨7, 1, .input⟩] }

def dynamicCallee : Callable := ⟨"dynamic", ⟨[.viewed false], false, .value, [], []⟩⟩
def byteCallee : Callable := ⟨"byte", ⟨[.borrowed 1 false], false, .value, [], []⟩⟩

theorem acquire_input :
    enabled [] reader initial (.root 7 1 .shared .input 0) = some inputState := by decide

theorem dynamic_call :
    enabled [dynamicCallee] reader inputState (.invoke "dynamic" [.loan 7]) = some inputState := by decide

theorem fixed_byte_call_refused :
    enabled [byteCallee] reader inputState (.invoke "byte" [.loan 7]) = none := by decide

theorem symbolic_subextent_refused :
    enabled [] reader inputState (.restrict 7 ⟨7, 0, 0⟩) = none := by decide

theorem view_length_cannot_be_forged :
    enabled [] reader inputState (.view 7 ⟨7, 0, 1⟩ 2 false) = none := by decide

theorem concrete_zero_bytes :
    (findLoan (scaleState (viewWeight reader (fun _ => 0)) inputState) 7).map
      (fun l => l.region.count) = some 0 := by decide

theorem concrete_large_bytes :
    (findLoan (scaleState (viewWeight reader (fun _ => 4096)) inputState) 7).map
      (fun l => l.region.count) = some 4096 := by decide

theorem actual_span_call (n : Nat) :
    passArgument (scaleState (viewWeight reader (fun _ => n)) inputState) (.viewed false) (.loan 7) =
      some (scaleState (viewWeight reader (fun _ => n)) inputState) :=
  view_call_scale _ (by decide : passArgument inputState (.viewed false) (.loan 7) = some inputState)

end WholeViewControls

end Mettapedia.Ownership
