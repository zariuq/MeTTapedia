import Mettapedia.Machines.CMemory.PermissionFlow

/-!
# Controls: permission plans

Mandatory first iterations run from a recording transition: continue, break,
the mandatory body, and a refused step.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CMemory.PermissionFlow

namespace Controls

private def mark (state : List Nat) (event : Nat) : Option (List Nat) := some (state ++ [event])
private def doneAfter (event : Nat) : Plan Nat := .step event .ret

-- Continue skips the rest of its branch and reaches the latch exactly once.
example : check mark (fun _ => true)
    (resumeIteration (.branch .continueLoop (.step 2 .done) (.step 77 .done))
      (doneAfter 1) (doneAfter 3)) [] =
    some [⟨.returned, [1]⟩, ⟨.returned, [2, 77, 1]⟩] := by decide

-- Break bypasses the condition/repeat continuation.
example : check mark (fun _ => true)
    (resumeIteration .breakLoop (doneAfter 1) (doneAfter 3)) [] =
    some [⟨.returned, [3]⟩] := by decide

-- The mandatory body cannot be replaced by an optional zero-iteration path.
example : check mark (fun _ => true)
    (resumeIteration (.step 7 .done) .ret .ret) [] =
    some [⟨.returned, [7]⟩] := by decide

private def refused (_ : Nat) (_ : Unit) : Option Nat := none
example : check refused (fun _ => true)
    (resumeIteration (.step () .done) .ret .ret) 0 = none := by decide

end Controls

end Mettapedia.Machines.CMemory.PermissionFlow
