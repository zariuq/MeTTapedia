import Mettapedia.Languages.MeTTa.PeTTa.LibTransform

/-!
# Erasing and restoring copies is not an ordered one-occurrence take

The existing authored-library model explicitly moves surviving equal copies
to the end. A stable single deletion has the same payload bag in this control
but a different subsequent enumeration. This does not judge a native adapter
without inspecting its ordering contract.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.StoreInteraction.ReferenceOrder

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa.LibTransform (commitOne)

def a : Atom := .symbol "a"
def x : Atom := .symbol "x"
def y : Atom := .symbol "y"
def input : List Atom := [a, x, a, y]

theorem reference_moves_the_remaining_copy : commitOne input a 1 = [x, y, a] := by decide
theorem stable_deletion_keeps_relative_order : input.erase a = [x, a, y] := by decide

theorem equal_bag_is_not_equal_order :
    (commitOne input a 1).Perm (input.erase a) ∧ commitOne input a 1 ≠ input.erase a := by decide

end Mettapedia.Machines.StoreInteraction.ReferenceOrder
