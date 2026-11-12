import Mettapedia.Machines.Cursor.KeyFrontNativeFixtures

/-! # A removed boundary between adjacent variable bands -/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.KeyFrontBoundaryFixtures

open KeyFrontNativeFixtures

def changed : List Nat := labels.filter (· != 1) ++ [9]

theorem changed_observation : changed = [0, 2, 3, 4, 5, 6, 9] := by decide

def line : String := "(rr-held (" ++ String.intercalate " " ((labels.take 1).map toString) ++ ") (" ++
  String.intercalate " " (changed.map toString) ++ ") (" ++
  String.intercalate " " ((labels.drop 1).map toString) ++ "))"

theorem boundary_observation :
    line = "(rr-held (0) (0 2 3 4 5 6 9) (1 2 3 4 5 6))" := by decide

end Mettapedia.Machines.Cursor.KeyFrontBoundaryFixtures
