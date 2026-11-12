import Mettapedia.Machines.Cursor.KeyFrontControls

/-!
# Key-range fixture observations

The positive occurrence labels come from the separately checked structural
rows and their unifier witnesses, not a native engine run. The serialization
used by the external fixture renderer is ordinary symbol/expression syntax.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.KeyFrontNativeFixtures

open KeyFrontControls
open KeyFrontTerms KeyFrontSelection KeyFrontRanges
open TermPathPosting (Term subst)

def labels : List Nat := ((rows.take 7).zipIdx).map Prod.snd

theorem label_observation : labels = [0, 1, 2, 3, 4, 5, 6] := by decide

def line : String := "(rr-keys (" ++ String.intercalate " " (labels.map toString) ++ "))"

theorem line_observation : line = "(rr-keys (0 1 2 3 4 5 6))" := by decide

def wideQuery : Term := .node (.key 10 :: List.replicate 20 (.key 7) ++ [.key 8])
def wideRow : Term := .node (.key 10 :: List.replicate 20 (.key 7) ++ [.var 0])

theorem late_row_unifies : subst (fun _ => .key 8) wideRow = wideQuery := by
  simp [wideQuery, wideRow, subst]

theorem variable_has_instance (term : Term) : Matches term (.var 0) := by
  refine ⟨(fun _ => .key 0), (fun _ => subst (fun _ => .key 0) term), ?_⟩
  simp [subst]

def afterWrite : List Nat := (labels.filter (· != 6)) ++ [9]

theorem updated_labels : afterWrite = [0, 1, 2, 3, 4, 5, 9] := by decide

def exports : List (String × String) :=
  [("keys", line),
   ("held-first", "(rr-held-first (taken (0) more-possible))"),
   ("held-rest", "(rr-held-rest (taken (" ++
       String.intercalate " " ((labels.drop 1).map toString) ++ ") complete))"),
   ("updated", "(rr-updated (" ++ String.intercalate " " (afterWrite.map toString) ++ "))"),
   ("held", "(rr-held (" ++ String.intercalate " " ((labels.take 1).map toString) ++ ") (" ++
       String.intercalate " " (afterWrite.map toString) ++ ") (" ++
       String.intercalate " " ((labels.drop 1).map toString) ++ "))"),
   ("wide", "(rr-wide (0 1))"), ("unknown", "(rr-unknown (0))")]

end Mettapedia.Machines.Cursor.KeyFrontNativeFixtures
