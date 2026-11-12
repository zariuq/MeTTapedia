import Mettapedia.Machines.Cursor.KeyFrontAdmission
import Mettapedia.Machines.Cursor.KeyFrontSelection

/-!
# Ground-front controls: boundaries, variable bands and bounded admission
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.KeyFrontControls

open KeyFrontRanges KeyFrontCompleteness KeyFrontTerms KeyFrontAdmission KeyFrontSelection
open TermPathPosting (Term subst)

def query : Term := .node [.key 10, .node [.key 20, .key 30], .key 40]

def rows : List Term :=
  [.var 0,
   .node [.var 0, .node [.key 20, .key 30], .key 40],
   .node [.key 10, .var 0, .key 40],
   .node [.key 10, .node [.var 0, .key 30], .key 40],
   .node [.key 10, .node [.key 20, .var 0], .key 40],
   .node [.key 10, .node [.key 20, .key 30], .var 0],
   query,
   .node [.key 999, .node [.key 20, .key 30], .key 40]]

theorem every_node_is_retained : rows.map (fun row => possible (front (encode query)) (encode row)) =
    [true, true, true, true, true, true, true, false] := by
  simp only [rows, query, List.map_cons, List.map_nil, encode,
    List.flatMap_cons, List.flatMap_nil]
  decide

theorem bands_and_rigid_rows_are_ordered :
    (rows.take 7).Pairwise (fun left right => encode left < encode right) := by
  have ordered : ((rows.take 7).map encode).Pairwise (· < ·) := by
    simp only [rows, query, List.take_succ_cons, List.take_zero,
      List.map_cons, List.map_nil, encode, List.flatMap_cons, List.flatMap_nil]
    decide
  simpa only [List.pairwise_map] using ordered

def wrongArity : Term := .node [.var 0, .key 999]

def replacements : List Term :=
  [query, .key 10, .node [.key 20, .key 30], .key 20, .key 30, .key 40, query]

/-- Every retained positive row has an actual structural substitution
witness, independently of the executable front selector. -/
theorem positive_rows_unify : List.Forall₂
    (fun row replacement => subst (fun _ => replacement) row = query)
    (rows.take 7) replacements := by
  simp [rows, query, replacements, subst]

theorem rigid_clash_has_no_match :
    ¬ Matches query (.node [.key 999, .node [.key 20, .key 30], .key 40]) := by
  rintro ⟨queryEnvironment, rowEnvironment, common⟩
  have first := congrArg (fun term => match term with
    | .node children => children.head?
    | _ => none) common
  simp [query, subst] at first

theorem candidates_are_not_answers :
    possible (front (encode query)) (encode wrongArity) = true ∧ ¬ Matches query wrongArity := by
  constructor
  · simp only [query, wrongArity, encode, List.flatMap_cons, List.flatMap_nil]
    decide
  · rintro ⟨queryEnvironment, rowEnvironment, common⟩
    have sizes := congrArg (fun term => match term with
      | .node children => children.length
      | _ => 0) common
    simp [query, wrongArity, subst] at sizes

def boundaryLeft : Term := .node [.node [.key 1], .key 2]
def boundaryRight : Term := .node [.node [.key 1, .key 2]]

/-- Bare preorder node labels lose expression boundaries. The actual encoded
keys retain delimiters and distinguish these two non-unifiable ground terms. -/
theorem delimiters_are_needed :
    (encode boundaryLeft).filter (fun token => kind token != 0) =
      (encode boundaryRight).filter (fun token => kind token != 0) ∧
    encode boundaryLeft ≠ encode boundaryRight := by
  simp only [boundaryLeft, boundaryRight, encode, List.flatMap_cons, List.flatMap_nil]
  decide

theorem no_common_ground_instance : ¬ Matches boundaryLeft boundaryRight := by
  rintro ⟨queryEnvironment, rowEnvironment, common⟩
  have sizes := congrArg (fun term => match term with
    | .node children => children.length
    | _ => 0) common
  simp [boundaryLeft, boundaryRight, subst] at sizes

theorem positive_count_does_not_imply_nonempty_query_band :
    earlyCount [[compound, rigid 8, varToken 0, close]] 2 = 1 ∧
      ¬ Band [compound, rigid 9] [compound, rigid 8, varToken 0, close] := by
  constructor
  · decide
  · rintro ⟨name, later, equal⟩
    have second := congrArg (fun key : Key => key[1]?) equal
    norm_num [rigid, compound] at second

def wide : Key := compound :: List.replicate 20 (rigid 7) ++ [varToken 0, close]

theorem late_variables_force_truncation :
    firstNode wide = some 21 ∧ lateCount 16 [wide] = 1 ∧
      nodes (selectedFront 16 [wide] (front wide)) = 16 := by decide

theorem no_late_rows_keep_the_long_front :
    lateCount 16 [[compound, varToken 0, close]] = 0 ∧
      selectedFront 16 [[compound, varToken 0, close]] (front wide) = front wide := by decide

theorem duplicate_rows_count_twice : earlyCount
    [[compound, varToken 0, close], [compound, varToken 0, close]] 1 = 2 := by decide

#print axioms KeyFrontTerms.encode_subst
#print axioms KeyFrontTerms.unifier_not_refuted
#print axioms KeyFrontAdmission.selected_front_complete
#print axioms KeyFrontSelection.indexed_exact

end Mettapedia.Machines.Cursor.KeyFrontControls
