import Mettapedia.GSLT.LanguageDef.DeterministicEquations.ListData
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.Computation

/-!
# An authored list append program

Traversal is performed by equations. The primitive boundary supplies only
typed list viewing and construction. Elements are passed as values without
being executed, and their order and multiplicity are retained.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations

def listAppendProgram : Program := [
  ⟨"append", "nik:list-append", [.var "left", .var "right"],
    .expr [.sym "nik:append-view", .expr [.sym "nik:list-view", .var "left"], .var "right"]⟩,
  ⟨"append-empty", "nik:append-view", [.sym "List:Nil", .var "right"], .var "right"⟩,
  ⟨"append-cons", "nik:append-view", [.expr [.sym "List:Cons", .var "first", .var "rest"], .var "right"],
    .expr [.sym "nik:list-cons", .var "first", .expr [.sym "nik:list-append", .var "rest", .var "right"]]⟩]

theorem listAppendProgram_leftLinear : LeftLinear listAppendProgram := by
  simp [LeftLinear, listAppendProgram, patternVarsList, patternVars]

private theorem append_start (left right : List Term) (result : Term)
    (next : Applies listAppendProgram computationalHost "nik:append-view"
      [listView left, .list right] result) :
    Applies listAppendProgram computationalHost "nik:list-append" [.list left, .list right] result := by
  refine Applies.equation (equation := listAppendProgram[0])
    (environment := [("left", .list left), ("right", .list right)]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil)) next
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
    (.primitive (by rfl) (computationalHost_list_view left))

private theorem append_cons (first : Term) (rest right : List Term)
    (tail : Applies listAppendProgram computationalHost "nik:list-append"
      [.list rest, .list right] (.list (rest ++ right))) :
    Applies listAppendProgram computationalHost "nik:append-view"
      [listView (first :: rest), .list right] (.list ((first :: rest) ++ right)) := by
  refine Applies.equation (equation := listAppendProgram[2])
    (environment := [("first", first), ("rest", .list rest), ("right", .list right)]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons ?_ .nil))
    (.primitive (by rfl) (computationalHost_list_cons first (rest ++ right)))
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) tail

theorem list_append_computes (left right : List Term) :
    Applies listAppendProgram computationalHost "nik:list-append"
      [.list left, .list right] (.list (left ++ right)) := by
  induction left with
  | nil => exact append_start [] right _ ⟨1, rfl⟩
  | cons first rest ih => exact append_start (first :: rest) right _ (append_cons first rest right ih)

theorem list_append_result_exact (left right : List Term) (result : Term) :
    Applies listAppendProgram computationalHost "nik:list-append" [.list left, .list right] result ↔
      result = .list (left ++ right) := by
  constructor
  · exact fun run => run.deterministic (list_append_computes left right)
  · rintro rfl
    exact list_append_computes left right

theorem append_retains_duplicates_and_order (first second : Term) :
    Applies listAppendProgram computationalHost "nik:list-append"
      [.list [first, second], .list [first]] (.list [first, second, first]) :=
  list_append_computes _ _

theorem append_does_not_execute_call_shaped_element :
    Applies listAppendProgram computationalHost "nik:list-append"
      [.list [.expr [.sym "nik:list-view", .sym "Invalid"]], .list []]
      (.list [.expr [.sym "nik:list-view", .sym "Invalid"]]) :=
  list_append_computes _ _

theorem append_cannot_drop_an_element :
    ¬ Applies listAppendProgram computationalHost "nik:list-append"
      [.list [.sym "a"], .list [.sym "b"]] (.list [.sym "a"]) := by
  intro run
  have impossible := run.deterministic (list_append_computes [.sym "a"] [.sym "b"])
  cases impossible

end Mettapedia.GSLT.LanguageDef.DeterministicEquations
