import Mettapedia.GSLT.LanguageDef.DeterministicEquations.ListData
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.Computation

/-!
# Authored natural-list membership

List traversal and short-circuiting are equations. The host only views lists
and compares unbounded natural values. Multiplicity and ordering of the input
do not change membership, and no sorting or finite-set primitive is required.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations

def naturalMembershipProgram : Program := [
  ⟨"member", "nik:nat-member", [.var "index", .var "values"],
    .expr [.sym "nik:member-view", .var "index", .expr [.sym "nik:list-view", .var "values"]]⟩,
  ⟨"member-empty", "nik:member-view", [.var "index", .sym "List:Nil"], .sym "False"⟩,
  ⟨"member-cons", "nik:member-view",
    [.var "index", .expr [.sym "List:Cons", .var "first", .var "rest"]],
    .expr [.sym "nik:member-equal", .expr [.sym "nik:nat-eq", .var "index", .var "first"],
      .var "index", .var "rest"]⟩,
  ⟨"member-found", "nik:member-equal", [.sym "True", .var "index", .var "rest"], .sym "True"⟩,
  ⟨"member-next", "nik:member-equal", [.sym "False", .var "index", .var "rest"],
    .expr [.sym "nik:nat-member", .var "index", .var "rest"]⟩]

theorem naturalMembershipProgram_leftLinear : LeftLinear naturalMembershipProgram := by
  simp [LeftLinear, naturalMembershipProgram, patternVarsList, patternVars]

private theorem member_start (index : Nat) (values : List Nat) (result : Term)
    (next : Applies naturalMembershipProgram computationalHost "nik:member-view"
      [natural index, listView (values.map natural)] result) :
    Applies naturalMembershipProgram computationalHost "nik:nat-member"
      [natural index, .list (values.map natural)] result := by
  refine Applies.equation (equation := naturalMembershipProgram[0])
    (environment := [("index", natural index), ("values", .list (values.map natural))])
    (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons ?_ .nil)) next
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
    (.primitive (by rfl) (computationalHost_list_view _))

private theorem member_cons (index first : Nat) (rest : List Nat) (result : Term)
    (next : Applies naturalMembershipProgram computationalHost "nik:member-equal"
      [boolean (decide (index = first)), natural index, .list (rest.map natural)] result) :
    Applies naturalMembershipProgram computationalHost "nik:member-view"
      [natural index, listView ((first :: rest).map natural)] result := by
  refine Applies.equation (equation := naturalMembershipProgram[2])
    (environment := [("index", natural index), ("first", natural first),
      ("rest", .list (rest.map natural))]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) next
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))
    (.primitive (by rfl) (computationalHost_binary (operation := .equal) rfl _ _ (by decide) (by decide)))

private theorem member_next (index : Nat) (rest : List Nat) (result : Term)
    (next : Applies naturalMembershipProgram computationalHost "nik:nat-member"
      [natural index, .list (rest.map natural)] result) :
    Applies naturalMembershipProgram computationalHost "nik:member-equal"
      [.sym "False", natural index, .list (rest.map natural)] result := by
  refine Applies.equation (equation := naturalMembershipProgram[4])
    (environment := [("index", natural index), ("rest", .list (rest.map natural))])
    (by rfl) (by rfl) ?_
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) next

theorem natural_membership_computes (index : Nat) (values : List Nat) :
    Applies naturalMembershipProgram computationalHost "nik:nat-member"
      [natural index, .list (values.map natural)] (boolean (decide (index ∈ values))) := by
  induction values with
  | nil => exact member_start index [] _ ⟨1, rfl⟩
  | cons first rest ih =>
      refine member_start index (first :: rest) _ (member_cons index first rest _ ?_)
      by_cases same : index = first
      · simp only [same, decide_true, boolean, List.mem_cons, true_or]
        exact ⟨1, rfl⟩
      · simpa [same, boolean] using member_next index rest _ ih

theorem natural_membership_result_exact (index : Nat) (values : List Nat) (result : Term) :
    Applies naturalMembershipProgram computationalHost "nik:nat-member"
      [natural index, .list (values.map natural)] result ↔
      result = boolean (decide (index ∈ values)) := by
  constructor
  · exact fun run => run.deterministic (natural_membership_computes index values)
  · rintro rfl
    exact natural_membership_computes index values

theorem membership_retains_unbounded_indices :
    Applies naturalMembershipProgram computationalHost "nik:nat-member"
      [natural 18446744073709551616, .list [natural 0, natural 18446744073709551616]]
      (.sym "True") := by
  simpa [boolean] using natural_membership_computes 18446744073709551616 [0, 18446744073709551616]

theorem membership_does_not_wrap_indices :
    Applies naturalMembershipProgram computationalHost "nik:nat-member"
      [natural 18446744073709551616, .list [natural 0]] (.sym "False") := by
  simpa [boolean] using natural_membership_computes 18446744073709551616 [0]

theorem membership_ignores_duplicate_occurrences :
    Applies naturalMembershipProgram computationalHost "nik:nat-member"
      [natural 2, .list [natural 0, natural 0, natural 2, natural 2]] (.sym "True") := by
  simpa [boolean] using natural_membership_computes 2 [0, 0, 2, 2]

theorem absent_member_cannot_accept :
    ¬ Applies naturalMembershipProgram computationalHost "nik:nat-member"
      [natural 1, .list [natural 0, natural 2]] (.sym "True") := by
  intro run
  have impossible := run.deterministic (natural_membership_computes 1 [0, 2])
  simp [boolean] at impossible

end Mettapedia.GSLT.LanguageDef.DeterministicEquations
