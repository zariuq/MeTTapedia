import Mettapedia.GSLT.LanguageDef.DeterministicEquations.NaturalMembershipProgram
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.ProgramSuffix

/-!
# Authored removal of every selected natural-list occurrence

Membership and filtering are equation computations. Every matching occurrence
is removed; order and multiplicity of retained entries are preserved.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations

def naturalDifferenceEquations : Program := [
  ⟨"difference", "nik:nat-difference", [.var "source", .var "removed"],
    .expr [.sym "nik:difference-view", .expr [.sym "nik:list-view", .var "source"], .var "removed"]⟩,
  ⟨"difference-empty", "nik:difference-view", [.sym "List:Nil", .var "removed"], .list []⟩,
  ⟨"difference-cons", "nik:difference-view",
    [.expr [.sym "List:Cons", .var "first", .var "rest"], .var "removed"],
    .expr [.sym "nik:difference-keep", .expr [.sym "nik:nat-member", .var "first", .var "removed"],
      .var "first", .expr [.sym "nik:nat-difference", .var "rest", .var "removed"]]⟩,
  ⟨"difference-remove", "nik:difference-keep", [.sym "True", .var "first", .var "rest"], .var "rest"⟩,
  ⟨"difference-keep", "nik:difference-keep", [.sym "False", .var "first", .var "rest"],
    .expr [.sym "nik:list-cons", .var "first", .var "rest"]⟩]

def naturalDifferenceProgram : Program := naturalMembershipProgram ++ naturalDifferenceEquations

theorem naturalDifferenceProgram_leftLinear : LeftLinear naturalDifferenceProgram := by
  simp only [naturalDifferenceProgram, LeftLinear, List.mem_append, or_imp, forall_and]
  refine ⟨naturalMembershipProgram_leftLinear, ?_⟩
  simp [naturalDifferenceEquations, patternVarsList, patternVars]

private theorem membership_reused (index : Nat) (values : List Nat) :
    Applies naturalDifferenceProgram computationalHost "nik:nat-member"
      [natural index, .list (values.map natural)] (boolean (decide (index ∈ values))) :=
  (Applies.append_iff naturalMembershipProgram naturalDifferenceEquations computationalHost
    (by decide) "nik:nat-member" (by decide) _ _).mpr (natural_membership_computes index values)

private theorem difference_start (source removed : List Nat) (result : Term)
    (next : Applies naturalDifferenceProgram computationalHost "nik:difference-view"
      [listView (source.map natural), .list (removed.map natural)] result) :
    Applies naturalDifferenceProgram computationalHost "nik:nat-difference"
      [.list (source.map natural), .list (removed.map natural)] result := by
  refine Applies.equation (equation := naturalDifferenceProgram[5])
    (environment := [("source", .list (source.map natural)), ("removed", .list (removed.map natural))])
    (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil)) next
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
    (.primitive (by rfl) (computationalHost_list_view _))

private theorem keep_computes (member : Bool) (first : Nat) (rest : List Nat) :
    Applies naturalDifferenceProgram computationalHost "nik:difference-keep"
      [boolean member, natural first, .list (rest.map natural)]
      (.list ((if member then rest else first :: rest).map natural)) := by
  cases member with
  | true => exact ⟨1, rfl⟩
  | false =>
      refine Applies.equation (equation := naturalDifferenceProgram[9])
        (environment := [("first", natural first), ("rest", .list (rest.map natural))]) (by rfl) (by rfl) ?_
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))
        (.primitive (by rfl) (computationalHost_list_cons _ _))

private theorem difference_cons (first : Nat) (rest removed result : List Nat)
    (tail : Applies naturalDifferenceProgram computationalHost "nik:nat-difference"
      [.list (rest.map natural), .list (removed.map natural)] (.list (result.map natural))) :
    Applies naturalDifferenceProgram computationalHost "nik:difference-view"
      [listView ((first :: rest).map natural), .list (removed.map natural)]
      (.list ((if decide (first ∈ removed) then result else first :: result).map natural)) := by
  refine Applies.equation (equation := naturalDifferenceProgram[7])
    (environment := [("first", natural first), ("rest", .list (rest.map natural)),
      ("removed", .list (removed.map natural))]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) (.cons ?_ .nil)))
    (keep_computes _ _ _)
  · exact Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (membership_reused first removed)
  · exact Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) tail

theorem natural_difference_computes (source removed : List Nat) :
    Applies naturalDifferenceProgram computationalHost "nik:nat-difference"
      [.list (source.map natural), .list (removed.map natural)]
      (.list ((source.filter fun index => !removed.contains index).map natural)) := by
  induction source with
  | nil => exact difference_start [] removed _ ⟨1, rfl⟩
  | cons first rest ih =>
      apply difference_start
      by_cases member : first ∈ removed <;>
        simpa [member] using difference_cons first rest removed _ ih

theorem natural_difference_result_exact (source removed : List Nat) (result : Term) :
    Applies naturalDifferenceProgram computationalHost "nik:nat-difference"
      [.list (source.map natural), .list (removed.map natural)] result ↔
      result = .list ((source.filter fun index => !removed.contains index).map natural) := by
  constructor
  · exact fun run => run.deterministic (natural_difference_computes source removed)
  · rintro rfl; exact natural_difference_computes source removed

namespace NaturalDifferenceControls

theorem remove_all_repeated_selected_values :
    Applies naturalDifferenceProgram computationalHost "nik:nat-difference"
      [.list ([0, 1, 0, 2, 1].map natural), .list [natural 0]] (.list ([1, 2, 1].map natural)) :=
  natural_difference_computes [0, 1, 0, 2, 1] [0]

theorem removal_does_not_deduplicate_survivors :
    ¬ Applies naturalDifferenceProgram computationalHost "nik:nat-difference"
      [.list ([0, 1, 0, 2, 1].map natural), .list [natural 0]] (.list ([1, 2].map natural)) := by
  intro run
  have impossible := run.deterministic remove_all_repeated_selected_values
  cases impossible

theorem indices_are_not_wrapped :
    Applies naturalDifferenceProgram computationalHost "nik:nat-difference"
      [.list [natural 18446744073709551616], .list [natural 0]]
      (.list [natural 18446744073709551616]) := natural_difference_computes [18446744073709551616] [0]

end NaturalDifferenceControls

end Mettapedia.GSLT.LanguageDef.DeterministicEquations
