import Mettapedia.Languages.Maude.Syntax

/-! Substitution on the first-order IR. Ground identity terms are invariant
under a rule's valuation; in particular a compound identity does not become
a new rule metavariable. -/

set_option autoImplicit false

namespace Mettapedia.Languages.Maude

theorem Term.substitute_ground (assignment : Valuation) (term : Term)
    (ground : term.variables = []) : term.substitute assignment = term := by
  revert ground
  refine Term.rec
    (motive_1 := fun term => term.variables = [] → term.substitute assignment = term)
    (motive_2 := fun terms => terms.flatMap Term.variables = [] →
      terms.map (Term.substitute assignment) = terms)
    ?_ ?_ ?_ ?_ term
  · intro name impossible
    simp [Term.variables] at impossible
  · intro id arguments ih ground
    rw [Term.substitute, ih (by simpa [Term.variables] using ground)]
  · intro _
    rfl
  · intro head tail first rest ground
    simp only [List.flatMap_cons, List.append_eq_nil_iff] at ground
    simp only [List.map_cons, first ground.1, rest ground.2]

theorem substitute_preserves_sort {signature : Signature} {source target : VariableContext}
    (assignment : Valuation)
    (typedAssignment : ∀ name sort, source.lookup name = some sort → HasSort signature target (assignment name) sort)
    {term : Term} {sort : String} (typed : HasSort signature source term sort) :
    HasSort signature target (term.substitute assignment) sort := by
  refine HasSort.rec
    (motive_1 := fun term sort _ => HasSort signature target (term.substitute assignment) sort)
    (motive_2 := fun terms sorts _ => List.Forall₂ (HasSort signature target)
      (terms.map (Term.substitute assignment)) sorts)
    ?_ ?_ ?_ ?_ typed
  · intro name sort found
    rw [Term.substitute]
    exact typedAssignment name sort found
  · intro declaration arguments member _ ih
    rw [Term.substitute]
    exact .app member ih
  · exact .nil
  · intro first sort rest sorts _ _ firstIH restIH
    exact .cons firstIH restIH

end Mettapedia.Languages.Maude
