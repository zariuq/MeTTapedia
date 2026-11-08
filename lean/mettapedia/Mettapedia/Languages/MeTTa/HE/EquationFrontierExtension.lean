import Mettapedia.Languages.MeTTa.HE.Spec.Eval

/-! Complete frontier transport across independently rejected appended rows. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

theorem EquationFrontierRel.append_rejected (base : Space) (live : List Atom) (query : Atom) (before : Bindings)
    (works : List EquationWork) (extra : List Atom)
    (frontier : EquationFrontierRel base live query before works)
    (rejected : ∀ row ∈ extra, ∀ position, EquationRowResultsRel live query before position row []) :
    EquationFrontierRel (Space.ofList (base.atoms ++ extra)) live query before works := by
  have suffix : ∀ (rows : List Atom) (position : Nat),
      (∀ row ∈ rows, ∀ index, EquationRowResultsRel live query before index row []) →
      List.Forall₂ (fun pair block => EquationRowResultsRel live query before pair.2 pair.1 block)
        (rows.zipIdx position) (List.replicate rows.length []) := by
    intro rows
    induction rows with
    | nil => intro _ _; exact .nil
    | cons row rows ih =>
        intro position absent
        simp only [List.zipIdx_cons, List.length_cons, List.replicate_succ]
        exact .cons (absent row (by simp) position)
          (ih (position + 1) (fun value member index => absent value (List.mem_cons_of_mem _ member) index))
  cases frontier with
  | @completed blocks paired =>
      have extended := List.rel_append paired (suffix extra base.atoms.length rejected)
      have complete : EquationFrontierRel (Space.ofList (base.atoms ++ extra)) live query before
          (blocks ++ List.replicate extra.length []).flatten := by
        apply EquationFrontierRel.completed
        simpa [Space.ofList, List.zipIdx_append] using extended
      simpa using complete

end Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps
