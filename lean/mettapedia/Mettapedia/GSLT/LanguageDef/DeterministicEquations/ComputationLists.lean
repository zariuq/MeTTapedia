import Mettapedia.GSLT.LanguageDef.DeterministicEquations.Computation

/-!
# Ordered list construction in the shared equation evaluator

The list introduction law composes the actual child evaluations in order.
It does not quote or bypass those children. A missing variable fails, and
insufficient fuel remains exhaustion rather than a completed refusal.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations

theorem Evaluates.list {P : Program} {H : Host} {environment : Env} {sources results : List Term}
    (children : List.Forall₂ (Evaluates P H environment) sources results) :
    Evaluates P H environment (.list sources) (.list results) := by
  obtain ⟨fuel, computed⟩ := evaluates_items children
  refine ⟨fuel + 1, ?_⟩
  change (match evalItems P H fuel environment sources with
    | .values values => Outcome.value (.list values)
    | .stop outcome => outcome) = .value (.list results)
  rw [computed fuel (Nat.le_refl fuel)]

namespace ComputationListsControls

theorem empty_list_completes (P : Program) (H : Host) (environment : Env) :
    Evaluates P H environment (.list []) (.list []) := Evaluates.list .nil

theorem two_children_keep_order (P : Program) (H : Host) (first second : Term) :
    Evaluates P H [("first", first), ("second", second)]
      (.list [.var "second", .var "first", .var "second"]) (.list [second, first, second]) :=
  Evaluates.list (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))

theorem missing_child_fails (P : Program) (H : Host) :
    eval P H 2 [] (.list [.sym "prior", .var "missing", .sym "later"]) = .failure := rfl

theorem no_fuel_is_not_refusal (P : Program) (H : Host) (environment : Env) (sources : List Term) :
    eval P H 0 environment (.list sources) = .exhausted := rfl

theorem child_exhaustion_is_not_empty_success (P : Program) (H : Host) :
    eval P H 1 [] (.list [.sym "item"]) = .exhausted := rfl

theorem completed_children_exclude_other_lists {P : Program} {H : Host} {environment : Env}
    {sources results other : List Term}
    (children : List.Forall₂ (Evaluates P H environment) sources results)
    (different : other ≠ results) :
    ¬ Evaluates P H environment (.list sources) (.list other) := by
  intro invented
  exact different (Term.list.inj (invented.deterministic (Evaluates.list children)))

end ComputationListsControls

end Mettapedia.GSLT.LanguageDef.DeterministicEquations
