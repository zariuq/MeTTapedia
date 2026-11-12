import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeEquationSolver

/-!
# Checked reduction of constant and reflexive type equations

These equations simplify the existing executable unifier's Boolean decision.
They are proved through its satisfiability theorem, not another solver. Their
evaluation registration permits kernel-checked finite controls to reuse the
proof instead of expanding the total unifier for each scalar constraint.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeEquationScalarReduction

variable {V : Type} [DecidableEq V]

omit [DecidableEq V] in
theorem sat_symbol_cons (left right : String) (rest : List (Eqn V)) :
    Sat ((.sym left, .sym right) :: rest) ↔ left = right ∧ Sat rest := by
  constructor
  · rintro ⟨solution, solved⟩
    have parts := (solves_cons solution _ _).mp solved
    exact ⟨Ty.sym.inj parts.1, solution, parts.2⟩
  · rintro ⟨rfl, solution, solved⟩
    exact ⟨solution, (solves_cons solution _ _).mpr ⟨rfl, solved⟩⟩

@[cbv_eval] theorem check_symbol_cons (left right : String) (rest : List (Eqn V)) :
    TypeEquationSolver.check ((.sym left, .sym right) :: rest) =
      if left = right then TypeEquationSolver.check rest else false := by
  apply Bool.eq_iff_iff.mpr
  by_cases same : left = right
  · simp [same, TypeEquationSolver.check_iff_sat, sat_symbol_cons]
  · simp [same, TypeEquationSolver.check_iff_sat, sat_symbol_cons]

@[cbv_eval] theorem check_reflexive_cons (type : Ty V) (rest : List (Eqn V)) :
    TypeEquationSolver.check ((type, type) :: rest) = TypeEquationSolver.check rest := by
  apply Bool.eq_iff_iff.mpr
  rw [TypeEquationSolver.check_iff_sat, TypeEquationSolver.check_iff_sat]
  constructor
  · rintro ⟨solution, solved⟩
    exact ⟨solution, ((solves_cons solution _ _).mp solved).2⟩
  · rintro ⟨solution, solved⟩
    exact ⟨solution, (solves_cons solution _ _).mpr ⟨rfl, solved⟩⟩

@[cbv_eval] theorem check_nil : TypeEquationSolver.check ([] : List (Eqn V)) = true :=
  TypeEquationSolver.check_iff_sat _ |>.mpr sat_nil

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeEquationScalarReduction
