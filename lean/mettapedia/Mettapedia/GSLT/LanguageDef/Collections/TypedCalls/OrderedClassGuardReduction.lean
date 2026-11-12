import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.OrderedTypeRelation
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeEquationScalarReduction

/-!
# Exact reduction of a single primitive-class guard

The original equation store is retained, including its order and duplicates.
A failed store cannot be repaired by the metatype fallback. The returned
equation is retained even though it is reflexive.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.OrderedClassGuardReduction

variable {V : Type} [DecidableEq V]

omit [DecidableEq V] in
theorem sat_append_reflexive (store : List (Eqn V)) (type : Ty V) :
    Sat (store ++ [(type, type)]) ↔ Sat store := by
  constructor
  · exact Sat.left
  · rintro ⟨assignment, solved⟩
    exact ⟨assignment, (solves_append _ _ _).mpr
      ⟨solved, (solves_singleton _ _).mpr rfl⟩⟩

@[cbv_eval] theorem check_append_reflexive (store : List (Eqn V)) (type : Ty V) :
    TypeEquationSolver.check (store ++ [(type, type)]) = TypeEquationSolver.check store := by
  apply Bool.eq_iff_iff.mpr
  simp only [TypeEquationSolver.check_iff_sat, sat_append_reflexive]

theorem check_append_of_rejection (store suffix : List (Eqn V))
    (rejected : TypeEquationSolver.check store = false) :
    TypeEquationSolver.check (store ++ suffix) = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  have earlier := (TypeEquationSolver.check_iff_sat store).mpr
    ((TypeEquationSolver.check_iff_sat _).mp accepted).left
  simp [rejected] at earlier

theorem exact_class (rename : DVar → V) (store : List (Eqn V)) (name : String) :
    OrderedTypeRelation.exactTypes rename store (.sym name) ⟨[], [classDeriv name]⟩ =
      if TypeEquationSolver.check store then [store ++ [(.sym name, .sym name)]] else [] := by
  simp [OrderedTypeRelation.exactTypes, OrderedTypeRelation.effective, classDeriv,
    Ty.map]
  simp [List.filter_cons, check_append_reflexive]

@[cbv_eval] theorem guard_class (rename : DVar → V) (store : List (Eqn V)) (name kind : String) :
    OrderedTypeRelation.guardOrdered rename store (.sym name) ⟨[], [classDeriv name]⟩ kind =
      if TypeEquationSolver.check store then [store ++ [(.sym name, .sym name)]] else [] := by
  unfold OrderedTypeRelation.guardOrdered
  rw [exact_class]
  cases accepted : TypeEquationSolver.check store with
  | true => simp
  | false =>
      have fallback := check_append_of_rejection store [(.sym kind, .sym name)] accepted
      simp [fallback]

namespace Controls

abbrev empty : List (Eqn String) := []

theorem a_class_guard_keeps_its_equation :
    OrderedTypeRelation.guardOrdered (fun _ => "unused") empty (.sym "Number")
      ⟨[], [classDeriv "Number"]⟩ "Grounded" = [[(.sym "Number", .sym "Number")]] := by
  rw [guard_class]
  simp [empty, TypeEquationScalarReduction.check_nil]

theorem metatype_fallback_cannot_rescue_a_conflicting_store :
    OrderedTypeRelation.guardOrdered (fun _ => "unused")
      ([ (.sym "left", .sym "right") ] : List (Eqn String)) (.sym "Number")
      ⟨[], [classDeriv "Number"]⟩ "Number" = [] := by
  rw [guard_class]
  cbv

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.OrderedClassGuardReduction
