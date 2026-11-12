import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.StepConnection

/-!
# The level part of a store, decided symbolically

A store of the solver is term equations followed by level constraints, each written as the equation
`sort (max u w) ≐ sort w` (`withLevels`). Its solutions at a valuation are the solutions of the
term equations, provided the valuation satisfies the level constraints (`models_withLevels`). The
level solver `decideSat` then gives one of three verdicts on the level part, uniformly in the
valuation:

* **refuted**: an unsatisfiable level part leaves no solution at any valuation
  (`refuted_everywhere`), whatever the term equations;
* **deleted**: a constraint entailed by the others can be dropped, exactly, at every valuation that
  satisfies the others (`drop_entailed`);
* **postponed**: a satisfiable constraint that is not entailed stays; the cross store's `b ≤ a` is
  one (`Cross.pending_undecided`).

Positive control: the cross store's level part `a ≤ b` is satisfiable, so the store is not refuted
by levels. Negative control: adding `b + 1 ≤ a` refutes it at every valuation (`cross_strict`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

open Interface

namespace CumulativeCodes

variable {v : Nat → Nat}

/-- Term equations followed by level constraints, as one store. -/
def withLevels {Δ : Ctx} (S : EquationStore (Term Δ)) (C : LevelStore) : EquationStore (Term Δ) :=
  S ++ C.map levelEquation

theorem models_withLevels {Δ Γ : Ctx} (f : Assign v Δ Γ) (S : EquationStore (Term Δ))
    (C : LevelStore) :
    (frames v).Models f (withLevels S C) ↔ (frames v).Models f S ∧ C.Satisfies v := by
  unfold withLevels
  rw [Frames.models_append]
  constructor
  · rintro ⟨solved, levels⟩
    refine ⟨solved, fun c hc => ?_⟩
    exact (solves_levelEquation f c).mp (levels _ (List.mem_map_of_mem hc))
  · rintro ⟨solved, levels⟩
    refine ⟨solved, fun e he => ?_⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp he
    exact (solves_levelEquation f c).mpr (levels c hc)

/-- **Refuted by levels, at every valuation.** -/
theorem refuted_everywhere {Δ : Ctx} (S : EquationStore (Term Δ)) {C : LevelStore}
    (unsat : decideSat C = false) (v : Nat → Nat) : ¬ (frames v).Solvable (withLevels S C) := by
  rintro ⟨Γ, f, solved⟩
  have sat : LevelStore.Satisfiable C := ⟨v, ((models_withLevels f S C).mp solved).2⟩
  rw [← decideSat_iff, unsat] at sat
  cases sat

/-- **An entailed constraint is deleted exactly**, at every valuation satisfying the others. -/
theorem drop_entailed {Δ : Ctx} (S : EquationStore (Term Δ)) {C : LevelStore} {c : LevelLe}
    (entailed : C.Entails c) (sat : C.Satisfies v) :
    Exact (frames v) (withLevels S (c :: C)) ((frames v).id Δ) (withLevels S C) := by
  apply exact_id_of_equivalent
  intro Γ f
  rw [models_withLevels, models_withLevels]
  constructor
  · rintro ⟨solved, levels⟩
    exact ⟨solved, fun d hd => levels d (List.mem_cons_of_mem _ hd)⟩
  · rintro ⟨solved, levels⟩
    refine ⟨solved, fun d hd => ?_⟩
    rcases List.mem_cons.mp hd with rfl | hd
    · exact entailed v sat
    · exact levels d hd

namespace Cross

/-- **Positive**: the cross store's level part is satisfiable; levels do not refute it. -/
theorem cross_levels_satisfiable : decideSat levels = true := by decide

/-- **Negative**: with `b + 1 ≤ a` added to `a ≤ b`, the cross store is refuted by levels at every
valuation. -/
theorem cross_strict (v : Nat → Nat) :
    ¬ (frames v).Solvable (withLevels store (⟨.succ b, a⟩ :: levels)) :=
  refuted_everywhere store (by decide) v

end Cross

end CumulativeCodes

#print axioms CumulativeCodes.models_withLevels
#print axioms CumulativeCodes.refuted_everywhere
#print axioms CumulativeCodes.drop_entailed
#print axioms CumulativeCodes.Cross.cross_strict

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
