import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.PatternSolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.CrossStoreLevels

/-!
# Controls for the solver of cumulative codes

Over `X, V : Sort 0 ⟶ Sort 0` (unknowns 0 and 1):

* **solved** (positive): `X par ≐ arr (V par) gnd` is solved in one step, and the answer is
  principal (`solved_run`, `solved_principal_answer`);
* **no well-founded solution** (negative): `X par ≐ arr (X par) gnd` is refuted with that reason
  and has no solution (`occurs_refuted`);
* **clash** (negative): `gnd ≐ arr gnd gnd` is refuted (`clash_refuted`);
* **levels**: `sort a ≐ sort 1` is a level equation; it is deleted where `a` is `1` and refuted
  with reason `levels` where `a` is `0` (`level_equation_holds`, `level_equation_refuted`).

On the cross store (`CrossStoreLevels`): where `a < b` no transition and no refutation applies, so
the solver stops with the equation postponed (`cross_stopped`); where `a = b` it solves the store
in one step (`cross_solved_at_equal_levels`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

open Interface

namespace CumulativeCodes

namespace SolverControls

/-- `X, V : Sort 0 ⟶ Sort 0`. -/
def ctx : Ctx := [⟨.const 0, .const 0⟩, ⟨.const 0, .const 0⟩]

theorem decls (v : Nat → Nat) : ∀ (W : Nat) (d : Decl), ctx[W]? = some d →
    Level.value v d.dom = 0 ∧ Level.value v d.cod = 0 := by
  intro W d h
  match W, h with
  | 0, h =>
      simp only [ctx, List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl⟩
  | 1, h =>
      simp only [ctx, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl⟩
  | n + 2, h => simp [ctx] at h

/-- `X par`. -/
def X : Term ctx := ⟨.app 0 .par, .app (by decide) .par⟩

/-- `arr (V par) gnd`. -/
def target : Term ctx := ⟨.arr (.app 1 .par) .gnd, .arr (.app (by decide) .par) .gnd⟩

/-- `arr (X par) gnd`. -/
def loop : Term ctx := ⟨.arr (.app 0 .par) .gnd, .arr (.app (by decide) .par) .gnd⟩

/-- The solving assignment `X := arr (V par) gnd`. -/
def answer (v : Nat → Nat) : Assign v ctx ctx :=
  ⟨Function.update Tm.idA 0 target.1,
    update_typed (decls v) 0 (.arr (.app rfl (.par le_rfl) le_rfl) .gnd)⟩

/-- **Positive: a run to the empty store.** -/
theorem solved_run (v : Nat → Nat) :
    (solver v).Reaches [(X, target)] ctx ((frames v).comp ((frames v).id ctx) (answer v)) [] :=
  .step (Rule.solveLeft rfl rfl rfl) (.refl _)

theorem solved_principal_answer (v : Nat → Nat) :
    (frames v).Principal [(X, target)] ((frames v).comp ((frames v).id ctx) (answer v)) :=
  solved_principal (solved_run v)

/-- The store is in the uniform pattern fragment. -/
theorem solved_uniform (v : Nat → Nat) : Uniform v ctx 0 0 [(X, target)] := by
  refine ⟨decls v, fun e he => ?_, fun e he => ?_⟩
  · simp only [List.mem_singleton] at he
    subst he
    exact ⟨.app rfl (.par le_rfl) le_rfl, .arr (.app rfl (.par le_rfl) le_rfl) .gnd⟩
  · simp only [List.mem_singleton] at he
    subst he
    exact ⟨.app 0, .arr (.app 1) .gnd⟩

/-- **Negative: the occurs check refutes with "no well-founded solution".** -/
theorem occurs_refuted (v : Nat → Nat) :
    Refutes v [(X, loop)] .noWellFoundedSolution ∧ ¬ (frames v).Solvable [(X, loop)] := by
  have r : Refutes v [(X, loop)] .noWellFoundedSolution :=
    .occursLeft rfl (.arr (.app 0) .gnd) (by simp [loop, Tm.unknowns]) (by simp [loop])
  exact ⟨r, r.sound⟩

/-- `gnd`. -/
def ground : Term ctx := ⟨.gnd, .gnd⟩

/-- `arr gnd gnd`. -/
def arrow : Term ctx := ⟨.arr .gnd .gnd, .arr .gnd .gnd⟩

/-- **Negative: a clash of heads.** -/
theorem clash_refuted (v : Nat → Nat) :
    Refutes v [(ground, arrow)] .clash ∧ ¬ (frames v).Solvable [(ground, arrow)] := by
  have r : Refutes v [(ground, arrow)] .clash := .clash (h := 1) (h' := 3) rfl rfl (by decide)
  exact ⟨r, r.sound⟩

/-- `sort a` and `sort 1`. -/
def sortA : Term ctx := ⟨.sort (.param 0), .sort _⟩
def sortOne : Term ctx := ⟨.sort (.const 1), .sort _⟩

/-- **Levels, positive**: where `a` is `1`, the level equation is deleted. -/
theorem level_equation_holds :
    Rule (fun _ => 1) [(sortA, sortOne)] ctx ((frames (fun _ => 1)).id ctx) [] :=
  .delete rfl

/-- **Levels, negative**: where `a` is `0`, it is refuted with reason `levels`. -/
theorem level_equation_refuted :
    Refutes (fun _ => 0) [(sortA, sortOne)] .levels ∧
      ¬ (frames (fun _ => 0)).Solvable [(sortA, sortOne)] := by
  have r : Refutes (fun _ => 0) [(sortA, sortOne)] .levels := .levels rfl rfl (by decide)
  exact ⟨r, r.sound⟩

end SolverControls

namespace Cross

variable {v : Nat → Nat}

/-- **The cross equation is postponed where `a < b`**, whatever follows it: no transition and no
refutation applies. -/
theorem cross_stopped_cons (lt : Level.value v a < Level.value v b)
    (S : EquationStore (Term ctx)) : (solver v).Stopped ((X, Y) :: S) := by
  refine ⟨fun n τ R' r => ?_, fun reason r => ?_⟩
  · change Rule v ((X, Y) :: S) n τ R' at r
    have typed0 := τ.2 0 ⟨a, a⟩ rfl
    have typed1 := τ.2 1 ⟨b, b⟩ rfl
    cases r with
    | delete same =>
        have := Tm.app.inj same
        exact absurd this.1 (by decide)
    | decompose h _ _ _ _ _ => cases h
    | solveLeft hl _ hσ =>
        obtain ⟨hX, _⟩ := Tm.app.inj hl
        subst hX
        have typed := typed0
        rw [hσ, Function.update_self] at typed
        obtain ⟨d, hd, _, hc⟩ := Ty.app_inv typed
        simp only [ctx, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hd
        subst hd
        exact absurd hc (by simp only; omega)
    | solveRight hr _ hσ =>
        obtain ⟨hX, _⟩ := Tm.app.inj hr
        subst hX
        have typed := typed1
        rw [hσ, Function.update_self] at typed
        obtain ⟨d, hd, ht, _⟩ := Ty.app_inv typed
        simp only [ctx, List.getElem?_cons_zero, Option.some.injEq] at hd
        subst hd
        have := Ty.par_inv ht
        dsimp only at this
        omega
  · change Refutes v ((X, Y) :: S) reason at r
    cases r with
    | clash h₁ _ _ => cases h₁
    | levels h₁ _ _ => cases h₁
    | occursLeft hl _ hX _ =>
        obtain ⟨hX', _⟩ := Tm.app.inj hl
        subst hX'
        simp [Y, Tm.unknowns] at hX
    | occursRight hr _ hX _ =>
        obtain ⟨hX', _⟩ := Tm.app.inj hr
        subst hX'
        simp [X, Tm.unknowns] at hX

/-- **The cross store is postponed where `a < b`.** -/
theorem cross_stopped (lt : Level.value v a < Level.value v b) : (solver v).Stopped store :=
  cross_stopped_cons lt []

/-- The assignment `X := Y par`, typed where `a = b`. -/
def merge (v : Nat → Nat) (eq : Level.value v a = Level.value v b) : Assign v ctx ctx :=
  ⟨Function.update Tm.idA 0 (.app 1 .par), by
    intro W d hW
    by_cases h : W = 0
    · subst h
      rw [Function.update_self]
      simp only [ctx, List.getElem?_cons_zero, Option.some.injEq] at hW
      subst hW
      exact .app (d := ⟨b, b⟩) rfl (.par (le_of_eq eq)) (le_of_eq eq.symm)
    · rw [Function.update_of_ne h]
      exact idA_typed ctx W d hW⟩

/-- **The cross store is solved where `a = b`**, in one step. -/
theorem cross_solved_at_equal_levels (eq : Level.value v a = Level.value v b) :
    (solver v).Reaches store ctx ((frames v).comp ((frames v).id ctx) (merge v eq)) [] ∧
      (frames v).Principal store ((frames v).comp ((frames v).id ctx) (merge v eq)) := by
  have run : (solver v).Reaches store ctx ((frames v).comp ((frames v).id ctx) (merge v eq)) [] :=
    .step (Rule.solveLeft rfl rfl rfl) (.refl _)
  exact ⟨run, solved_principal run⟩

end Cross

end CumulativeCodes

#print axioms CumulativeCodes.SolverControls.solved_principal_answer
#print axioms CumulativeCodes.SolverControls.occurs_refuted
#print axioms CumulativeCodes.SolverControls.clash_refuted
#print axioms CumulativeCodes.SolverControls.level_equation_refuted
#print axioms CumulativeCodes.Cross.cross_stopped
#print axioms CumulativeCodes.Cross.cross_solved_at_equal_levels

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
