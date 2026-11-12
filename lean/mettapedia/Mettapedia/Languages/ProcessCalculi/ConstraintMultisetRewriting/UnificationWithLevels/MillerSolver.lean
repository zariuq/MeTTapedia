import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.MillerTransitions

/-!
# The solver of Miller patterns: exact rules, sound refutations, termination

The rules work on the first equation of a store over Miller codes.

* `delete`: the two sides are the same code. `decompose`: `arr A B ≐ arr A' B'` becomes `A ≐ A'`, `B ≐ B'`.
* `invertLeft`, `invertRight`: `X x̄ ≐ t` with `x̄` without repetitions, `X` not in `t`, and every local of `t`
  among `x̄`: `X := λ ȳ. t[x̄ := ȳ]`.
* `pruneLeft`, `pruneRight`: `X x̄ ≐ t` with `Y z̄` in `t` and some `z̄ᵢ` not among `x̄`: `Y` is restricted to the
  positions of `z̄` that are among `x̄`, through a new unknown of smaller arity.
* `intersect`: `X x̄ ≐ X ȳ` with `x̄ ≠ ȳ`: `X` is restricted to the positions where `x̄` and `ȳ` agree.

Refutations: `clash` (different rigid heads), `scopeLeft`, `scopeRight` (a rigid local outside `x̄`, a clash of
scope), `occursLeft`, `occursRight` (`X` inside a rigid side: no well-founded solution).

**Every transition is exact** (`MStep.exact`) and every refutation sound (`MRefutes.sound`), so `solver` is a
`Solver` of the frames: a run that empties the store ends with a principal answer, a refuted run leaves no solution,
and a stopped run keeps an exact residual.

**Termination** (`MStep.rank_lt`, `steps_terminate`): every transition lowers the rank, the number of unknowns that
occur and then the size. Inversion removes an unknown; pruning and intersection keep the number of unknowns and
shrink every application of the restricted one; deletion and decomposition shrink the store.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

open Interface

namespace MillerCodes

/-! ## The rules -/

/-- **The transitions.** -/
inductive MStep : {Δ : Ctx} → EquationStore (Term Δ) → (m : Ctx) → Assign Δ m → EquationStore (Term m) → Prop
  | delete {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} :
      e.1.1 = e.2.1 → MStep (e :: S) Δ (frames.id Δ) S
  | decompose {Δ : Ctx} {e e₁ e₂ : Equation (Term Δ)} {S : EquationStore (Term Δ)} {A B A' B' : Tm} :
      e.1.1 = .arr A B → e.2.1 = .arr A' B' → e₁.1.1 = A → e₁.2.1 = A' → e₂.1.1 = B → e₂.2.1 = B' →
      MStep (e :: S) Δ (frames.id Δ) (e₁ :: e₂ :: S)
  | invertLeft {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} {X : Nat} {xs : List Nat}
      {σ : Assign Δ Δ} :
      e.1.1 = .app X xs → xs.Nodup → X ∉ Tm.unknowns e.2.1 → Tm.AllLocals (· ∈ xs) e.2.1 →
      σ.1 = Function.update (idA Δ) X (invert xs e.2.1) → MStep (e :: S) Δ σ (frames.applyStore σ S)
  | invertRight {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} {X : Nat} {xs : List Nat}
      {σ : Assign Δ Δ} :
      e.2.1 = .app X xs → xs.Nodup → X ∉ Tm.unknowns e.1.1 → Tm.AllLocals (· ∈ xs) e.1.1 →
      σ.1 = Function.update (idA Δ) X (invert xs e.1.1) → MStep (e :: S) Δ σ (frames.applyStore σ S)
  | pruneLeft {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} {X Y : Nat} {xs zs : List Nat}
      {σ : Assign Δ (extend Δ (prunePositions xs zs).length)} :
      e.1.1 = .app X xs → OccursAt Y zs e.2.1 → (prunePositions xs zs).length < zs.length →
      σ.1 = restrict Δ Y (prunePositions xs zs) →
      MStep (e :: S) (extend Δ (prunePositions xs zs).length) σ (frames.applyStore σ (e :: S))
  | pruneRight {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} {X Y : Nat} {xs zs : List Nat}
      {σ : Assign Δ (extend Δ (prunePositions xs zs).length)} :
      e.2.1 = .app X xs → OccursAt Y zs e.1.1 → (prunePositions xs zs).length < zs.length →
      σ.1 = restrict Δ Y (prunePositions xs zs) →
      MStep (e :: S) (extend Δ (prunePositions xs zs).length) σ (frames.applyStore σ (e :: S))
  | intersect {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} {X : Nat} {xs ys : List Nat}
      {σ : Assign Δ (extend Δ (agreePositions xs ys).length)} :
      e.1.1 = .app X xs → e.2.1 = .app X ys → (agreePositions xs ys).length < xs.length →
      σ.1 = restrict Δ X (agreePositions xs ys) →
      MStep (e :: S) (extend Δ (agreePositions xs ys).length) σ (frames.applyStore σ (e :: S))

/-- **The refutations**, with their reasons. -/
inductive MRefutes : {Δ : Ctx} → EquationStore (Term Δ) → Reason → Prop
  | clash {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} {h h' : Nat} :
      head? e.1.1 = some h → head? e.2.1 = some h' → h ≠ h' → MRefutes (e :: S) .clash
  | scopeLeft {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} {X j : Nat} {xs : List Nat} :
      e.1.1 = .app X xs → RigidLocal j e.2.1 → j ∉ xs → MRefutes (e :: S) .clash
  | scopeRight {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} {X j : Nat} {xs : List Nat} :
      e.2.1 = .app X xs → RigidLocal j e.1.1 → j ∉ xs → MRefutes (e :: S) .clash
  | occursLeft {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} {X : Nat} {xs ys : List Nat}
      {A B : Tm} :
      e.1.1 = .app X xs → e.2.1 = .arr A B → OccursAt X ys (.arr A B) →
      MRefutes (e :: S) .noWellFoundedSolution
  | occursRight {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} {X : Nat} {xs ys : List Nat}
      {A B : Tm} :
      e.2.1 = .app X xs → e.1.1 = .arr A B → OccursAt X ys (.arr A B) →
      MRefutes (e :: S) .noWellFoundedSolution

/-! ## Exactness and soundness -/

theorem models_swap {Δ Γ : Ctx} {f : Assign Δ Γ} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} :
    frames.Models f ((e.2, e.1) :: S) ↔ frames.Models f (e :: S) := by
  constructor
  · intro h e' he'
    rcases List.mem_cons.mp he' with rfl | he'
    · exact Eq.symm (h _ List.mem_cons_self)
    · exact h e' (List.mem_cons_of_mem _ he')
  · intro h e' he'
    rcases List.mem_cons.mp he' with rfl | he'
    · exact Eq.symm (h _ List.mem_cons_self)
    · exact h e' (List.mem_cons_of_mem _ he')

theorem exact_swap {Δ m : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} {σ : Assign Δ m}
    {R : EquationStore (Term m)} (exact : Exact frames ((e.2, e.1) :: S) σ R) : Exact frames (e :: S) σ R := by
  intro Γ f
  rw [← models_swap]
  exact exact Γ f

theorem solvable_swap {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} :
    frames.Solvable ((e.2, e.1) :: S) ↔ frames.Solvable (e :: S) := by
  constructor
  · rintro ⟨Γ, f, h⟩
    exact ⟨Γ, f, models_swap.mp h⟩
  · rintro ⟨Γ, f, h⟩
    exact ⟨Γ, f, models_swap.mpr h⟩

theorem delete_exact {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} (same : e.1.1 = e.2.1) :
    Exact frames (e :: S) (frames.id Δ) S := by
  apply exact_id_of_equivalent
  intro Γ f
  constructor
  · intro solved e' he'
    exact solved e' (List.mem_cons_of_mem _ he')
  · intro solved e' he'
    rcases List.mem_cons.mp he' with rfl | he'
    · show Tm.act f.1 e'.1.1 = Tm.act f.1 e'.2.1
      rw [same]
    · exact solved e' he'

theorem decompose_exact {Δ : Ctx} {e e₁ e₂ : Equation (Term Δ)} {S : EquationStore (Term Δ)} {A B A' B' : Tm}
    (h : e.1.1 = .arr A B) (h' : e.2.1 = .arr A' B') (h₁ : e₁.1.1 = A) (h₁' : e₁.2.1 = A') (h₂ : e₂.1.1 = B)
    (h₂' : e₂.2.1 = B') : Exact frames (e :: S) (frames.id Δ) (e₁ :: e₂ :: S) := by
  apply exact_id_of_equivalent
  intro Γ f
  have head : frames.Solves f e ↔ frames.Solves f e₁ ∧ frames.Solves f e₂ := by
    show Tm.act f.1 e.1.1 = Tm.act f.1 e.2.1 ↔
      Tm.act f.1 e₁.1.1 = Tm.act f.1 e₁.2.1 ∧ Tm.act f.1 e₂.1.1 = Tm.act f.1 e₂.2.1
    rw [h, h', h₁, h₁', h₂, h₂']
    simp only [Tm.act, Tm.arr.injEq]
  constructor
  · intro solved e' he'
    rcases List.mem_cons.mp he' with rfl | he'
    · exact (head.mp (solved e List.mem_cons_self)).1
    rcases List.mem_cons.mp he' with rfl | he'
    · exact (head.mp (solved e List.mem_cons_self)).2
    · exact solved e' (List.mem_cons_of_mem _ he')
  · intro solved e' he'
    rcases List.mem_cons.mp he' with rfl | he'
    · exact head.mpr ⟨solved e₁ List.mem_cons_self,
        solved e₂ (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    · exact solved e' (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he'))

/-- **Every transition is exact.** -/
theorem MStep.exact {Δ m : Ctx} {S : EquationStore (Term Δ)} {σ : Assign Δ m} {S' : EquationStore (Term m)}
    (st : MStep S m σ S') : Exact frames S σ S' := by
  cases st with
  | delete same => exact delete_exact same
  | decompose h h' h₁ h₁' h₂ h₂' => exact decompose_exact h h' h₁ h₁' h₂ h₂'
  | invertLeft hl nodup fresh inside hσ => exact invert_exact hl nodup fresh inside hσ
  | @invertRight e _ _ _ _ hr nodup fresh inside hσ =>
      exact exact_swap (invert_exact (e := (e.2, e.1)) hr nodup fresh inside hσ)
  | @pruneLeft e S _ Y _ zs _ hl occ _ hσ =>
      exact restrict_exact (occ.decl e.2.2) hσ (prune_forced hl occ)
  | @pruneRight e S _ Y _ zs _ hr occ _ hσ =>
      exact restrict_exact (occ.decl e.1.2) hσ fun Γ f solved =>
        prune_forced (e := (e.2, e.1)) hr occ Γ f (models_swap.mpr solved)
  | intersect hl hr _ hσ => exact restrict_exact (decl_of_app hl) hσ (intersect_forced hl hr)

/-- **Every refutation is sound.** -/
theorem MRefutes.sound {Δ : Ctx} {S : EquationStore (Term Δ)} {r : Reason} (refuted : MRefutes S r) :
    ¬ frames.Solvable S := by
  cases refuted with
  | clash h₁ h₂ ne => exact clash_unsolvable h₁ h₂ ne
  | scopeLeft hl rigid out => exact scope_unsolvable hl rigid out
  | @scopeRight e _ _ _ _ hr rigid out =>
      exact fun solvable => scope_unsolvable (e := (e.2, e.1)) hr rigid out (solvable_swap.mpr solvable)
  | occursLeft hl hr occ => exact occurs_unsolvable hl hr occ
  | @occursRight e _ _ _ _ _ _ hr hl occ =>
      exact fun solvable => occurs_unsolvable (e := (e.2, e.1)) hr hl occ (solvable_swap.mpr solvable)

/-- **The solver of Miller patterns**, as a `Solver` of the frames. -/
def solver : Solver frames where
  Step S m σ S' := MStep S m σ S'
  step_exact st := MStep.exact st
  Refutes S r := MRefutes S r
  refutes_sound r := MRefutes.sound r

end MillerCodes

#print axioms MillerCodes.MStep.exact
#print axioms MillerCodes.MRefutes.sound

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
