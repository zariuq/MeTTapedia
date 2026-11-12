import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.MillerDecision

/-!
# Controls for Miller patterns

Every run below is a run of `MillerCodes.solver`, and every answer is principal by `solved_principal`.

* **Inversion** (positive): `X 5 7 ≐ arr 7 5` is solved by `X := λ a b. arr b a` (`inversion_run`,
  `inversion_body`).
* **Pruning, then inversion** (positive): `X 5 ≐ arr (Y 5 6) gnd`. The local `6` cannot appear in `X`'s instance, so
  `Y` is restricted to its first argument, `Y := λ a b. Y' a`; then `X := λ a. arr (Y' a) gnd` (`pruning_run`).
* **Intersection** (positive): `X 5 6 ≐ X 5 7`. Only the first argument agrees, so `X := λ a b. X' a`, after which
  the equation is trivial (`intersection_run`).
* **Scope** (negative): `X 5 ≐ 6` is refuted, the local `6` being outside `X`'s arguments (`scope_refuted`).
* **Occurs** (negative): `X 5 ≐ arr (X 5) gnd` is refuted with no well-founded solution (`occurs_refuted`).
* **The condition cannot be dropped** (negative): `X 5 5 ≐ 5`, whose arguments repeat, is not a pattern. It is
  solvable, by `X := λ a b. a` and by `X := λ a b. b`, and has no principal answer (`nonpattern_no_principal`). So
  the decision does not extend to all stores with repeated arguments; some of them still have principal answers.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

open Interface

namespace MillerCodes

namespace Controls

/-! ## Inversion -/

/-- `X` of arity 2. -/
def ctx₁ : Ctx := [2]

/-- `X 5 7`. -/
def lhs₁ : Term ctx₁ := ⟨.app 0 [5, 7], .app rfl⟩

/-- `arr 7 5`. -/
def rhs₁ : Term ctx₁ := ⟨.arr (.loc 7) (.loc 5), .arr (.loc 7) (.loc 5)⟩

def store₁ : EquationStore (Term ctx₁) := [(lhs₁, rhs₁)]

theorem inside₁ : Tm.AllLocals (· ∈ [5, 7]) rhs₁.1 := .arr (.loc (by simp)) (.loc (by simp))

/-- The answer `X := λ a b. arr b a`. -/
def answer₁ : Assign ctx₁ ctx₁ :=
  ⟨Function.update (idA ctx₁) 0 (invert [5, 7] rhs₁.1), invert_typed rfl rhs₁.2 inside₁⟩

/-- The inverted body renames `7` to the second parameter and `5` to the first. -/
theorem inversion_body : invert [5, 7] rhs₁.1 = .arr (.loc 1) (.loc 0) := by decide

/-- **Positive: inversion solves the store**, with a principal answer. -/
theorem inversion_run : solver.Reaches store₁ ctx₁ (frames.comp (frames.id ctx₁) answer₁) [] :=
  .step (MStep.invertLeft (X := 0) (xs := [5, 7]) rfl (by decide) (by simp [rhs₁, Tm.unknowns]) inside₁ rfl)
    (.refl [])

theorem inversion_principal : frames.Principal store₁ (frames.comp (frames.id ctx₁) answer₁) :=
  solved_principal inversion_run

/-! ## Pruning, then inversion -/

/-- `X` of arity 1 (unknown 0) and `Y` of arity 2 (unknown 1). -/
def ctx₂ : Ctx := [1, 2]

/-- `X 5`. -/
def lhs₂ : Term ctx₂ := ⟨.app 0 [5], .app rfl⟩

/-- `arr (Y 5 6) gnd`. -/
def rhs₂ : Term ctx₂ := ⟨.arr (.app 1 [5, 6]) .gnd, .arr (.app rfl) .gnd⟩

def store₂ : EquationStore (Term ctx₂) := [(lhs₂, rhs₂)]

/-- Pruning keeps the first argument of `Y` only. -/
theorem positions₂ : prunePositions [5] [5, 6] = [0] := by decide

/-- The pruning `Y := λ a b. Y' a`, with `Y'` of arity 1 the new unknown 2. -/
def pruning₂ : Assign ctx₂ (extend ctx₂ (prunePositions [5] [5, 6]).length) :=
  ⟨restrict ctx₂ 1 (prunePositions [5] [5, 6]), restrict_typed rfl prunePositions_below⟩

/-- After pruning, the right side is `arr (Y' 5) gnd`. -/
theorem pruned_side : Tm.act pruning₂.1 rhs₂.1 = .arr (.app 2 [5]) .gnd := by decide

theorem pruned_scoped : Scoped (extend ctx₂ (prunePositions [5] [5, 6]).length) (Tm.act pruning₂.1 rhs₂.1) :=
  Scoped.act pruning₂.2 rhs₂.2

theorem pruned_inside : Tm.AllLocals (· ∈ [5]) (Tm.act pruning₂.1 rhs₂.1) := by
  rw [pruned_side]
  exact .arr (.app (by simp)) .gnd

/-- Then `X := λ a. arr (Y' a) gnd`. -/
def answer₂ : Assign (extend ctx₂ (prunePositions [5] [5, 6]).length) (extend ctx₂ (prunePositions [5] [5, 6]).length) :=
  ⟨Function.update (idA _) 0 (invert [5] (Tm.act pruning₂.1 rhs₂.1)),
    invert_typed rfl pruned_scoped pruned_inside⟩

/-- **Positive: pruning, then inversion, solves the store**, with a principal answer. -/
theorem pruning_run :
    solver.Reaches store₂ (extend ctx₂ (prunePositions [5] [5, 6]).length)
      (frames.comp (frames.comp (frames.id _) answer₂) pruning₂) [] :=
  .step (MStep.pruneLeft (X := 0) (Y := 1) (xs := [5]) (zs := [5, 6]) rfl (.left .here) (by decide) rfl)
    (.step (MStep.invertLeft (X := 0) (xs := [5]) rfl (by decide)
        (by show 0 ∉ Tm.unknowns (Tm.act pruning₂.1 rhs₂.1); rw [pruned_side]; decide) pruned_inside rfl)
      (.refl []))

theorem pruning_principal :
    frames.Principal store₂ (frames.comp (frames.comp (frames.id _) answer₂) pruning₂) :=
  solved_principal pruning_run

/-! ## Intersection -/

/-- `X` of arity 2. -/
def ctx₃ : Ctx := [2]

/-- `X 5 6`. -/
def lhs₃ : Term ctx₃ := ⟨.app 0 [5, 6], .app rfl⟩

/-- `X 5 7`. -/
def rhs₃ : Term ctx₃ := ⟨.app 0 [5, 7], .app rfl⟩

def store₃ : EquationStore (Term ctx₃) := [(lhs₃, rhs₃)]

/-- The intersection `X := λ a b. X' a`, with `X'` of arity 1 the new unknown 1. -/
def intersecting : Assign ctx₃ (extend ctx₃ (agreePositions [5, 6] [5, 7]).length) :=
  ⟨restrict ctx₃ 0 (agreePositions [5, 6] [5, 7]), restrict_typed rfl agreePositions_below⟩

/-- **Positive: intersection, then deletion, solves the store**, with a principal answer. -/
theorem intersection_run :
    solver.Reaches store₃ (extend ctx₃ (agreePositions [5, 6] [5, 7]).length)
      (frames.comp (frames.comp (frames.id _) (frames.id _)) intersecting) [] :=
  .step (MStep.intersect (X := 0) (xs := [5, 6]) (ys := [5, 7]) rfl rfl (by decide) rfl)
    (.step (MStep.delete (by decide)) (.refl []))

theorem intersection_principal :
    frames.Principal store₃ (frames.comp (frames.comp (frames.id _) (frames.id _)) intersecting) :=
  solved_principal intersection_run

/-! ## Refutations -/

/-- `X` of arity 1. -/
def ctx₄ : Ctx := [1]

/-- `X 5`. -/
def lhs₄ : Term ctx₄ := ⟨.app 0 [5], .app rfl⟩

/-- **Negative: a local outside the arguments is refuted**: `X 5 ≐ 6`. -/
theorem scope_refuted :
    MRefutes [(lhs₄, (⟨.loc 6, .loc 6⟩ : Term ctx₄))] .clash ∧
      ¬ frames.Solvable [(lhs₄, (⟨.loc 6, .loc 6⟩ : Term ctx₄))] := by
  have r : MRefutes [(lhs₄, (⟨.loc 6, .loc 6⟩ : Term ctx₄))] .clash :=
    .scopeLeft (X := 0) (xs := [5]) rfl .here (by decide)
  exact ⟨r, r.sound⟩

/-- `arr (X 5) gnd`. -/
def loop₄ : Term ctx₄ := ⟨.arr (.app 0 [5]) .gnd, .arr (.app rfl) .gnd⟩

/-- **Negative: the occurs check refutes with no well-founded solution**: `X 5 ≐ arr (X 5) gnd`. -/
theorem occurs_refuted :
    MRefutes [(lhs₄, loop₄)] .noWellFoundedSolution ∧ ¬ frames.Solvable [(lhs₄, loop₄)] := by
  have r : MRefutes [(lhs₄, loop₄)] .noWellFoundedSolution :=
    .occursLeft (X := 0) (xs := [5]) (ys := [5]) rfl rfl (.left .here)
  exact ⟨r, r.sound⟩

/-! ## The boundary: repeated arguments -/

/-- `X` of arity 2. -/
def ctx₆ : Ctx := [2]

/-- `X 5 5`. -/
def lhs₆ : Term ctx₆ := ⟨.app 0 [5, 5], .app rfl⟩

/-- `5`. -/
def rhs₆ : Term ctx₆ := ⟨.loc 5, .loc 5⟩

def store₆ : EquationStore (Term ctx₆) := [(lhs₆, rhs₆)]

theorem body_typed (i : Nat) (lt : i < 2) : TyA ctx₆ [] (fun _ => .loc i) := by
  intro W k hW
  match W, hW with
  | 0, hW =>
      simp only [ctx₆, List.getElem?_cons_zero, Option.some.injEq] at hW
      subst hW
      exact ⟨.loc i, .loc lt⟩
  | n + 1, hW => simp [ctx₆] at hW

/-- `X := λ a b. a`. -/
def first : Assign ctx₆ [] := ⟨fun _ => .loc 0, body_typed 0 (by decide)⟩

/-- `X := λ a b. b`. -/
def second : Assign ctx₆ [] := ⟨fun _ => .loc 1, body_typed 1 (by decide)⟩

theorem first_solves : frames.Models first store₆ := by
  intro e he
  simp only [store₆, List.mem_singleton] at he
  subst he
  rfl

theorem second_solves : frames.Models second store₆ := by
  intro e he
  simp only [store₆, List.mem_singleton] at he
  subst he
  rfl

/-- **Negative: with repeated arguments there is no principal answer.** `X 5 5 ≐ 5` is not a pattern; it is
solved by `X := λ a b. a` and by `X := λ a b. b`, and no solution factors both: a principal answer must send `X` to a
local, and a local is fixed by every later instantiation. -/
theorem nonpattern_no_principal :
    ¬ Patterns store₆ ∧ frames.Solvable store₆ ∧
      ∀ (m : Ctx) (σ : Assign ctx₆ m), ¬ frames.Principal store₆ σ := by
  refine ⟨fun h => ?_, ⟨[], first, first_solves⟩, fun m σ principal => ?_⟩
  · have p := (h _ List.mem_cons_self).1
    cases p with
    | app nd => exact absurd nd (by decide)
  · have hs : Tm.rename (Tm.spread [5, 5]) (σ.1 0) = .loc 5 := principal.sound _ List.mem_cons_self
    obtain ⟨i, hi⟩ : ∃ i, σ.1 0 = .loc i := by
      cases h : σ.1 0 with
      | loc i => exact ⟨i, rfl⟩
      | gnd =>
          rw [h] at hs
          cases hs
      | arr _ _ =>
          rw [h] at hs
          cases hs
      | app _ _ =>
          rw [h] at hs
          cases hs
    have key : ∀ g : Assign m [], Tm.act (compA g.1 σ.1) (.app 0 [0, 1]) = .loc (Tm.spread [0, 1] i) := by
      intro g
      show Tm.rename (Tm.spread [0, 1]) (Tm.act g.1 (σ.1 0)) = _
      rw [hi]
      rfl
    obtain ⟨g₀, h₀⟩ := principal.factors [] first first_solves
    obtain ⟨g₁, h₁⟩ := principal.factors [] second second_solves
    have e₀ : Tm.loc 0 = Tm.loc (Tm.spread [0, 1] i) :=
      (h₀ (⟨.app 0 [0, 1], .app rfl⟩ : Term ctx₆)).trans (key g₀)
    have e₁ : Tm.loc 1 = Tm.loc (Tm.spread [0, 1] i) :=
      (h₁ (⟨.app 0 [0, 1], .app rfl⟩ : Term ctx₆)).trans (key g₁)
    have contra := e₀.trans e₁.symm
    cases contra

end Controls

end MillerCodes

#print axioms MillerCodes.Controls.inversion_run
#print axioms MillerCodes.Controls.inversion_principal
#print axioms MillerCodes.Controls.pruning_run
#print axioms MillerCodes.Controls.pruning_principal
#print axioms MillerCodes.Controls.intersection_run
#print axioms MillerCodes.Controls.intersection_principal
#print axioms MillerCodes.Controls.scope_refuted
#print axioms MillerCodes.Controls.occurs_refuted
#print axioms MillerCodes.Controls.nonpattern_no_principal

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
