import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.CumulativeCodes

/-!
# The cross store with level variables: its principality is a level constraint

Over `X : Sort a ⟶ Sort a` and `Y : Sort b ⟶ Sort b`, with the parameter of `Sort a`, the store

  `X par ≐ Y par`   (that is, `λ (x : Sort a). X x ≐ λ (x : Sort a). Y x`)

is typed under the cumulativity constraint `a ≤ b`: the parameter, of `Sort a`, is passed to `Y`,
which expects `Sort b`. At every valuation of the levels that satisfies `a ≤ b`:

* the store is solvable: the identity and the constant family at the ground type solve it
  (`identity_solves`, `constant_solves`);
* the answer sending both unknowns to one unknown `U : Sort b ⟶ Sort a` solves it
  (`answer_solves`);
* **the store has a principal answer exactly when `b ≤ a`** (`principal_iff`); then that answer is
  principal (`answer_principal`), and since it is an epimorphism (`answer_epi`) it is the initial
  solution (`answer_initial`); when `a < b` no answer is principal (`no_principal`).

So the store's lack of a most general answer is the level constraint `b ≤ a`, not a property of
its terms. The cumulativity constraint neither entails nor refutes `b ≤ a` (`pending_undecided`):
a solver that decides levels with `decideSat` keeps the equation and records `b ≤ a` as the
constraint it waits on. The answer together with `b ≤ a` is a principal constrained answer
(`postponed_level_constraint`). Keeping the equation is exact (`postponing_exact`), and where
`a < b` every run of every exact solver that stops, stops postponed (`forced_postponement`).

Positive control: at `a = b` the answer is principal. Negative control: at `a = 0` and `b = 1`,
the universes of the refuted promise, the store is solvable and no answer is principal
(`plain_principality_fails`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

open Interface

namespace CumulativeCodes

namespace Cross

/-- The level variables `a` (index 0) and `b` (index 1). -/
abbrev a : Level := .param 0
abbrev b : Level := .param 1

/-- `X : Sort a ⟶ Sort a` is unknown 0 and `Y : Sort b ⟶ Sort b` is unknown 1. -/
def ctx : Ctx := [⟨a, a⟩, ⟨b, b⟩]

/-- `X par`. -/
def X : Term ctx := ⟨.app 0 .par, .app (by decide) .par⟩

/-- `Y par`. -/
def Y : Term ctx := ⟨.app 1 .par, .app (by decide) .par⟩

/-- **The cross store**: `X par ≐ Y par`. -/
def store : EquationStore (Term ctx) := [(X, Y)]

/-- Its cumulativity constraint, `a ≤ b`. -/
def levels : LevelStore := [⟨a, b⟩]

/-- The level constraint its principality waits on, `b ≤ a`. -/
def pending : LevelLe := ⟨b, a⟩

variable {v : Nat → Nat}

theorem tyA {Γ : Ctx} {σ : Nat → Tm}
    (hX : Ty v Γ (Level.value v a) (σ 0) (Level.value v a))
    (hY : Ty v Γ (Level.value v b) (σ 1) (Level.value v b)) : TyA v ctx Γ σ := by
  intro W d h
  match W, h with
  | 0, h =>
      simp only [ctx, List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact hX
  | 1, h =>
      simp only [ctx, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact hY
  | n + 2, h => simp [ctx] at h

/-- A typed assignment solves the store exactly when it gives `X` and `Y` the same body, once
levels are evaluated. -/
theorem solves_iff {Γ : Ctx} (σ : Assign v ctx Γ) :
    (frames v).Models σ store ↔ Tm.lower v (σ.1 0) = Tm.lower v (σ.1 1) := by
  rw [models_iff]
  constructor
  · intro h
    have := h (X, Y) (List.mem_singleton_self _)
    simpa [X, Y, Tm.act] using this
  · intro h e he
    simp only [store, List.mem_singleton] at he
    subst he
    simpa [X, Y, Tm.act] using h

/-- The identity on both universes. -/
def identity (v : Nat → Nat) : Assign v ctx [] :=
  ⟨fun _ => .par, tyA (.par le_rfl) (.par le_rfl)⟩

/-- The constant family at the ground type. -/
def constant (v : Nat → Nat) : Assign v ctx [] :=
  ⟨fun _ => .gnd, tyA .gnd .gnd⟩

theorem identity_solves (v : Nat → Nat) : (frames v).Models (identity v) store :=
  (solves_iff _).mpr rfl

theorem constant_solves (v : Nat → Nat) : (frames v).Models (constant v) store :=
  (solves_iff _).mpr rfl

/-- **The cross store is solvable at every valuation.** -/
theorem solvable (v : Nat → Nat) : (frames v).Solvable store :=
  ⟨[], identity v, identity_solves v⟩

/-- The context of the answer: one unknown `U : Sort b ⟶ Sort a`. -/
def answerCtx : Ctx := [⟨b, a⟩]

theorem answer_typed (le : Level.value v a ≤ Level.value v b) :
    TyA v ctx answerCtx (fun _ => .app 0 .par) :=
  tyA (Ty.app (d := ⟨b, a⟩) rfl (.par le) le_rfl) (Ty.app (d := ⟨b, a⟩) rfl (.par le_rfl) le)

/-- **The answer**: `X := U`, `Y := U`, with `U : Sort b ⟶ Sort a`. It is typed under `a ≤ b`. -/
def answer (v : Nat → Nat) (le : Level.value v a ≤ Level.value v b) : Assign v ctx answerCtx :=
  ⟨fun _ => .app 0 .par, answer_typed le⟩

theorem answer_solves (le : Level.value v a ≤ Level.value v b) :
    (frames v).Models (answer v le) store :=
  (solves_iff _).mpr rfl

/-- **Positive control: under `b ≤ a` the answer is principal.** -/
theorem answer_principal (le : Level.value v a ≤ Level.value v b)
    (ge : Level.value v b ≤ Level.value v a) : (frames v).Principal store (answer v le) := by
  refine ⟨answer_solves le, ?_⟩
  intro Θ f solved
  have same := (solves_iff f).mp solved
  have tyY : Ty v Θ (Level.value v b) (f.1 1) (Level.value v b) := f.2 1 ⟨b, b⟩ rfl
  have typed : TyA v answerCtx Θ (fun _ => f.1 1) := by
    intro W d h
    match W, h with
    | 0, h =>
        simp only [answerCtx, List.getElem?_cons_zero, Option.some.injEq] at h
        subst h
        exact tyY.mono ge
    | n + 1, h => simp [answerCtx] at h
  refine ⟨⟨fun _ => f.1 1, typed⟩, ?_⟩
  refine agree_of_unknowns (f := f) (g := (frames v).comp ⟨fun _ => f.1 1, typed⟩ (answer v le)) ?_
  intro W hW
  show Tm.lower v (f.1 W) = Tm.lower v (Tm.compA (fun _ => f.1 1) (fun _ => Tm.app 0 Tm.par) W)
  simp only [Tm.compA, Tm.act, Tm.inst_par_self]
  match W, hW with
  | 0, _ => exact same
  | 1, _ => rfl
  | n + 2, h => simp [ctx] at h

/-- The answer is an epimorphism on terms: two assignments that agree after it agree on `U`. -/
theorem answer_epi (le : Level.value v a ≤ Level.value v b) : EpiOnTerms (frames v) (answer v le) := by
  intro Γ g h same
  apply agree_of_unknowns
  intro W hW
  have hW0 : W = 0 := by
    simp only [answerCtx, List.length_cons, List.length_nil] at hW
    omega
  subst hW0
  have h' : Tm.lower v (Tm.act g.1 (Tm.act (answer v le).1 X.1)) =
      Tm.lower v (Tm.act h.1 (Tm.act (answer v le).1 X.1)) := same X
  simpa only [X, answer, Tm.act, Tm.inst, Tm.inst_par_self] using h'

/-- **The universal property, concretely: under `b ≤ a` the answer is the initial solution** of the
cross store: every solution factors through it, uniquely up to the frame's equality. -/
theorem answer_initial (le : Level.value v a ≤ Level.value v b)
    (ge : Level.value v b ≤ Level.value v a) : InitialSolution (frames v) store (answer v le) :=
  Principal.initial (answer_principal le ge) (answer_epi le)

/-- **Negative control: when `a < b` no answer is principal.** The identity and the constant
family both factor through a principal answer; the body it gives `Y` would then be a code of
`Sort a` over a parameter of `Sort b` whose instance is that parameter. -/
theorem no_principal (lt : Level.value v a < Level.value v b) {Γ : Ctx} (σ : Assign v ctx Γ) :
    ¬ (frames v).Principal store σ := by
  intro principal
  have same := (solves_iff σ).mp principal.sound
  obtain ⟨g₁, h₁⟩ := principal.factors [] (identity v) (identity_solves v)
  obtain ⟨g₂, h₂⟩ := principal.factors [] (constant v) (constant_solves v)
  have e₁ : Tm.act (fun W => Tm.lower v (g₁.1 W)) (Tm.lower v (σ.1 1)) = .par := by
    have h : Tm.lower v (Tm.act (identity v).1 Y.1) =
        Tm.lower v (Tm.act (Tm.compA g₁.1 σ.1) Y.1) := h₁ Y
    simp only [identity, Y, Tm.act, Tm.compA, Tm.inst_par_self, Tm.lower] at h
    rw [Tm.lower_act] at h
    exact h.symm
  have e₂ : Tm.act (fun W => Tm.lower v (g₂.1 W)) (Tm.lower v (σ.1 1)) = .gnd := by
    have h : Tm.lower v (Tm.act (constant v).1 Y.1) =
        Tm.lower v (Tm.act (Tm.compA g₂.1 σ.1) Y.1) := h₂ Y
    simp only [constant, Y, Tm.act, Tm.compA, Tm.inst_par_self, Tm.inst, Tm.lower] at h
    rw [Tm.lower_act] at h
    exact h.symm
  have tyX : Ty v Γ (Level.value v a) (Tm.lower v (σ.1 0)) (Level.value v a) :=
    (σ.2 0 ⟨a, a⟩ rfl).lower
  have tyY : Ty v Γ (Level.value v b) (Tm.lower v (σ.1 1)) (Level.value v b) :=
    (σ.2 1 ⟨b, b⟩ rfl).lower
  rw [same] at tyX
  generalize Tm.lower v (σ.1 1) = s at e₁ e₂ tyX tyY
  cases s with
  | par => simp [Tm.act] at e₂
  | gnd => simp [Tm.act] at e₁
  | sort k => simp [Tm.act] at e₁
  | arr A B => simp [Tm.act] at e₁
  | app W t =>
      obtain ⟨d, hd, _, hc⟩ := Ty.app_inv tyX
      obtain ⟨d', hd', ht', _⟩ := Ty.app_inv tyY
      rw [hd] at hd'
      cases hd'
      have small : Ty v Γ (Level.value v b) (.app W t) (Level.value v a) := .app hd ht' hc
      have moved := Ty.act g₁.2.lower small
      rw [e₁] at moved
      have := Ty.par_inv moved
      omega

/-- **Principality of the cross store is the level constraint `b ≤ a`.** -/
theorem principal_iff (le : Level.value v a ≤ Level.value v b) :
    (∃ (Γ : Ctx) (σ : Assign v ctx Γ), (frames v).Principal store σ) ↔ pending.Holds v := by
  constructor
  · rintro ⟨Γ, σ, principal⟩
    by_contra h
    simp only [pending, LevelLe.Holds] at h
    exact no_principal (by omega) σ principal
  · intro ge
    exact ⟨answerCtx, answer v le, answer_principal le ge⟩

/-- The cumulativity constraint neither entails nor refutes the pending one. -/
theorem pending_undecided :
    ¬ levels.Entails pending ∧ ¬ levels.Entails (LevelStore.negation pending) ∧
      LevelStore.Satisfiable (pending :: levels) ∧
      LevelStore.Satisfiable (LevelStore.negation pending :: levels) :=
  ⟨by decide, by decide, by decide, by decide⟩

theorem le_of_satisfies {v : Nat → Nat} (sat : levels.Satisfies v) :
    Level.value v a ≤ Level.value v b :=
  sat ⟨a, b⟩ (List.mem_singleton_self _)

/-- **The cross store becomes a postponed level constraint with a principal constrained answer.**
The pending constraint `b ≤ a` is undecided by the cumulativity constraint; at every valuation that
satisfies the cumulativity constraint the store is solvable, the answer solves it, the store has a
principal answer exactly when the pending constraint holds, and then the answer is principal. -/
theorem postponed_level_constraint :
    (¬ levels.Entails pending ∧ ¬ levels.Entails (LevelStore.negation pending)) ∧
      ∀ (v : Nat → Nat) (sat : levels.Satisfies v),
        (frames v).Solvable store ∧
        (frames v).Models (answer v (le_of_satisfies sat)) store ∧
        ((∃ (Γ : Ctx) (σ : Assign v ctx Γ), (frames v).Principal store σ) ↔ pending.Holds v) ∧
        (pending.Holds v → (frames v).Principal store (answer v (le_of_satisfies sat))) :=
  ⟨⟨pending_undecided.1, pending_undecided.2.1⟩, fun v sat =>
    ⟨solvable v, answer_solves _, principal_iff (le_of_satisfies sat),
      fun ge => answer_principal _ ge⟩⟩

/-- Keeping the equation is an exact transition. -/
theorem postponing_exact (v : Nat → Nat) : Exact (frames v) store ((frames v).id ctx) store :=
  exact_id_of_equivalent (fun _ _ => Iff.rfl)

/-- **Where `a < b`, postponement is forced**: every run of every exact solver on the cross store
keeps a nonempty residual that no refutation applies to, and the residual is exact. -/
theorem forced_postponement (lt : Level.value v a < Level.value v b) (P : Solver (frames v))
    {m : Ctx} {σ : Assign v ctx m} {R : EquationStore (Term m)} (run : P.Reaches store m σ R) :
    R ≠ [] ∧ (∀ r : Reason, ¬ P.Refutes R r) ∧ Exact (frames v) store σ R :=
  postponed_of_solvable_no_principal (solvable v) (fun _ σ => no_principal lt σ) run

/-- **Negative control at the universes of the refuted promise** (`a = 0`, `b = 1`): the store is
solvable and no answer is principal. -/
theorem plain_principality_fails :
    (frames (fun i => i)).Solvable store ∧
      ∀ (Γ : Ctx) (σ : Assign (fun i => i) ctx Γ), ¬ (frames (fun i => i)).Principal store σ :=
  ⟨solvable _, fun _ σ => no_principal (by decide) σ⟩

/-- **Positive control at equal universes** (`a = b = 1`). -/
theorem principal_at_equal_levels :
    (frames (fun _ => 1)).Principal store (answer (fun _ => 1) le_rfl) :=
  answer_principal le_rfl le_rfl

end Cross

end CumulativeCodes

#print axioms CumulativeCodes.Cross.principal_iff
#print axioms CumulativeCodes.Cross.no_principal
#print axioms CumulativeCodes.Cross.answer_principal
#print axioms CumulativeCodes.Cross.answer_initial
#print axioms CumulativeCodes.Cross.postponed_level_constraint
#print axioms CumulativeCodes.Cross.forced_postponement
#print axioms CumulativeCodes.Cross.plain_principality_fails
#print axioms CumulativeCodes.Cross.principal_at_equal_levels

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
