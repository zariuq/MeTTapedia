import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.CumulativeCodes

/-!
# A solver for cumulative codes: exact rules, termination, and decision on uniform patterns

The solver works on the first equation of a store, at a valuation `v` of the level variables.

* `delete`: an equation whose sides are the same code once levels are evaluated is removed.
* `decompose`: `arr A B ≐ arr A' B'` becomes `A ≐ A'` and `B ≐ B'`.
* `solveLeft`, `solveRight`: `X par ≐ t` with `X` not in `t` instantiates `X` by `t` everywhere,
  provided `t` is a code of `X`'s declaration (the assignment must be typed).

Refutations, with their reason as data:

* `clash`: two different rigid heads;
* `levels`: `sort k ≐ sort k'` where `k` and `k'` have different values;
* `occursLeft`, `occursRight`: `X par ≐ t` where `t` is a pattern that properly contains `X`:
  **no well-founded solution** (the instance of `t` is larger than the instance of `X`).

**Every transition is exact** (`Rule.exact`) and every refutation is sound (`Refutes.sound`), so
`solver v` is a `Solver` of the frames, and the general theorems apply: a run that empties the
store gives a principal answer, a refuted run leaves no solution, and a run that stops with
equations left has an exact residual.

**Termination** on every store: each transition lowers the rank (the number of unknowns that
occur, then the size), lexicographically (`Rule.rank_lt`, `rules_terminate`).

**Decision on the uniform pattern fragment** (`Uniform`): every unknown is declared
`Sort p ⟶ Sort ℓ`, the parameter is of `Sort p`, every side is a pattern (each unknown is applied to
the parameter) and a code of `Sort ℓ`. On it the solver is never stopped with equations left
(`progress`); so every store of the fragment is decided: it reaches the empty store or a refutation
(`decided`), hence has a principal answer or no solution (`principal_or_unsolvable`).

The fragment's two conditions are sufficient, not the boundary. Outside "the parameter is of the
unknown's domain", principality can fail (the cross store, `CrossStoreLevels`). The "one codomain"
condition is stricter than necessary: `MeetSolver` decides the larger fragment of compatible groups
by meet narrowing (`MeetSolver.principal_or_unsolvable`), and even that fragment is not the
boundary (`outside_solved`).

Positive examples: `X par ≐ arr (V par) gnd` is solved; `arr A B ≐ arr A B` is deleted. Negative
examples: `X par ≐ arr (X par) gnd` is refuted with no well-founded solution; `gnd ≐ arr gnd gnd`
is a clash (`PatternSolverControls`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

open Interface

namespace CumulativeCodes

namespace Tm

/-- Every unknown in the code is applied to the parameter. -/
inductive Pattern : Tm → Prop
  | par : Pattern .par
  | gnd : Pattern .gnd
  | sort (l : Level) : Pattern (.sort l)
  | arr {A B : Tm} : Pattern A → Pattern B → Pattern (.arr A B)
  | app (W : Nat) : Pattern (.app W .par)

/-- The unknowns of a code. -/
def unknowns : Tm → Finset Nat
  | par => ∅
  | gnd => ∅
  | sort _ => ∅
  | arr A B => unknowns A ∪ unknowns B
  | app W t => insert W (unknowns t)

/-- The head of a rigid code; an applied unknown has none. -/
def head? : Tm → Option Nat
  | par => some 0
  | gnd => some 1
  | sort _ => some 2
  | arr _ _ => some 3
  | app _ _ => none

theorem occurs_iff (X : Nat) : ∀ t : Tm, occurs X t = true ↔ X ∈ unknowns t
  | par => by simp [occurs, unknowns]
  | gnd => by simp [occurs, unknowns]
  | sort _ => by simp [occurs, unknowns]
  | arr A B => by
      simp only [occurs, unknowns, Bool.or_eq_true, Finset.mem_union, occurs_iff X A,
        occurs_iff X B]
  | app W t => by
      simp only [occurs, unknowns, Bool.or_eq_true, beq_iff_eq, Finset.mem_insert, occurs_iff X t]
      exact or_congr_left eq_comm

theorem size_lower (v : Nat → Nat) : ∀ t : Tm, size (lower v t) = size t
  | par => rfl
  | gnd => rfl
  | sort _ => rfl
  | arr A B => by simp only [lower, size, size_lower v A, size_lower v B]
  | app W t => by simp only [lower, size, size_lower v t]

theorem unknowns_inst (u : Tm) : ∀ t : Tm, unknowns (inst u t) ⊆ unknowns t ∪ unknowns u
  | par => by simp [inst, unknowns]
  | gnd => by simp [inst, unknowns]
  | sort _ => by simp [inst, unknowns]
  | arr A B => by
      intro x hx
      simp only [inst, unknowns, Finset.mem_union] at hx ⊢
      rcases hx with hx | hx
      · rcases Finset.mem_union.mp (unknowns_inst u A hx) with h | h <;> simp [h]
      · rcases Finset.mem_union.mp (unknowns_inst u B hx) with h | h <;> simp [h]
  | app W t => by
      intro x hx
      simp only [inst, unknowns, Finset.mem_insert, Finset.mem_union] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inl (Or.inl hx)
      · rcases Finset.mem_union.mp (unknowns_inst u t hx) with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h

/-- Instantiating `X` by `u` removes `X` and adds at most the unknowns of `u`. -/
theorem unknowns_act_update (X : Nat) (u : Tm) :
    ∀ t : Tm, unknowns (act (Function.update idA X u) t) ⊆ (unknowns t).erase X ∪ unknowns u
  | par => by simp [act, unknowns]
  | gnd => by simp [act, unknowns]
  | sort _ => by simp [act, unknowns]
  | arr A B => by
      intro x hx
      simp only [act, unknowns, Finset.mem_union] at hx
      simp only [unknowns, Finset.mem_union, Finset.mem_erase]
      rcases hx with hx | hx
      · rcases Finset.mem_union.mp (unknowns_act_update X u A hx) with h | h
        · exact Or.inl ⟨(Finset.mem_erase.mp h).1, Or.inl (Finset.mem_erase.mp h).2⟩
        · exact Or.inr h
      · rcases Finset.mem_union.mp (unknowns_act_update X u B hx) with h | h
        · exact Or.inl ⟨(Finset.mem_erase.mp h).1, Or.inr (Finset.mem_erase.mp h).2⟩
        · exact Or.inr h
  | app W t => by
      intro x hx
      have hx' := unknowns_inst _ _ hx
      simp only [unknowns, Finset.mem_union, Finset.mem_erase, Finset.mem_insert]
      rcases Finset.mem_union.mp hx' with h | h
      · by_cases hW : W = X
        · subst hW
          rw [Function.update_self] at h
          exact Or.inr h
        · rw [Function.update_of_ne hW] at h
          simp only [idA, unknowns, Finset.mem_insert] at h
          rcases h with h | h
          · subst h
            exact Or.inl ⟨hW, Or.inl rfl⟩
          · simp at h
      · rcases Finset.mem_union.mp (unknowns_act_update X u t h) with h | h
        · exact Or.inl ⟨(Finset.mem_erase.mp h).1, Or.inr (Finset.mem_erase.mp h).2⟩
        · exact Or.inr h

theorem Pattern.act {σ : Nat → Tm} (hσ : ∀ W, Pattern (σ W)) :
    ∀ {t : Tm}, Pattern t → Pattern (Tm.act σ t)
  | _, .par => .par
  | _, .gnd => .gnd
  | _, .sort l => .sort l
  | _, .arr hA hB => .arr (Pattern.act hσ hA) (Pattern.act hσ hB)
  | _, .app W => by
      show Pattern (inst Tm.par (σ W))
      rw [inst_par_self]
      exact hσ W

/-- In a pattern, an occurrence of `X` makes the instance at least as large as `X`'s body. -/
theorem size_le_of_mem {σ : Nat → Tm} {X : Nat} :
    ∀ {t : Tm}, Pattern t → X ∈ unknowns t → size (σ X) ≤ size (Tm.act σ t)
  | _, .par, h => by simp [unknowns] at h
  | _, .gnd, h => by simp [unknowns] at h
  | _, .sort _, h => by simp [unknowns] at h
  | _, .arr hA hB, h => by
      simp only [unknowns, Finset.mem_union] at h
      simp only [Tm.act, size]
      rcases h with h | h
      · have := size_le_of_mem (σ := σ) hA h
        omega
      · have := size_le_of_mem (σ := σ) hB h
        omega
  | _, .app W, h => by
      simp only [unknowns, Finset.mem_insert] at h
      rcases h with h | h
      · subst h
        show size (σ X) ≤ size (inst Tm.par (σ X))
        rw [inst_par_self]
      · simp at h

/-- **The occurs check's measure**: a pattern that properly contains `X` has a larger instance than
`X`. -/
theorem size_lt_of_occurs {σ : Nat → Tm} {X : Nat} {t : Tm} (hp : Pattern t)
    (hX : X ∈ unknowns t) (hne : t ≠ .app X .par) : size (σ X) < size (Tm.act σ t) := by
  cases hp with
  | par => simp [unknowns] at hX
  | gnd => simp [unknowns] at hX
  | sort _ => simp [unknowns] at hX
  | arr hA hB =>
      simp only [unknowns, Finset.mem_union] at hX
      simp only [Tm.act, size]
      rcases hX with h | h
      · have := size_le_of_mem (σ := σ) hA h
        omega
      · have := size_le_of_mem (σ := σ) hB h
        omega
  | app W =>
      simp only [unknowns, Finset.mem_insert] at hX
      rcases hX with h | h
      · subst h
        exact absurd rfl hne
      · simp at h

/-- A rigid head survives acting and evaluating levels. -/
theorem head?_lower_act (v : Nat → Nat) (σ : Nat → Tm) {t : Tm} {h : Nat}
    (ht : head? t = some h) : head? (lower v (Tm.act σ t)) = some h := by
  cases t with
  | par => exact ht
  | gnd => exact ht
  | sort _ => exact ht
  | arr _ _ => exact ht
  | app _ _ => cases ht

end Tm

/-! ## Measures of stores -/

def storeUnknowns {Δ : Ctx} : EquationStore (Term Δ) → Finset Nat
  | [] => ∅
  | e :: S => Tm.unknowns e.1.1 ∪ Tm.unknowns e.2.1 ∪ storeUnknowns S

def storeSize {Δ : Ctx} : EquationStore (Term Δ) → Nat
  | [] => 0
  | e :: S => Tm.size e.1.1 + Tm.size e.2.1 + storeSize S

/-- The rank of a store: the number of unknowns that occur, then the size. -/
def rank {Δ : Ctx} (S : EquationStore (Term Δ)) : Nat × Nat :=
  ((storeUnknowns S).card, storeSize S)

/-- The lexicographic order of ranks. -/
def RankLt (x y : Nat × Nat) : Prop := Prod.Lex (· < ·) (· < ·) x y

theorem rankLt_wf : WellFounded RankLt := (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf

theorem rankLt_of {x y : Nat × Nat} (h₁ : x.1 ≤ y.1) (h₂ : x.1 = y.1 → x.2 < y.2) : RankLt x y := by
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  rcases Nat.lt_or_eq_of_le h₁ with h | h
  · exact Prod.Lex.left _ _ h
  · simp only at h
    subst h
    exact Prod.Lex.right _ (h₂ rfl)

theorem storeUnknowns_applyStore {v : Nat → Nat} {Δ : Ctx} {σ : Assign v Δ Δ} {X : Nat} {u : Tm}
    (hσ : σ.1 = Function.update Tm.idA X u) :
    ∀ S : EquationStore (Term Δ),
      storeUnknowns ((frames v).applyStore σ S) ⊆ (storeUnknowns S).erase X ∪ Tm.unknowns u
  | [] => by simp [Frames.applyStore, storeUnknowns]
  | e :: S => by
      intro x hx
      have rest := storeUnknowns_applyStore hσ S
      simp only [Frames.applyStore, List.map_cons, storeUnknowns, Finset.mem_union] at hx
      simp only [storeUnknowns, Finset.mem_union, Finset.mem_erase]
      have left : Tm.unknowns (Tm.act σ.1 e.1.1) ⊆ (Tm.unknowns e.1.1).erase X ∪ Tm.unknowns u := by
        rw [hσ]
        exact Tm.unknowns_act_update X u e.1.1
      have right : Tm.unknowns (Tm.act σ.1 e.2.1) ⊆ (Tm.unknowns e.2.1).erase X ∪ Tm.unknowns u := by
        rw [hσ]
        exact Tm.unknowns_act_update X u e.2.1
      rcases hx with (hx | hx) | hx
      · rcases Finset.mem_union.mp (left hx) with h | h
        · exact Or.inl ⟨(Finset.mem_erase.mp h).1, Or.inl (Or.inl (Finset.mem_erase.mp h).2)⟩
        · exact Or.inr h
      · rcases Finset.mem_union.mp (right hx) with h | h
        · exact Or.inl ⟨(Finset.mem_erase.mp h).1, Or.inl (Or.inr (Finset.mem_erase.mp h).2)⟩
        · exact Or.inr h
      · have hx' : x ∈ storeUnknowns ((frames v).applyStore σ S) := by
          simpa [Frames.applyStore] using hx
        rcases Finset.mem_union.mp (rest hx') with h | h
        · exact Or.inl ⟨(Finset.mem_erase.mp h).1, Or.inr (Finset.mem_erase.mp h).2⟩
        · exact Or.inr h

/-! ## The rules -/

variable {v : Nat → Nat}

/-- **The transitions.** -/
inductive Rule (v : Nat → Nat) : {Δ : Ctx} → EquationStore (Term Δ) → (m : Ctx) → Assign v Δ m →
    EquationStore (Term m) → Prop
  | delete {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} :
      Tm.lower v e.1.1 = Tm.lower v e.2.1 → Rule v (e :: S) Δ ((frames v).id Δ) S
  | decompose {Δ : Ctx} {e e₁ e₂ : Equation (Term Δ)} {S : EquationStore (Term Δ)}
      {A B A' B' : Tm} :
      e.1.1 = .arr A B → e.2.1 = .arr A' B' → e₁.1.1 = A → e₁.2.1 = A' → e₂.1.1 = B →
      e₂.2.1 = B' → Rule v (e :: S) Δ ((frames v).id Δ) (e₁ :: e₂ :: S)
  | solveLeft {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} {X : Nat}
      {σ : Assign v Δ Δ} :
      e.1.1 = .app X .par → Tm.occurs X e.2.1 = false →
      σ.1 = Function.update Tm.idA X e.2.1 → Rule v (e :: S) Δ σ ((frames v).applyStore σ S)
  | solveRight {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} {X : Nat}
      {σ : Assign v Δ Δ} :
      e.2.1 = .app X .par → Tm.occurs X e.1.1 = false →
      σ.1 = Function.update Tm.idA X e.1.1 → Rule v (e :: S) Δ σ ((frames v).applyStore σ S)

/-- **The refutations**, with their reasons. -/
inductive Refutes (v : Nat → Nat) : {Δ : Ctx} → EquationStore (Term Δ) → Reason → Prop
  | clash {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} {h h' : Nat} :
      Tm.head? e.1.1 = some h → Tm.head? e.2.1 = some h' → h ≠ h' → Refutes v (e :: S) .clash
  | levels {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} {k k' : Level} :
      e.1.1 = .sort k → e.2.1 = .sort k' → Level.value v k ≠ Level.value v k' →
      Refutes v (e :: S) .levels
  | occursLeft {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} {X : Nat} :
      e.1.1 = .app X .par → Tm.Pattern e.2.1 → X ∈ Tm.unknowns e.2.1 → e.2.1 ≠ .app X .par →
      Refutes v (e :: S) .noWellFoundedSolution
  | occursRight {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} {X : Nat} :
      e.2.1 = .app X .par → Tm.Pattern e.1.1 → X ∈ Tm.unknowns e.1.1 → e.1.1 ≠ .app X .par →
      Refutes v (e :: S) .noWellFoundedSolution

/-- The first equation of a solved store is solved. -/
theorem solves_head {Δ Γ : Ctx} {f : Assign v Δ Γ} {e : Equation (Term Δ)}
    {S : EquationStore (Term Δ)} (solved : (frames v).Models f (e :: S)) :
    Tm.lower v (Tm.act f.1 e.1.1) = Tm.lower v (Tm.act f.1 e.2.1) :=
  solved e List.mem_cons_self

theorem act_app_par (σ : Nat → Tm) (X : Nat) : Tm.act σ (.app X .par) = σ X := by
  show Tm.inst .par (σ X) = σ X
  exact Tm.inst_par_self _

/-- **Every refutation is sound.** -/
theorem Refutes.sound {Δ : Ctx} {S : EquationStore (Term Δ)} {r : Reason} (refuted : Refutes v S r) :
    ¬ (frames v).Solvable S := by
  rintro ⟨Γ, f, solved⟩
  cases refuted with
  | clash h₁ h₂ ne =>
      have same := solves_head solved
      have one := Tm.head?_lower_act v f.1 h₁
      have two := Tm.head?_lower_act v f.1 h₂
      rw [same, two] at one
      exact ne (Option.some.inj one).symm
  | levels h₁ h₂ ne =>
      have same := solves_head solved
      rw [h₁, h₂] at same
      exact ne (Mettapedia.TypeTheory.UniverseLevel.LevelExpr.const.inj (Tm.sort.inj same))
  | occursLeft h₁ hp hX hne =>
      have same := solves_head solved
      rw [h₁, act_app_par] at same
      have sizes := congrArg Tm.size same
      rw [Tm.size_lower, Tm.size_lower] at sizes
      have := Tm.size_lt_of_occurs (σ := f.1) hp hX hne
      omega
  | occursRight h₂ hp hX hne =>
      have same := solves_head solved
      rw [h₂, act_app_par] at same
      have sizes := congrArg Tm.size same
      rw [Tm.size_lower, Tm.size_lower] at sizes
      have := Tm.size_lt_of_occurs (σ := f.1) hp hX hne
      omega

/-- Equations with the same solutions can replace each other at the head of a store. -/
theorem equivalent_cons {Δ : Ctx} {e : Equation (Term Δ)} {S S' : EquationStore (Term Δ)}
    (head : ∀ (Γ : Ctx) (f : Assign v Δ Γ), (frames v).Solves f e ↔ (frames v).Models f S')
    : (frames v).Equivalent (e :: S) (S' ++ S) := by
  intro Γ f
  constructor
  · intro solved
    rw [Frames.models_append]
    exact ⟨(head Γ f).mp (solved e List.mem_cons_self),
      fun e'' he'' => solved e'' (List.mem_cons_of_mem _ he'')⟩
  · intro solved e'' he''
    rw [Frames.models_append] at solved
    rcases List.mem_cons.mp he'' with rfl | he''
    · exact (head Γ f).mpr solved.1
    · exact solved.2 e'' he''

/-- **The solving transition is exact.** -/
theorem solve_exact {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} {X : Nat}
    {σ : Assign v Δ Δ} (hl : e.1.1 = .app X .par) (fresh : Tm.occurs X e.2.1 = false)
    (hσ : σ.1 = Function.update Tm.idA X e.2.1) :
    Exact (frames v) (e :: S) σ ((frames v).applyStore σ S) := by
  have fixes : Tm.act σ.1 e.2.1 = e.2.1 := by
    rw [Tm.act_congr_occurs (τ := Tm.idA)
      (fun V hV => by rw [hσ, Function.update_of_ne hV]) e.2.1 fresh, Tm.act_id]
  have atX : σ.1 X = e.2.1 := by rw [hσ, Function.update_self]
  intro Γ f
  constructor
  · intro solved
    have first : Tm.lower v (f.1 X) = Tm.lower v (Tm.act f.1 e.2.1) := by
      have h := solves_head solved
      rw [hl, act_app_par] at h
      exact h
    have agree : Agree (frames v) f ((frames v).comp f σ) := by
      apply agree_of_unknowns
      intro W _
      show Tm.lower v (f.1 W) = Tm.lower v (Tm.act f.1 (σ.1 W))
      by_cases hW : W = X
      · subst hW
        rw [atX]
        exact first
      · rw [hσ, Function.update_of_ne hW]
        show Tm.lower v (f.1 W) = Tm.lower v (Tm.act f.1 (.app W .par))
        rw [act_app_par]
    refine ⟨f, agree, ?_⟩
    rw [Frames.models_applyStore]
    exact (models_of_agree agree S).mp (fun e' he' => solved e' (List.mem_cons_of_mem _ he'))
  · rintro ⟨g, fg, solvedG⟩
    rw [Frames.models_applyStore] at solvedG
    apply (models_of_agree fg (e :: S)).mpr
    intro e' he'
    rcases List.mem_cons.mp he' with rfl | he'
    · show Tm.lower v (Tm.act (Tm.compA g.1 σ.1) e'.1.1) =
        Tm.lower v (Tm.act (Tm.compA g.1 σ.1) e'.2.1)
      rw [Tm.act_comp, Tm.act_comp, fixes, hl, act_app_par, atX]
    · exact solvedG e' he'

/-- Swapping the sides of the head equation keeps the solutions. -/
theorem exact_swap {Δ m : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)}
    {σ : Assign v Δ m} {R : EquationStore (Term m)} (exact : Exact (frames v) ((e.2, e.1) :: S) σ R) :
    Exact (frames v) (e :: S) σ R := by
  intro Γ f
  rw [← exact Γ f]
  constructor
  · intro solved e' he'
    rcases List.mem_cons.mp he' with rfl | he'
    · exact ((frames v).equivalence Γ).symm (solved e List.mem_cons_self)
    · exact solved e' (List.mem_cons_of_mem _ he')
  · intro solved e' he'
    rcases List.mem_cons.mp he' with rfl | he'
    · exact ((frames v).equivalence Γ).symm (solved _ List.mem_cons_self)
    · exact solved e' (List.mem_cons_of_mem _ he')

theorem delete_exact {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)}
    (same : Tm.lower v e.1.1 = Tm.lower v e.2.1) :
    Exact (frames v) (e :: S) ((frames v).id Δ) S := by
  apply exact_id_of_equivalent
  intro Γ f
  constructor
  · intro solved e' he'
    exact solved e' (List.mem_cons_of_mem _ he')
  · intro solved e' he'
    rcases List.mem_cons.mp he' with rfl | he'
    · show Tm.lower v (Tm.act f.1 e'.1.1) = Tm.lower v (Tm.act f.1 e'.2.1)
      rw [Tm.lower_act, Tm.lower_act, same]
    · exact solved e' he'

theorem decompose_exact {Δ : Ctx} {e e₁ e₂ : Equation (Term Δ)} {S : EquationStore (Term Δ)}
    {A B A' B' : Tm} (h : e.1.1 = .arr A B) (h' : e.2.1 = .arr A' B') (h₁ : e₁.1.1 = A)
    (h₁' : e₁.2.1 = A') (h₂ : e₂.1.1 = B) (h₂' : e₂.2.1 = B') :
    Exact (frames v) (e :: S) ((frames v).id Δ) (e₁ :: e₂ :: S) := by
  apply exact_id_of_equivalent
  refine equivalent_cons (S' := [e₁, e₂]) (fun Γ f => ?_)
  constructor
  · intro solved e'' he''
    have same : Tm.lower v (Tm.act f.1 e.1.1) = Tm.lower v (Tm.act f.1 e.2.1) := solved
    rw [h, h'] at same
    simp only [Tm.act, Tm.lower, Tm.arr.injEq] at same
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he''
    rcases he'' with rfl | rfl
    · show Tm.lower v (Tm.act f.1 e''.1.1) = Tm.lower v (Tm.act f.1 e''.2.1)
      rw [h₁, h₁']
      exact same.1
    · show Tm.lower v (Tm.act f.1 e''.1.1) = Tm.lower v (Tm.act f.1 e''.2.1)
      rw [h₂, h₂']
      exact same.2
  · intro solved
    have one : Tm.lower v (Tm.act f.1 e₁.1.1) = Tm.lower v (Tm.act f.1 e₁.2.1) :=
      solved e₁ (by simp)
    have two : Tm.lower v (Tm.act f.1 e₂.1.1) = Tm.lower v (Tm.act f.1 e₂.2.1) :=
      solved e₂ (by simp)
    show Tm.lower v (Tm.act f.1 e.1.1) = Tm.lower v (Tm.act f.1 e.2.1)
    rw [h, h']
    rw [h₁, h₁'] at one
    rw [h₂, h₂'] at two
    simp only [Tm.act, Tm.lower, one, two]

theorem solveRight_exact {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} {X : Nat}
    {σ : Assign v Δ Δ} (hr : e.2.1 = .app X .par) (fresh : Tm.occurs X e.1.1 = false)
    (hσ : σ.1 = Function.update Tm.idA X e.1.1) :
    Exact (frames v) (e :: S) σ ((frames v).applyStore σ S) :=
  exact_swap (solve_exact (e := (e.2, e.1)) hr fresh hσ)

/-- **Every transition is exact.** -/
theorem Rule.exact {Δ m : Ctx} {S : EquationStore (Term Δ)} {σ : Assign v Δ m}
    {S' : EquationStore (Term m)} (r : Rule v S m σ S') : Exact (frames v) S σ S' := by
  cases r with
  | delete same => exact delete_exact same
  | decompose h h' h₁ h₁' h₂ h₂' => exact decompose_exact h h' h₁ h₁' h₂ h₂'
  | solveLeft hl fresh hσ => exact solve_exact hl fresh hσ
  | solveRight hr fresh hσ => exact solveRight_exact hr fresh hσ

/-! ## Termination -/

theorem storeUnknowns_mem_cons {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)}
    {x : Nat} (hx : x ∈ Tm.unknowns e.1.1 ∨ x ∈ Tm.unknowns e.2.1 ∨ x ∈ storeUnknowns S) :
    x ∈ storeUnknowns (e :: S) := by
  simp only [storeUnknowns, Finset.mem_union]
  rcases hx with hx | hx | hx
  · exact Or.inl (Or.inl hx)
  · exact Or.inl (Or.inr hx)
  · exact Or.inr hx

theorem solve_rank {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} {X : Nat}
    {σ : Assign v Δ Δ} (hl : e.1.1 = .app X .par) (fresh : Tm.occurs X e.2.1 = false)
    (hσ : σ.1 = Function.update Tm.idA X e.2.1) :
    (storeUnknowns ((frames v).applyStore σ S)).card < (storeUnknowns (e :: S)).card := by
  have notIn : X ∉ Tm.unknowns e.2.1 := by
    intro h
    rw [← Tm.occurs_iff] at h
    rw [h] at fresh
    cases fresh
  have inside : storeUnknowns ((frames v).applyStore σ S) ⊆ (storeUnknowns (e :: S)).erase X := by
    intro x hx
    rcases Finset.mem_union.mp (storeUnknowns_applyStore hσ S hx) with h | h
    · exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp h).1,
        storeUnknowns_mem_cons (Or.inr (Or.inr (Finset.mem_erase.mp h).2))⟩
    · exact Finset.mem_erase.mpr ⟨fun hxX => notIn (hxX ▸ h), storeUnknowns_mem_cons (Or.inr (Or.inl h))⟩
  have member : X ∈ storeUnknowns (e :: S) :=
    storeUnknowns_mem_cons (Or.inl (by rw [hl]; simp [Tm.unknowns]))
  exact lt_of_le_of_lt (Finset.card_le_card inside) (Finset.card_erase_lt_of_mem member)

theorem Tm.size_pos : ∀ t : Tm, 0 < Tm.size t
  | .par => Nat.one_pos
  | .gnd => Nat.one_pos
  | .sort _ => Nat.one_pos
  | .arr _ _ => Nat.succ_pos _
  | .app _ _ => Nat.succ_pos _

theorem delete_rank {Δ : Ctx} (e : Equation (Term Δ)) (S : EquationStore (Term Δ)) :
    RankLt (rank S) (rank (e :: S)) := by
  apply rankLt_of
  · exact Finset.card_le_card (fun x hx => storeUnknowns_mem_cons (Or.inr (Or.inr hx)))
  · intro _
    show storeSize S < storeSize (e :: S)
    simp only [storeSize]
    have := Tm.size_pos e.1.1
    omega

theorem decompose_rank {Δ : Ctx} {e e₁ e₂ : Equation (Term Δ)} {S : EquationStore (Term Δ)}
    {A B A' B' : Tm} (h : e.1.1 = .arr A B) (h' : e.2.1 = .arr A' B') (h₁ : e₁.1.1 = A)
    (h₁' : e₁.2.1 = A') (h₂ : e₂.1.1 = B) (h₂' : e₂.2.1 = B') :
    RankLt (rank (e₁ :: e₂ :: S)) (rank (e :: S)) := by
  apply rankLt_of
  · apply Finset.card_le_card
    intro x hx
    simp only [storeUnknowns, Finset.mem_union] at hx
    rw [h₁, h₁', h₂, h₂'] at hx
    apply storeUnknowns_mem_cons
    rw [h, h']
    simp only [Tm.unknowns, Finset.mem_union]
    tauto
  · intro _
    show storeSize (e₁ :: e₂ :: S) < storeSize (e :: S)
    simp only [storeSize]
    rw [h₁, h₁', h₂, h₂', h, h']
    simp only [Tm.size]
    omega

theorem solveRight_rank {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} {X : Nat}
    {σ : Assign v Δ Δ} (hr : e.2.1 = .app X .par) (fresh : Tm.occurs X e.1.1 = false)
    (hσ : σ.1 = Function.update Tm.idA X e.1.1) :
    (storeUnknowns ((frames v).applyStore σ S)).card < (storeUnknowns (e :: S)).card := by
  have swapped := solve_rank (v := v) (e := (e.2, e.1)) (S := S) hr fresh hσ
  have same : storeUnknowns ((e.2, e.1) :: S) = storeUnknowns (e :: S) := by
    simp only [storeUnknowns, Finset.union_comm (Tm.unknowns e.2.1)]
  rw [same] at swapped
  exact swapped

/-- **Every transition lowers the rank.** -/
theorem Rule.rank_lt {Δ : Ctx} {S S' : EquationStore (Term Δ)} {σ : Assign v Δ Δ}
    (r : Rule v S Δ σ S') : RankLt (rank S') (rank S) := by
  cases r with
  | delete _ => exact delete_rank _ _
  | decompose h h' h₁ h₁' h₂ h₂' => exact decompose_rank h h' h₁ h₁' h₂ h₂'
  | solveLeft hl fresh hσ => exact Prod.Lex.left _ _ (solve_rank hl fresh hσ)
  | solveRight hr fresh hσ => exact Prod.Lex.left _ _ (solveRight_rank hr fresh hσ)

/-- **The transitions terminate**: there is no infinite run on any store. -/
theorem rules_terminate (Δ : Ctx) :
    WellFounded (fun S' S : EquationStore (Term Δ) => ∃ σ : Assign v Δ Δ, Rule v S Δ σ S') :=
  Subrelation.wf (fun ⟨_, r⟩ => r.rank_lt) (InvImage.wf rank rankLt_wf)

/-! ## The uniform pattern fragment -/

/-- **The uniform pattern fragment** at a valuation: every unknown is declared
`Sort p ⟶ Sort ℓ`, every side is a pattern and a code of `Sort ℓ` over a parameter of `Sort p`. -/
structure Uniform (v : Nat → Nat) (Δ : Ctx) (p ℓ : Nat) (S : EquationStore (Term Δ)) : Prop where
  decls : ∀ (W : Nat) (d : Decl), Δ[W]? = some d → Level.value v d.dom = p ∧ Level.value v d.cod = ℓ
  typed : ∀ e ∈ S, Ty v Δ p e.1.1 ℓ ∧ Ty v Δ p e.2.1 ℓ
  pattern : ∀ e ∈ S, Tm.Pattern e.1.1 ∧ Tm.Pattern e.2.1

/-- The instantiation of an unknown by a code of the fragment is typed. -/
theorem update_typed {Δ : Ctx} {p ℓ : Nat}
    (decls : ∀ (W : Nat) (d : Decl), Δ[W]? = some d → Level.value v d.dom = p ∧ Level.value v d.cod = ℓ)
    (X : Nat) {t : Tm} (ht : Ty v Δ p t ℓ) : TyA v Δ Δ (Function.update Tm.idA X t) := by
  intro W d hW
  by_cases h : W = X
  · subst h
    rw [Function.update_self]
    obtain ⟨hd, hc⟩ := decls W d hW
    rw [hd, hc]
    exact ht
  · rw [Function.update_of_ne h]
    exact idA_typed Δ W d hW

theorem Ty.arr_inv {Γ : Ctx} {p : Nat} {A B : Tm} {l : Nat} (h : Ty v Γ p (.arr A B) l) :
    Ty v Γ p A l ∧ Ty v Γ p B l := by
  cases h with
  | arr hA hB => exact ⟨hA, hB⟩

theorem Pattern.arr_inv {A B : Tm} (h : Tm.Pattern (.arr A B)) : Tm.Pattern A ∧ Tm.Pattern B := by
  cases h with
  | arr hA hB => exact ⟨hA, hB⟩

theorem decompose_uniform {Δ : Ctx} {p ℓ : Nat} {e e₁ e₂ : Equation (Term Δ)}
    {S : EquationStore (Term Δ)} {A B A' B' : Tm} (h₀ : e.1.1 = .arr A B) (h₀' : e.2.1 = .arr A' B')
    (h₁ : e₁.1.1 = A) (h₁' : e₁.2.1 = A') (h₂ : e₂.1.1 = B) (h₂' : e₂.2.1 = B')
    (h : Uniform v Δ p ℓ (e :: S)) : Uniform v Δ p ℓ (e₁ :: e₂ :: S) := by
  obtain ⟨t₁, t₂⟩ := h.typed e List.mem_cons_self
  obtain ⟨p₁, p₂⟩ := h.pattern e List.mem_cons_self
  rw [h₀] at t₁ p₁
  rw [h₀'] at t₂ p₂
  refine ⟨h.decls, fun e' he' => ?_, fun e' he' => ?_⟩
  · rcases List.mem_cons.mp he' with rfl | he'
    · rw [h₁, h₁']
      exact ⟨(Ty.arr_inv t₁).1, (Ty.arr_inv t₂).1⟩
    rcases List.mem_cons.mp he' with rfl | he'
    · rw [h₂, h₂']
      exact ⟨(Ty.arr_inv t₁).2, (Ty.arr_inv t₂).2⟩
    exact h.typed e' (List.mem_cons_of_mem _ he')
  · rcases List.mem_cons.mp he' with rfl | he'
    · rw [h₁, h₁']
      exact ⟨(Pattern.arr_inv p₁).1, (Pattern.arr_inv p₂).1⟩
    rcases List.mem_cons.mp he' with rfl | he'
    · rw [h₂, h₂']
      exact ⟨(Pattern.arr_inv p₁).2, (Pattern.arr_inv p₂).2⟩
    exact h.pattern e' (List.mem_cons_of_mem _ he')

theorem solve_uniform {Δ : Ctx} {p ℓ : Nat} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)}
    {X : Nat} {u : Tm} {σ : Assign v Δ Δ} (hσ : σ.1 = Function.update Tm.idA X u)
    (hu : Tm.Pattern u) (h : Uniform v Δ p ℓ (e :: S)) :
    Uniform v Δ p ℓ ((frames v).applyStore σ S) := by
  have bodies : ∀ W, Tm.Pattern (σ.1 W) := by
    intro W
    rw [hσ]
    by_cases hW : W = X
    · subst hW
      rw [Function.update_self]
      exact hu
    · rw [Function.update_of_ne hW]
      exact .app W
  refine ⟨h.decls, fun e' he' => ?_, fun e' he' => ?_⟩
  · obtain ⟨e'', he'', rfl⟩ := List.mem_map.mp he'
    obtain ⟨one, two⟩ := h.typed e'' (List.mem_cons_of_mem _ he'')
    exact ⟨Ty.act σ.2 one, Ty.act σ.2 two⟩
  · obtain ⟨e'', he'', rfl⟩ := List.mem_map.mp he'
    obtain ⟨one, two⟩ := h.pattern e'' (List.mem_cons_of_mem _ he'')
    exact ⟨Tm.Pattern.act bodies one, Tm.Pattern.act bodies two⟩

/-- **The transitions keep the fragment.** -/
theorem Rule.uniform {Δ : Ctx} {p ℓ : Nat} {S S' : EquationStore (Term Δ)} {σ : Assign v Δ Δ}
    (r : Rule v S Δ σ S') (h : Uniform v Δ p ℓ S) : Uniform v Δ p ℓ S' := by
  cases r with
  | delete _ =>
      exact ⟨h.decls, fun e he => h.typed e (List.mem_cons_of_mem _ he),
        fun e he => h.pattern e (List.mem_cons_of_mem _ he)⟩
  | decompose h₀ h₀' h₁ h₁' h₂ h₂' => exact decompose_uniform h₀ h₀' h₁ h₁' h₂ h₂' h
  | solveLeft _ _ hσ => exact solve_uniform hσ (h.pattern _ List.mem_cons_self).2 h
  | solveRight _ _ hσ => exact solve_uniform hσ (h.pattern _ List.mem_cons_self).1 h

theorem Scoped.arr_inv {n : Nat} {A B : Tm} (h : Scoped n (.arr A B)) : Scoped n A ∧ Scoped n B := by
  cases h with
  | arr hA hB => exact ⟨hA, hB⟩

/-- **Progress on the fragment**: a nonempty store of the fragment has a transition or a
refutation. -/
theorem progress {Δ : Ctx} {p ℓ : Nat} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)}
    (h : Uniform v Δ p ℓ (e :: S)) :
    (∃ (σ : Assign v Δ Δ) (S' : EquationStore (Term Δ)), Rule v (e :: S) Δ σ S') ∨
      ∃ r : Reason, Refutes v (e :: S) r := by
  obtain ⟨⟨s, hs⟩, ⟨t, ht⟩⟩ := e
  obtain ⟨ts, tt⟩ := h.typed _ List.mem_cons_self
  obtain ⟨ps, pt⟩ := h.pattern _ List.mem_cons_self
  simp only at ts tt ps pt
  by_cases same : Tm.lower v s = Tm.lower v t
  · exact Or.inl ⟨_, _, .delete same⟩
  -- a flexible left side
  have flexLeft : ∀ X, s = .app X .par →
      (∃ (σ : Assign v Δ Δ) (S' : EquationStore (Term Δ)),
        Rule v ((⟨s, hs⟩, ⟨t, ht⟩) :: S) Δ σ S') ∨
        ∃ r : Reason, Refutes v ((⟨s, hs⟩, ⟨t, ht⟩) :: S) r := by
    intro X hX
    cases hocc : Tm.occurs X t with
    | false =>
        exact Or.inl ⟨⟨Function.update Tm.idA X t, update_typed h.decls X tt⟩, _,
          .solveLeft hX hocc rfl⟩
    | true =>
        refine Or.inr ⟨_, .occursLeft hX pt ((Tm.occurs_iff X t).mp hocc) ?_⟩
        intro htX
        exact same (by rw [hX, show t = .app X .par from htX])
  have flexRight : ∀ X, t = .app X .par →
      (∃ (σ : Assign v Δ Δ) (S' : EquationStore (Term Δ)),
        Rule v ((⟨s, hs⟩, ⟨t, ht⟩) :: S) Δ σ S') ∨
        ∃ r : Reason, Refutes v ((⟨s, hs⟩, ⟨t, ht⟩) :: S) r := by
    intro X hX
    cases hocc : Tm.occurs X s with
    | false =>
        exact Or.inl ⟨⟨Function.update Tm.idA X s, update_typed h.decls X ts⟩, _,
          .solveRight hX hocc rfl⟩
    | true =>
        refine Or.inr ⟨_, .occursRight hX ps ((Tm.occurs_iff X s).mp hocc) ?_⟩
        intro hsX
        exact same (by rw [hX, show s = .app X .par from hsX])
  cases ps with
  | app X => exact flexLeft X rfl
  | par =>
      cases pt with
      | app X => exact flexRight X rfl
      | par => exact absurd rfl same
      | gnd => exact Or.inr ⟨_, .clash (h := 0) (h' := 1) rfl rfl (by decide)⟩
      | sort _ => exact Or.inr ⟨_, .clash (h := 0) (h' := 2) rfl rfl (by decide)⟩
      | arr _ _ => exact Or.inr ⟨_, .clash (h := 0) (h' := 3) rfl rfl (by decide)⟩
  | gnd =>
      cases pt with
      | app X => exact flexRight X rfl
      | par => exact Or.inr ⟨_, .clash (h := 1) (h' := 0) rfl rfl (by decide)⟩
      | gnd => exact absurd rfl same
      | sort _ => exact Or.inr ⟨_, .clash (h := 1) (h' := 2) rfl rfl (by decide)⟩
      | arr _ _ => exact Or.inr ⟨_, .clash (h := 1) (h' := 3) rfl rfl (by decide)⟩
  | sort k =>
      cases pt with
      | app X => exact flexRight X rfl
      | par => exact Or.inr ⟨_, .clash (h := 2) (h' := 0) rfl rfl (by decide)⟩
      | gnd => exact Or.inr ⟨_, .clash (h := 2) (h' := 1) rfl rfl (by decide)⟩
      | sort k' =>
          refine Or.inr ⟨_, .levels rfl rfl ?_⟩
          intro hk
          exact same (by simp only [Tm.lower, hk])
      | arr _ _ => exact Or.inr ⟨_, .clash (h := 2) (h' := 3) rfl rfl (by decide)⟩
  | @arr A B pA pB =>
      cases pt with
      | app X => exact flexRight X rfl
      | par => exact Or.inr ⟨_, .clash (h := 3) (h' := 0) rfl rfl (by decide)⟩
      | gnd => exact Or.inr ⟨_, .clash (h := 3) (h' := 1) rfl rfl (by decide)⟩
      | sort _ => exact Or.inr ⟨_, .clash (h := 3) (h' := 2) rfl rfl (by decide)⟩
      | @arr A' B' pA' pB' =>
          obtain ⟨sA, sB⟩ := Scoped.arr_inv hs
          obtain ⟨sA', sB'⟩ := Scoped.arr_inv ht
          exact Or.inl ⟨_, (⟨A, sA⟩, ⟨A', sA'⟩) :: (⟨B, sB⟩, ⟨B', sB'⟩) :: S,
            .decompose rfl rfl rfl rfl rfl rfl⟩

/-! ## The solver and its decision on the fragment -/

/-- **The solver**, as a `Solver` of the frames. -/
def solver (v : Nat → Nat) : Solver (frames v) where
  Step S m σ S' := Rule v S m σ S'
  step_exact r := Rule.exact r
  Refutes S r := Refutes v S r
  refutes_sound r := Refutes.sound r

/-- **Decision on the uniform pattern fragment**: every store of the fragment has a run that ends
in the empty store or in a refutation. -/
theorem decided {Δ : Ctx} {p ℓ : Nat} (S : EquationStore (Term Δ)) (h : Uniform v Δ p ℓ S) :
    ∃ (σ : Assign v Δ Δ) (R : EquationStore (Term Δ)), (solver v).Reaches S Δ σ R ∧
      (R = [] ∨ ∃ r : Reason, Refutes v R r) := by
  induction S using (InvImage.wf rank rankLt_wf).induction with
  | h S ih =>
      match S, h with
      | [], _ => exact ⟨_, _, .refl [], Or.inl rfl⟩
      | e :: S, h =>
          rcases progress h with ⟨σ, S', r⟩ | ⟨reason, refuted⟩
          · obtain ⟨τ, R, run, ends⟩ := ih S' r.rank_lt (r.uniform h)
            exact ⟨_, R, .step r run, ends⟩
          · exact ⟨_, _, .refl _, Or.inr ⟨reason, refuted⟩⟩

/-- **Principal or unsolvable**: every store of the uniform pattern fragment has a principal
answer, reached by the solver, or no solution. -/
theorem principal_or_unsolvable {Δ : Ctx} {p ℓ : Nat} (S : EquationStore (Term Δ))
    (h : Uniform v Δ p ℓ S) :
    (∃ σ : Assign v Δ Δ, (frames v).Principal S σ) ∨ ¬ (frames v).Solvable S := by
  obtain ⟨σ, R, run, ends⟩ := decided S h
  rcases ends with rfl | ⟨r, refuted⟩
  · exact Or.inl ⟨σ, solved_principal run⟩
  · exact Or.inr (refuted_none (P := solver v) run refuted)

end CumulativeCodes

#print axioms CumulativeCodes.Rule.exact
#print axioms CumulativeCodes.Refutes.sound
#print axioms CumulativeCodes.Rule.rank_lt
#print axioms CumulativeCodes.rules_terminate
#print axioms CumulativeCodes.progress
#print axioms CumulativeCodes.decided
#print axioms CumulativeCodes.principal_or_unsolvable

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
