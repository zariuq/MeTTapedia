import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.MillerCodes
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.StepConnection

/-!
# Inversion, pruning and intersection, by construction, each exact

In a flex equation `X x̄ ≐ t` over Miller codes, with `x̄` a list of distinct locals, a solution `f` makes
`f X` with its parameters spread over `x̄` equal to the instance of `t` (`solves_flex`). Three transitions follow
from this, each defined by a construction and each exact.

* **Inversion** (`invert_exact`): where every local of `t` is among `x̄` and `X` does not occur in `t`, the answer
  `X := λ ȳ. t[x̄ := ȳ]` is the renaming of `t` by the inverse of `x̄` (`Tm.idx`). Solving the store along it
  loses no solution and adds none.
* **Restriction** (`restrict_exact`): an unknown `Y` of arity `k` is replaced by `λ ȳ. Y' (ȳ at P)`, with `Y'` new,
  of arity `|P|`. It is exact as soon as every solution sends `Y` to a body whose parameters are among `P`.
  * **Pruning** (`prune_forced`): in `X x̄ ≐ t`, where `Y z̄` occurs in `t`, every solution uses only the
    parameters `i` of `Y` with `z̄ᵢ` among `x̄`, since the instance of `t` has only locals of `x̄`.
  * **Intersection** (`intersect_forced`): in `X x̄ ≐ X ȳ`, every solution uses only the parameters `i` with
    `x̄ᵢ = ȳᵢ`.

  In Vezzosi and Abel's reading, intersection is an equalizer of renamings and pruning a pullback; here each is
  built as a morphism of the frames through which every solution factors.
* **Refutations** with their reasons: different rigid heads (`clash_unsolvable`); a rigid local of `t` outside `x̄`
  (`scope_unsolvable`, a clash of scope); `X` inside a rigid `t` (`occurs_unsolvable`, no well-founded solution).

Since every transition is exact, a run that empties the store ends with a principal answer of `Frames.Principal`
(`ExactTransitions.solved_principal`); the solver and its decision on the pattern fragment are in `MillerSolver`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

open Interface

namespace MillerCodes

/-! ## Flex equations -/

theorem act_app (σ : Nat → Tm) (X : Nat) (args : List Nat) :
    Tm.act σ (.app X args) = Tm.rename (Tm.spread args) (σ X) := rfl

theorem decl_of_app {Δ : Ctx} {e : Equation (Term Δ)} {X : Nat} {xs : List Nat} (hl : e.1.1 = .app X xs) :
    Δ[X]? = some xs.length :=
  Scoped.app_inv (hl ▸ e.1.2)

theorem decl_of_app_right {Δ : Ctx} {e : Equation (Term Δ)} {X : Nat} {xs : List Nat} (hr : e.2.1 = .app X xs) :
    Δ[X]? = some xs.length :=
  Scoped.app_inv (hr ▸ e.2.2)

/-- **A solution of a flex equation**: `f X` with its parameters spread over `x̄` is the instance of `t`. -/
theorem solves_flex {Δ Γ : Ctx} {f : Assign Δ Γ} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} {X : Nat}
    {xs : List Nat} (hl : e.1.1 = .app X xs) (solved : frames.Models f (e :: S)) :
    Tm.rename (Tm.spread xs) (f.1 X) = Tm.act f.1 e.2.1 := by
  have same : Tm.act f.1 e.1.1 = Tm.act f.1 e.2.1 := solved e List.mem_cons_self
  rwa [hl, act_app] at same

/-- The flex side has only the locals of `x̄`. -/
theorem flex_locals {Δ Γ : Ctx} (f : Assign Δ Γ) {X : Nat} {xs : List Nat} (hX : Δ[X]? = some xs.length) :
    Tm.AllLocals (· ∈ xs) (Tm.rename (Tm.spread xs) (f.1 X)) :=
  (f.2 X _ hX).2.rename fun _ hi => Tm.spread_mem hi

theorem Tm.AllLocals.of_rename {P : Nat → Prop} {ρ : Nat → Nat} :
    ∀ {t : Tm}, Tm.AllLocals P (Tm.rename ρ t) → Tm.AllLocals (fun i => P (ρ i)) t
  | .loc _, h => by
      cases h with
      | loc hi => exact .loc hi
  | .gnd, _ => .gnd
  | .arr _ _, h => by
      cases h with
      | arr hA hB => exact .arr (Tm.AllLocals.of_rename hA) (Tm.AllLocals.of_rename hB)
  | .app _ _, h => by
      cases h with
      | app hargs => exact .app fun i hi => hargs _ (List.mem_map_of_mem hi)

/-! ## Inversion -/

/-- **The inverted body**: `t` with each local renamed to its index in `x̄`. -/
def invert (xs : List Nat) (t : Tm) : Tm := Tm.rename (Tm.idx xs) t

theorem invert_typed {Δ : Ctx} {X : Nat} {xs : List Nat} {t : Tm} (hX : Δ[X]? = some xs.length)
    (sc : Scoped Δ t) (inside : Tm.AllLocals (· ∈ xs) t) :
    TyA Δ Δ (Function.update (idA Δ) X (invert xs t)) := by
  intro W k hW
  by_cases h : W = X
  · subst h
    rw [Function.update_self]
    rw [hX] at hW
    cases hW
    exact ⟨sc.rename _, Tm.AllLocals.rename (ρ := Tm.idx xs) (Q := (· < xs.length))
      (fun _ hj => Tm.idx_lt hj) inside⟩
  · rw [Function.update_of_ne h]
    exact idA_typed Δ W k hW

/-- An assignment that differs from the identity only at `X` fixes a scoped code without `X`. -/
theorem act_update_fixed {Δ : Ctx} {X : Nat} {b : Tm} {t : Tm} (fresh : X ∉ Tm.unknowns t)
    (sc : Scoped Δ t) : Tm.act (Function.update (idA Δ) X b) t = t := by
  rw [act_congr (τ := idA Δ) fun W hW =>
    Function.update_of_ne (fun h => fresh (by rw [← h]; exact hW)) _ _]
  exact act_id sc

/-- **Inversion is exact.** -/
theorem invert_exact {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} {X : Nat} {xs : List Nat}
    {σ : Assign Δ Δ} (hl : e.1.1 = .app X xs) (nodup : xs.Nodup) (fresh : X ∉ Tm.unknowns e.2.1)
    (inside : Tm.AllLocals (· ∈ xs) e.2.1) (hσ : σ.1 = Function.update (idA Δ) X (invert xs e.2.1)) :
    Exact frames (e :: S) σ (frames.applyStore σ S) := by
  have hX := decl_of_app hl
  intro Γ f
  constructor
  · intro solved
    have same := solves_flex hl solved
    have agree : Agree frames f (frames.comp f σ) := by
      apply agree_of_bodies
      intro W hW
      show f.1 W = Tm.act f.1 (σ.1 W)
      rw [hσ]
      by_cases h : W = X
      · subst h
        rw [Function.update_self, invert, act_rename f.2 _ e.2.2, ← same, Tm.rename_rename]
        exact (Tm.rename_fix (fun i hi => Tm.idx_spread nodup hi) (f.2 W _ hX).2).symm
      · rw [Function.update_of_ne h]
        exact (act_idA_body f.2 (List.getElem?_eq_getElem hW)).symm
    refine ⟨f, agree, ?_⟩
    rw [Frames.models_applyStore]
    exact (models_of_agree agree S).mp (fun e' he' => solved e' (List.mem_cons_of_mem _ he'))
  · rintro ⟨g, fg, solvedG⟩
    rw [Frames.models_applyStore] at solvedG
    apply (models_of_agree fg (e :: S)).mpr
    intro e' he'
    rcases List.mem_cons.mp he' with rfl | he'
    · show Tm.act (compA g.1 σ.1) e'.1.1 = Tm.act (compA g.1 σ.1) e'.2.1
      rw [act_comp g.2 σ.2 e'.1.2, act_comp g.2 σ.2 e'.2.2, hl, act_app, hσ, Function.update_self,
        act_update_fixed fresh e'.2.2, invert, Tm.rename_rename,
        Tm.rename_fix (fun j hj => Tm.spread_idx hj) inside]
    · exact solvedG e' he'

/-! ## Restriction -/

/-- The context with one more unknown, of arity `n`, at the end. -/
def extend (Δ : Ctx) (n : Nat) : Ctx := Δ ++ [n]

theorem extend_old {Δ : Ctx} {n W : Nat} (h : W < Δ.length) : (extend Δ n)[W]? = Δ[W]? :=
  List.getElem?_append_left h

theorem extend_new {Δ : Ctx} {n : Nat} : (extend Δ n)[Δ.length]? = some n := by
  simp [extend]

theorem lt_of_extend {Δ : Ctx} {n W k : Nat} (h : (extend Δ n)[W]? = some k) (ne : W ≠ Δ.length) :
    W < Δ.length := by
  have lt := (List.getElem?_eq_some_iff.mp h).1
  simp only [extend, List.length_append, List.length_cons, List.length_nil] at lt
  omega

/-- **The restriction of `Y` to the positions `P`**: `Y := λ ȳ. Y' (ȳ at P)`, with `Y'` the new last unknown. -/
def restrict (Δ : Ctx) (Y : Nat) (P : List Nat) : Nat → Tm :=
  Function.update (idA Δ) Y (.app Δ.length P)

theorem restrict_typed {Δ : Ctx} {Y k : Nat} {P : List Nat} (hY : Δ[Y]? = some k) (below : ∀ i ∈ P, i < k) :
    TyA Δ (extend Δ P.length) (restrict Δ Y P) := by
  intro W k' hW
  by_cases h : W = Y
  · subst h
    rw [restrict, Function.update_self]
    rw [hY] at hW
    cases hW
    exact ⟨.app extend_new, .app below⟩
  · rw [restrict, Function.update_of_ne h]
    have lt : W < Δ.length := (List.getElem?_eq_some_iff.mp hW).1
    refine ⟨.app ?_, .app fun i hi => ?_⟩
    · rw [extend_old lt, List.length_range, arity_of hW]
      exact hW
    · rw [List.mem_range, arity_of hW] at hi
      exact hi

/-- **Restriction is exact** as soon as every solution sends `Y` to a body whose parameters are among `P`. -/
theorem restrict_exact {Δ : Ctx} {S : EquationStore (Term Δ)} {Y k : Nat} {P : List Nat}
    (hY : Δ[Y]? = some k) {σ : Assign Δ (extend Δ P.length)} (hσ : σ.1 = restrict Δ Y P)
    (forced : ∀ (Γ : Ctx) (f : Assign Δ Γ), frames.Models f S → Tm.AllLocals (· ∈ P) (f.1 Y)) :
    Exact frames S σ (frames.applyStore σ S) := by
  apply (exact_applyStore_iff S σ).mpr
  intro Γ f solved
  have locs := forced Γ f solved
  let body : Nat → Tm := fun W => if W = Δ.length then Tm.rename (Tm.idx P) (f.1 Y) else f.1 W
  have typed : TyA (extend Δ P.length) Γ body := by
    intro W k' hW
    by_cases hW' : W = Δ.length
    · subst hW'
      rw [extend_new] at hW
      cases hW
      simp only [body, if_pos rfl]
      exact ⟨(f.2 Y k hY).1.rename _, Tm.AllLocals.rename (ρ := Tm.idx P) (Q := (· < P.length))
        (fun _ hj => Tm.idx_lt hj) locs⟩
    · rw [extend_old (lt_of_extend hW hW')] at hW
      simp only [body, if_neg hW']
      exact f.2 W k' hW
  refine ⟨⟨body, typed⟩, agree_of_bodies fun W hW => ?_⟩
  show f.1 W = Tm.act body (σ.1 W)
  rw [hσ]
  by_cases hWY : W = Y
  · subst hWY
    rw [restrict, Function.update_self, act_app]
    simp only [body, if_pos rfl, Tm.rename_rename]
    exact (Tm.rename_fix (fun j hj => Tm.spread_idx hj) locs).symm
  · rw [restrict, Function.update_of_ne hWY]
    obtain ⟨k', hk'⟩ : ∃ k', Δ[W]? = some k' := ⟨_, List.getElem?_eq_getElem hW⟩
    show f.1 W = Tm.rename (Tm.spread (List.range (arity Δ W))) (body W)
    simp only [body, if_neg (Nat.ne_of_lt hW)]
    refine (Tm.rename_fix (fun i hi => ?_) (f.2 W k' hk').2).symm
    rw [arity_of hk', Tm.spread_of_lt (by rw [List.length_range]; exact hi), List.getElem_range]

/-! ## Pruning and intersection -/

/-- An application of `Y` to `zs` at a position of a code, outside the arguments of another unknown. -/
inductive OccursAt (Y : Nat) (zs : List Nat) : Tm → Prop
  | here : OccursAt Y zs (.app Y zs)
  | left {A B : Tm} : OccursAt Y zs A → OccursAt Y zs (.arr A B)
  | right {A B : Tm} : OccursAt Y zs B → OccursAt Y zs (.arr A B)

theorem OccursAt.of_mem {Y : Nat} : ∀ {t : Tm}, Y ∈ Tm.unknowns t → ∃ zs, OccursAt Y zs t
  | .loc _, h => by simp [Tm.unknowns] at h
  | .gnd, h => by simp [Tm.unknowns] at h
  | .arr A B, h => by
      simp only [Tm.unknowns, Finset.mem_union] at h
      rcases h with h | h
      · obtain ⟨zs, o⟩ := OccursAt.of_mem h
        exact ⟨zs, .left o⟩
      · obtain ⟨zs, o⟩ := OccursAt.of_mem h
        exact ⟨zs, .right o⟩
  | .app W zs, h => by
      simp only [Tm.unknowns, Finset.mem_singleton] at h
      subst h
      exact ⟨zs, .here⟩

theorem OccursAt.mem {Y : Nat} {zs : List Nat} : ∀ {t : Tm}, OccursAt Y zs t → Y ∈ Tm.unknowns t
  | _, .here => by simp [Tm.unknowns]
  | _, .left o => by simp only [Tm.unknowns, Finset.mem_union]; exact Or.inl o.mem
  | _, .right o => by simp only [Tm.unknowns, Finset.mem_union]; exact Or.inr o.mem

theorem OccursAt.decl {Δ : Ctx} {Y : Nat} {zs : List Nat} :
    ∀ {t : Tm}, OccursAt Y zs t → Scoped Δ t → Δ[Y]? = some zs.length
  | _, .here, h => Scoped.app_inv h
  | _, .left o, h => o.decl (Scoped.arr_inv h).1
  | _, .right o, h => o.decl (Scoped.arr_inv h).2

/-- The locals of an instance include those of the instance of each occurrence. -/
theorem OccursAt.locals {P : Nat → Prop} {σ : Nat → Tm} {Y : Nat} {zs : List Nat} :
    ∀ {t : Tm}, OccursAt Y zs t → Tm.AllLocals P (Tm.act σ t) →
      Tm.AllLocals P (Tm.rename (Tm.spread zs) (σ Y))
  | _, .here, h => h
  | _, .left o, h => by
      cases h with
      | arr hA _ => exact o.locals hA
  | _, .right o, h => by
      cases h with
      | arr _ hB => exact o.locals hB

/-- The positions kept by pruning `Y z̄` against `x̄`: those `i` with `z̄ᵢ` among `x̄`. -/
def prunePositions (xs zs : List Nat) : List Nat :=
  (List.range zs.length).filter fun i => decide (Tm.spread zs i ∈ xs)

/-- The positions kept by intersecting `x̄` with `ȳ`: those `i` with `x̄ᵢ = ȳᵢ`. -/
def agreePositions (xs ys : List Nat) : List Nat :=
  (List.range xs.length).filter fun i => decide (Tm.spread xs i = Tm.spread ys i)

theorem prunePositions_below {xs zs : List Nat} : ∀ i ∈ prunePositions xs zs, i < zs.length := by
  intro i hi
  simp only [prunePositions, List.mem_filter, List.mem_range] at hi
  exact hi.1

theorem agreePositions_below {xs ys : List Nat} : ∀ i ∈ agreePositions xs ys, i < xs.length := by
  intro i hi
  simp only [agreePositions, List.mem_filter, List.mem_range] at hi
  exact hi.1

/-- **What pruning reads from `X x̄ ≐ t`**: every solution sends an unknown `Y` applied to `z̄` in `t` to a body
whose parameters are among the positions of `z̄` that are in `x̄`. -/
theorem prune_forced {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} {X Y : Nat}
    {xs zs : List Nat} (hl : e.1.1 = .app X xs) (occ : OccursAt Y zs e.2.1) (Γ : Ctx) (f : Assign Δ Γ)
    (solved : frames.Models f (e :: S)) : Tm.AllLocals (· ∈ prunePositions xs zs) (f.1 Y) := by
  have left := flex_locals f (decl_of_app hl)
  rw [solves_flex hl solved] at left
  have inY := Tm.AllLocals.of_rename (occ.locals left)
  have below := (f.2 Y _ (occ.decl e.2.2)).2
  refine (inY.and below).mono fun i hi => ?_
  simp only [prunePositions, List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨hi.2, hi.1⟩

/-- **What intersection reads from `X x̄ ≐ X ȳ`**: every solution sends `X` to a body whose parameters are among
the positions where `x̄` and `ȳ` agree. -/
theorem intersect_forced {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} {X : Nat}
    {xs ys : List Nat} (hl : e.1.1 = .app X xs) (hr : e.2.1 = .app X ys) (Γ : Ctx) (f : Assign Δ Γ)
    (solved : frames.Models f (e :: S)) : Tm.AllLocals (· ∈ agreePositions xs ys) (f.1 X) := by
  have same := solves_flex hl solved
  rw [hr, act_app] at same
  have agree := Tm.AllLocals.of_rename_eq same
  have below := (f.2 X _ (decl_of_app hl)).2
  refine (agree.and below).mono fun i hi => ?_
  simp only [agreePositions, List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨hi.2, hi.1⟩

/-! ## Refutations -/

/-- The head of a rigid code; an applied unknown has none. -/
def head? : Tm → Option Nat
  | .loc i => some (i + 2)
  | .gnd => some 0
  | .arr _ _ => some 1
  | .app _ _ => none

theorem head?_act (σ : Nat → Tm) {t : Tm} {h : Nat} (ht : head? t = some h) : head? (Tm.act σ t) = some h := by
  cases t with
  | loc _ => exact ht
  | gnd => exact ht
  | arr _ _ => exact ht
  | app _ _ => cases ht

/-- **A clash of rigid heads has no solution.** -/
theorem clash_unsolvable {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} {h h' : Nat}
    (h₁ : head? e.1.1 = some h) (h₂ : head? e.2.1 = some h') (ne : h ≠ h') :
    ¬ frames.Solvable (e :: S) := by
  rintro ⟨Γ, f, solved⟩
  have same : Tm.act f.1 e.1.1 = Tm.act f.1 e.2.1 := solved e List.mem_cons_self
  have one := head?_act f.1 h₁
  rw [same, head?_act f.1 h₂] at one
  exact ne (Option.some.inj one).symm

/-- A local at a position of a code, outside the arguments of an unknown. -/
inductive RigidLocal (j : Nat) : Tm → Prop
  | here : RigidLocal j (.loc j)
  | left {A B : Tm} : RigidLocal j A → RigidLocal j (.arr A B)
  | right {A B : Tm} : RigidLocal j B → RigidLocal j (.arr A B)

theorem RigidLocal.act {j : Nat} (σ : Nat → Tm) : ∀ {t : Tm}, RigidLocal j t → RigidLocal j (Tm.act σ t)
  | _, .here => .here
  | _, .left r => .left (r.act σ)
  | _, .right r => .right (r.act σ)

theorem RigidLocal.holds {j : Nat} {P : Nat → Prop} : ∀ {t : Tm}, RigidLocal j t → Tm.AllLocals P t → P j
  | _, .here, h => by
      cases h with
      | loc hj => exact hj
  | _, .left r, h => by
      cases h with
      | arr hA _ => exact r.holds hA
  | _, .right r, h => by
      cases h with
      | arr _ hB => exact r.holds hB

/-- **A rigid local outside the pattern's locals has no solution**: the flex side only has the locals of `x̄`. -/
theorem scope_unsolvable {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} {X j : Nat}
    {xs : List Nat} (hl : e.1.1 = .app X xs) (rigid : RigidLocal j e.2.1) (out : j ∉ xs) :
    ¬ frames.Solvable (e :: S) := by
  rintro ⟨Γ, f, solved⟩
  have left := flex_locals f (decl_of_app hl)
  rw [solves_flex hl solved] at left
  exact out ((rigid.act f.1).holds left)

theorem OccursAt.size_le {σ : Nat → Tm} {X : Nat} {ys : List Nat} :
    ∀ {t : Tm}, OccursAt X ys t → Tm.size (σ X) ≤ Tm.size (Tm.act σ t)
  | _, .here => by rw [act_app, Tm.size_rename]
  | _, .left o => by
      have := o.size_le (σ := σ)
      simp only [Tm.act, Tm.size]
      omega
  | _, .right o => by
      have := o.size_le (σ := σ)
      simp only [Tm.act, Tm.size]
      omega

/-- **`X` inside a rigid side: no well-founded solution**, since the instance of that side is larger than `X`'s. -/
theorem occurs_unsolvable {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} {X : Nat}
    {xs ys : List Nat} {A B : Tm} (hl : e.1.1 = .app X xs) (hr : e.2.1 = .arr A B) (occ : OccursAt X ys (.arr A B)) :
    ¬ frames.Solvable (e :: S) := by
  rintro ⟨Γ, f, solved⟩
  have same := congrArg Tm.size (solves_flex hl solved)
  rw [Tm.size_rename, hr] at same
  cases occ with
  | left o =>
      have := o.size_le (σ := f.1)
      simp only [Tm.act, Tm.size] at same
      omega
  | right o =>
      have := o.size_le (σ := f.1)
      simp only [Tm.act, Tm.size] at same
      omega

end MillerCodes

#print axioms MillerCodes.solves_flex
#print axioms MillerCodes.invert_exact
#print axioms MillerCodes.restrict_exact
#print axioms MillerCodes.prune_forced
#print axioms MillerCodes.intersect_forced
#print axioms MillerCodes.clash_unsolvable
#print axioms MillerCodes.scope_unsolvable
#print axioms MillerCodes.occurs_unsolvable

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
