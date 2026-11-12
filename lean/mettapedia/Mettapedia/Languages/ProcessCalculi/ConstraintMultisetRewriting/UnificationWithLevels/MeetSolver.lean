import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.MeetNarrowing

/-!
# The solver with meet narrowing: decision on compatible groups

* **The rules** (`MeetStep`): those of `PatternSolver`, and meet narrowing (`MeetNarrowing`) on either side, for an
  unknown of the pattern that does not fit the flexible side's declaration. The refutations are those of
  `CodomainNarrowing`. Every transition is exact (`MeetStep.exact`) and every refutation sound, so `solver` is a
  `Solver` of the frames.
* **Termination** (`MeetStep.measure_lt`, `steps_terminate`): the rules of `PatternSolver` lower the rank; meet
  narrowing keeps the number of unknowns and the size and lowers the potential, the sum over the unknowns of the
  store of their codomain plus the distance of their domain below the largest domain of the context.
* **The fragment** (`Grouped`, `CompatibleGroups`): both sides of every equation are patterns, and the unknowns are
  put in groups so that the unknowns of each equation lie in one group and any two unknowns of one group have
  compatible declarations (`Compatible`). The transitions keep it (`MeetStep.compatibleGroups`): a solving step keeps
  the groups, and meet narrowing puts the new unknown in the group of the one it replaces, since the meet is
  compatible with every declaration compatible with both of its arguments (`compatible_meet`).
* **Decision** (`progress`, `decided`, `principal_or_unsolvable`): every store of the fragment has a principal answer
  or no solution. Whatever the order of the transitions, no run from the fragment stops postponed: a run that stops,
  stops at the empty store, with a principal answer (`never_postponed`, `stopped_principal`).

The fragment contains the uniform pattern fragment of `PatternSolver` (one group), the fragment with one domain per
equation of `CodomainNarrowing` (one group for each domain), and the store of
`CodomainNarrowingControls.domain_raising`, on which the solver of `CodomainNarrowing` stops and this one ends solved
(`compatibleGroups_of_uniform`, `compatibleGroups_of_oneDomain`, `raising_solved`).

**Controls.** The condition cannot be dropped: where `a < b` the cross store lies outside, is solvable, and has no
principal answer (`fragment_needed`); and meet narrowing between incompatible declarations is not exact
(`meet_needs_compatible`). It is not the boundary of principality: `Y par ≐ gnd, X par ≐ Y par` with the cross
declarations lies outside where `a < b`, and the solver solves it with a principal answer (`outside_solved`). Outside
the fragment the transitions are still exact and terminate, so a run there ends solved, refuted, or postponed with an
exact residual.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

open Interface

namespace CumulativeCodes

namespace Meet

open Narrowing

variable {v : Nat → Nat}

/-! ## The rules -/

/-- **The transitions**: the rules of `PatternSolver`, and meet narrowing on either side. -/
inductive MeetStep (v : Nat → Nat) : {Δ : Ctx} → EquationStore (Term Δ) → (m : Ctx) → Assign v Δ m →
    EquationStore (Term m) → Prop
  | rule {Δ : Ctx} {S S' : EquationStore (Term Δ)} {σ : Assign v Δ Δ} :
      Rule v S Δ σ S' → MeetStep v S Δ σ S'
  | meetLeft {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} {X W : Nat} {dX dW : Decl}
      {σ : Assign v Δ (Δ ++ [meetDecl v dX dW])} :
      e.1.1 = .app X .par → Tm.Pattern e.2.1 → W ∈ Tm.unknowns e.2.1 → Δ[X]? = some dX → Δ[W]? = some dW →
      Compatible v dX dW → ¬ Fits v dX dW → σ.1 = Function.update Tm.idA W (.app Δ.length .par) →
      MeetStep v (e :: S) (Δ ++ [meetDecl v dX dW]) σ ((frames v).applyStore σ (e :: S))
  | meetRight {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} {X W : Nat} {dX dW : Decl}
      {σ : Assign v Δ (Δ ++ [meetDecl v dX dW])} :
      e.2.1 = .app X .par → Tm.Pattern e.1.1 → W ∈ Tm.unknowns e.1.1 → Δ[X]? = some dX → Δ[W]? = some dW →
      Compatible v dX dW → ¬ Fits v dX dW → σ.1 = Function.update Tm.idA W (.app Δ.length .par) →
      MeetStep v (e :: S) (Δ ++ [meetDecl v dX dW]) σ ((frames v).applyStore σ (e :: S))

/-- **Every transition is exact.** -/
theorem MeetStep.exact {Δ m : Ctx} {S : EquationStore (Term Δ)} {σ : Assign v Δ m}
    {S' : EquationStore (Term m)} (st : MeetStep v S m σ S') : Exact (frames v) S σ S' := by
  cases st with
  | rule r => exact r.exact
  | meetLeft hl hp hW hX hdW compat _ hσ =>
      refine meet_exact hσ fun Γ f solved => ?_
      have forced := meet_forced_left hl hp hW hX hdW compat Γ f solved
      exact forced
  | meetRight hr hp hW hX hdW compat _ hσ =>
      refine meet_exact hσ fun Γ f solved => ?_
      have forced := meet_forced_right hr hp hW hX hdW compat Γ f solved
      exact forced

/-- **The solver with meet narrowing**, as a `Solver` of the frames. -/
def solver (v : Nat → Nat) : Solver (frames v) where
  Step S m σ S' := MeetStep v S m σ S'
  step_exact st := MeetStep.exact st
  Refutes S r := NarrowRefutes v S r
  refutes_sound r := NarrowRefutes.sound r

/-! ## Termination -/

/-- The largest domain declared by a context, at the valuation. -/
def maxDom (v : Nat → Nat) : Ctx → Nat
  | [] => 0
  | d :: Δ => max (Level.value v d.dom) (maxDom v Δ)

theorem dom_le_maxDom : ∀ {Δ : Ctx} {W : Nat} {d : Decl}, Δ[W]? = some d → Level.value v d.dom ≤ maxDom v Δ
  | [], _, _, h => by simp at h
  | _ :: _, 0, _, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact le_max_left _ _
  | _ :: _, _ + 1, _, h => by
      simp only [List.getElem?_cons_succ] at h
      exact le_trans (dom_le_maxDom h) (le_max_right _ _)

theorem maxDom_append (d : Decl) : ∀ Δ : Ctx, maxDom v (Δ ++ [d]) = max (maxDom v Δ) (Level.value v d.dom)
  | [] => by simp [maxDom]
  | _ :: Δ => by simp only [List.cons_append, maxDom, maxDom_append d Δ, max_assoc]

/-- The weight of an unknown: its codomain, plus how far its domain lies below the largest domain of the context. -/
def weight (v : Nat → Nat) (Δ : Ctx) (W : Nat) : Nat :=
  match Δ[W]? with
  | some d => Level.value v d.cod + (maxDom v Δ - Level.value v d.dom)
  | none => 0

theorem weight_of {Δ : Ctx} {W : Nat} {d : Decl} (h : Δ[W]? = some d) :
    weight v Δ W = Level.value v d.cod + (maxDom v Δ - Level.value v d.dom) := by
  unfold weight
  rw [h]

/-- The potential of a store: the sum of the weights of its unknowns. -/
def potential (v : Nat → Nat) {Δ : Ctx} (S : EquationStore (Term Δ)) : Nat :=
  (storeUnknowns S).sum (weight v Δ)

/-- The measure of a store at its context: its rank, then its potential. -/
def meetMeasure (v : Nat → Nat) (x : (Δ : Ctx) × EquationStore (Term Δ)) : (Nat × Nat) × Nat :=
  (rank x.2, potential v x.2)

theorem Scoped.unknowns_lt {n : Nat} : ∀ {t : Tm}, Scoped n t → ∀ W ∈ Tm.unknowns t, W < n
  | _, .par, _, h => by simp [Tm.unknowns] at h
  | _, .gnd, _, h => by simp [Tm.unknowns] at h
  | _, .sort _, _, h => by simp [Tm.unknowns] at h
  | _, .arr hA hB, W, h => by
      simp only [Tm.unknowns, Finset.mem_union] at h
      rcases h with h | h
      · exact Scoped.unknowns_lt hA W h
      · exact Scoped.unknowns_lt hB W h
  | _, .app hW ht, W, h => by
      simp only [Tm.unknowns, Finset.mem_insert] at h
      rcases h with rfl | h
      · exact hW
      · exact Scoped.unknowns_lt ht W h

theorem storeUnknowns_lt {Δ : Ctx} : ∀ S : EquationStore (Term Δ), ∀ W ∈ storeUnknowns S, W < Δ.length
  | [], _, h => by simp [storeUnknowns] at h
  | e :: S, W, h => by
      simp only [storeUnknowns, Finset.mem_union] at h
      rcases h with (h | h) | h
      · exact Scoped.unknowns_lt e.1.2 W h
      · exact Scoped.unknowns_lt e.2.2 W h
      · exact storeUnknowns_lt S W h

theorem storeUnknowns_applyStore' {Δ m : Ctx} {σ : Assign v Δ m} {X : Nat} {u : Tm}
    (hσ : σ.1 = Function.update Tm.idA X u) :
    ∀ S : EquationStore (Term Δ),
      storeUnknowns ((frames v).applyStore σ S) ⊆ (storeUnknowns S).erase X ∪ Tm.unknowns u
  | [] => by simp [Frames.applyStore, storeUnknowns]
  | e :: S => by
      intro x hx
      have rest := storeUnknowns_applyStore' hσ S
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

theorem size_act_meet (W n : Nat) : ∀ t : Tm,
    Tm.size (Tm.act (Function.update Tm.idA W (.app n .par)) t) = Tm.size t
  | .par => rfl
  | .gnd => rfl
  | .sort _ => rfl
  | .arr A B => by simp only [Tm.act, Tm.size, size_act_meet W n A, size_act_meet W n B]
  | .app V t => by
      show Tm.size (Tm.inst (Tm.act _ t) (Function.update Tm.idA W (.app n .par) V)) = Tm.size t + 1
      by_cases h : V = W
      · subst h
        rw [Function.update_self]
        simp only [Tm.inst, Tm.size, size_act_meet V n t]
      · rw [Function.update_of_ne h]
        simp only [Tm.idA, Tm.inst, Tm.size, size_act_meet W n t]

theorem storeSize_meet {Δ m : Ctx} {σ : Assign v Δ m} {W n : Nat}
    (hσ : σ.1 = Function.update Tm.idA W (.app n .par)) :
    ∀ S : EquationStore (Term Δ), storeSize ((frames v).applyStore σ S) = storeSize S
  | [] => rfl
  | e :: S => by
      show Tm.size (Tm.act σ.1 e.1.1) + Tm.size (Tm.act σ.1 e.2.1) +
          storeSize ((frames v).applyStore σ S) = Tm.size e.1.1 + Tm.size e.2.1 + storeSize S
      rw [hσ, size_act_meet, size_act_meet, storeSize_meet hσ S]

theorem unknowns_app_par (n : Nat) : Tm.unknowns (.app n .par) = {n} := by
  simp [Tm.unknowns]

theorem meet_card_le {Δ : Ctx} {S : EquationStore (Term Δ)} {W : Nat} {d' : Decl} {σ : Assign v Δ (Δ ++ [d'])}
    (hσ : σ.1 = Function.update Tm.idA W (.app Δ.length .par)) (hW : W ∈ storeUnknowns S) :
    (storeUnknowns ((frames v).applyStore σ S)).card ≤ (storeUnknowns S).card := by
  have sub := storeUnknowns_applyStore' hσ S
  rw [unknowns_app_par] at sub
  calc (storeUnknowns ((frames v).applyStore σ S)).card
      ≤ ((storeUnknowns S).erase W ∪ {Δ.length}).card := Finset.card_le_card sub
    _ ≤ ((storeUnknowns S).erase W).card + 1 := by
        refine le_trans (Finset.card_union_le _ _) ?_
        simp
    _ = (storeUnknowns S).card := by
        rw [Finset.card_erase_of_mem hW]
        have := Finset.card_pos.mpr ⟨W, hW⟩
        omega

/-- **Meet narrowing lowers the potential.** -/
theorem meet_potential_lt {Δ : Ctx} {S : EquationStore (Term Δ)} {X W : Nat} {dX dW : Decl}
    {σ : Assign v Δ (Δ ++ [meetDecl v dX dW])} (hσ : σ.1 = Function.update Tm.idA W (.app Δ.length .par))
    (hW : W ∈ storeUnknowns S) (hX : Δ[X]? = some dX) (hdW : Δ[W]? = some dW) (notFit : ¬ Fits v dX dW) :
    potential v ((frames v).applyStore σ S) < potential v S := by
  have sub := storeUnknowns_applyStore' hσ S
  rw [unknowns_app_par] at sub
  have notin : Δ.length ∉ (storeUnknowns S).erase W :=
    fun h => lt_irrefl _ (storeUnknowns_lt S _ (Finset.mem_of_mem_erase h))
  have maxEq : maxDom v (Δ ++ [meetDecl v dX dW]) = maxDom v Δ := by
    rw [maxDom_append, meetDecl_dom]
    exact max_eq_left (max_le (dom_le_maxDom hX) (dom_le_maxDom hdW))
  have old : ∀ V ∈ (storeUnknowns S).erase W, weight v (Δ ++ [meetDecl v dX dW]) V = weight v Δ V := by
    intro V hV
    have lt := storeUnknowns_lt S V (Finset.mem_of_mem_erase hV)
    unfold weight
    rw [getElem?_append_old lt, maxEq]
  have new : weight v (Δ ++ [meetDecl v dX dW]) Δ.length < weight v Δ W := by
    rw [weight_of getElem?_append_new, weight_of hdW, maxEq, meetDecl_dom, meetDecl_cod]
    have one := dom_le_maxDom (v := v) hX
    have two := dom_le_maxDom (v := v) hdW
    unfold Fits at notFit
    omega
  calc potential v ((frames v).applyStore σ S)
      ≤ ((storeUnknowns S).erase W ∪ {Δ.length}).sum (weight v (Δ ++ [meetDecl v dX dW])) :=
        Finset.sum_le_sum_of_subset sub
    _ = ((storeUnknowns S).erase W).sum (weight v (Δ ++ [meetDecl v dX dW])) +
          weight v (Δ ++ [meetDecl v dX dW]) Δ.length := by
        rw [Finset.sum_union (Finset.disjoint_singleton_right.mpr notin), Finset.sum_singleton]
    _ = ((storeUnknowns S).erase W).sum (weight v Δ) + weight v (Δ ++ [meetDecl v dX dW]) Δ.length := by
        rw [Finset.sum_congr rfl old]
    _ < ((storeUnknowns S).erase W).sum (weight v Δ) + weight v Δ W := Nat.add_lt_add_left new _
    _ = potential v S := Finset.sum_erase_add _ _ hW

/-- **Every transition lowers the measure.** -/
theorem MeetStep.measure_lt {Δ m : Ctx} {S : EquationStore (Term Δ)} {σ : Assign v Δ m}
    {S' : EquationStore (Term m)} (st : MeetStep v S m σ S') :
    MeasureLt (meetMeasure v ⟨m, S'⟩) (meetMeasure v ⟨Δ, S⟩) := by
  cases st with
  | rule r => exact Prod.Lex.left _ _ r.rank_lt
  | @meetLeft e S X W dX dW σ _ _ hWm hX hdW _ notFit hσ =>
      have hW : W ∈ storeUnknowns (e :: S) := storeUnknowns_mem_cons (Or.inr (Or.inl hWm))
      have cardLe := meet_card_le hσ hW
      have sizeEq := storeSize_meet hσ (e :: S)
      have potLt := meet_potential_lt hσ hW hX hdW notFit
      show Prod.Lex RankLt (· < ·) (rank _, potential v _) (rank _, potential v _)
      rcases Nat.lt_or_eq_of_le cardLe with lt | eq
      · exact Prod.Lex.left _ _ (Prod.Lex.left _ _ lt)
      · have same : rank ((frames v).applyStore σ (e :: S)) = rank (e :: S) := by
          unfold rank
          rw [eq, sizeEq]
        rw [same]
        exact Prod.Lex.right _ potLt
  | @meetRight e S X W dX dW σ _ _ hWm hX hdW _ notFit hσ =>
      have hW : W ∈ storeUnknowns (e :: S) := storeUnknowns_mem_cons (Or.inl hWm)
      have cardLe := meet_card_le hσ hW
      have sizeEq := storeSize_meet hσ (e :: S)
      have potLt := meet_potential_lt hσ hW hX hdW notFit
      show Prod.Lex RankLt (· < ·) (rank _, potential v _) (rank _, potential v _)
      rcases Nat.lt_or_eq_of_le cardLe with lt | eq
      · exact Prod.Lex.left _ _ (Prod.Lex.left _ _ lt)
      · have same : rank ((frames v).applyStore σ (e :: S)) = rank (e :: S) := by
          unfold rank
          rw [eq, sizeEq]
        rw [same]
        exact Prod.Lex.right _ potLt

/-- **The transitions terminate**: there is no infinite run from any store at any context. -/
theorem steps_terminate (v : Nat → Nat) :
    WellFounded (fun y x : (Δ : Ctx) × EquationStore (Term Δ) =>
      ∃ σ : Assign v x.1 y.1, MeetStep v x.2 y.1 σ y.2) :=
  Subrelation.wf (fun ⟨_, st⟩ => st.measure_lt) (InvImage.wf (meetMeasure v) measureLt_wf)

/-! ## The fragment: compatible groups -/

/-- The unknowns of an equation. -/
def eqUnknowns {Δ : Ctx} (e : Equation (Term Δ)) : Finset Nat :=
  Tm.unknowns e.1.1 ∪ Tm.unknowns e.2.1

theorem eqUnknowns_subset {Δ : Ctx} : ∀ {S : EquationStore (Term Δ)} {e : Equation (Term Δ)}, e ∈ S →
    eqUnknowns e ⊆ storeUnknowns S
  | [], _, h => by simp at h
  | _ :: _, _, h => by
      intro A hA
      rcases List.mem_cons.mp h with rfl | h
      · rcases Finset.mem_union.mp hA with hA | hA
        · exact storeUnknowns_mem_cons (Or.inl hA)
        · exact storeUnknowns_mem_cons (Or.inr (Or.inl hA))
      · exact storeUnknowns_mem_cons (Or.inr (Or.inr (eqUnknowns_subset h hA)))

/-- **A grouping of the unknowns** by `g`: both sides of every equation are patterns, the unknowns of each equation
lie in one group, and any two unknowns of the store in one group have compatible declarations. -/
structure Grouped (v : Nat → Nat) (Δ : Ctx) (S : EquationStore (Term Δ)) (g : Nat → Nat) : Prop where
  pattern : ∀ e ∈ S, Tm.Pattern e.1.1 ∧ Tm.Pattern e.2.1
  together : ∀ e ∈ S, ∀ A ∈ eqUnknowns e, ∀ B ∈ eqUnknowns e, g A = g B
  compatible : ∀ A ∈ storeUnknowns S, ∀ B ∈ storeUnknowns S, g A = g B →
    ∀ dA dB, Δ[A]? = some dA → Δ[B]? = some dB → Compatible v dA dB

/-- **The fragment of compatible groups**: the unknowns of the store have a grouping. -/
def CompatibleGroups (v : Nat → Nat) (Δ : Ctx) (S : EquationStore (Term Δ)) : Prop :=
  ∃ g : Nat → Nat, Grouped v Δ S g

/-- Two unknowns of one equation of the fragment have compatible declarations. -/
theorem Grouped.compatible_of_mem {Δ : Ctx} {S : EquationStore (Term Δ)} {g : Nat → Nat} (h : Grouped v Δ S g)
    {e : Equation (Term Δ)} (he : e ∈ S) {X W : Nat} (inX : X ∈ eqUnknowns e) (inW : W ∈ eqUnknowns e)
    {dX dW : Decl} (hX : Δ[X]? = some dX) (hW : Δ[W]? = some dW) : Compatible v dX dW :=
  h.compatible X (eqUnknowns_subset he inX) W (eqUnknowns_subset he inW) (h.together e he X inX W inW) dX dW hX hW

/-- Instantiating `X` by `u` keeps the other unknowns of a side, and brings those of `u` only where `X` occurs. -/
theorem mem_unknowns_act_update {X : Nat} {u : Tm} : ∀ {t : Tm} {A : Nat},
    A ∈ Tm.unknowns (Tm.act (Function.update Tm.idA X u) t) →
      (A ∈ Tm.unknowns t ∧ A ≠ X) ∨ (X ∈ Tm.unknowns t ∧ A ∈ Tm.unknowns u)
  | .par, _, h => by simp [Tm.act, Tm.unknowns] at h
  | .gnd, _, h => by simp [Tm.act, Tm.unknowns] at h
  | .sort _, _, h => by simp [Tm.act, Tm.unknowns] at h
  | .arr _ _, _, h => by
      simp only [Tm.act, Tm.unknowns, Finset.mem_union] at h ⊢
      rcases h with h | h
      · rcases mem_unknowns_act_update h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
        · exact Or.inl ⟨Or.inl h₁, h₂⟩
        · exact Or.inr ⟨Or.inl h₁, h₂⟩
      · rcases mem_unknowns_act_update h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
        · exact Or.inl ⟨Or.inr h₁, h₂⟩
        · exact Or.inr ⟨Or.inr h₁, h₂⟩
  | .app W _, _, h => by
      have h' := Tm.unknowns_inst _ _ h
      simp only [Tm.unknowns, Finset.mem_insert]
      rcases Finset.mem_union.mp h' with h'' | h''
      · by_cases hW : W = X
        · subst hW
          rw [Function.update_self] at h''
          exact Or.inr ⟨Or.inl rfl, h''⟩
        · rw [Function.update_of_ne hW] at h''
          simp only [Tm.idA, Tm.unknowns, Finset.mem_insert] at h''
          rcases h'' with h'' | h''
          · subst h''
            exact Or.inl ⟨Or.inl rfl, hW⟩
          · simp at h''
      · rcases mem_unknowns_act_update h'' with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
        · exact Or.inl ⟨Or.inr h₁, h₂⟩
        · exact Or.inr ⟨Or.inr h₁, h₂⟩

/-- **Instantiation keeps an equation in one group**, when the unknowns of `u` are in `X`'s group. -/
theorem together_act {g : Nat → Nat} {X : Nat} {u : Tm} (hu : ∀ A ∈ Tm.unknowns u, g A = g X) {s t : Tm}
    (h : ∀ A ∈ Tm.unknowns s ∪ Tm.unknowns t, ∀ B ∈ Tm.unknowns s ∪ Tm.unknowns t, g A = g B) :
    ∀ A ∈ Tm.unknowns (Tm.act (Function.update Tm.idA X u) s) ∪
        Tm.unknowns (Tm.act (Function.update Tm.idA X u) t),
      ∀ B ∈ Tm.unknowns (Tm.act (Function.update Tm.idA X u) s) ∪
        Tm.unknowns (Tm.act (Function.update Tm.idA X u) t), g A = g B := by
  have wit : ∀ {r : Tm} {A : Nat}, A ∈ Tm.unknowns (Tm.act (Function.update Tm.idA X u) r) →
      ∃ C ∈ Tm.unknowns r, g A = g C := by
    intro r A hA
    rcases mem_unknowns_act_update hA with ⟨hA', _⟩ | ⟨hX, hA'⟩
    · exact ⟨A, hA', rfl⟩
    · exact ⟨X, hX, hu A hA'⟩
  have wit₂ : ∀ A ∈ Tm.unknowns (Tm.act (Function.update Tm.idA X u) s) ∪
      Tm.unknowns (Tm.act (Function.update Tm.idA X u) t), ∃ C ∈ Tm.unknowns s ∪ Tm.unknowns t, g A = g C := by
    intro A hA
    rcases Finset.mem_union.mp hA with hA | hA
    · obtain ⟨C, hC, eq⟩ := wit hA
      exact ⟨C, Finset.mem_union_left _ hC, eq⟩
    · obtain ⟨C, hC, eq⟩ := wit hA
      exact ⟨C, Finset.mem_union_right _ hC, eq⟩
  intro A hA B hB
  obtain ⟨C, hC, eqA⟩ := wit₂ A hA
  obtain ⟨D, hD, eqB⟩ := wit₂ B hB
  rw [eqA, eqB]
  exact h C hC D hD

theorem pattern_act_update {X : Nat} {u : Tm} (hu : Tm.Pattern u) :
    ∀ {t : Tm}, Tm.Pattern t → Tm.Pattern (Tm.act (Function.update Tm.idA X u) t) := by
  apply Tm.Pattern.act
  intro W
  by_cases hW : W = X
  · subst hW
    rw [Function.update_self]
    exact hu
  · rw [Function.update_of_ne hW]
    exact .app W

theorem patterns_applyStore {Δ m : Ctx} {S : EquationStore (Term Δ)} {σ : Assign v Δ m} {X : Nat}
    {u : Tm} (hσ : σ.1 = Function.update Tm.idA X u) (hu : Tm.Pattern u)
    (pattern : ∀ e ∈ S, Tm.Pattern e.1.1 ∧ Tm.Pattern e.2.1) :
    ∀ e ∈ (frames v).applyStore σ S, Tm.Pattern e.1.1 ∧ Tm.Pattern e.2.1 := by
  intro e' he'
  obtain ⟨e'', he'', rfl⟩ := List.mem_map.mp he'
  obtain ⟨one, two⟩ := pattern e'' he''
  show Tm.Pattern (Tm.act σ.1 e''.1.1) ∧ Tm.Pattern (Tm.act σ.1 e''.2.1)
  rw [hσ]
  exact ⟨pattern_act_update hu one, pattern_act_update hu two⟩

theorem together_applyStore {Δ m : Ctx} {S : EquationStore (Term Δ)} {σ : Assign v Δ m} {g : Nat → Nat}
    {X : Nat} {u : Tm} (hσ : σ.1 = Function.update Tm.idA X u) (hu : ∀ A ∈ Tm.unknowns u, g A = g X)
    (h : ∀ e ∈ S, ∀ A ∈ eqUnknowns e, ∀ B ∈ eqUnknowns e, g A = g B) :
    ∀ e ∈ (frames v).applyStore σ S, ∀ A ∈ eqUnknowns e, ∀ B ∈ eqUnknowns e, g A = g B := by
  intro e' he'
  obtain ⟨e'', he'', rfl⟩ := List.mem_map.mp he'
  show ∀ A ∈ Tm.unknowns (Tm.act σ.1 e''.1.1) ∪ Tm.unknowns (Tm.act σ.1 e''.2.1),
    ∀ B ∈ Tm.unknowns (Tm.act σ.1 e''.1.1) ∪ Tm.unknowns (Tm.act σ.1 e''.2.1), g A = g B
  rw [hσ]
  exact together_act hu (h e'' he'')

/-- **Meet narrowing keeps a grouping**, with the new unknown in the group of the one it replaces. -/
theorem Grouped.meet {Δ : Ctx} {S : EquationStore (Term Δ)} {g : Nat → Nat} {e : Equation (Term Δ)} {X W : Nat}
    {dX dW : Decl} {σ : Assign v Δ (Δ ++ [meetDecl v dX dW])} (h : Grouped v Δ S g)
    (hσ : σ.1 = Function.update Tm.idA W (.app Δ.length .par)) (he : e ∈ S) (inX : X ∈ eqUnknowns e)
    (inW : W ∈ eqUnknowns e) (hX : Δ[X]? = some dX) (hW : Δ[W]? = some dW) :
    Grouped v (Δ ++ [meetDecl v dX dW]) ((frames v).applyStore σ S) (Function.update g Δ.length (g W)) := by
  have same : ∀ A ∈ storeUnknowns S, Function.update g Δ.length (g W) A = g A := fun A hA =>
    Function.update_of_ne (Nat.ne_of_lt (storeUnknowns_lt S A hA)) _ _
  have inXs : X ∈ storeUnknowns S := eqUnknowns_subset he inX
  have inWs : W ∈ storeUnknowns S := eqUnknowns_subset he inW
  have gXW : g X = g W := h.together e he X inX W inW
  refine ⟨patterns_applyStore hσ (.app _) h.pattern, together_applyStore hσ ?_ ?_, ?_⟩
  · intro A hA
    rw [unknowns_app_par, Finset.mem_singleton] at hA
    subst hA
    rw [Function.update_self, same W inWs]
  · intro e' he' A hA B hB
    rw [same A (eqUnknowns_subset he' hA), same B (eqUnknowns_subset he' hB)]
    exact h.together e' he' A hA B hB
  · have sub := storeUnknowns_applyStore' hσ S
    rw [unknowns_app_par] at sub
    have decl : ∀ C ∈ storeUnknowns ((frames v).applyStore σ S), ∀ dC,
        (Δ ++ [meetDecl v dX dW])[C]? = some dC →
          (C = Δ.length ∧ dC = meetDecl v dX dW) ∨ (C ∈ storeUnknowns S ∧ Δ[C]? = some dC) := by
      intro C hC dC hdC
      rcases Finset.mem_union.mp (sub hC) with hC | hC
      · have inS := Finset.mem_of_mem_erase hC
        rw [getElem?_append_old (storeUnknowns_lt S C inS)] at hdC
        exact Or.inr ⟨inS, hdC⟩
      · rw [Finset.mem_singleton] at hC
        subst hC
        rw [getElem?_append_new] at hdC
        exact Or.inl ⟨rfl, (Option.some.inj hdC).symm⟩
    intro A hA B hB gAB dA dB hdA hdB
    rcases decl A hA dA hdA with ⟨rfl, rfl⟩ | ⟨inA, oldA⟩ <;>
      rcases decl B hB dB hdB with ⟨rfl, rfl⟩ | ⟨inB, oldB⟩
    · exact Compatible.refl _
    · rw [Function.update_self, same B inB] at gAB
      exact compatible_meet (h.compatible X inXs B inB (gXW.trans gAB) dX dB hX oldB)
        (h.compatible W inWs B inB gAB dW dB hW oldB)
    · rw [Function.update_self, same A inA] at gAB
      exact (compatible_meet (h.compatible X inXs A inA (gXW.trans gAB.symm) dX dA hX oldA)
        (h.compatible W inWs A inA gAB.symm dW dA hW oldA)).symm
    · rw [same A inA, same B inB] at gAB
      exact h.compatible A inA B inB gAB dA dB oldA oldB

/-- The unknowns after a solving step are among those before. -/
theorem solve_subset {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} {σ : Assign v Δ Δ} {X : Nat}
    {u : Tm} (hσ : σ.1 = Function.update Tm.idA X u) (hu : Tm.unknowns u ⊆ eqUnknowns e) :
    storeUnknowns ((frames v).applyStore σ S) ⊆ storeUnknowns (e :: S) := by
  intro x hx
  rcases Finset.mem_union.mp (storeUnknowns_applyStore' hσ S hx) with hx | hx
  · exact storeUnknowns_mem_cons (Or.inr (Or.inr (Finset.mem_of_mem_erase hx)))
  · exact eqUnknowns_subset List.mem_cons_self (hu hx)

/-- **The transitions keep the fragment.** -/
theorem MeetStep.compatibleGroups {Δ m : Ctx} {S : EquationStore (Term Δ)} {σ : Assign v Δ m}
    {S' : EquationStore (Term m)} (st : MeetStep v S m σ S') (h : CompatibleGroups v Δ S) :
    CompatibleGroups v m S' := by
  obtain ⟨g, h⟩ := h
  cases st with
  | rule r =>
      cases r with
      | @delete e S _ =>
          exact ⟨g, fun e' he' => h.pattern e' (List.mem_cons_of_mem _ he'),
            fun e' he' => h.together e' (List.mem_cons_of_mem _ he'),
            fun x hx y hy => h.compatible x (storeUnknowns_mem_cons (Or.inr (Or.inr hx)))
              y (storeUnknowns_mem_cons (Or.inr (Or.inr hy)))⟩
      | @decompose e e₁ e₂ S A B A' B' h₀ h₀' h₁ h₁' h₂ h₂' =>
          obtain ⟨p₁, p₂⟩ := h.pattern _ List.mem_cons_self
          rw [h₀] at p₁
          rw [h₀'] at p₂
          have head := h.together _ List.mem_cons_self
          have sub₁ : eqUnknowns e₁ ⊆ eqUnknowns e := by
            intro x hx
            simp only [eqUnknowns, h₀, h₀', h₁, h₁', Tm.unknowns, Finset.mem_union] at hx ⊢
            tauto
          have sub₂ : eqUnknowns e₂ ⊆ eqUnknowns e := by
            intro x hx
            simp only [eqUnknowns, h₀, h₀', h₂, h₂', Tm.unknowns, Finset.mem_union] at hx ⊢
            tauto
          have subS : storeUnknowns (e₁ :: e₂ :: S) ⊆ storeUnknowns (e :: S) := by
            intro x hx
            simp only [storeUnknowns, Finset.mem_union] at hx
            rw [h₁, h₁', h₂, h₂'] at hx
            apply storeUnknowns_mem_cons
            rw [h₀, h₀']
            simp only [Tm.unknowns, Finset.mem_union]
            tauto
          refine ⟨g, fun e' he' => ?_, fun e' he' => ?_,
            fun x hx y hy => h.compatible x (subS hx) y (subS hy)⟩
          · rcases List.mem_cons.mp he' with rfl | he'
            · rw [h₁, h₁']
              exact ⟨(Pattern.arr_inv p₁).1, (Pattern.arr_inv p₂).1⟩
            rcases List.mem_cons.mp he' with rfl | he'
            · rw [h₂, h₂']
              exact ⟨(Pattern.arr_inv p₁).2, (Pattern.arr_inv p₂).2⟩
            exact h.pattern e' (List.mem_cons_of_mem _ he')
          · rcases List.mem_cons.mp he' with rfl | he'
            · exact fun x hx y hy => head x (sub₁ hx) y (sub₁ hy)
            rcases List.mem_cons.mp he' with rfl | he'
            · exact fun x hx y hy => head x (sub₂ hx) y (sub₂ hy)
            exact h.together e' (List.mem_cons_of_mem _ he')
      | @solveLeft e S X σ hl _ hσ =>
          have inX : X ∈ eqUnknowns e := Finset.mem_union_left _ (by rw [hl]; simp [Tm.unknowns])
          have hu : ∀ A ∈ Tm.unknowns e.2.1, g A = g X := fun A hA =>
            h.together e List.mem_cons_self A (Finset.mem_union_right _ hA) X inX
          have old := solve_subset (e := e) (S := S) hσ fun x hx => Finset.mem_union_right _ hx
          exact ⟨g, patterns_applyStore hσ (h.pattern _ List.mem_cons_self).2
            (fun e' he' => h.pattern e' (List.mem_cons_of_mem _ he')),
            together_applyStore hσ hu (fun e' he' => h.together e' (List.mem_cons_of_mem _ he')),
            fun x hx y hy => h.compatible x (old hx) y (old hy)⟩
      | @solveRight e S X σ hr _ hσ =>
          have inX : X ∈ eqUnknowns e := Finset.mem_union_right _ (by rw [hr]; simp [Tm.unknowns])
          have hu : ∀ A ∈ Tm.unknowns e.1.1, g A = g X := fun A hA =>
            h.together e List.mem_cons_self A (Finset.mem_union_left _ hA) X inX
          have old := solve_subset (e := e) (S := S) hσ fun x hx => Finset.mem_union_left _ hx
          exact ⟨g, patterns_applyStore hσ (h.pattern _ List.mem_cons_self).1
            (fun e' he' => h.pattern e' (List.mem_cons_of_mem _ he')),
            together_applyStore hσ hu (fun e' he' => h.together e' (List.mem_cons_of_mem _ he')),
            fun x hx y hy => h.compatible x (old hx) y (old hy)⟩
  | @meetLeft e S X W dX dW σ hl _ hWm hX hdW _ _ hσ =>
      exact ⟨_, h.meet hσ List.mem_cons_self (Finset.mem_union_left _ (by rw [hl]; simp [Tm.unknowns]))
        (Finset.mem_union_right _ hWm) hX hdW⟩
  | @meetRight e S X W dX dW σ hr _ hWm hX hdW _ _ hσ =>
      exact ⟨_, h.meet hσ List.mem_cons_self (Finset.mem_union_right _ (by rw [hr]; simp [Tm.unknowns]))
        (Finset.mem_union_left _ hWm) hX hdW⟩

/-! ## Progress and decision -/

/-- The meet narrowing morphism for `W` against `X`. -/
def meetMorphism (v : Nat → Nat) {Δ : Ctx} {W : Nat} (dX : Decl) {dW : Decl} (hW : Δ[W]? = some dW) :
    Assign v Δ (Δ ++ [meetDecl v dX dW]) :=
  meetAssign v (meetDecl v dX dW) hW (by rw [meetDecl_dom]; exact le_max_right _ _)
    (by rw [meetDecl_cod]; exact min_le_right _ _)

/-- **Progress on the fragment**: a nonempty store of the fragment has a transition or a refutation. -/
theorem progress {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)}
    (h : CompatibleGroups v Δ (e :: S)) :
    (∃ (m : Ctx) (σ : Assign v Δ m) (S' : EquationStore (Term m)), MeetStep v (e :: S) m σ S') ∨
      ∃ r : Reason, NarrowRefutes v (e :: S) r := by
  obtain ⟨g, hg⟩ := h
  have compat : ∀ X ∈ eqUnknowns e, ∀ W ∈ eqUnknowns e, ∀ dX dW, Δ[X]? = some dX → Δ[W]? = some dW →
      Compatible v dX dW := fun X inX W inW _ _ hX hW => hg.compatible_of_mem List.mem_cons_self inX inW hX hW
  obtain ⟨ps, pt⟩ := hg.pattern _ List.mem_cons_self
  obtain ⟨⟨s, hs⟩, ⟨t, ht⟩⟩ := e
  simp only at ps pt
  by_cases same : Tm.lower v s = Tm.lower v t
  · exact Or.inl ⟨_, _, _, .rule (.delete same)⟩
  have flexLeft : ∀ X, s = .app X .par →
      (∃ (m : Ctx) (σ : Assign v Δ m) (S' : EquationStore (Term m)),
        MeetStep v ((⟨s, hs⟩, ⟨t, ht⟩) :: S) m σ S') ∨
        ∃ r : Reason, NarrowRefutes v ((⟨s, hs⟩, ⟨t, ht⟩) :: S) r := by
    intro X hX
    subst hX
    obtain ⟨dX, hdX⟩ := decl_of_scoped_app hs
    cases hocc : Tm.occurs X t with
    | true =>
        refine Or.inr ⟨_, .rule (.occursLeft rfl pt ((Tm.occurs_iff X t).mp hocc) ?_)⟩
        intro htX
        exact same (by rw [show t = .app X .par from htX])
    | false =>
        cases hfit : rigidFits v (Level.value v dX.dom) (Level.value v dX.cod) t with
        | false => exact Or.inr ⟨_, .misfitLeft rfl hdX hfit⟩
        | true =>
            by_cases big : ∃ W ∈ Tm.unknowns t, ∃ dW, Δ[W]? = some dW ∧ ¬ Fits v dX dW
            · obtain ⟨W, hW, dW, hdW, notFit⟩ := big
              exact Or.inl ⟨_, meetMorphism v dX hdW, _, .meetLeft rfl pt hW hdX hdW
                (compat X (Finset.mem_union_left _ (by simp [Tm.unknowns])) W (Finset.mem_union_right _ hW)
                  dX dW hdX hdW) notFit rfl⟩
            · have typed : Ty v Δ (Level.value v dX.dom) t (Level.value v dX.cod) :=
                Ty.of_fits pt ht hfit fun W hW d hd => by
                  by_cases fits : Fits v dX d
                  · exact ⟨fits.2, fits.1⟩
                  · exact absurd ⟨W, hW, d, hd, fits⟩ big
              exact Or.inl ⟨_, ⟨Function.update Tm.idA X t, update_typed_of_ty hdX typed⟩, _,
                .rule (.solveLeft rfl hocc rfl)⟩
  have flexRight : ∀ X, t = .app X .par →
      (∃ (m : Ctx) (σ : Assign v Δ m) (S' : EquationStore (Term m)),
        MeetStep v ((⟨s, hs⟩, ⟨t, ht⟩) :: S) m σ S') ∨
        ∃ r : Reason, NarrowRefutes v ((⟨s, hs⟩, ⟨t, ht⟩) :: S) r := by
    intro X hX
    subst hX
    obtain ⟨dX, hdX⟩ := decl_of_scoped_app ht
    cases hocc : Tm.occurs X s with
    | true =>
        refine Or.inr ⟨_, .rule (.occursRight rfl ps ((Tm.occurs_iff X s).mp hocc) ?_)⟩
        intro hsX
        exact same (by rw [show s = .app X .par from hsX])
    | false =>
        cases hfit : rigidFits v (Level.value v dX.dom) (Level.value v dX.cod) s with
        | false => exact Or.inr ⟨_, .misfitRight rfl hdX hfit⟩
        | true =>
            by_cases big : ∃ W ∈ Tm.unknowns s, ∃ dW, Δ[W]? = some dW ∧ ¬ Fits v dX dW
            · obtain ⟨W, hW, dW, hdW, notFit⟩ := big
              exact Or.inl ⟨_, meetMorphism v dX hdW, _, .meetRight rfl ps hW hdX hdW
                (compat X (Finset.mem_union_right _ (by simp [Tm.unknowns])) W (Finset.mem_union_left _ hW)
                  dX dW hdX hdW) notFit rfl⟩
            · have typed : Ty v Δ (Level.value v dX.dom) s (Level.value v dX.cod) :=
                Ty.of_fits ps hs hfit fun W hW d hd => by
                  by_cases fits : Fits v dX d
                  · exact ⟨fits.2, fits.1⟩
                  · exact absurd ⟨W, hW, d, hd, fits⟩ big
              exact Or.inl ⟨_, ⟨Function.update Tm.idA X s, update_typed_of_ty hdX typed⟩, _,
                .rule (.solveRight rfl hocc rfl)⟩
  cases ps with
  | app X => exact flexLeft X rfl
  | par =>
      cases pt with
      | app X => exact flexRight X rfl
      | par => exact absurd rfl same
      | gnd => exact Or.inr ⟨_, .rule (.clash (h := 0) (h' := 1) rfl rfl (by decide))⟩
      | sort _ => exact Or.inr ⟨_, .rule (.clash (h := 0) (h' := 2) rfl rfl (by decide))⟩
      | arr _ _ => exact Or.inr ⟨_, .rule (.clash (h := 0) (h' := 3) rfl rfl (by decide))⟩
  | gnd =>
      cases pt with
      | app X => exact flexRight X rfl
      | par => exact Or.inr ⟨_, .rule (.clash (h := 1) (h' := 0) rfl rfl (by decide))⟩
      | gnd => exact absurd rfl same
      | sort _ => exact Or.inr ⟨_, .rule (.clash (h := 1) (h' := 2) rfl rfl (by decide))⟩
      | arr _ _ => exact Or.inr ⟨_, .rule (.clash (h := 1) (h' := 3) rfl rfl (by decide))⟩
  | sort k =>
      cases pt with
      | app X => exact flexRight X rfl
      | par => exact Or.inr ⟨_, .rule (.clash (h := 2) (h' := 0) rfl rfl (by decide))⟩
      | gnd => exact Or.inr ⟨_, .rule (.clash (h := 2) (h' := 1) rfl rfl (by decide))⟩
      | sort k' =>
          refine Or.inr ⟨_, .rule (.levels rfl rfl ?_)⟩
          intro hk
          exact same (by simp only [Tm.lower, hk])
      | arr _ _ => exact Or.inr ⟨_, .rule (.clash (h := 2) (h' := 3) rfl rfl (by decide))⟩
  | @arr A B pA pB =>
      cases pt with
      | app X => exact flexRight X rfl
      | par => exact Or.inr ⟨_, .rule (.clash (h := 3) (h' := 0) rfl rfl (by decide))⟩
      | gnd => exact Or.inr ⟨_, .rule (.clash (h := 3) (h' := 1) rfl rfl (by decide))⟩
      | sort _ => exact Or.inr ⟨_, .rule (.clash (h := 3) (h' := 2) rfl rfl (by decide))⟩
      | @arr A' B' pA' pB' =>
          obtain ⟨sA, sB⟩ := Scoped.arr_inv hs
          obtain ⟨sA', sB'⟩ := Scoped.arr_inv ht
          exact Or.inl ⟨_, _, (⟨A, sA⟩, ⟨A', sA'⟩) :: (⟨B, sB⟩, ⟨B', sB'⟩) :: S,
            .rule (.decompose rfl rfl rfl rfl rfl rfl)⟩

/-- **Decision on the fragment**: every store of the fragment has a run, through new unknowns, that ends in the empty
store or in a refutation. -/
theorem decided {Δ : Ctx} (S : EquationStore (Term Δ)) (h : CompatibleGroups v Δ S) :
    ∃ (m : Ctx) (σ : Assign v Δ m) (R : EquationStore (Term m)), (solver v).Reaches S m σ R ∧
      (R = [] ∨ ∃ r : Reason, NarrowRefutes v R r) := by
  suffices key : ∀ x : (Δ : Ctx) × EquationStore (Term Δ), CompatibleGroups v x.1 x.2 →
      ∃ (m : Ctx) (σ : Assign v x.1 m) (R : EquationStore (Term m)), (solver v).Reaches x.2 m σ R ∧
        (R = [] ∨ ∃ r : Reason, NarrowRefutes v R r) from key ⟨Δ, S⟩ h
  intro x
  induction x using (InvImage.wf (meetMeasure v) measureLt_wf).induction with
  | h x ih =>
      obtain ⟨Δ, S⟩ := x
      intro h
      match S, h with
      | [], _ => exact ⟨Δ, _, [], .refl [], Or.inl rfl⟩
      | e :: S, h =>
          rcases progress h with ⟨m, σ, S', st⟩ | ⟨reason, refuted⟩
          · obtain ⟨n, τ, R, run, ends⟩ := ih ⟨m, S'⟩ st.measure_lt (st.compatibleGroups h)
            exact ⟨n, _, R, .step st run, ends⟩
          · exact ⟨Δ, _, _, .refl _, Or.inr ⟨reason, refuted⟩⟩

/-- **Principal or unsolvable, with several domains and codomains**: every store of the fragment of compatible
groups has a principal answer, reached by the solver, or no solution. -/
theorem principal_or_unsolvable {Δ : Ctx} (S : EquationStore (Term Δ)) (h : CompatibleGroups v Δ S) :
    (∃ (m : Ctx) (σ : Assign v Δ m), (frames v).Principal S σ) ∨ ¬ (frames v).Solvable S := by
  obtain ⟨m, σ, R, run, ends⟩ := decided S h
  rcases ends with rfl | ⟨r, refuted⟩
  · exact Or.inl ⟨m, σ, solved_principal run⟩
  · exact Or.inr (refuted_none (P := solver v) run refuted)

/-- **On the fragment no run stops postponed**: whatever the order of its transitions, a run from a store of the
fragment that stops, stops at the empty store. -/
theorem never_postponed {Δ m : Ctx} {S : EquationStore (Term Δ)} {σ : Assign v Δ m} {R : EquationStore (Term m)}
    (run : (solver v).Reaches S m σ R) : CompatibleGroups v Δ S → (solver v).Stopped R → R = [] := by
  induction run with
  | refl S =>
      intro h stopped
      match S, h, stopped with
      | [], _, _ => rfl
      | _ :: _, h, stopped =>
          rcases progress h with ⟨n, τ, R', st⟩ | ⟨r, refuted⟩
          · exact absurd st (stopped.1 n τ R')
          · exact absurd refuted (stopped.2 r)
  | step st _ ih =>
      intro h stopped
      exact ih (MeetStep.compatibleGroups st h) stopped

/-- **Every run from the fragment that stops gives a principal answer.** -/
theorem stopped_principal {Δ m : Ctx} {S : EquationStore (Term Δ)} {σ : Assign v Δ m} {R : EquationStore (Term m)}
    (run : (solver v).Reaches S m σ R) (h : CompatibleGroups v Δ S) (stopped : (solver v).Stopped R) :
    (frames v).Principal S σ := by
  have empty := never_postponed run h stopped
  subst empty
  exact solved_principal run

/-! ## What the fragment contains -/

/-- **Positive: declarations with one domain are compatible.** -/
theorem one_domain_compatible {dX dW : Decl} (same : Level.value v dX.dom = Level.value v dW.dom) :
    Compatible v dX dW := by
  unfold Compatible
  rw [same, max_self]
  by_cases h₁ : Level.value v dW.dom ≤ Level.value v dX.cod
  · by_cases h₂ : Level.value v dW.dom ≤ Level.value v dW.cod
    · exact Or.inl (le_min h₁ h₂)
    · exact Or.inr (Or.inr (Nat.lt_of_not_le h₂))
  · exact Or.inr (Or.inl (Nat.lt_of_not_le h₁))

/-- **One group**: a store of patterns whose unknowns are pairwise compatible is in the fragment. -/
theorem compatibleGroups_of_pairwise {Δ : Ctx} {S : EquationStore (Term Δ)}
    (pattern : ∀ e ∈ S, Tm.Pattern e.1.1 ∧ Tm.Pattern e.2.1)
    (pairwise : ∀ A ∈ storeUnknowns S, ∀ B ∈ storeUnknowns S, ∀ dA dB, Δ[A]? = some dA → Δ[B]? = some dB →
      Compatible v dA dB) : CompatibleGroups v Δ S :=
  ⟨fun _ => 0, pattern, fun _ _ _ _ _ _ => rfl, fun A hA B hB _ => pairwise A hA B hB⟩

/-- **The uniform pattern fragment of `PatternSolver` is contained**, in one group. -/
theorem compatibleGroups_of_uniform {Δ : Ctx} {p ℓ : Nat} {S : EquationStore (Term Δ)} (h : Uniform v Δ p ℓ S) :
    CompatibleGroups v Δ S :=
  compatibleGroups_of_pairwise h.pattern fun A _ B _ dA dB hdA hdB =>
    one_domain_compatible ((h.decls A dA hdA).1.trans (h.decls B dB hdB).1.symm)

/-- The domain of an unknown at the valuation; `0` for an undeclared one. -/
def domainOf (v : Nat → Nat) (Δ : Ctx) (A : Nat) : Nat :=
  match Δ[A]? with
  | some d => Level.value v d.dom
  | none => 0

theorem domainOf_of {Δ : Ctx} {A : Nat} {d : Decl} (h : Δ[A]? = some d) :
    domainOf v Δ A = Level.value v d.dom := by
  unfold domainOf
  rw [h]

/-- **The fragment with one domain per equation of `CodomainNarrowing` is contained**: group the unknowns by their
domain. -/
theorem compatibleGroups_of_oneDomain {Δ : Ctx} {S : EquationStore (Term Δ)} (h : OneDomain v Δ S) :
    CompatibleGroups v Δ S := by
  refine ⟨domainOf v Δ, h.pattern, fun e he A hA B hB => ?_, fun A _ B _ gAB dA dB hdA hdB => ?_⟩
  · obtain ⟨p, dl, dr⟩ := h.domain e he
    have dom : ∀ C ∈ eqUnknowns e, domainOf v Δ C = p := by
      intro C hC
      have lt := storeUnknowns_lt S C (eqUnknowns_subset he hC)
      rw [domainOf_of (List.getElem?_eq_getElem lt)]
      rcases Finset.mem_union.mp hC with hC | hC
      · exact dl C hC _ (List.getElem?_eq_getElem lt)
      · exact dr C hC _ (List.getElem?_eq_getElem lt)
    rw [dom A hA, dom B hB]
  · rw [domainOf_of hdA, domainOf_of hdB] at gAB
    exact one_domain_compatible gAB

open NarrowingControls in
theorem raising_compatibleGroups (v : Nat → Nat) : CompatibleGroups v ctxR storeR := by
  refine compatibleGroups_of_pairwise (fun e he => ?_) (fun X _ W _ dX dW hX hW => ?_)
  · simp only [storeR, List.mem_singleton] at he
    subst he
    exact ⟨.app 0, .arr (.app 1) .gnd⟩
  · have decl : ∀ (V : Nat) (d : Decl), ctxR[V]? = some d →
        d = ⟨.const 1, .const 2⟩ ∨ d = ⟨.const 0, .const 2⟩ := by
      intro V d hd
      match V, hd with
      | 0, hd =>
          simp only [ctxR, List.getElem?_cons_zero, Option.some.injEq] at hd
          exact Or.inl hd.symm
      | 1, hd =>
          simp only [ctxR, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hd
          exact Or.inr hd.symm
      | n + 2, hd => simp [ctxR] at hd
    rcases decl X dX hX with rfl | rfl <;> rcases decl W dW hW with rfl | rfl <;>
      exact Or.inl (by simp)

open NarrowingControls in
/-- **Positive: the store that the solver of `CodomainNarrowing` leaves stopped is solved here**, with a principal
answer: `X par ≐ arr (W par) gnd` with `X : Sort 1 ⟶ Sort 2` and `W : Sort 0 ⟶ Sort 2`. -/
theorem raising_solved (v : Nat → Nat) :
    ∃ (m : Ctx) (σ : Assign v ctxR m), (solver v).Reaches storeR m σ [] ∧ (frames v).Principal storeR σ := by
  obtain ⟨m, σ, R, run, ends⟩ := decided storeR (raising_compatibleGroups v)
  rcases ends with rfl | ⟨r, refuted⟩
  · exact ⟨m, σ, run, solved_principal run⟩
  · exact absurd (answerR_principal v).solvable (refuted_none (P := solver v) run refuted)

/-! ## The condition is needed -/

/-- **Negative: the cross store's declarations are incompatible where `a < b`**: the larger domain `b` is above the
smaller codomain `a`, and both admit the parameter. -/
theorem cross_incompatible (lt : v 0 < v 1) : ¬ Compatible v ⟨Cross.a, Cross.a⟩ ⟨Cross.b, Cross.b⟩ := by
  unfold Compatible
  simp only [Cross.a, Cross.b, Level.value_param]
  omega

/-- **Negative: the cross store lies outside the fragment where `a < b`**: its two unknowns share an equation. -/
theorem cross_outside (lt : v 0 < v 1) : ¬ CompatibleGroups v Cross.ctx Cross.store := by
  rintro ⟨g, h⟩
  exact cross_incompatible lt (h.compatible_of_mem (e := (Cross.X, Cross.Y)) (X := 0) (W := 1) List.mem_cons_self
    (by simp [eqUnknowns, Cross.X, Cross.Y, Tm.unknowns]) (by simp [eqUnknowns, Cross.X, Cross.Y, Tm.unknowns])
    rfl rfl)

/-- **Negative: the condition of the fragment cannot be dropped.** Where `a < b` the cross store lies outside the
fragment, is solvable, and has no principal answer: the conclusion of `principal_or_unsolvable` fails there. -/
theorem fragment_needed (lt : v 0 < v 1) :
    ¬ CompatibleGroups v Cross.ctx Cross.store ∧ (frames v).Solvable Cross.store ∧
      ∀ (Γ : Ctx) (σ : Assign v Cross.ctx Γ), ¬ (frames v).Principal Cross.store σ :=
  ⟨cross_outside lt, Cross.solvable v, fun _ σ => Cross.no_principal lt σ⟩

/-- **Negative: the declarations of `domain_needed` are incompatible.** -/
theorem domain_needed_incompatible : ¬ Compatible v ⟨.const 0, .const 1⟩ ⟨.const 2, .const 2⟩ := by
  unfold Compatible
  simp

open NarrowingControls in
/-- The meet narrowing of `W` against `X` in the store of `domain_needed`: `W := W' par`, `W' : Sort 2 ⟶ Sort 1`. -/
def meetD (v : Nat → Nat) : Assign v ctxD (ctxD ++ [meetDecl v ⟨.const 0, .const 1⟩ ⟨.const 2, .const 2⟩]) :=
  meetMorphism v ⟨.const 0, .const 1⟩ (W := 1) (show ctxD[1]? = some ⟨.const 2, .const 2⟩ from rfl)

open NarrowingControls in
/-- **Negative: between incompatible declarations meet narrowing is not exact.** In the store of `domain_needed`,
`X : Sort 0 ⟶ Sort 1` and `W : Sort 2 ⟶ Sort 2` are incompatible; the solution sending both to the parameter does not
factor through `W := W' par` with `W'` at the meet `Sort 2 ⟶ Sort 1`, which admits no parameter. -/
theorem meet_needs_compatible (v : Nat → Nat) :
    ¬ Compatible v ⟨.const 0, .const 1⟩ ⟨.const 2, .const 2⟩ ∧ (frames v).Models (both v) storeD ∧
      ¬ Exact (frames v) storeD (meetD v) ((frames v).applyStore (meetD v) storeD) := by
  refine ⟨domain_needed_incompatible, both_solves v, fun exact => ?_⟩
  obtain ⟨g, fg, _⟩ := (exact [] (both v)).mp (both_solves v)
  have h : Tm.lower v (Tm.act (fun _ => Tm.par) (.app 1 .par)) =
      Tm.lower v (Tm.act (Tm.compA g.1 (meetD v).1) (.app 1 .par)) := fg WD
  have hσ : (meetD v).1 1 = .app 2 .par := rfl
  rw [Tm.act_comp, act_app_par, act_app_par, hσ, act_app_par] at h
  have typed : Ty v [] (Level.value v (meetDecl v ⟨.const 0, .const 1⟩ ⟨.const 2, .const 2⟩).dom) (g.1 2)
      (Level.value v (meetDecl v ⟨.const 0, .const 1⟩ ⟨.const 2, .const 2⟩).cod) := g.2 2 _ rfl
  rw [meetDecl_dom, meetDecl_cod] at typed
  have lowered := typed.lower
  rw [← h] at lowered
  have := Ty.par_inv lowered
  simp at this

/-! ## The fragment is not the boundary -/

/-- `gnd` in the cross context. -/
def gndC : Term Cross.ctx := ⟨.gnd, .gnd⟩

/-- `Y par ≐ gnd, X par ≐ Y par`, with the cross declarations `X : Sort a ⟶ Sort a` and `Y : Sort b ⟶ Sort b`. -/
def storeG : EquationStore (Term Cross.ctx) := [(Cross.Y, gndC), (Cross.X, Cross.Y)]

/-- The instantiation `Y := gnd`. -/
def solveY (v : Nat → Nat) : Assign v Cross.ctx Cross.ctx :=
  ⟨Function.update Tm.idA 1 .gnd, update_typed_of_ty (dX := ⟨Cross.b, Cross.b⟩) rfl .gnd⟩

theorem storeG_solvable (v : Nat → Nat) : (frames v).Solvable storeG := by
  refine ⟨[], Cross.constant v, fun e he => ?_⟩
  simp [storeG] at he
  rcases he with rfl | rfl <;> rfl

/-- **Positive outside the fragment: the fragment is not the boundary of principality.** Where `a < b`,
`Y par ≐ gnd, X par ≐ Y par` has incompatible unknowns in one equation, so it lies outside the fragment; the solver
still solves it, with a principal answer: `Y := gnd` leaves `X par ≐ gnd`, which lies inside. -/
theorem outside_solved (v : Nat → Nat) (lt : v 0 < v 1) :
    ¬ CompatibleGroups v Cross.ctx storeG ∧
      ∃ (m : Ctx) (σ : Assign v Cross.ctx m), (solver v).Reaches storeG m σ [] ∧ (frames v).Principal storeG σ := by
  refine ⟨?_, ?_⟩
  · rintro ⟨g, h⟩
    exact cross_incompatible lt (h.compatible_of_mem (e := (Cross.X, Cross.Y)) (X := 0) (W := 1)
      (List.mem_cons_of_mem _ List.mem_cons_self)
      (by simp [eqUnknowns, Cross.X, Cross.Y, Tm.unknowns]) (by simp [eqUnknowns, Cross.X, Cross.Y, Tm.unknowns])
      rfl rfl)
  · have step : (solver v).Step storeG Cross.ctx (solveY v)
        ((frames v).applyStore (solveY v) [(Cross.X, Cross.Y)]) :=
      MeetStep.rule (Rule.solveLeft (e := (Cross.Y, gndC)) rfl rfl rfl)
    have groups : CompatibleGroups v Cross.ctx ((frames v).applyStore (solveY v) [(Cross.X, Cross.Y)]) := by
      have sub := storeUnknowns_applyStore' (σ := solveY v) (X := 1) (u := .gnd) rfl [(Cross.X, Cross.Y)]
      have only : ∀ C ∈ storeUnknowns ((frames v).applyStore (solveY v) [(Cross.X, Cross.Y)]), C = 0 := by
        intro C hC
        have hC' := sub hC
        simp [storeUnknowns, Cross.X, Cross.Y, Tm.unknowns] at hC'
        omega
      refine compatibleGroups_of_pairwise
        (patterns_applyStore (σ := solveY v) (X := 1) (u := .gnd) rfl .gnd ?_) ?_
      · intro e he
        simp only [List.mem_singleton] at he
        subst he
        exact ⟨.app 0, .app 1⟩
      · intro A hA B hB dA dB hdA hdB
        rw [only A hA] at hdA
        rw [only B hB, hdA] at hdB
        cases hdB
        exact Compatible.refl _
    obtain ⟨m, τ, R, run, ends⟩ := decided _ groups
    rcases ends with rfl | ⟨r, refuted⟩
    · exact ⟨m, _, .step step run, solved_principal (.step step run)⟩
    · exact absurd (storeG_solvable v) (refuted_none (P := solver v) (.step step run) refuted)

end Meet

end CumulativeCodes

#print axioms CumulativeCodes.Meet.MeetStep.exact
#print axioms CumulativeCodes.Meet.meet_potential_lt
#print axioms CumulativeCodes.Meet.MeetStep.measure_lt
#print axioms CumulativeCodes.Meet.steps_terminate
#print axioms CumulativeCodes.Meet.MeetStep.compatibleGroups
#print axioms CumulativeCodes.Meet.progress
#print axioms CumulativeCodes.Meet.decided
#print axioms CumulativeCodes.Meet.principal_or_unsolvable
#print axioms CumulativeCodes.Meet.never_postponed
#print axioms CumulativeCodes.Meet.stopped_principal
#print axioms CumulativeCodes.Meet.compatibleGroups_of_uniform
#print axioms CumulativeCodes.Meet.compatibleGroups_of_oneDomain
#print axioms CumulativeCodes.Meet.raising_solved
#print axioms CumulativeCodes.Meet.fragment_needed
#print axioms CumulativeCodes.Meet.meet_needs_compatible
#print axioms CumulativeCodes.Meet.outside_solved

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
