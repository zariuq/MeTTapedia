import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.FixedPointAnswers

/-!
# Narrowing a codomain: several codomains, one domain per equation

The solver of `PatternSolver` decides the uniform pattern fragment, where all unknowns share one domain and one
codomain. With several codomains a pattern equation can have a principal answer that no instantiation reaches. In
`X par ≐ arr (Y par) gnd`, with `X : Sort 0 ⟶ Sort 0` and `Y : Sort 0 ⟶ Sort 1`, the body `arr (Y par) gnd` is not a
code of `Sort 0`, so `X` cannot be instantiated by it; yet every solution sends `Y` to a code of `Sort 0`, because that
code is part of `X`'s body. **Narrowing** records what the equation forces: `Y`'s declaration is narrowed to `X`'s
codomain, and then `X` is instantiated.

* **The transition** moves along the identity on codes, which is typed by cumulativity, to the context with the
  narrower declaration (`narrowAssign`). It is exact as soon as every solution already sends the unknown into the
  narrower declaration (`narrow_exact`). In `X par ≐ t` that holds for every unknown of the pattern `t` whose domain
  is at most `X`'s (`forced_left`, `forced_right`).
* **The universe refutation**: a universe, or the parameter, in the rigid part of `t` that does not fit `X`'s
  codomain leaves no solution (`not_ty_of_rigidFits`, `misfit_unsolvable_left`), with reason `levels`.
* **The solver** (`Narrowing.solver`) adds narrowing and the universe refutation to the rules of `PatternSolver`.
  Every transition is exact and every refutation sound. Every run terminates: each transition lowers the rank, or keeps
  it and lowers the sum of the codomains of the context (`NarrowStep.measure_lt`, `steps_terminate`).
* **Decision with one domain per equation** (`OneDomain`): both sides of every equation are patterns, and the unknowns
  of each equation share one domain; codomains are free. The transitions keep the fragment (`NarrowStep.oneDomain`)
  and on a nonempty store one of them, or a refutation, applies (`progress`). So every store of the fragment has a
  principal answer or no solution (`principal_or_unsolvable`).

**The domain condition cannot be dropped, and it is not the sharp boundary.** It cannot be dropped: the cross store
(`CrossStoreLevels`) equates two unknowns of different domains and has no principal answer where `a < b`, and
narrowing an unknown whose domain is above `X`'s to `X`'s codomain loses solutions (`CodomainNarrowingControls`). It
is not sharp: `X par ≐ arr (W par) gnd` with `X : Sort 1 ⟶ Sort 2` and `W : Sort 0 ⟶ Sort 2` lies outside the
fragment, the rules here stop on it, and it has a principal answer through a new unknown with `W`'s codomain and
`X`'s domain (`CodomainNarrowingControls.domain_raising`). That rule, meet narrowing, is in `MeetNarrowing`, and
`MeetSolver` decides a fragment that contains this one and that store (`Meet.compatibleGroups_of_oneDomain`,
`Meet.raising_solved`). The exact boundary of principality with several domains is open.

**Levels.** Which rule applies to an equation is a comparison of codomains at the valuation: narrowing where
`cod X < cod W`, instantiation where every unknown fits. With level variables that comparison is a level constraint,
which a store of level constraints may leave undecided (`CodomainNarrowingControls.level_question`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

open Interface

namespace CumulativeCodes

variable {v : Nat → Nat}

/-! ## Typing: levels by value, the parameter's universe, inversion along a pattern -/

/-- **Typing reads levels only through their values**: a code is typed when its evaluation is. -/
theorem Ty.of_lower {Γ : Ctx} {p : Nat} : ∀ (t : Tm) {l : Nat}, Ty v Γ p (Tm.lower v t) l → Ty v Γ p t l
  | .par, _, h => h
  | .gnd, _, h => h
  | .sort k, _, h => by
      change Ty v Γ p (.sort (.const (Level.value v k))) _ at h
      cases h with
      | sort hk => exact .sort hk
  | .arr A B, _, h => by
      change Ty v Γ p (.arr (Tm.lower v A) (Tm.lower v B)) _ at h
      cases h with
      | arr hA hB => exact .arr (Ty.of_lower A hA) (Ty.of_lower B hB)
  | .app W t, _, h => by
      change Ty v Γ p (.app W (Tm.lower v t)) _ at h
      cases h with
      | app hW ht hc => exact .app hW (Ty.of_lower t ht) hc

/-- Codes with the same evaluation have the same types. -/
theorem Ty.of_lower_eq {Γ : Ctx} {p : Nat} {s t : Tm} {l : Nat} (same : Tm.lower v s = Tm.lower v t)
    (h : Ty v Γ p s l) : Ty v Γ p t l := by
  have h' := h.lower
  rw [same] at h'
  exact Ty.of_lower t h'

/-- **A smaller parameter universe keeps typing.** -/
theorem Ty.param_le {Γ : Ctx} {p q : Nat} {t : Tm} {l : Nat} (h : Ty v Γ p t l) (le : q ≤ p) :
    Ty v Γ q t l := by
  induction h with
  | par h => exact .par (le_trans le h)
  | gnd => exact .gnd
  | sort h => exact .sort h
  | arr _ _ ihA ihB => exact .arr ihA ihB
  | app hW _ hc ih => exact .app hW ih hc

/-- **Inversion along a pattern**: where an instance of a pattern is a code of `Sort l`, so is the body of each of
its unknowns. -/
theorem Ty.of_pattern_mem {Γ : Ctx} {q l : Nat} {σ : Nat → Tm} {W : Nat} :
    ∀ {t : Tm}, Tm.Pattern t → W ∈ Tm.unknowns t → Ty v Γ q (Tm.act σ t) l → Ty v Γ q (σ W) l
  | _, .par, h, _ => by simp [Tm.unknowns] at h
  | _, .gnd, h, _ => by simp [Tm.unknowns] at h
  | _, .sort _, h, _ => by simp [Tm.unknowns] at h
  | _, @Tm.Pattern.arr A B hA hB, h, ht => by
      simp only [Tm.unknowns, Finset.mem_union] at h
      obtain ⟨tA, tB⟩ := Ty.arr_inv (show Ty v Γ q (.arr (Tm.act σ A) (Tm.act σ B)) l from ht)
      rcases h with h | h
      · exact Ty.of_pattern_mem hA h tA
      · exact Ty.of_pattern_mem hB h tB
  | _, .app V, h, ht => by
      simp only [Tm.unknowns, Finset.mem_insert] at h
      rcases h with rfl | h
      · rwa [act_app_par] at ht
      · simp at h

/-! ## The rigid part of a code against a universe -/

/-- Whether the rigid part of a code fits `Sort l` with the parameter of `Sort q`: every universe in it is a member
of `Sort l`, and so is the parameter where it stands outside the argument of an unknown. -/
def rigidFits (v : Nat → Nat) (q l : Nat) : Tm → Bool
  | .par => decide (q ≤ l)
  | .gnd => true
  | .sort k => decide (Level.value v k + 1 ≤ l)
  | .arr A B => rigidFits v q l A && rigidFits v q l B
  | .app _ _ => true

/-- **A misfit refutes**: where the rigid part of `t` does not fit, no instance of `t` is a code of `Sort l`. -/
theorem not_ty_of_rigidFits {Γ : Ctx} {q l : Nat} (σ : Nat → Tm) :
    ∀ t : Tm, rigidFits v q l t = false → ¬ Ty v Γ q (Tm.act σ t) l
  | .par, h, ht => by
      simp only [rigidFits, decide_eq_false_iff_not] at h
      exact h (Ty.par_inv ht)
  | .gnd, h, _ => by simp [rigidFits] at h
  | .sort k, h, ht => by
      simp only [rigidFits, decide_eq_false_iff_not] at h
      change Ty v Γ q (.sort k) l at ht
      cases ht with
      | sort hk => exact h hk
  | .arr A B, h, ht => by
      simp only [rigidFits, Bool.and_eq_false_iff] at h
      obtain ⟨tA, tB⟩ := Ty.arr_inv (show Ty v Γ q (.arr (Tm.act σ A) (Tm.act σ B)) l from ht)
      rcases h with h | h
      · exact not_ty_of_rigidFits σ A h tA
      · exact not_ty_of_rigidFits σ B h tB
  | .app _ _, h, _ => by simp [rigidFits] at h

/-- **A pattern that fits is typed**: its rigid part fits, and every unknown in it has a codomain at most `l` and a
domain at least `q`. -/
theorem Ty.of_fits {Δ : Ctx} {q l : Nat} :
    ∀ {t : Tm}, Tm.Pattern t → Scoped Δ.length t → rigidFits v q l t = true →
      (∀ W ∈ Tm.unknowns t, ∀ d, Δ[W]? = some d → Level.value v d.cod ≤ l ∧ q ≤ Level.value v d.dom) →
      Ty v Δ q t l
  | _, .par, _, h, _ => .par (by simpa [rigidFits] using h)
  | _, .gnd, _, _, _ => .gnd
  | _, .sort _, _, h, _ => .sort (by simpa [rigidFits] using h)
  | _, @Tm.Pattern.arr A B hA hB, sc, h, hu => by
      obtain ⟨sA, sB⟩ := Scoped.arr_inv sc
      simp only [rigidFits, Bool.and_eq_true] at h
      exact .arr (Ty.of_fits hA sA h.1 fun W hW => hu W (by simp [Tm.unknowns, hW]))
        (Ty.of_fits hB sB h.2 fun W hW => hu W (by simp [Tm.unknowns, hW]))
  | _, .app W, sc, _, hu => by
      have hW : W < Δ.length := by
        cases sc with
        | app hW _ => exact hW
      obtain ⟨hc, hq⟩ := hu W (by simp [Tm.unknowns]) Δ[W] (List.getElem?_eq_getElem hW)
      exact .app (List.getElem?_eq_getElem hW) (.par hq) hc

/-- The instantiation of `X` by a code of its declaration is typed. -/
theorem update_typed_of_ty {Δ : Ctx} {X : Nat} {dX : Decl} (hX : Δ[X]? = some dX) {t : Tm}
    (ht : Ty v Δ (Level.value v dX.dom) t (Level.value v dX.cod)) : TyA v Δ Δ (Function.update Tm.idA X t) := by
  intro W d hW
  rcases eq_or_ne W X with rfl | h
  · rw [Function.update_self]
    rw [hX] at hW
    cases hW
    exact ht
  · rw [Function.update_of_ne h]
    exact idA_typed Δ W d hW

theorem lt_length_of_getElem? {Δ : Ctx} {W : Nat} {d : Decl} (h : Δ[W]? = some d) : W < Δ.length :=
  (List.getElem?_eq_some_iff.mp h).1

theorem decl_of_scoped_app {Δ : Ctx} {X : Nat} {t : Tm} (h : Scoped Δ.length (.app X t)) :
    ∃ d, Δ[X]? = some d := by
  cases h with
  | app hX _ => exact ⟨_, List.getElem?_eq_getElem hX⟩

/-! ## Narrowing a declaration -/

/-- **The narrowing morphism**: the identity on codes, from `Δ` to `Δ` with `W`'s declaration replaced by one with the
same domain and a codomain at most the original. It is typed by cumulativity. -/
def narrowAssign (v : Nat → Nat) {Δ : Ctx} {W : Nat} {dW : Decl} (d' : Decl) (hW : Δ[W]? = some dW)
    (dom : d'.dom = dW.dom) (cod : Level.value v d'.cod ≤ Level.value v dW.cod) : Assign v Δ (Δ.set W d') :=
  ⟨Tm.idA, fun V d hV => by
    by_cases h : V = W
    · subst h
      rw [hW] at hV
      cases hV
      exact .app (List.getElem?_set_self (lt_length_of_getElem? hW)) (.par (le_of_eq (by rw [dom]))) cod
    · exact .app (by rw [List.getElem?_set_ne (Ne.symm h)]; exact hV) (.par le_rfl) le_rfl⟩

/-- **Narrowing is exact** as soon as every solution already sends the unknown into the narrower declaration. -/
theorem narrow_exact {Δ : Ctx} {S : EquationStore (Term Δ)} {W : Nat} {dW d' : Decl}
    {σ : Assign v Δ (Δ.set W d')} (hσ : σ.1 = Tm.idA) (hW : Δ[W]? = some dW) (dom : d'.dom = dW.dom)
    (forced : ∀ (Γ : Ctx) (f : Assign v Δ Γ), (frames v).Models f S →
      Ty v Γ (Level.value v dW.dom) (f.1 W) (Level.value v d'.cod)) :
    Exact (frames v) S σ ((frames v).applyStore σ S) := by
  apply (exact_applyStore_iff S σ).mpr
  intro Γ f solved
  have typed : TyA v (Δ.set W d') Γ f.1 := by
    intro V d hV
    by_cases h : V = W
    · subst h
      rw [List.getElem?_set_self (lt_length_of_getElem? hW)] at hV
      cases hV
      rw [dom]
      exact forced Γ f solved
    · rw [List.getElem?_set_ne (Ne.symm h)] at hV
      exact f.2 V d hV
  refine ⟨⟨f.1, typed⟩, fun t => ?_⟩
  show Tm.lower v (Tm.act f.1 t.1) = Tm.lower v (Tm.act (Tm.compA f.1 σ.1) t.1)
  rw [Tm.act_comp, hσ, Tm.act_id]

/-- **What `X par ≐ t` forces**: every solution sends an unknown `W` of the pattern `t` to a code of `X`'s codomain,
over a parameter of `W`'s domain when that domain is at most `X`'s. -/
theorem forced_left {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} {X W : Nat} {dX dW : Decl}
    (hl : e.1.1 = .app X .par) (hp : Tm.Pattern e.2.1) (hW : W ∈ Tm.unknowns e.2.1) (hX : Δ[X]? = some dX)
    (dom : Level.value v dW.dom ≤ Level.value v dX.dom) (Γ : Ctx) (f : Assign v Δ Γ)
    (solved : (frames v).Models f (e :: S)) :
    Ty v Γ (Level.value v dW.dom) (f.1 W) (Level.value v dX.cod) := by
  have same := solves_head solved
  rw [hl, act_app_par] at same
  exact (Ty.of_pattern_mem hp hW (Ty.of_lower_eq same (f.2 X dX hX))).param_le dom

/-- The same on the right side. -/
theorem forced_right {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} {X W : Nat} {dX dW : Decl}
    (hr : e.2.1 = .app X .par) (hp : Tm.Pattern e.1.1) (hW : W ∈ Tm.unknowns e.1.1) (hX : Δ[X]? = some dX)
    (dom : Level.value v dW.dom ≤ Level.value v dX.dom) (Γ : Ctx) (f : Assign v Δ Γ)
    (solved : (frames v).Models f (e :: S)) :
    Ty v Γ (Level.value v dW.dom) (f.1 W) (Level.value v dX.cod) := by
  have same := solves_head solved
  rw [hr, act_app_par] at same
  exact (Ty.of_pattern_mem hp hW (Ty.of_lower_eq same.symm (f.2 X dX hX))).param_le dom

/-- **The universe refutation is sound**: `X par ≐ t` with the rigid part of `t` not fitting `X`'s declaration has
no solution. -/
theorem misfit_unsolvable_left {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} {X : Nat}
    {dX : Decl} (hl : e.1.1 = .app X .par) (hX : Δ[X]? = some dX)
    (misfit : rigidFits v (Level.value v dX.dom) (Level.value v dX.cod) e.2.1 = false) :
    ¬ (frames v).Solvable (e :: S) := by
  rintro ⟨Γ, f, solved⟩
  have same := solves_head solved
  rw [hl, act_app_par] at same
  exact not_ty_of_rigidFits f.1 e.2.1 misfit (Ty.of_lower_eq same (f.2 X dX hX))

theorem misfit_unsolvable_right {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} {X : Nat}
    {dX : Decl} (hr : e.2.1 = .app X .par) (hX : Δ[X]? = some dX)
    (misfit : rigidFits v (Level.value v dX.dom) (Level.value v dX.cod) e.1.1 = false) :
    ¬ (frames v).Solvable (e :: S) := by
  rintro ⟨Γ, f, solved⟩
  have same := solves_head solved
  rw [hr, act_app_par] at same
  exact not_ty_of_rigidFits f.1 e.1.1 misfit (Ty.of_lower_eq same.symm (f.2 X dX hX))

/-! ## The solver with narrowing -/

namespace Narrowing

/-- **The transitions**: the rules of `PatternSolver`, and narrowing on either side. -/
inductive NarrowStep (v : Nat → Nat) : {Δ : Ctx} → EquationStore (Term Δ) → (m : Ctx) → Assign v Δ m →
    EquationStore (Term m) → Prop
  | rule {Δ : Ctx} {S S' : EquationStore (Term Δ)} {σ : Assign v Δ Δ} :
      Rule v S Δ σ S' → NarrowStep v S Δ σ S'
  | narrowLeft {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} {X W : Nat} {dX dW : Decl}
      {σ : Assign v Δ (Δ.set W ⟨dW.dom, dX.cod⟩)} :
      e.1.1 = .app X .par → Tm.Pattern e.2.1 → W ∈ Tm.unknowns e.2.1 → Δ[X]? = some dX →
      Δ[W]? = some dW → Level.value v dW.dom ≤ Level.value v dX.dom →
      Level.value v dX.cod < Level.value v dW.cod → σ.1 = Tm.idA →
      NarrowStep v (e :: S) (Δ.set W ⟨dW.dom, dX.cod⟩) σ ((frames v).applyStore σ (e :: S))
  | narrowRight {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} {X W : Nat} {dX dW : Decl}
      {σ : Assign v Δ (Δ.set W ⟨dW.dom, dX.cod⟩)} :
      e.2.1 = .app X .par → Tm.Pattern e.1.1 → W ∈ Tm.unknowns e.1.1 → Δ[X]? = some dX →
      Δ[W]? = some dW → Level.value v dW.dom ≤ Level.value v dX.dom →
      Level.value v dX.cod < Level.value v dW.cod → σ.1 = Tm.idA →
      NarrowStep v (e :: S) (Δ.set W ⟨dW.dom, dX.cod⟩) σ ((frames v).applyStore σ (e :: S))

/-- **The refutations**: those of `PatternSolver`, and a rigid part that does not fit, on either side. -/
inductive NarrowRefutes (v : Nat → Nat) : {Δ : Ctx} → EquationStore (Term Δ) → Reason → Prop
  | rule {Δ : Ctx} {S : EquationStore (Term Δ)} {r : Reason} : Refutes v S r → NarrowRefutes v S r
  | misfitLeft {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} {X : Nat} {dX : Decl} :
      e.1.1 = .app X .par → Δ[X]? = some dX →
      rigidFits v (Level.value v dX.dom) (Level.value v dX.cod) e.2.1 = false → NarrowRefutes v (e :: S) .levels
  | misfitRight {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} {X : Nat} {dX : Decl} :
      e.2.1 = .app X .par → Δ[X]? = some dX →
      rigidFits v (Level.value v dX.dom) (Level.value v dX.cod) e.1.1 = false → NarrowRefutes v (e :: S) .levels

/-- **Every transition is exact.** -/
theorem NarrowStep.exact {Δ m : Ctx} {S : EquationStore (Term Δ)} {σ : Assign v Δ m}
    {S' : EquationStore (Term m)} (st : NarrowStep v S m σ S') : Exact (frames v) S σ S' := by
  cases st with
  | rule r => exact r.exact
  | narrowLeft hl hp hW hX hdW dom _ hσ =>
      refine narrow_exact hσ hdW rfl fun Γ f solved => ?_
      have forced := forced_left hl hp hW hX dom Γ f solved
      exact forced
  | narrowRight hr hp hW hX hdW dom _ hσ =>
      refine narrow_exact hσ hdW rfl fun Γ f solved => ?_
      have forced := forced_right hr hp hW hX dom Γ f solved
      exact forced

/-- **Every refutation is sound.** -/
theorem NarrowRefutes.sound {Δ : Ctx} {S : EquationStore (Term Δ)} {r : Reason} (refuted : NarrowRefutes v S r) :
    ¬ (frames v).Solvable S := by
  cases refuted with
  | rule r => exact r.sound
  | misfitLeft hl hX misfit => exact misfit_unsolvable_left hl hX misfit
  | misfitRight hr hX misfit => exact misfit_unsolvable_right hr hX misfit

/-- **The solver with narrowing**, as a `Solver` of the frames. -/
def solver (v : Nat → Nat) : Solver (frames v) where
  Step S m σ S' := NarrowStep v S m σ S'
  step_exact st := NarrowStep.exact st
  Refutes S r := NarrowRefutes v S r
  refutes_sound r := NarrowRefutes.sound r

/-! ## Termination -/

/-- The sum of the codomains of a context, at the valuation. -/
def codSum (v : Nat → Nat) : Ctx → Nat
  | [] => 0
  | d :: Δ => Level.value v d.cod + codSum v Δ

/-- Narrowing a declaration lowers the sum of the codomains. -/
theorem codSum_set_lt (v : Nat → Nat) : ∀ {Δ : Ctx} {W : Nat} {dW d' : Decl}, Δ[W]? = some dW →
    Level.value v d'.cod < Level.value v dW.cod → codSum v (Δ.set W d') < codSum v Δ
  | [], _, _, _, h, _ => by simp at h
  | _ :: _, 0, _, _, h, lt => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp only [List.set_cons_zero, codSum]
      omega
  | _ :: Δ, W + 1, _, _, h, lt => by
      simp only [List.getElem?_cons_succ] at h
      simp only [List.set_cons_succ, codSum]
      have := codSum_set_lt v (Δ := Δ) h lt
      omega

theorem storeUnknowns_applyStore_id {Δ m : Ctx} {σ : Assign v Δ m} (hσ : σ.1 = Tm.idA) :
    ∀ S : EquationStore (Term Δ), storeUnknowns ((frames v).applyStore σ S) = storeUnknowns S
  | [] => rfl
  | e :: S => by
      show Tm.unknowns (Tm.act σ.1 e.1.1) ∪ Tm.unknowns (Tm.act σ.1 e.2.1) ∪
          storeUnknowns ((frames v).applyStore σ S) = Tm.unknowns e.1.1 ∪ Tm.unknowns e.2.1 ∪ storeUnknowns S
      rw [hσ, Tm.act_id, Tm.act_id, storeUnknowns_applyStore_id hσ S]

theorem storeSize_applyStore_id {Δ m : Ctx} {σ : Assign v Δ m} (hσ : σ.1 = Tm.idA) :
    ∀ S : EquationStore (Term Δ), storeSize ((frames v).applyStore σ S) = storeSize S
  | [] => rfl
  | e :: S => by
      show Tm.size (Tm.act σ.1 e.1.1) + Tm.size (Tm.act σ.1 e.2.1) +
          storeSize ((frames v).applyStore σ S) = Tm.size e.1.1 + Tm.size e.2.1 + storeSize S
      rw [hσ, Tm.act_id, Tm.act_id, storeSize_applyStore_id hσ S]

/-- Transport along the identity on codes keeps the rank. -/
theorem rank_applyStore_id {Δ m : Ctx} {σ : Assign v Δ m} (hσ : σ.1 = Tm.idA) (S : EquationStore (Term Δ)) :
    rank ((frames v).applyStore σ S) = rank S := by
  unfold rank
  rw [storeUnknowns_applyStore_id hσ, storeSize_applyStore_id hσ]

/-- The measure of a store at its context: its rank, then the sum of the codomains of the context. -/
def narrowMeasure (v : Nat → Nat) (x : (Δ : Ctx) × EquationStore (Term Δ)) : (Nat × Nat) × Nat :=
  (rank x.2, codSum v x.1)

/-- The lexicographic order of measures. -/
def MeasureLt : (Nat × Nat) × Nat → (Nat × Nat) × Nat → Prop := Prod.Lex RankLt (· < ·)

theorem measureLt_wf : WellFounded MeasureLt := (Prod.lex ⟨RankLt, rankLt_wf⟩ Nat.lt_wfRel).wf

/-- **Every transition lowers the measure.** -/
theorem NarrowStep.measure_lt {Δ m : Ctx} {S : EquationStore (Term Δ)} {σ : Assign v Δ m}
    {S' : EquationStore (Term m)} (st : NarrowStep v S m σ S') :
    MeasureLt (narrowMeasure v ⟨m, S'⟩) (narrowMeasure v ⟨Δ, S⟩) := by
  cases st with
  | rule r => exact Prod.Lex.left _ _ r.rank_lt
  | narrowLeft _ _ _ _ hdW _ lt hσ =>
      show Prod.Lex RankLt (· < ·) (rank _, codSum v _) (rank _, codSum v _)
      rw [rank_applyStore_id hσ]
      exact Prod.Lex.right _ (codSum_set_lt v hdW lt)
  | narrowRight _ _ _ _ hdW _ lt hσ =>
      show Prod.Lex RankLt (· < ·) (rank _, codSum v _) (rank _, codSum v _)
      rw [rank_applyStore_id hσ]
      exact Prod.Lex.right _ (codSum_set_lt v hdW lt)

/-- **The transitions terminate**: there is no infinite run from any store at any context. -/
theorem steps_terminate (v : Nat → Nat) :
    WellFounded (fun y x : (Δ : Ctx) × EquationStore (Term Δ) =>
      ∃ σ : Assign v x.1 y.1, NarrowStep v x.2 y.1 σ y.2) :=
  Subrelation.wf (fun ⟨_, st⟩ => st.measure_lt) (InvImage.wf (narrowMeasure v) measureLt_wf)

/-! ## The fragment with one domain per equation -/

/-- Every unknown of the code is declared with a domain of value `p`. -/
def DomainAt (v : Nat → Nat) (Δ : Ctx) (p : Nat) (t : Tm) : Prop :=
  ∀ W ∈ Tm.unknowns t, ∀ d, Δ[W]? = some d → Level.value v d.dom = p

/-- **The fragment with one domain per equation**: both sides of every equation are patterns, and the unknowns of
each equation are declared with one domain. Codomains are free, and so are the domains of different equations. -/
structure OneDomain (v : Nat → Nat) (Δ : Ctx) (S : EquationStore (Term Δ)) : Prop where
  pattern : ∀ e ∈ S, Tm.Pattern e.1.1 ∧ Tm.Pattern e.2.1
  domain : ∀ e ∈ S, ∃ p, DomainAt v Δ p e.1.1 ∧ DomainAt v Δ p e.2.1

theorem OneDomain.tail {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)}
    (h : OneDomain v Δ (e :: S)) : OneDomain v Δ S :=
  ⟨fun e' he' => h.pattern e' (List.mem_cons_of_mem _ he'),
    fun e' he' => h.domain e' (List.mem_cons_of_mem _ he')⟩

theorem DomainAt.arr_inv {Δ : Ctx} {p : Nat} {A B : Tm} (h : DomainAt v Δ p (.arr A B)) :
    DomainAt v Δ p A ∧ DomainAt v Δ p B :=
  ⟨fun W hW => h W (by simp [Tm.unknowns, hW]), fun W hW => h W (by simp [Tm.unknowns, hW])⟩

theorem act_update_of_not_mem {X : Nat} {t s : Tm} (h : X ∉ Tm.unknowns s) :
    Tm.act (Function.update Tm.idA X t) s = s := by
  have fresh : Tm.occurs X s = false := by
    cases hc : Tm.occurs X s with
    | false => rfl
    | true => exact absurd ((Tm.occurs_iff X s).mp hc) h
  rw [Tm.act_congr_occurs (τ := Tm.idA) (fun V hV => by rw [Function.update_of_ne hV]) s fresh, Tm.act_id]

/-- Instantiating `X` by a code whose unknowns have `X`'s domain keeps one domain. -/
theorem domainAt_solve {Δ : Ctx} {p p₀ X : Nat} {t s : Tm} {dX : Decl} (hX : Δ[X]? = some dX)
    (hXp : Level.value v dX.dom = p₀) (ht : DomainAt v Δ p₀ t) (hs : DomainAt v Δ p s) :
    DomainAt v Δ p (Tm.act (Function.update Tm.idA X t) s) := by
  by_cases hXs : X ∈ Tm.unknowns s
  · intro W hW d hd
    rcases Finset.mem_union.mp (Tm.unknowns_act_update X t s hW) with h | h
    · exact hs W (Finset.mem_erase.mp h).2 d hd
    · rw [ht W h d hd, ← hXp]
      exact hs X hXs dX hX
  · rw [act_update_of_not_mem hXs]
    exact hs

/-- Narrowing keeps domains. -/
theorem domainAt_set {Δ : Ctx} {p W : Nat} {dW d' : Decl} {t : Tm} (hW : Δ[W]? = some dW)
    (dom : d'.dom = dW.dom) (h : DomainAt v Δ p t) : DomainAt v (Δ.set W d') p t := by
  intro V hV d hd
  by_cases hVW : V = W
  · subst hVW
    rw [List.getElem?_set_self (lt_length_of_getElem? hW)] at hd
    cases hd
    rw [dom]
    exact h V hV dW hW
  · rw [List.getElem?_set_ne (Ne.symm hVW)] at hd
    exact h V hV d hd

theorem solve_oneDomain {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} {X : Nat} {u : Tm}
    {σ : Assign v Δ Δ} (hσ : σ.1 = Function.update Tm.idA X u) (hu : Tm.Pattern u) {dX : Decl}
    (hdX : Δ[X]? = some dX) {p₀ : Nat} (hXp : Level.value v dX.dom = p₀) (hup : DomainAt v Δ p₀ u)
    (h : OneDomain v Δ (e :: S)) : OneDomain v Δ ((frames v).applyStore σ S) := by
  have bodies : ∀ W, Tm.Pattern (σ.1 W) := by
    intro W
    rw [hσ]
    by_cases hW : W = X
    · subst hW
      rw [Function.update_self]
      exact hu
    · rw [Function.update_of_ne hW]
      exact .app W
  refine ⟨fun e' he' => ?_, fun e' he' => ?_⟩
  · obtain ⟨e'', he'', rfl⟩ := List.mem_map.mp he'
    obtain ⟨one, two⟩ := h.pattern e'' (List.mem_cons_of_mem _ he'')
    exact ⟨Tm.Pattern.act bodies one, Tm.Pattern.act bodies two⟩
  · obtain ⟨e'', he'', rfl⟩ := List.mem_map.mp he'
    obtain ⟨p, one, two⟩ := h.domain e'' (List.mem_cons_of_mem _ he'')
    refine ⟨p, ?_, ?_⟩
    · show DomainAt v Δ p (Tm.act σ.1 e''.1.1)
      rw [hσ]
      exact domainAt_solve hdX hXp hup one
    · show DomainAt v Δ p (Tm.act σ.1 e''.2.1)
      rw [hσ]
      exact domainAt_solve hdX hXp hup two

theorem narrow_oneDomain {Δ : Ctx} {S : EquationStore (Term Δ)} {W : Nat} {dW d' : Decl}
    {σ : Assign v Δ (Δ.set W d')} (hσ : σ.1 = Tm.idA) (hW : Δ[W]? = some dW) (dom : d'.dom = dW.dom)
    (h : OneDomain v Δ S) : OneDomain v (Δ.set W d') ((frames v).applyStore σ S) := by
  refine ⟨fun e' he' => ?_, fun e' he' => ?_⟩
  · obtain ⟨e'', he'', rfl⟩ := List.mem_map.mp he'
    show Tm.Pattern (Tm.act σ.1 e''.1.1) ∧ Tm.Pattern (Tm.act σ.1 e''.2.1)
    rw [hσ, Tm.act_id, Tm.act_id]
    exact h.pattern e'' he''
  · obtain ⟨e'', he'', rfl⟩ := List.mem_map.mp he'
    obtain ⟨p, one, two⟩ := h.domain e'' he''
    refine ⟨p, ?_, ?_⟩
    · show DomainAt v (Δ.set W d') p (Tm.act σ.1 e''.1.1)
      rw [hσ, Tm.act_id]
      exact domainAt_set hW dom one
    · show DomainAt v (Δ.set W d') p (Tm.act σ.1 e''.2.1)
      rw [hσ, Tm.act_id]
      exact domainAt_set hW dom two

/-- **The transitions keep the fragment.** -/
theorem NarrowStep.oneDomain {Δ m : Ctx} {S : EquationStore (Term Δ)} {σ : Assign v Δ m}
    {S' : EquationStore (Term m)} (st : NarrowStep v S m σ S') (h : OneDomain v Δ S) : OneDomain v m S' := by
  cases st with
  | rule r =>
      cases r with
      | delete _ => exact h.tail
      | decompose h₀ h₀' h₁ h₁' h₂ h₂' =>
          obtain ⟨p₁, p₂⟩ := h.pattern _ List.mem_cons_self
          obtain ⟨p, d₁, d₂⟩ := h.domain _ List.mem_cons_self
          rw [h₀] at p₁ d₁
          rw [h₀'] at p₂ d₂
          refine ⟨fun e' he' => ?_, fun e' he' => ?_⟩
          · rcases List.mem_cons.mp he' with rfl | he'
            · rw [h₁, h₁']
              exact ⟨(Pattern.arr_inv p₁).1, (Pattern.arr_inv p₂).1⟩
            rcases List.mem_cons.mp he' with rfl | he'
            · rw [h₂, h₂']
              exact ⟨(Pattern.arr_inv p₁).2, (Pattern.arr_inv p₂).2⟩
            exact h.pattern e' (List.mem_cons_of_mem _ he')
          · rcases List.mem_cons.mp he' with rfl | he'
            · rw [h₁, h₁']
              exact ⟨p, d₁.arr_inv.1, d₂.arr_inv.1⟩
            rcases List.mem_cons.mp he' with rfl | he'
            · rw [h₂, h₂']
              exact ⟨p, d₁.arr_inv.2, d₂.arr_inv.2⟩
            exact h.domain e' (List.mem_cons_of_mem _ he')
      | @solveLeft e S X σ hl _ hσ =>
          obtain ⟨dX, hdX⟩ := decl_of_scoped_app (show Scoped Δ.length (.app X .par) from hl ▸ e.1.2)
          obtain ⟨p, d₁, d₂⟩ := h.domain _ List.mem_cons_self
          rw [hl] at d₁
          exact solve_oneDomain hσ (h.pattern _ List.mem_cons_self).2 hdX
            (d₁ X (by simp [Tm.unknowns]) dX hdX) d₂ h
      | @solveRight e S X σ hr _ hσ =>
          obtain ⟨dX, hdX⟩ := decl_of_scoped_app (show Scoped Δ.length (.app X .par) from hr ▸ e.2.2)
          obtain ⟨p, d₁, d₂⟩ := h.domain _ List.mem_cons_self
          rw [hr] at d₂
          exact solve_oneDomain hσ (h.pattern _ List.mem_cons_self).1 hdX
            (d₂ X (by simp [Tm.unknowns]) dX hdX) d₁ h
  | narrowLeft _ _ _ _ hdW _ _ hσ => exact narrow_oneDomain hσ hdW rfl h
  | narrowRight _ _ _ _ hdW _ _ hσ => exact narrow_oneDomain hσ hdW rfl h

/-! ## Progress and decision -/

/-- **Progress on the fragment**: a nonempty store of the fragment has a transition or a refutation. -/
theorem progress {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} (h : OneDomain v Δ (e :: S)) :
    (∃ (m : Ctx) (σ : Assign v Δ m) (S' : EquationStore (Term m)), NarrowStep v (e :: S) m σ S') ∨
      ∃ r : Reason, NarrowRefutes v (e :: S) r := by
  obtain ⟨⟨s, hs⟩, ⟨t, ht⟩⟩ := e
  obtain ⟨ps, pt⟩ := h.pattern _ List.mem_cons_self
  obtain ⟨p, ds, dt⟩ := h.domain _ List.mem_cons_self
  simp only at ps pt ds dt
  by_cases same : Tm.lower v s = Tm.lower v t
  · exact Or.inl ⟨_, _, _, .rule (.delete same)⟩
  have flexLeft : ∀ X, s = .app X .par →
      (∃ (m : Ctx) (σ : Assign v Δ m) (S' : EquationStore (Term m)),
        NarrowStep v ((⟨s, hs⟩, ⟨t, ht⟩) :: S) m σ S') ∨
        ∃ r : Reason, NarrowRefutes v ((⟨s, hs⟩, ⟨t, ht⟩) :: S) r := by
    intro X hX
    subst hX
    obtain ⟨dX, hdX⟩ := decl_of_scoped_app hs
    have pX : Level.value v dX.dom = p := ds X (by simp [Tm.unknowns]) dX hdX
    cases hocc : Tm.occurs X t with
    | true =>
        refine Or.inr ⟨_, .rule (.occursLeft rfl pt ((Tm.occurs_iff X t).mp hocc) ?_)⟩
        intro htX
        exact same (by rw [show t = .app X .par from htX])
    | false =>
        cases hfit : rigidFits v (Level.value v dX.dom) (Level.value v dX.cod) t with
        | false => exact Or.inr ⟨_, .misfitLeft rfl hdX hfit⟩
        | true =>
            by_cases big : ∃ W ∈ Tm.unknowns t, ∃ dW, Δ[W]? = some dW ∧
                Level.value v dX.cod < Level.value v dW.cod
            · obtain ⟨W, hW, dW, hdW, lt⟩ := big
              have dom : Level.value v dW.dom ≤ Level.value v dX.dom := by rw [dt W hW dW hdW, pX]
              exact Or.inl ⟨_, narrowAssign v ⟨dW.dom, dX.cod⟩ hdW rfl lt.le, _,
                .narrowLeft rfl pt hW hdX hdW dom lt rfl⟩
            · have typed : Ty v Δ (Level.value v dX.dom) t (Level.value v dX.cod) :=
                Ty.of_fits pt ht hfit fun W hW d hd =>
                  ⟨Nat.le_of_not_lt fun lt => big ⟨W, hW, d, hd, lt⟩, by rw [dt W hW d hd, pX]⟩
              exact Or.inl ⟨_, ⟨Function.update Tm.idA X t, update_typed_of_ty hdX typed⟩, _,
                .rule (.solveLeft rfl hocc rfl)⟩
  have flexRight : ∀ X, t = .app X .par →
      (∃ (m : Ctx) (σ : Assign v Δ m) (S' : EquationStore (Term m)),
        NarrowStep v ((⟨s, hs⟩, ⟨t, ht⟩) :: S) m σ S') ∨
        ∃ r : Reason, NarrowRefutes v ((⟨s, hs⟩, ⟨t, ht⟩) :: S) r := by
    intro X hX
    subst hX
    obtain ⟨dX, hdX⟩ := decl_of_scoped_app ht
    have pX : Level.value v dX.dom = p := dt X (by simp [Tm.unknowns]) dX hdX
    cases hocc : Tm.occurs X s with
    | true =>
        refine Or.inr ⟨_, .rule (.occursRight rfl ps ((Tm.occurs_iff X s).mp hocc) ?_)⟩
        intro hsX
        exact same (by rw [show s = .app X .par from hsX])
    | false =>
        cases hfit : rigidFits v (Level.value v dX.dom) (Level.value v dX.cod) s with
        | false => exact Or.inr ⟨_, .misfitRight rfl hdX hfit⟩
        | true =>
            by_cases big : ∃ W ∈ Tm.unknowns s, ∃ dW, Δ[W]? = some dW ∧
                Level.value v dX.cod < Level.value v dW.cod
            · obtain ⟨W, hW, dW, hdW, lt⟩ := big
              have dom : Level.value v dW.dom ≤ Level.value v dX.dom := by rw [ds W hW dW hdW, pX]
              exact Or.inl ⟨_, narrowAssign v ⟨dW.dom, dX.cod⟩ hdW rfl lt.le, _,
                .narrowRight rfl ps hW hdX hdW dom lt rfl⟩
            · have typed : Ty v Δ (Level.value v dX.dom) s (Level.value v dX.cod) :=
                Ty.of_fits ps hs hfit fun W hW d hd =>
                  ⟨Nat.le_of_not_lt fun lt => big ⟨W, hW, d, hd, lt⟩, by rw [ds W hW d hd, pX]⟩
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

/-- **Decision on the fragment**: every store of the fragment has a run, through narrowed contexts, that ends in the
empty store or in a refutation. -/
theorem decided {Δ : Ctx} (S : EquationStore (Term Δ)) (h : OneDomain v Δ S) :
    ∃ (m : Ctx) (σ : Assign v Δ m) (R : EquationStore (Term m)), (solver v).Reaches S m σ R ∧
      (R = [] ∨ ∃ r : Reason, NarrowRefutes v R r) := by
  suffices key : ∀ x : (Δ : Ctx) × EquationStore (Term Δ), OneDomain v x.1 x.2 →
      ∃ (m : Ctx) (σ : Assign v x.1 m) (R : EquationStore (Term m)), (solver v).Reaches x.2 m σ R ∧
        (R = [] ∨ ∃ r : Reason, NarrowRefutes v R r) from key ⟨Δ, S⟩ h
  intro x
  induction x using (InvImage.wf (narrowMeasure v) measureLt_wf).induction with
  | h x ih =>
      obtain ⟨Δ, S⟩ := x
      intro h
      match S, h with
      | [], _ => exact ⟨Δ, _, [], .refl [], Or.inl rfl⟩
      | e :: S, h =>
          rcases progress h with ⟨m, σ, S', st⟩ | ⟨reason, refuted⟩
          · obtain ⟨n, τ, R, run, ends⟩ := ih ⟨m, S'⟩ st.measure_lt (st.oneDomain h)
            exact ⟨n, _, R, .step st run, ends⟩
          · exact ⟨Δ, _, _, .refl _, Or.inr ⟨reason, refuted⟩⟩

/-- **Principal or unsolvable, with several codomains**: every store of the fragment with one domain per equation
has a principal answer, reached by the solver, or no solution. -/
theorem principal_or_unsolvable {Δ : Ctx} (S : EquationStore (Term Δ)) (h : OneDomain v Δ S) :
    (∃ (m : Ctx) (σ : Assign v Δ m), (frames v).Principal S σ) ∨ ¬ (frames v).Solvable S := by
  obtain ⟨m, σ, R, run, ends⟩ := decided S h
  rcases ends with rfl | ⟨r, refuted⟩
  · exact Or.inl ⟨m, σ, solved_principal run⟩
  · exact Or.inr (refuted_none (P := solver v) run refuted)

end Narrowing

end CumulativeCodes

#print axioms CumulativeCodes.Ty.of_lower
#print axioms CumulativeCodes.Ty.of_pattern_mem
#print axioms CumulativeCodes.not_ty_of_rigidFits
#print axioms CumulativeCodes.Ty.of_fits
#print axioms CumulativeCodes.narrow_exact
#print axioms CumulativeCodes.forced_left
#print axioms CumulativeCodes.misfit_unsolvable_left
#print axioms CumulativeCodes.Narrowing.NarrowStep.exact
#print axioms CumulativeCodes.Narrowing.NarrowRefutes.sound
#print axioms CumulativeCodes.Narrowing.NarrowStep.measure_lt
#print axioms CumulativeCodes.Narrowing.steps_terminate
#print axioms CumulativeCodes.Narrowing.NarrowStep.oneDomain
#print axioms CumulativeCodes.Narrowing.progress
#print axioms CumulativeCodes.Narrowing.decided
#print axioms CumulativeCodes.Narrowing.principal_or_unsolvable

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
