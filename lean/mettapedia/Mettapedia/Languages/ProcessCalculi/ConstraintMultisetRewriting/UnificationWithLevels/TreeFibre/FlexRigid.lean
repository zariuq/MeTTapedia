import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.TrueMeet
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentOccursCheck

/-!
# Flex-rigid equations with meet narrowing: arrow codes, narrowing and solving in one exact step

Universe unknowns `X : U_u` and equations `X ≐ t` at a universe `U_v`, where `t` is a **first-order arrow code**
(`Arrow`): an unknown, a head, or `Π (_ : A). h` with `A` again an arrow code and `h` a head. Every unknown of an
arrow code occurs along its domains (`holdsVar_of_mem`), so the tree's meet narrowing applies to each.

* **Typing** (`arrow_typed`): an arrow code is a type of `U_u` when its unknowns are declared at universes below `u`
  and its heads are typed by universes below `u`.
* **Misfit** (`arrow_misfit`): when a head of `t` is typed by no universe below `u`, no type of `U_u` equals an
  instance of `t`; the equation has no solution.
* **Occurs** (`arrow_domainOccurrence`): an unknown of `t` other than `t` itself occurs along domains; the tree's
  occurs check refutes the equation (`ContextualDependentOccursCheck.OccursShape.refutes`).
* **Narrow and solve** (`narrowSolveUpdate`, `narrowSolve_exact`): every unknown of `t` declared above `u` is
  declared again at `U_u` (`lowerSet`), and `X := t`. Every solution factors: it sends each such unknown to a type
  equal to a type of `U_u` (`HoldsVar.small`), and `X` to a type equal to its instance of `t`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentUniverseInjective ContextualDependentCumulative

variable {Head L : Type} [UniverseLevel.LevelOrder L]

/-! ## Arrow codes -/

section Codes

/-- **A first-order arrow code**: an unknown, a head, or `Π (_ : A). h` with `A` an arrow code and `h` a head. -/
inductive Arrow {n : Nat} : Tm Head n → Prop
  | var (Y : Fin n) : Arrow (.var Y)
  | head (h : Head) : Arrow (.head h)
  | pi {A : Tm Head n} (h : Head) : Arrow A → Arrow (.pi A (.head h))

/-- Whether a code is an arrow code, decided. -/
def isArrow : {n : Nat} → Tm Head n → Bool
  | _, .var _ => true
  | _, .head _ => true
  | _, .pi A (.head _) => isArrow A
  | _, _ => false

theorem arrow_of_isArrow : ∀ {n : Nat} {t : Tm Head n}, isArrow t = true → Arrow t
  | _, .var Y, _ => .var Y
  | _, .head h, _ => .head h
  | _, .pi A (.head h), found => .pi h (arrow_of_isArrow (by simpa [isArrow] using found))
  | _, .pi _ (.var _), found => by simp [isArrow] at found
  | _, .pi _ (.const _), found => by simp [isArrow] at found
  | _, .pi _ (.pi _ _), found => by simp [isArrow] at found
  | _, .pi _ (.sigma _ _), found => by simp [isArrow] at found
  | _, .pi _ (.id _ _ _), found => by simp [isArrow] at found
  | _, .pi _ (.lam _), found => by simp [isArrow] at found
  | _, .pi _ (.app _ _), found => by simp [isArrow] at found
  | _, .pi _ (.pair _ _), found => by simp [isArrow] at found
  | _, .pi _ (.fst _), found => by simp [isArrow] at found
  | _, .pi _ (.snd _), found => by simp [isArrow] at found
  | _, .pi _ (.refl _), found => by simp [isArrow] at found
  | _, .const _, found => by simp [isArrow] at found
  | _, .sigma _ _, found => by simp [isArrow] at found
  | _, .id _ _ _, found => by simp [isArrow] at found
  | _, .lam _, found => by simp [isArrow] at found
  | _, .app _ _, found => by simp [isArrow] at found
  | _, .pair _ _, found => by simp [isArrow] at found
  | _, .fst _, found => by simp [isArrow] at found
  | _, .snd _, found => by simp [isArrow] at found
  | _, .refl _, found => by simp [isArrow] at found

theorem isArrow_of_arrow {n : Nat} {t : Tm Head n} (arrow : Arrow t) : isArrow t = true := by
  induction arrow with
  | var => rfl
  | head => rfl
  | pi _ _ ih => simpa [isArrow] using ih

/-- The heads of an arrow code. -/
def arrowHeads : {n : Nat} → Tm Head n → List Head
  | _, .head h => [h]
  | _, .pi A (.head h) => h :: arrowHeads A
  | _, _ => []

/-- `X := t`, the identity elsewhere, on codes. -/
def solveSub {n : Nat} (X : Fin n) (t : Tm Head n) : Sub Head n n := fun i => if i = X then t else .var i

theorem solveSub_self {n : Nat} (X : Fin n) (t : Tm Head n) : solveSub X t X = t := by simp [solveSub]

theorem solveSub_ne {n : Nat} {X i : Fin n} (t : Tm Head n) (h : i ≠ X) : solveSub X t i = .var i := by
  simp [solveSub, h]

/-- **An arrow code without `X` is fixed by `X := t`.** -/
theorem subst_solveSub_fixed {n : Nat} {X : Fin n} (t : Tm Head n) :
    ∀ {s : Tm Head n}, Arrow s → X ∉ domainVars s → Presentation.subst (solveSub X t) s = s := by
  intro s arrow
  induction arrow with
  | var Y =>
      intro absent
      have ne : Y ≠ X := fun same => absent (by rw [same]; exact List.mem_singleton_self X)
      change solveSub X t Y = .var Y
      exact solveSub_ne t ne
  | head => intro _; rfl
  | pi h _ ih =>
      intro absent
      change Tm.pi (Presentation.subst (solveSub X t) _) (.head h) = _
      rw [ih absent]

/-- **Arrow codes are kept by `X := t` for an arrow code `t`.** -/
theorem arrow_subst_solve {n : Nat} {X : Fin n} {t : Tm Head n} (arrowT : Arrow t) :
    ∀ {s : Tm Head n}, Arrow s → Arrow (Presentation.subst (solveSub X t) s) := by
  intro s arrow
  induction arrow with
  | var Y =>
      change Arrow (solveSub X t Y)
      by_cases h : Y = X
      · rw [h, solveSub_self]
        exact arrowT
      · rw [solveSub_ne t h]
        exact .var Y
  | head h => exact .head h
  | pi h _ ih => exact .pi h ih

/-- The heads of an instance are heads of the code or of `t`. -/
theorem arrowHeads_subst_solve {n : Nat} {X : Fin n} {t : Tm Head n} :
    ∀ {s : Tm Head n}, Arrow s → ∀ h ∈ arrowHeads (Presentation.subst (solveSub X t) s),
      h ∈ arrowHeads s ∨ h ∈ arrowHeads t := by
  intro s arrow
  induction arrow with
  | var Y =>
      intro h member
      change h ∈ arrowHeads (solveSub X t Y) at member
      by_cases same : Y = X
      · rw [same, solveSub_self] at member
        exact .inr member
      · rw [solveSub_ne t same] at member
        cases member
  | head h => intro h' member; exact .inl member
  | pi h _ ih =>
      intro h' member
      change h' ∈ h :: arrowHeads (Presentation.subst (solveSub X t) _) at member
      rcases List.mem_cons.mp member with rfl | member
      · exact .inl List.mem_cons_self
      · rcases ih h' member with inner | inT
        · exact .inl (List.mem_cons_of_mem _ inner)
        · exact .inr inT

/-- The unknowns of an instance are unknowns of the code other than `X`, or unknowns of `t`. -/
theorem domainVars_subst_solve {n : Nat} {X : Fin n} {t : Tm Head n} :
    ∀ {s : Tm Head n}, Arrow s → ∀ Y ∈ domainVars (Presentation.subst (solveSub X t) s),
      (Y ∈ domainVars s ∧ Y ≠ X) ∨ Y ∈ domainVars t := by
  intro s arrow
  induction arrow with
  | var Z =>
      intro Y member
      change Y ∈ domainVars (solveSub X t Z) at member
      by_cases same : Z = X
      · rw [same, solveSub_self] at member
        exact .inr member
      · rw [solveSub_ne t same] at member
        have hY : Y = Z := List.mem_singleton.mp member
        subst hY
        exact .inl ⟨List.mem_singleton_self _, same⟩
  | head h => intro Y member; cases member
  | pi h _ ih =>
      intro Y member
      exact ih Y member

/-- **In an arrow code, an unknown other than the code itself occurs along domains.** -/
theorem arrow_domainOccurrence {n : Nat} {X : Fin n} :
    ∀ {t : Tm Head n}, Arrow t → X ∈ domainVars t → t ≠ .var X →
      ContextualDependentOccursCheck.DomainOccurrence (.var X) t := by
  intro t arrow
  induction arrow with
  | var Y =>
      intro member ne
      have hY : X = Y := List.mem_singleton.mp member
      exact absurd (by rw [hY]) ne
  | head h => intro member; cases member
  | @pi A h _ ih =>
      intro member _
      by_cases same : A = Tm.var X
      · rw [same]
        exact .here true
      · exact .deeper true (ih member same)

end Codes

/-! ## Typing and misfits -/

section Typing

variable {S : Setting Head L}

/-- **An arrow code is a type of `U_u`** when its unknowns are declared at universes below `u` and its heads are
typed by universes below `u`. -/
theorem arrow_typed (algebra : CumulativeAlgebra S.R) {u : Head} (hu : S.R.isUniverse u) :
    ∀ {n : Nat} {Γ : Ctx Head n} {t : Tm Head n}, Arrow t → CtxFormed S.R Γ →
      (∀ Y ∈ domainVars t, ∃ w, Ctx.lookup Γ Y = .head w ∧ S.R.cumulative w u) →
      (∀ h ∈ arrowHeads t, ∃ k, S.R.headTyping h k ∧ S.R.cumulative k u) →
      Typed S.R Γ t (.head u) := by
  intro n Γ t arrow
  induction arrow with
  | var Y =>
      intro _ vars _
      obtain ⟨w, hw, c⟩ := vars Y (List.mem_singleton_self Y)
      have typed := Derivable.var (R := S.R) (Γ := Γ) Y
      rw [hw] at typed
      exact Derivable.cumul typed c
  | head h =>
      intro _ _ heads
      obtain ⟨k, typing, c⟩ := heads h (List.mem_singleton_self h)
      exact Derivable.cumul (Derivable.headType typing) c
  | @pi A h _ ih =>
      intro formed vars heads
      have tA : Typed S.R Γ A (.head u) :=
        ih formed vars (fun h' member => heads h' (List.mem_cons_of_mem _ member))
      obtain ⟨k, typing, c⟩ := heads h List.mem_cons_self
      have tB : Typed S.R (.snoc Γ A) (.head h) (.head u) := Derivable.cumul (Derivable.headType typing) c
      obtain ⟨w', join'⟩ := S.levels.join_exists hu hu
      exact Derivable.cumul (Derivable.piForm tA hu tB hu join')
        (algebra.join_least join' (S.levels.cumulative_refl hu) (S.levels.cumulative_refl hu))

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra rigid complete in
/-- **A misfit head refutes**: if a head of an arrow code is typed by no universe below `u`, no type of `U_u` is equal
to an instance of the code. -/
theorem arrow_misfit {u h₀ : Head} (hu : S.R.isUniverse u)
    (apart : ∀ k, S.R.headTyping h₀ k → ¬ S.R.cumulative k u) :
    ∀ {n : Nat} {t : Tm Head n}, Arrow t → h₀ ∈ arrowHeads t → ∀ {m : Nat} {Δ : Ctx Head m}, CtxFormed S.R Δ →
      ∀ (σ : Sub Head n m) {s : Tm Head m}, Typed S.R Δ s (.head u) → ¬ TypeEq S.R Δ s (Presentation.subst σ t) := by
  intro n t arrow
  induction arrow with
  | var Y => intro member; cases member
  | head h =>
      intro member m Δ formed σ s ts
      have same : h₀ = h := List.mem_singleton.mp member
      subst same
      exact sort_not_small facts roots heads algebra rigid complete formed hu apart ts
  | @pi A h _ ih =>
      intro member m Δ formed σ s ts equal
      change TypeEq S.R Δ s (.pi (Presentation.subst σ A) (.head h)) at equal
      obtain ⟨A', B', tA', eA', tB', eB'⟩ := small_pi facts roots heads algebra rigid complete formed hu ts equal
      rcases List.mem_cons.mp member with same | inner
      · subst same
        exact sort_not_small facts roots heads algebra rigid complete
          (formed.snoc ⟨u, hu, tA'⟩) hu apart tB' eB'
      · exact ih inner formed σ tA' eA'

end Typing

/-! ## Lowering several declarations -/

section Lowering

/-- The telescope with every declaration in `chosen` replaced by the universe `u`. -/
def lowerSet : {n : Nat} → Ctx Head n → (Fin n → Bool) → Head → Ctx Head n
  | _, .nil, _, _ => .nil
  | _, .snoc Γ A, chosen, u =>
      .snoc (lowerSet Γ (fun i => chosen i.succ) u) (if chosen 0 = true then .head u else A)

theorem lookup_lowerSet_in : ∀ {n : Nat} (Γ : Ctx Head n) (chosen : Fin n → Bool) (u : Head) (i : Fin n),
    chosen i = true → Ctx.lookup (lowerSet Γ chosen u) i = .head u := by
  intro n Γ
  induction Γ with
  | nil => intro _ _ i; exact i.elim0
  | snoc Γ A ih =>
      intro chosen u i inside
      cases i using Fin.cases with
      | zero =>
          simp only [lowerSet, Ctx.lookup_snoc_zero, inside, if_true]
          rfl
      | succ i =>
          simp only [lowerSet, Ctx.lookup_snoc_succ]
          rw [ih (fun j => chosen j.succ) u i inside]
          rfl

theorem lookup_lowerSet_out : ∀ {n : Nat} (Γ : Ctx Head n) (chosen : Fin n → Bool) (u : Head) (i : Fin n),
    chosen i = false → Ctx.lookup (lowerSet Γ chosen u) i = Ctx.lookup Γ i := by
  intro n Γ
  induction Γ with
  | nil => intro _ _ i; exact i.elim0
  | snoc Γ A ih =>
      intro chosen u i outside
      cases i using Fin.cases with
      | zero => simp only [lowerSet, Ctx.lookup_snoc_zero, outside, Bool.false_eq_true, if_false]
      | succ i =>
          simp only [lowerSet, Ctx.lookup_snoc_succ]
          rw [ih (fun j => chosen j.succ) u i outside]

variable {R : Rules Head}

theorem lowerSet_narrows : ∀ {n : Nat} (Γ : Ctx Head n) (chosen : Fin n → Bool) {u : Head},
    (∀ i, chosen i = true → ∃ w, Ctx.lookup Γ i = .head w ∧ R.cumulative u w) →
    CtxNarrows R Γ (lowerSet Γ chosen u) := by
  intro n Γ
  induction Γ with
  | nil => intro _ _ _; exact .nil
  | snoc Γ A ih =>
      intro chosen u lowerable
      have inner := ih (fun i => chosen i.succ) (u := u) (fun i inside => by
        obtain ⟨w, hw, c⟩ := lowerable i.succ inside
        rw [Ctx.lookup_snoc_succ] at hw
        exact ⟨w, rename_wk_inj (hw.trans rfl), c⟩)
      simp only [lowerSet]
      split
      · rename_i inside
        obtain ⟨w, hw, c⟩ := lowerable 0 inside
        rw [Ctx.lookup_snoc_zero] at hw
        have same : A = .head w := rename_wk_inj (hw.trans rfl)
        subst same
        exact .lower inner c
      · exact .same A inner

end Lowering

section LoweringFormed

variable {S : Setting Head L}

theorem lowerSet_formed : ∀ {n : Nat} (Γ : Ctx Head n) (chosen : Fin n → Bool) {u : Head}, S.R.isUniverse u →
    CtxFormed S.R Γ → (∀ i, chosen i = true → ∃ w, Ctx.lookup Γ i = .head w ∧ S.R.cumulative u w) →
    CtxFormed S.R (lowerSet Γ chosen u) := by
  intro n Γ
  induction Γ with
  | nil => intro _ _ _ _ _; exact .nil
  | snoc Γ A ih =>
      intro chosen u hu formed lowerable
      cases formed with
      | snoc formedΓ typeA =>
          have lowerable' : ∀ i, chosen i.succ = true → ∃ w, Ctx.lookup Γ i = .head w ∧ S.R.cumulative u w := by
            intro i inside
            obtain ⟨w, hw, c⟩ := lowerable i.succ inside
            rw [Ctx.lookup_snoc_succ] at hw
            exact ⟨w, rename_wk_inj (hw.trans rfl), c⟩
          have inner := ih (fun i => chosen i.succ) hu formedΓ lowerable'
          simp only [lowerSet]
          split
          · exact inner.snoc (IsType.head_of_universe hu)
          · exact inner.snoc (isType_narrow (lowerSet_narrows Γ (fun i => chosen i.succ) lowerable') typeA)

end LoweringFormed

/-! ## Narrow and solve -/

section Rule

variable {S : Setting Head L}

/-- **A flex-rigid equation of a universe unknown and an arrow code**: `X ≐ t` at `U_v`, with `X : U_u`. -/
structure FlexArrow {Θ : Context S.R} (e : Equation (TotalTerm Θ)) where
  v : Head
  X : Fin Θ.arity
  u : Head
  annotation_left : e.1.1.code = .head v
  annotation_right : e.2.1.code = .head v
  side_left : e.1.2.code = .var X
  declared : Ctx.lookup Θ.raw X = .head u
  universe_u : S.R.isUniverse u
  universe_v : S.R.isUniverse v
  arrow : Arrow e.2.2.code

/-- Every declaration of the telescope is a universe. -/
def AllUniverseDecls (Θ : Context S.R) : Prop :=
  ∀ i : Fin Θ.arity, ∃ w, Ctx.lookup Θ.raw i = .head w ∧ S.R.isUniverse w

variable [DecidableRel S.R.cumulative]

/-- The unknowns of `t` declared at universes not below `u`. -/
def misfitSet {n : Nat} (Γ : Ctx Head n) (u : Head) (t : Tm Head n) : Fin n → Bool :=
  fun i => decide (i ∈ domainVars t) &&
    match declaredUniverse Γ i with
    | some w => !decide (S.R.cumulative w u)
    | none => false

theorem misfitSet_mem {n : Nat} {Γ : Ctx Head n} {u : Head} {t : Tm Head n} {i : Fin n}
    (h : misfitSet (S := S) Γ u t i = true) : i ∈ domainVars t := by
  unfold misfitSet at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem misfitSet_out {n : Nat} {Γ : Ctx Head n} {u : Head} {t : Tm Head n} {i : Fin n} {w : Head}
    (declared : Ctx.lookup Γ i = .head w) (h : misfitSet (S := S) Γ u t i = false) (member : i ∈ domainVars t) :
    S.R.cumulative w u := by
  unfold misfitSet declaredUniverse at h
  rw [declared] at h
  simp only [headOf, Bool.and_eq_false_iff, decide_eq_false_iff_not, Bool.not_eq_eq_eq_not, Bool.not_false,
    decide_eq_true_eq] at h
  rcases h with absent | below
  · exact absurd member absent
  · exact below

theorem misfitSet_in {n : Nat} {Γ : Ctx Head n} {u : Head} {t : Tm Head n} {i : Fin n} {w : Head}
    (declared : Ctx.lookup Γ i = .head w) (h : misfitSet (S := S) Γ u t i = true) : ¬ S.R.cumulative w u := by
  unfold misfitSet declaredUniverse at h
  rw [declared] at h
  simp only [headOf, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not] at h
  exact h.2

/-- **The conditions of narrow-and-solve** on a read equation: no occurrence of `X`, heads typed below `u`, and
every unknown of `t` declared at a universe comparable with `u`. -/
structure Solvable' {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexArrow e) : Prop where
  absent : v.X ∉ domainVars e.2.2.code
  heads : ∀ h ∈ arrowHeads e.2.2.code, ∃ k, S.R.headTyping h k ∧ S.R.cumulative k v.u
  universes : AllUniverseDecls Θ
  comparable : ∀ Y ∈ domainVars e.2.2.code, ∀ w, Ctx.lookup Θ.raw Y = .head w →
    S.R.cumulative w v.u ∨ S.R.cumulative v.u w

theorem Solvable'.lowerable {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {v : FlexArrow e} (ok : Solvable' v) :
    ∀ i, misfitSet (S := S) Θ.raw v.u e.2.2.code i = true → ∃ w, Ctx.lookup Θ.raw i = .head w ∧ S.R.cumulative v.u w := by
  intro i inside
  obtain ⟨w, hw, _⟩ := ok.universes i
  refine ⟨w, hw, ?_⟩
  rcases ok.comparable i (misfitSet_mem inside) w hw with below | above
  · exact absurd below (misfitSet_in hw inside)
  · exact above

/-- **The telescope with the misfit unknowns lowered to `U_u`.** -/
abbrev narrowed {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexArrow e) (ok : Solvable' v) : Context S.R where
  arity := Θ.arity
  raw := lowerSet Θ.raw (misfitSet (S := S) Θ.raw v.u e.2.2.code) v.u
  formed := lowerSet_formed Θ.raw _ v.universe_u Θ.formed ok.lowerable

theorem narrowed_narrows {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexArrow e) (ok : Solvable' v) :
    CtxNarrows S.R Θ.raw (narrowed v ok).raw :=
  lowerSet_narrows Θ.raw _ ok.lowerable

/-- **The right side is a type of `U_u` over the narrowed telescope.** -/
theorem narrowed_typed (algebra : CumulativeAlgebra S.R) {Θ : Context S.R} {e : Equation (TotalTerm Θ)}
    (v : FlexArrow e) (ok : Solvable' v) :
    Typed S.R (lowerSet Θ.raw (misfitSet (S := S) Θ.raw v.u e.2.2.code) v.u) e.2.2.code (.head v.u) := by
  refine arrow_typed algebra v.universe_u v.arrow (narrowed v ok).formed ?_ ok.heads
  intro Y member
  cases inside : misfitSet (S := S) Θ.raw v.u e.2.2.code Y with
  | true => exact ⟨v.u, lookup_lowerSet_in Θ.raw _ v.u Y inside, S.levels.cumulative_refl v.universe_u⟩
  | false =>
      obtain ⟨w, hw, _⟩ := ok.universes Y
      exact ⟨w, (lookup_lowerSet_out Θ.raw _ v.u Y inside).trans hw, misfitSet_out hw inside member⟩

/-- **`X := t` is a typed substitution from the narrowed telescope.** -/
theorem narrowSolve_typed (algebra : CumulativeAlgebra S.R) {Θ : Context S.R} {e : Equation (TotalTerm Θ)}
    (v : FlexArrow e) (ok : Solvable' v) :
    SubstMor S.R Θ.raw (lowerSet Θ.raw (misfitSet (S := S) Θ.raw v.u e.2.2.code) v.u)
      (solveSub v.X e.2.2.code) := by
  intro i
  obtain ⟨w, hw, _⟩ := ok.universes i
  rw [hw]
  change Typed S.R _ (solveSub v.X e.2.2.code i) (.head w)
  by_cases h : i = v.X
  · rw [h, solveSub_self]
    have same : w = v.u := by
      rw [h] at hw
      exact Tm.head.inj (hw.symm.trans v.declared)
    rw [same]
    exact narrowed_typed algebra v ok
  · rw [solveSub_ne _ h]
    have moved := (narrowed_narrows v ok).substMor i
    rw [subst_ids, hw] at moved
    exact moved

/-- **The answer `X := t`**, from the narrowed telescope. -/
def narrowSolve (algebra : CumulativeAlgebra S.R) {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexArrow e)
    (ok : Solvable' v) : narrowed v ok ⟶ Θ where
  substitution := solveSub v.X e.2.2.code
  typed := narrowSolve_typed algebra v ok

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

omit [DecidableRel S.R.cumulative] in
include facts roots heads algebra rigid complete in
/-- **What the equation forces of a misfit unknown**: every solution sends it to a type equal to a type of `U_u`. -/
theorem misfit_forced {Θ Δ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexArrow e) (σ : Δ ⟶ Θ)
    (solved : (frames S.levels).Solves σ e) {Y : Fin Θ.arity} (member : Y ∈ domainVars e.2.2.code) :
    ∃ small, Typed S.R Δ.raw small (.head v.u) ∧ TypeEq S.R Δ.raw small (σ.substitution Y) := by
  have equal := ((equivalent_iff S.levels _ _).mp solved).2
  change Equal S.R Δ.raw (Presentation.subst σ.substitution e.1.2.code)
    (Presentation.subst σ.substitution e.2.2.code) (Presentation.subst σ.substitution e.1.1.code) at equal
  rw [v.side_left, v.annotation_left] at equal
  have tX : Typed S.R Δ.raw (σ.substitution v.X) (.head v.u) := by
    have typed := σ.typed v.X
    rw [v.declared] at typed
    exact typed
  exact HoldsVar.small facts roots heads algebra rigid complete (holdsVar_of_mem member) Δ.formed v.universe_u
    σ.substitution tX ⟨v.v, v.universe_v, equal⟩

/-- **Narrow and solve**: the misfit unknowns declared again at `U_u`, and `X := t`; the solved equation is removed and
the rest of the store is instantiated. -/
def narrowSolveUpdate {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexArrow e) (ok : Solvable' v)
    (rest : EquationStore (TotalTerm Θ)) : Update S.levels (e :: rest) where
  target := narrowed v ok
  answer := narrowSolve algebra v ok
  remaining := (frames S.levels).applyStore (narrowSolve algebra v ok) rest
  sound := by
    intro Δ g solved e' member
    rcases List.mem_cons.mp member with rfl | member
    · apply e_of_codes
      · change Presentation.subst (subComp g.substitution (solveSub v.X e'.2.2.code)) e'.1.1.code =
          Presentation.subst (subComp g.substitution (solveSub v.X e'.2.2.code)) e'.2.1.code
        rw [v.annotation_left, v.annotation_right]
      · change Presentation.subst (subComp g.substitution (solveSub v.X e'.2.2.code)) e'.1.2.code =
          Presentation.subst (subComp g.substitution (solveSub v.X e'.2.2.code)) e'.2.2.code
        have fixed : Presentation.subst (subComp g.substitution (solveSub v.X e'.2.2.code)) e'.2.2.code =
            Presentation.subst g.substitution e'.2.2.code := by
          change Presentation.subst (fun i => Presentation.subst g.substitution (solveSub v.X e'.2.2.code i))
            e'.2.2.code = _
          rw [← subst_comp, subst_solveSub_fixed _ v.arrow ok.absent]
        rw [fixed, v.side_left]
        change Presentation.subst g.substitution (solveSub v.X e'.2.2.code v.X) = _
        rw [solveSub_self]
    · exact (Frames.models_applyStore (X := frames S.levels) _ g rest).mp solved e' member
  complete := by
    intro Δ f solved
    have equation := solved e List.mem_cons_self
    let chosen := misfitSet (S := S) Θ.raw v.u e.2.2.code
    have smallOf : ∀ i, chosen i = true →
        ∃ small, Typed S.R Δ.raw small (.head v.u) ∧ TypeEq S.R Δ.raw small (f.substitution i) :=
      fun i inside => misfit_forced facts roots heads algebra rigid complete v f equation (misfitSet_mem inside)
    let value : Sub Head Θ.arity Δ.arity := fun i =>
      if inside : chosen i = true then Classical.choose (smallOf i inside) else f.substitution i
    have valueIn : ∀ i (inside : chosen i = true), value i = Classical.choose (smallOf i inside) :=
      fun i inside => dif_pos inside
    have valueOut : ∀ i, chosen i = false → value i = f.substitution i := by
      intro i outside
      have notIn : ¬ chosen i = true := by rw [outside]; decide
      exact dif_neg notIn
    -- The value agrees with the solution.
    have same : SubstEq S.R Θ.raw Δ.raw f.substitution value := by
      refine ⟨f.typed, fun i => ?_⟩
      obtain ⟨w, hw, huw⟩ := ok.universes i
      rw [hw]
      cases inside : chosen i with
      | true =>
          rw [valueIn i inside]
          obtain ⟨tSmall, eSmall⟩ := Classical.choose_spec (smallOf i inside)
          have tF : Typed S.R Δ.raw (f.substitution i) (.head w) := by
            have typed := f.typed i
            rw [hw] at typed
            exact typed
          obtain ⟨w', hw', c⟩ := ok.lowerable i inside
          have sameW : w' = w := Tm.head.inj (hw'.symm.trans hw)
          rw [sameW] at c
          obtain ⟨x, hx, eX⟩ := eSmall
          exact .symm (universe_injective facts roots heads algebra rigid complete Δ.formed huw hx
            (Derivable.cumul tSmall c) tF eX)
      | false =>
          rw [valueOut i inside]
          have tF := f.typed i
          rw [hw] at tF
          exact .refl tF
    -- The value is a solution over the narrowed telescope.
    have typed : SubstMor S.R (lowerSet Θ.raw chosen v.u) Δ.raw value := by
      intro i
      cases inside : chosen i with
      | true =>
          rw [lookup_lowerSet_in Θ.raw chosen v.u i inside, valueIn i inside]
          exact (Classical.choose_spec (smallOf i inside)).1
      | false =>
          rw [lookup_lowerSet_out Θ.raw chosen v.u i inside, valueOut i inside]
          obtain ⟨w, hw, _⟩ := ok.universes i
          have tF := f.typed i
          rw [hw] at tF ⊢
          exact tF
    let g : Δ ⟶ narrowed v ok := ⟨value, typed⟩
    -- The solution factors through the answer.
    have factored : homTypedEquality S.R f (g ≫ narrowSolve algebra v ok) := by
      refine ⟨f.typed, fun i => ?_⟩
      change Equal S.R Δ.raw (f.substitution i) (Presentation.subst value (solveSub v.X e.2.2.code i))
        (Presentation.subst f.substitution (Ctx.lookup Θ.raw i))
      by_cases h : i = v.X
      · rw [h, solveSub_self, v.declared]
        have eq := ((equivalent_iff S.levels _ _).mp equation).2
        change Equal S.R Δ.raw (Presentation.subst f.substitution e.1.2.code)
          (Presentation.subst f.substitution e.2.2.code) (Presentation.subst f.substitution e.1.1.code) at eq
        rw [v.side_left, v.annotation_left] at eq
        have tRight : Typed S.R Θ.raw e.2.2.code (.head v.v) := by
          have typed := e.2.2.typed
          rw [v.annotation_right] at typed
          exact typed
        have functional := Typed.functional tRight same
        have atV : Equal S.R Δ.raw (f.substitution v.X) (Presentation.subst value e.2.2.code) (.head v.v) :=
          eq.trans functional
        have tX : Typed S.R Δ.raw (f.substitution v.X) (.head v.u) := by
          have t := f.typed v.X
          rw [v.declared] at t
          exact t
        have tValue : Typed S.R Δ.raw (Presentation.subst value e.2.2.code) (.head v.u) := by
          have moved := (narrowed_typed algebra v ok).substitute typed
          exact moved
        exact universe_injective facts roots heads algebra rigid complete Δ.formed v.universe_u v.universe_v
          tX tValue atV
      · rw [solveSub_ne _ h]
        exact same.2 i
    refine ⟨g, ?_, act_equal_of_substEq S.levels factored⟩
    apply (Frames.models_applyStore (X := frames S.levels) _ g rest).mpr
    exact (Elimination.models_pointwise S.levels (act_equal_of_substEq S.levels factored) rest).mp
      (fun e' member => solved e' (List.mem_cons_of_mem _ member))

include facts roots heads algebra rigid complete in
/-- **Narrow and solve is exact.** -/
theorem narrowSolve_exact {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexArrow e) (ok : Solvable' v)
    (rest : EquationStore (TotalTerm Θ)) :
    Exact (frames S.levels) (e :: rest) (narrowSolve algebra v ok)
      ((frames S.levels).applyStore (narrowSolve algebra v ok) rest) :=
  (DependentFibre.exact_iff_update (levels := S.levels) _ _).mpr
    ⟨narrowSolveUpdate facts roots heads algebra rigid complete v ok rest, rfl, rfl, rfl⟩

end Rule

/-! ## The two refutations -/

section Refutations

variable {S : Setting Head L}
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra rigid complete in
/-- **An occurrence of `X` along the domains of `t` refutes** `X ≐ t`. -/
theorem occurs_refutes {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexArrow e)
    (member : v.X ∈ domainVars e.2.2.code) (ne : e.2.2.code ≠ .var v.X) (rest : EquationStore (TotalTerm Θ)) :
    ¬ (frames S.levels).Solvable (e :: rest) := by
  rintro ⟨Δ, σ, models⟩
  have occurrence := arrow_domainOccurrence v.arrow member ne
  rw [← v.side_left] at occurrence
  exact ContextualDependentOccursCheck.OccursShape.refutes facts roots heads algebra rigid complete
    ⟨v.v, v.universe_v, v.annotation_left, v.annotation_right, occurrence⟩ σ (models e List.mem_cons_self)

include facts roots heads algebra rigid complete in
/-- **A misfit head refutes** `X ≐ t`. -/
theorem misfit_refutes {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexArrow e) {h₀ : Head}
    (member : h₀ ∈ arrowHeads e.2.2.code) (apart : ∀ k, S.R.headTyping h₀ k → ¬ S.R.cumulative k v.u)
    (rest : EquationStore (TotalTerm Θ)) : ¬ (frames S.levels).Solvable (e :: rest) := by
  rintro ⟨Δ, σ, models⟩
  have equal := ((equivalent_iff S.levels _ _).mp (models e List.mem_cons_self)).2
  change Equal S.R Δ.raw (Presentation.subst σ.substitution e.1.2.code)
    (Presentation.subst σ.substitution e.2.2.code) (Presentation.subst σ.substitution e.1.1.code) at equal
  rw [v.side_left, v.annotation_left] at equal
  have tX : Typed S.R Δ.raw (σ.substitution v.X) (.head v.u) := by
    have typed := σ.typed v.X
    rw [v.declared] at typed
    exact typed
  exact arrow_misfit facts roots heads algebra rigid complete v.universe_u apart v.arrow member Δ.formed
    σ.substitution tX ⟨v.v, v.universe_v, equal⟩

end Refutations

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
