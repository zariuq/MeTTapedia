import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.Trimming
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.GlbGroups

/-!
# Initial solutions on the fragment of glb groups

Every solved run of the solver of glb groups ends with an answer the trimming theorem applies to: deleting the
solved unknowns gives the initial solution (`glbGroup_solved_initial`).

* **In place** (`InPlaceData`): the driver's state keeps the arity of the original telescope; its answer mentions
  only unknowns it fixes; each fixed unknown keeps its domains, at a codomain below its original declaration; the
  remaining equations mention only fixed unknowns.
* **One step** (`InPlaceData.step`): composing with a step that is the identity on the unknowns but one solved
  unknown `G`, sent to `λ x. F x` with `F` fixed, keeps the shape, when the step lowers declarations only and its
  remaining equations avoid `G`.
* **The rules are such steps** (`glbGroupRound_inPlace`): delete, domain raising, the true meet and the
  greatest-lower-bound rule, in either orientation; **the driver keeps the shape** (`drive_inPlace`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist

variable {Head L : Type} [UniverseLevel.LevelOrder L]

/-! ## Two facts of syntax -/

section Syntax

theorem mem_support_etaExp_one {n : Nat} {x j : Fin n} (h : j ∈ (etaExp 1 (.var x) : Tm Head n).support) :
    j = x := by
  change j ∈ (Tm.lam (.app (.var x.succ) (.var 0)) : Tm Head n).support at h
  simp only [Tm.support, mem_outerSupport, Finset.mem_union, Finset.mem_singleton] at h
  rcases h with h | h
  · exact Fin.succ_injective _ h
  · exact absurd h (Fin.succ_ne_zero j)

theorem subst_eq_var {n m : Nat} {s : Sub Head n m} {t : Tm Head n} {j : Fin m}
    (h : Presentation.subst s t = .var j) : ∃ k, t = .var k ∧ s k = .var j := by
  cases t with
  | var k => exact ⟨k, rfl, h⟩
  | const _ => cases h
  | head _ => cases h
  | pi _ _ => cases h
  | sigma _ _ => cases h
  | id _ _ _ => cases h
  | lam _ => cases h
  | app _ _ => cases h
  | pair _ _ => cases h
  | fst _ => cases h
  | snd _ => cases h
  | refl _ => cases h

theorem etaExp_ne_var {n : Nat} (x j : Fin n) : (etaExp 1 (.var x) : Tm Head n) ≠ .var j := by
  intro h
  cases h

end Syntax

/-! ## The shape of in-place answers -/

section Shape

variable {S : Setting Head L}

/-- **In place**: the answer keeps the arity, mentions only unknowns it fixes, each fixed unknown keeps its domains
below its original declaration, and the remaining equations mention only fixed unknowns. -/
structure InPlaceData {Γ Θ : Context S.R} (σ : Θ ⟶ Γ) (remaining : EquationStore (TotalTerm Θ)) : Prop where
  same : Θ.arity = Γ.arity
  families : ∀ j : Fin Θ.arity, ∃ (ps : List Head) (c : Head),
    Ctx.lookup Θ.raw j = famCode ps c ∧ AllUniverses S.R ps ∧ S.R.isUniverse c
  fixedSupport : ∀ (i : Fin Γ.arity) (j : Fin Θ.arity), j ∈ (σ.substitution i).support →
    σ.substitution (Fin.cast same j) = .var j
  lowered : ∀ j : Fin Θ.arity, σ.substitution (Fin.cast same j) = .var j →
    ∃ (ps : List Head) (c c' : Head), Ctx.lookup Θ.raw j = famCode ps c ∧
      Ctx.lookup Γ.raw (Fin.cast same j) = famCode ps c' ∧ S.R.isUniverse c' ∧ S.R.cumulative c c'
  remaining : ∀ e ∈ remaining, ∀ v : FitFlex e,
    σ.substitution (Fin.cast same v.left) = .var v.left ∧ σ.substitution (Fin.cast same v.right) = .var v.right

/-- **The start of a run is in place.** -/
theorem InPlaceData.pending {Γ : Context S.R} (problem : EquationStore (TotalTerm Γ))
    (families : ∀ j : Fin Γ.arity, ∃ (ps : List Head) (c : Head),
      Ctx.lookup Γ.raw j = famCode ps c ∧ AllUniverses S.R ps ∧ S.R.isUniverse c) :
    InPlaceData (𝟙 Γ) problem where
  same := rfl
  families := families
  fixedSupport := by
    intro i j member
    change j ∈ (Tm.var i : Tm Head Γ.arity).support at member
    simp only [Tm.support, Finset.mem_singleton] at member
    subst member
    rfl
  lowered := by
    intro j _
    obtain ⟨ps, c, d, _, uc⟩ := families j
    exact ⟨ps, c, c, d, d, uc, S.levels.cumulative_refl uc⟩
  remaining := fun _ _ _ => ⟨rfl, rfl⟩

/-- **One in-place step**: the identity on the unknowns but possibly one `G`, sent to `λ x. F x` with `F` fixed; the
step's telescope lowers codomains only; its remaining equations avoid `G` and mention only fixed unknowns. -/
theorem InPlaceData.step {Γ Θ Θ' : Context S.R} {σ : Θ ⟶ Γ} {R : EquationStore (TotalTerm Θ)}
    (inv : InPlaceData σ R) (trans : ∀ {u v w : Head}, S.R.cumulative u v → S.R.cumulative v w → S.R.cumulative u w)
    (τ : Θ' ⟶ Θ) (sameU : Θ'.arity = Θ.arity) (R' : EquationStore (TotalTerm Θ'))
    (G : Option (Fin Θ.arity)) (F : Fin Θ.arity)
    (sub : ∀ k : Fin Θ.arity,
      (G = some k ∧ F ≠ k ∧ σ.substitution (Fin.cast inv.same F) = .var F ∧
        τ.substitution k = etaExp 1 (.var (Fin.cast sameU.symm F))) ∨
      (G ≠ some k ∧ τ.substitution k = .var (Fin.cast sameU.symm k)))
    (decl : ∀ k : Fin Θ'.arity, ∃ (ps : List Head) (c c₀ : Head), Ctx.lookup Θ'.raw k = famCode ps c ∧
      Ctx.lookup Θ.raw (Fin.cast sameU k) = famCode ps c₀ ∧ AllUniverses S.R ps ∧ S.R.isUniverse c ∧
      S.R.cumulative c c₀)
    (rem : ∀ e ∈ R', ∀ v : FitFlex e,
      (G ≠ some (Fin.cast sameU v.left) ∧
        σ.substitution (Fin.cast inv.same (Fin.cast sameU v.left)) = .var (Fin.cast sameU v.left)) ∧
      (G ≠ some (Fin.cast sameU v.right) ∧
        σ.substitution (Fin.cast inv.same (Fin.cast sameU v.right)) = .var (Fin.cast sameU v.right))) :
    InPlaceData (τ ≫ σ) R' := by
  refine ⟨sameU.trans inv.same, ?_, ?_, ?_, ?_⟩
  · intro k
    obtain ⟨ps, c, _, dk, _, ups, uc, _⟩ := decl k
    exact ⟨ps, c, dk, ups, uc⟩
  · intro i j member
    change j ∈ (Presentation.subst τ.substitution (σ.substitution i)).support at member
    obtain ⟨k, hk, hj⟩ := Miller.support_subst_sub _ τ.substitution member
    have fixedK := inv.fixedSupport i k hk
    change Presentation.subst τ.substitution (σ.substitution (Fin.cast (sameU.trans inv.same) j)) = .var j
    rcases sub k with ⟨hG, hFk, fixedF, hτ⟩ | ⟨_, hτ⟩
    · rw [hτ] at hj
      have jF := mem_support_etaExp_one hj
      have castEq : Fin.cast (sameU.trans inv.same) j = Fin.cast inv.same F := by
        rw [jF]
        exact Fin.ext rfl
      rw [castEq, fixedF]
      change τ.substitution F = .var j
      rcases sub F with ⟨hG', _, _, _⟩ | ⟨_, hτF⟩
      · exact absurd (Option.some.inj (hG.symm.trans hG')) (fun same => hFk same.symm)
      · rw [hτF, jF]
    · rw [hτ] at hj
      have jk : j = Fin.cast sameU.symm k := by
        simpa only [Tm.support, Finset.mem_singleton] using hj
      have castEq : Fin.cast (sameU.trans inv.same) j = Fin.cast inv.same k := by
        rw [jk]
        exact Fin.ext rfl
      rw [castEq, fixedK]
      change τ.substitution k = .var j
      rw [hτ, jk]
  · intro j fixed
    change Presentation.subst τ.substitution (σ.substitution (Fin.cast (sameU.trans inv.same) j)) = .var j at fixed
    obtain ⟨k', hk', hτk'⟩ := subst_eq_var fixed
    rcases sub k' with ⟨_, _, _, hτ⟩ | ⟨_, hτ⟩
    · rw [hτ] at hτk'
      exact absurd hτk' (etaExp_ne_var _ _)
    · rw [hτ] at hτk'
      have jk : Fin.cast sameU.symm k' = j := Tm.var.inj hτk'
      have k'eq : k' = Fin.cast sameU j := by
        rw [← jk]
        exact Fin.ext rfl
      have castEq : Fin.cast (sameU.trans inv.same) j = Fin.cast inv.same k' := by
        rw [k'eq]
        exact Fin.ext rfl
      rw [castEq] at hk'
      obtain ⟨ps, c, c', dΘ, dΓ, uc', le⟩ := inv.lowered k' hk'
      obtain ⟨ps₂, c₂, c₀, d₂, d₀, _, _, le₂⟩ := decl j
      rw [← k'eq] at d₀
      obtain ⟨hps, hc⟩ := famCode_inj (d₀.symm.trans dΘ)
      rw [hc] at le₂
      refine ⟨ps₂, c₂, c', d₂, ?_, uc', trans le₂ le⟩
      rw [castEq, hps]
      exact dΓ
  · intro e member v
    obtain ⟨⟨hGl, fixedL⟩, ⟨hGr, fixedR⟩⟩ := rem e member v
    constructor
    · change Presentation.subst τ.substitution (σ.substitution (Fin.cast (sameU.trans inv.same) v.left)) =
        .var v.left
      have castEq : Fin.cast (sameU.trans inv.same) v.left = Fin.cast inv.same (Fin.cast sameU v.left) :=
        Fin.ext rfl
      rw [castEq, fixedL]
      change τ.substitution (Fin.cast sameU v.left) = .var v.left
      rcases sub (Fin.cast sameU v.left) with ⟨hG, _⟩ | ⟨_, hτ⟩
      · exact absurd hG hGl
      · rw [hτ]
        exact congrArg Tm.var (Fin.ext rfl)
    · change Presentation.subst τ.substitution (σ.substitution (Fin.cast (sameU.trans inv.same) v.right)) =
        .var v.right
      have castEq : Fin.cast (sameU.trans inv.same) v.right = Fin.cast inv.same (Fin.cast sameU v.right) :=
        Fin.ext rfl
      rw [castEq, fixedR]
      change τ.substitution (Fin.cast sameU v.right) = .var v.right
      rcases sub (Fin.cast sameU v.right) with ⟨hG, _⟩ | ⟨_, hτ⟩
      · exact absurd hG hGr
      · rw [hτ]
        exact congrArg Tm.var (Fin.ext rfl)

end Shape

/-! ## The rules of glb groups are in-place steps -/

section Rules

variable {S : Setting Head L} [DecidableEq Head] [DecidableRel S.R.cumulative] (algebra : CumulativeAlgebra S.R)

/-- **Domain raising avoids the solved unknown**: after `G := λ x. F x` and re-reading, every unknown of the remaining
equations is `F` or an unknown of the equations before, other than `G`. -/
theorem contract_avoids {Θ : Context S.R} {e₀ : Equation (TotalTerm Θ)} (fits : FitsView e₀) (all : AllFamilies Θ)
    (R₁ : EquationStore (TotalTerm Θ)) (fixed : Fin Θ.arity → Prop) (fixedF : fixed fits.F) (FG : fits.F ≠ fits.G)
    (shapes₁ : ∀ e₁ ∈ R₁, Nonempty (FitFlex e₁)) (h₁ : ∀ e₁ ∈ R₁, ∀ w : FitFlex e₁, fixed w.left ∧ fixed w.right) :
    ∀ e ∈ contractStore algebra fits all R₁, ∀ u : FitFlex e,
      (u.left ≠ fits.G ∧ fixed u.left) ∧ (u.right ≠ fits.G ∧ fixed u.right) := by
  intro e member u
  obtain ⟨e₁, inR, rfl⟩ := List.mem_map.mp member
  obtain ⟨w⟩ := shapes₁ e₁ inR
  obtain ⟨t, tl, tr⟩ := contract_view algebra fits all w
  obtain ⟨ul, ur⟩ := FitFlex.unique u t
  have side : ∀ X : Fin Θ.arity, fixed X → raiseVar fits.F fits.G X ≠ fits.G ∧ fixed (raiseVar fits.F fits.G X) := by
    intro X fx
    unfold raiseVar
    split_ifs with h
    · exact ⟨FG, fixedF⟩
    · exact ⟨h, fx⟩
  obtain ⟨fl, fr⟩ := h₁ e₁ inR w
  rw [ul, ur, tl, tr]
  exact ⟨side _ fl, side _ fr⟩

omit [DecidableEq Head] [DecidableRel S.R.cumulative] in
include algebra in
/-- **A lowering keeps the unknowns of every equation.** -/
theorem lowering_keeps {Θ : Context S.R} (ℓ : CodomainLowering Θ) (R₁ : EquationStore (TotalTerm Θ))
    (fixed : Fin Θ.arity → Prop) (shapes₁ : ∀ e₁ ∈ R₁, Nonempty (FitFlex e₁))
    (h₁ : ∀ e₁ ∈ R₁, ∀ w : FitFlex e₁, fixed w.left ∧ fixed w.right) :
    (∀ e ∈ (frames S.levels).applyStore ℓ.hom R₁, Nonempty (FitFlex e)) ∧
      (∀ e ∈ (frames S.levels).applyStore ℓ.hom R₁, ∀ u : FitFlex e, fixed u.left ∧ fixed u.right) := by
  constructor
  · intro e member
    obtain ⟨e₁, inR, rfl⟩ := List.mem_map.mp member
    obtain ⟨w⟩ := shapes₁ e₁ inR
    obtain ⟨t, _, _⟩ := lowering_view algebra ℓ w
    exact ⟨t⟩
  · intro e member u
    obtain ⟨e₁, inR, rfl⟩ := List.mem_map.mp member
    obtain ⟨w⟩ := shapes₁ e₁ inR
    obtain ⟨t, tl, tr⟩ := lowering_view algebra ℓ w
    obtain ⟨ul, ur⟩ := FitFlex.unique u t
    rw [ul, ur, tl, tr]
    exact h₁ e₁ inR w

omit [DecidableEq Head] [DecidableRel S.R.cumulative] in
include algebra in
/-- **The true meet's lowering keeps the unknowns of every equation.** -/
theorem meetLowering_keeps {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FitFlex e) (meets : Meets v)
    (R₁ : EquationStore (TotalTerm Θ)) (fixed : Fin Θ.arity → Prop) (shapes₁ : ∀ e₁ ∈ R₁, Nonempty (FitFlex e₁))
    (h₁ : ∀ e₁ ∈ R₁, ∀ w : FitFlex e₁, fixed w.left ∧ fixed w.right) :
    (∀ e' ∈ (frames S.levels).applyStore (lowerHom Θ v meets) R₁, Nonempty (FitFlex e')) ∧
      (∀ e' ∈ (frames S.levels).applyStore (lowerHom Θ v meets) R₁, ∀ u : FitFlex e', fixed u.left ∧ fixed u.right) := by
  constructor
  · intro e' member
    obtain ⟨e₁, inR, rfl⟩ := List.mem_map.mp member
    obtain ⟨w⟩ := shapes₁ e₁ inR
    obtain ⟨t, _, _⟩ := lower_view algebra v meets w
    exact ⟨t⟩
  · intro e' member u
    obtain ⟨e₁, inR, rfl⟩ := List.mem_map.mp member
    obtain ⟨w⟩ := shapes₁ e₁ inR
    obtain ⟨t, tl, tr⟩ := lower_view algebra v meets w
    obtain ⟨ul, ur⟩ := FitFlex.unique u t
    rw [ul, ur, tl, tr]
    exact h₁ e₁ inR w

end Rules

/-! ## The round and the driver keep the shape -/

section Round

variable {S : Setting Head L}
variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (glb : Head → Head → Option Head) (spec : ∀ {a b g : Head}, glb a b = some g → IsGlb S.R g a b)

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative] in
/-- Declarations of the same telescope, lowered by nothing. -/
theorem decl_same {Γ Θ : Context S.R} {σ : Θ ⟶ Γ} {R : EquationStore (TotalTerm Θ)} (inv : InPlaceData σ R) :
    ∀ k : Fin Θ.arity, ∃ (ps : List Head) (c c₀ : Head), Ctx.lookup Θ.raw k = famCode ps c ∧
      Ctx.lookup Θ.raw (Fin.cast rfl k) = famCode ps c₀ ∧ AllUniverses S.R ps ∧ S.R.isUniverse c ∧
      S.R.cumulative c c₀ := by
  intro k
  obtain ⟨ps, c, d, ups, uc⟩ := inv.families k
  exact ⟨ps, c, c, d, d, ups, uc, S.levels.cumulative_refl uc⟩

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative] in
/-- The substitution of domain raising, as an in-place step. -/
theorem sub_raise {Γ Θ : Context S.R} {σ : Θ ⟶ Γ} {R : EquationStore (TotalTerm Θ)} (inv : InPlaceData σ R)
    (F G : Fin Θ.arity) (FG : F ≠ G) (fixedF : σ.substitution (Fin.cast inv.same F) = .var F) :
    ∀ k : Fin Θ.arity,
      (some G = some k ∧ F ≠ k ∧ σ.substitution (Fin.cast inv.same F) = .var F ∧
        raiseSub (Head := Head) F G k = etaExp 1 (.var (Fin.cast (rfl : Θ.arity = Θ.arity).symm F))) ∨
      (some G ≠ some k ∧ raiseSub (Head := Head) F G k = .var (Fin.cast (rfl : Θ.arity = Θ.arity).symm k)) := by
  intro k
  by_cases hk : k = G
  · subst hk
    exact Or.inl ⟨rfl, FG, fixedF, raiseSub_self F k⟩
  · exact Or.inr ⟨fun h => hk (Option.some.inj h).symm, raiseSub_ne F G hk⟩

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative] in
/-- Declarations after the true meet's lowering. -/
theorem decl_meet {Γ Θ : Context S.R} {σ : Θ ⟶ Γ} {R : EquationStore (TotalTerm Θ)} (inv : InPlaceData σ R)
    {e : Equation (TotalTerm Θ)} (v : FitFlex e) (meets : Meets v) :
    ∀ k : Fin (lowered Θ v meets).arity, ∃ (ps : List Head) (c c₀ : Head),
      Ctx.lookup (lowered Θ v meets).raw k = famCode ps c ∧
      Ctx.lookup Θ.raw (Fin.cast (rfl : (lowered Θ v meets).arity = Θ.arity) k) = famCode ps c₀ ∧
      AllUniverses S.R ps ∧ S.R.isUniverse c ∧ S.R.cumulative c c₀ := by
  intro k
  by_cases hr : k = v.right
  · subst hr
    exact ⟨[v.pr], v.cl, v.cr, lowered_self Θ v meets, v.declared_right,
      fun _ member => (List.mem_singleton.mp member) ▸ v.universe_pr, v.universe_cl, meets.2.1⟩
  · obtain ⟨ps, c, d, ups, uc⟩ := inv.families k
    exact ⟨ps, c, c, (lowered_ne Θ v meets hr).trans d, d, ups, uc, S.levels.cumulative_refl uc⟩

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative] in
/-- Declarations after the greatest-lower-bound rule's two lowerings. -/
theorem decl_glb {Γ Θ : Context S.R} {σ : Θ ⟶ Γ} {R : EquationStore (TotalTerm Θ)} (inv : InPlaceData σ R)
    {e : Equation (TotalTerm Θ)} (v : FitFlex e) {g : Head} (glbm : GlbMeets v g) (distinct : v.right ≠ v.left) :
    ∀ k : Fin (glbLowerRight v glbm distinct).target.arity, ∃ (ps : List Head) (c c₀ : Head),
      Ctx.lookup (glbLowerRight v glbm distinct).target.raw k = famCode ps c ∧
      Ctx.lookup Θ.raw (Fin.cast (rfl : (glbLowerRight v glbm distinct).target.arity = Θ.arity) k) =
        famCode ps c₀ ∧ AllUniverses S.R ps ∧ S.R.isUniverse c ∧ S.R.cumulative c c₀ := by
  intro k
  by_cases hr : k = v.right
  · subst hr
    exact ⟨[v.pr], g, v.cr, (glbLowerRight v glbm distinct).lookup_self, v.declared_right,
      fun _ member => (List.mem_singleton.mp member) ▸ v.universe_pr, glbm.1.1, glbm.1.2.2.1⟩
  · by_cases hl : k = v.left
    · subst hl
      exact ⟨[v.pl], g, v.cl,
        ((glbLowerRight v glbm distinct).lookup_ne hr).trans (glbLowerLeft v glbm).lookup_self, v.declared_left,
        fun _ member => (List.mem_singleton.mp member) ▸ v.universe_pl, glbm.1.1, glbm.1.2.1⟩
    · obtain ⟨ps, c, d, ups, uc⟩ := inv.families k
      exact ⟨ps, c, c,
        ((glbLowerRight v glbm distinct).lookup_ne hr).trans (((glbLowerLeft v glbm).lookup_ne hl).trans d), d,
        ups, uc, S.levels.cumulative_refl uc⟩

/-- **Every progress of the round is an in-place step.** -/
theorem glbGroupRound_inPlace {Γ Θ : Context S.R} {σ : Θ ⟶ Γ} {problem : EquationStore (TotalTerm Θ)}
    {update : Update S.levels problem}
    {smaller : ContextualDependentWorklist.Below (storeRank update.remaining) (storeRank problem)}
    (inv : InPlaceData σ problem) (inside : InGlbFragment problem)
    (progressed : glbGroupRound facts roots heads algebra rigid complete headTypingUnique glb spec problem =
      .progress update smaller) :
    InPlaceData (update.answer ≫ σ) update.remaining := by
  cases problem with
  | nil => cases progressed
  | cons e rest =>
      let fixed : Fin Θ.arity → Prop := fun X => σ.substitution (Fin.cast inv.same X) = .var X
      have restShapes : ∀ e' ∈ rest, Nonempty (FitFlex e') :=
        fun e' member => inside.shapes e' (List.mem_cons_of_mem _ member)
      have restFixed : ∀ e' ∈ rest, ∀ w : FitFlex e', fixed w.left ∧ fixed w.right :=
        fun e' member w => inv.remaining e' (List.mem_cons_of_mem _ member) w
      have avoid : ∀ (G : Fin Θ.arity) {Θ' : Context S.R} (sameU : Θ'.arity = Θ.arity)
          (R' : EquationStore (TotalTerm Θ')),
          (∀ e'' ∈ R', ∀ u : FitFlex e'', (Fin.cast sameU u.left ≠ G ∧ fixed (Fin.cast sameU u.left)) ∧
            (Fin.cast sameU u.right ≠ G ∧ fixed (Fin.cast sameU u.right))) →
          ∀ e'' ∈ R', ∀ u : FitFlex e'',
            (some G ≠ some (Fin.cast sameU u.left) ∧
              σ.substitution (Fin.cast inv.same (Fin.cast sameU u.left)) = .var (Fin.cast sameU u.left)) ∧
            (some G ≠ some (Fin.cast sameU u.right) ∧
              σ.substitution (Fin.cast inv.same (Fin.cast sameU u.right)) = .var (Fin.cast sameU u.right)) := by
        intro G Θ' sameU R' h e'' member u
        obtain ⟨⟨nl, fl⟩, ⟨nr, fr⟩⟩ := h e'' member u
        exact ⟨⟨fun same => nl (Option.some.inj same).symm, fl⟩, ⟨fun same => nr (Option.some.inj same).symm, fr⟩⟩
      simp only [glbGroupRound] at progressed
      split_ifs at progressed with hall
      split at progressed
      · rename_i d hd
        have fixedL : fixed (viewOfFit hd).left := (inv.remaining e List.mem_cons_self (viewOfFit hd)).1
        have fixedR : fixed (viewOfFit hd).right := (inv.remaining e List.mem_cons_self (viewOfFit hd)).2
        unfold stepGlbGroup at progressed
        split_ifs at progressed with h1 h2 h3 h4 h5
        · -- delete
          cases progressed
          refine inv.step algebra.trans _ ?_ _ none (viewOfFit hd).left ?_ ?_ ?_
          · rfl
          · intro k
            exact Or.inr ⟨fun h => (nomatch h), rfl⟩
          · exact decl_same inv
          · intro e' member w
            obtain ⟨l, r⟩ := restFixed e' member w
            exact ⟨⟨fun h => (nomatch h), l⟩, ⟨fun h => (nomatch h), r⟩⟩
        · -- raise `left := λ x. right x`
          cases progressed
          refine inv.step algebra.trans _ ?_ _ (some (viewOfFit hd).left) (viewOfFit hd).right ?_ ?_ ?_
          · rfl
          · exact sub_raise inv (viewOfFit hd).right (viewOfFit hd).left (fun h => h1 h.symm) fixedR
          · exact decl_same inv
          · exact avoid _ _ _ (contract_avoids algebra ((viewOfFit hd).toFits (fun h => h1 h.symm) h2)
              (allFamilies_of_B hall) rest fixed fixedR (fun h => h1 h.symm) restShapes restFixed)
        · -- raise `right := λ x. left x`
          cases progressed
          refine inv.step algebra.trans _ ?_ _ (some (viewOfFit hd).right) (viewOfFit hd).left ?_ ?_ ?_
          · rfl
          · exact sub_raise inv (viewOfFit hd).left (viewOfFit hd).right h1 fixedL
          · exact decl_same inv
          · exact avoid _ _ _ (contract_avoids algebra ((viewOfFit hd).swap.toFits h1 h3)
              (allFamilies_of_B hall) rest fixed fixedL h1 restShapes restFixed)
        · -- the true meet, `left := λ x. right x`
          cases progressed
          refine inv.step algebra.trans _ ?_ _ (some (viewOfFit hd).left) (viewOfFit hd).right ?_ ?_ ?_
          · rfl
          · exact sub_raise inv (viewOfFit hd).right (viewOfFit hd).left (fun h => h1 h.symm) fixedR
          · exact decl_meet inv (viewOfFit hd) h4
          · obtain ⟨s₁, f₁⟩ := meetLowering_keeps algebra (viewOfFit hd) h4 rest fixed restShapes restFixed
            exact avoid _ _ _ (contract_avoids algebra (meetFits (viewOfFit hd) h4 (fun h => h1 h.symm))
              (lowered_families (viewOfFit hd) h4 (allFamilies_of_B hall)) _ fixed fixedR (fun h => h1 h.symm) s₁ f₁)
        · -- the true meet, `right := λ x. left x`
          cases progressed
          refine inv.step algebra.trans _ ?_ _ (some (viewOfFit hd).right) (viewOfFit hd).left ?_ ?_ ?_
          · rfl
          · exact sub_raise inv (viewOfFit hd).left (viewOfFit hd).right h1 fixedL
          · exact decl_meet inv (viewOfFit hd).swap h5
          · obtain ⟨s₁, f₁⟩ := meetLowering_keeps algebra (viewOfFit hd).swap h5 rest fixed restShapes restFixed
            exact avoid _ _ _ (contract_avoids algebra (meetFits (viewOfFit hd).swap h5 h1)
              (lowered_families (viewOfFit hd).swap h5 (allFamilies_of_B hall)) _ fixed fixedL h1 s₁ f₁)
        · -- the greatest-lower-bound rule
          unfold glbBranch at progressed
          split at progressed
          · rename_i g hg
            split_ifs at progressed with hl hr
            · cases progressed
              refine inv.step algebra.trans _ ?_ _ (some (viewOfFit hd).left) (viewOfFit hd).right ?_ ?_ ?_
              · rfl
              · exact sub_raise inv (viewOfFit hd).right (viewOfFit hd).left (fun h => h1 h.symm) fixedR
              · exact decl_glb inv (viewOfFit hd) ⟨spec hg, hl.1, hl.2.1, hl.2.2⟩ (fun h => h1 h.symm)
              · obtain ⟨s₁, f₁⟩ := lowering_keeps algebra
                  (glbLowerLeft (viewOfFit hd) ⟨spec hg, hl.1, hl.2.1, hl.2.2⟩) rest fixed restShapes restFixed
                obtain ⟨s₂, f₂⟩ := lowering_keeps algebra
                  (glbLowerRight (viewOfFit hd) ⟨spec hg, hl.1, hl.2.1, hl.2.2⟩ (fun h => h1 h.symm)) _ fixed s₁ f₁
                exact avoid _ _ _ (contract_avoids algebra
                  (glbFits algebra (viewOfFit hd) ⟨spec hg, hl.1, hl.2.1, hl.2.2⟩ (fun h => h1 h.symm)) _ _ fixed
                  fixedR (fun h => h1 h.symm) s₂ f₂)
            · cases progressed
              refine inv.step algebra.trans _ ?_ _ (some (viewOfFit hd).right) (viewOfFit hd).left ?_ ?_ ?_
              · rfl
              · exact sub_raise inv (viewOfFit hd).left (viewOfFit hd).right h1 fixedL
              · exact decl_glb inv (viewOfFit hd).swap ⟨(spec hg).symm, hr.1, hr.2.1, hr.2.2⟩ h1
              · obtain ⟨s₁, f₁⟩ := lowering_keeps algebra
                  (glbLowerLeft (viewOfFit hd).swap ⟨(spec hg).symm, hr.1, hr.2.1, hr.2.2⟩) rest fixed restShapes
                  restFixed
                obtain ⟨s₂, f₂⟩ := lowering_keeps algebra
                  (glbLowerRight (viewOfFit hd).swap ⟨(spec hg).symm, hr.1, hr.2.1, hr.2.2⟩ h1) _ fixed s₁ f₁
                exact avoid _ _ _ (contract_avoids algebra
                  (glbFits algebra (viewOfFit hd).swap ⟨(spec hg).symm, hr.1, hr.2.1, hr.2.2⟩ h1) _ _ fixed
                  fixedL h1 s₂ f₂)
          · cases progressed
      · cases progressed

/-- **The driver keeps the shape** on the fragment of glb groups. -/
theorem drive_inPlace {Γ : Context S.R} {original : EquationStore (TotalTerm Γ)} (fuel : Nat) :
    ∀ (state : Update S.levels original), InPlaceData state.answer state.remaining →
      InGlbFragment state.remaining → ∀ (final : Update S.levels original) (finished : final.remaining = []),
        drive (glbGroupSolver facts roots heads algebra rigid complete headTypingUnique glb spec) fuel state =
          .solved final finished → InPlaceData final.answer final.remaining := by
  induction fuel with
  | zero =>
      intro state _ _ final finished h
      cases h
  | succ fuel ih =>
      intro state inv inside final finished h
      rw [drive] at h
      cases ha : advance (glbGroupSolver facts roots heads algebra rigid complete headTypingUnique glb spec) state with
      | done outcome =>
          simp only [ha] at h
          unfold advance at ha
          split at ha
          · cases ha
            cases h
            exact inv
          · split at ha
            · cases ha
            · cases ha
              cases h
            · cases ha
              cases h
      | next next =>
          simp only [ha] at h
          unfold advance at ha
          split at ha
          · cases ha
          · split at ha
            · rename_i update smaller hround
              cases ha
              have inv' := glbGroupRound_inPlace facts roots heads algebra rigid complete headTypingUnique glb spec inv
                inside hround
              have inside' := glbGroupRound_stable facts roots heads algebra rigid complete headTypingUnique glb spec
                inside hround
              exact ih (state.then update) inv' inside' final finished h
            · cases ha
            · cases ha

include facts roots heads algebra rigid complete headTypingUnique spec in
/-- **Every solved run of the solver of glb groups, trimmed, is the initial solution**: deleting the unknowns its
answer does not fix. -/
theorem glbGroup_solved_initial {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)}
    (inside : InGlbFragment original) (inh : Miller.Inhabitants S.R)
    (families : ∀ j : Fin Θ.arity, ∃ (ps : List Head) (c : Head), Ctx.lookup Θ.raw j = famCode ps c ∧
      AllUniverses S.R ps ∧ S.R.isUniverse c)
    {fuel : Nat} {state : Update S.levels original} {finished : state.remaining = []}
    (solved : run (glbGroupSolver facts roots heads algebra rigid complete headTypingUnique glb spec) original fuel =
      .solved state finished) :
    ∃ (Δ : Context S.R) (answer : Δ ⟶ Θ), InitialSolution (frames S.levels) original answer := by
  have shape := drive_inPlace facts roots heads algebra rigid complete headTypingUnique glb spec fuel
    (Update.pending S.levels original) (InPlaceData.pending original families) inside state finished solved
  choose ps c hd hu huc using shape.families
  refine ⟨_, _, initial_of_trimmed facts roots heads algebra rigid complete inh (state.completed finished) shape.same
    (fun j => (ps j, c j)) hd (fun j => ⟨hu j, huc j⟩) shape.fixedSupport ?_⟩
  intro j fixed
  obtain ⟨ps', c₁, c', d₁, dΓ, uc', le⟩ := shape.lowered j fixed
  obtain ⟨hps, hc⟩ := famCode_inj ((hd j).symm.trans d₁)
  refine ⟨c', ?_, uc', ?_⟩
  · rw [dΓ, ← hps]
  · rw [hc]
    exact le

include facts roots heads algebra rigid complete headTypingUnique spec in
/-- **On the fragment of glb groups, deleting the solved unknowns from the solver's answer gives the initial
solution.** -/
theorem glbGroup_initial {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)}
    (inside : InGlbFragment original) (inh : Miller.Inhabitants S.R)
    (families : ∀ j : Fin Θ.arity, ∃ (ps : List Head) (c : Head), Ctx.lookup Θ.raw j = famCode ps c ∧
      AllUniverses S.R ps ∧ S.R.isUniverse c)
    (total : ∀ {a b : Head}, S.R.isUniverse a → S.R.isUniverse b → ∃ g, glb a b = some g) :
    ∃ (Δ : Context S.R) (answer : Δ ⟶ Θ), InitialSolution (frames S.levels) original answer := by
  obtain ⟨fuel, ends⟩ := glbGroup_decided facts roots heads algebra rigid complete headTypingUnique glb spec total inside
  rcases (ends fuel le_rfl).2 with ⟨state, finished, solved, _⟩ | ⟨absent, refuted⟩
  · exact glbGroup_solved_initial facts roots heads algebra rigid complete headTypingUnique glb spec inside inh families
      solved
  · exact absurd refuted (drive_ne_refuted
      (glbGroupSolver facts roots heads algebra rigid complete headTypingUnique glb spec)
      (fun problem absent =>
        glbGroupRound_ne_refuted facts roots heads algebra rigid complete headTypingUnique glb spec problem absent)
      fuel _ absent)

end Round

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
