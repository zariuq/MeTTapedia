import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.WhenTypesApply.Ladder
import Mettapedia.GSLT.Logic.ImageFinitenessNecessary

/-!
# Groundable: least fixed points are found at a finite unfolding, greatest ones refuted at one

A fixed point is approached by its unfoldings: from below, `∅, F ∅, F (F ∅), …` (`lower`), and from
above, `univ, F univ, …` (`upper`). On every system each lower stage lies in the least fixed point
and each upper stage contains the greatest one (`lower_subset_lfp`, `gfp_subset_upper`), the lower
stages grow and the upper ones shrink (`lower_mono`, `upper_anti`).

**The budgeted check** (`check`, `Verdict`) has three outcomes, as the budgeted conversion check
does: a state found in the `k`-th lower stage is a **member**, a state outside the `k`-th upper stage
is a **nonmember**, and otherwise the budget ran out (**undecided**). Running out is its own outcome.

* **Sound in all three outcomes**: "member" means in the least fixed point (`check_member`),
  "nonmember" means outside the greatest (`check_nonmember`), and "undecided" holds exactly when
  neither stage decided (`check_undecided_iff`).
* **Monotone in the budget**: a decided verdict is the verdict of every larger budget (`check_mono`).
* **The gap is never decided**: a state in the greatest fixed point and not in the least one is
  undecided at every budget (`check_gap`).
* **Complete in the limit on image-finite systems** (`lfp_eq_iUnion_of_plain`,
  `gfp_eq_iInter_of_plain`): for a body without negation or fixed points (`plain`) on a system with
  finitely many successors under each label (`ImageFinite`), the least fixed point is the union of the
  lower stages and the greatest one the intersection of the upper stages, because such a body
  commutes with increasing unions and with decreasing intersections there (`sat_union_of_plain`,
  `sat_inter_of_plain`). So **membership in a least fixed point is groundable**: some finite
  unfolding finds it (`satisfies_mu_iff_exists_stage`, `check_complete_lfp`); **non-membership in a
  greatest fixed point is refuted at some finite stage** (`satisfies_nu_iff_forall_stage`,
  `check_complete_gfp`).

**On the step.** The program "take one `T`" makes nothing, so its firings choose no fresh identity
and every store has finitely many successors on the nose (`countingKnowledge_imageFinite`). The even
reaches are groundable: a store can stop after an even number of steps exactly when a finite
unfolding of `μX. [·]⊥ ∨ ⟨·⟩⟨·⟩X` finds it (`evenReach_groundable`). Programs that make fresh
identities are image-finite only up to bisimilarity; `GroundableUpTo` carries the result to them
through the bisimulation quotient.

**Controls.**
* **A finite stage never confirms a greatest fixed point** (`chain_never_confirms`): on the
  one-letter chain, which is image-finite, no state has an infinite run, yet the state `k` lies in the
  `k`-th upper stage of `νX. ⟨·⟩X`.
* **Without image-finiteness stage ω is not enough** (`stage_omega_not_enough`): on the tree's
  counterexample to finitary adequacy, the state that branches to chains of every finite length has
  only finite runs, so it satisfies `μX. [·]X`, and it lies in no finite lower stage: the check answers
  "undecided" at every budget although the state is a member.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.WhenTypesApply.Groundable

open Set
open Mettapedia.Logic.ModalMuCalculus
open Mettapedia.Logic.ModalQuantaleSemantics.Boolean (bodyOrderHom satisfies_mu_iff_mem_lfp
  satisfies_nu_iff_mem_gfp)

universe u w

/-! ## Stages -/

section Stages

variable {S : Type u}

/-- The `k`-th unfolding from below. -/
def lower (F : Set S →o Set S) (k : ℕ) : Set S := F^[k] ∅

/-- The `k`-th unfolding from above. -/
def upper (F : Set S →o Set S) (k : ℕ) : Set S := F^[k] univ

theorem lower_succ (F : Set S →o Set S) (k : ℕ) : lower F (k + 1) = F (lower F k) :=
  Function.iterate_succ_apply' F k ∅

theorem upper_succ (F : Set S →o Set S) (k : ℕ) : upper F (k + 1) = F (upper F k) :=
  Function.iterate_succ_apply' F k univ

/-- **Every lower stage lies in the least fixed point.** -/
theorem lower_subset_lfp (F : Set S →o Set S) : ∀ k, lower F k ⊆ F.lfp
  | 0 => empty_subset _
  | k + 1 => by
      rw [lower_succ]
      calc F (lower F k) ⊆ F F.lfp := F.monotone (lower_subset_lfp F k)
        _ = F.lfp := F.map_lfp

/-- **Every upper stage contains the greatest fixed point.** -/
theorem gfp_subset_upper (F : Set S →o Set S) : ∀ k, F.gfp ⊆ upper F k
  | 0 => subset_univ _
  | k + 1 => by
      rw [upper_succ]
      calc F.gfp = F F.gfp := F.map_gfp.symm
        _ ⊆ F (upper F k) := F.monotone (gfp_subset_upper F k)

theorem lfp_subset_gfp (F : Set S →o Set S) : F.lfp ⊆ F.gfp := F.lfp_le F.map_gfp.le

theorem lower_mono (F : Set S →o Set S) : Monotone (lower F) := by
  refine monotone_nat_of_le_succ fun k => ?_
  induction k with
  | zero => exact empty_subset _
  | succ k ih =>
      calc lower F (k + 1) = F (lower F k) := lower_succ F k
        _ ⊆ F (lower F (k + 1)) := F.monotone ih
        _ = lower F (k + 1 + 1) := (lower_succ F (k + 1)).symm

theorem upper_anti (F : Set S →o Set S) : Antitone (upper F) := by
  refine antitone_nat_of_succ_le fun k => ?_
  induction k with
  | zero => exact subset_univ _
  | succ k ih =>
      calc upper F (k + 1 + 1) = F (upper F (k + 1)) := upper_succ F (k + 1)
        _ ⊆ F (upper F k) := F.monotone ih
        _ = upper F (k + 1) := (upper_succ F k).symm

/-! ## The budgeted check -/

/-- **The three outcomes of a budgeted fixed-point check.** -/
inductive Verdict where
  | member
  | nonmember
  | undecided
  deriving DecidableEq

/-- **The check with budget `k`**: found in the `k`-th lower stage, a member; outside the `k`-th
upper stage, a nonmember; otherwise the budget ran out. -/
noncomputable def check (F : Set S →o Set S) (k : ℕ) (s : S) : Verdict := by
  classical exact
    if s ∈ lower F k then .member else if s ∈ upper F k then .undecided else .nonmember

variable {F : Set S →o Set S} {k : ℕ} {s : S}

theorem check_eq_member_iff : check F k s = .member ↔ s ∈ lower F k := by
  unfold check
  by_cases low : s ∈ lower F k <;> by_cases up : s ∈ upper F k <;> simp [low, up]

theorem check_eq_nonmember_iff : check F k s = .nonmember ↔ s ∉ upper F k := by
  unfold check
  by_cases low : s ∈ lower F k
  · have up : s ∈ upper F k :=
      gfp_subset_upper F k (lfp_subset_gfp F (lower_subset_lfp F k low))
    simp [low, up]
  · by_cases up : s ∈ upper F k <;> simp [low, up]

/-- **"Member" is sound**: the state is in the least fixed point, hence in the greatest. -/
theorem check_member (verdict : check F k s = .member) : s ∈ F.lfp :=
  lower_subset_lfp F k (check_eq_member_iff.mp verdict)

/-- **"Nonmember" is sound**: the state is outside the greatest fixed point, hence the least. -/
theorem check_nonmember (verdict : check F k s = .nonmember) : s ∉ F.gfp :=
  fun inside => check_eq_nonmember_iff.mp verdict (gfp_subset_upper F k inside)

/-- **"Undecided" is exactly a budget outcome**: neither stage decided. -/
theorem check_undecided_iff : check F k s = .undecided ↔ s ∉ lower F k ∧ s ∈ upper F k := by
  unfold check
  by_cases low : s ∈ lower F k <;> by_cases up : s ∈ upper F k <;> simp [low, up]

/-- **Monotone in the budget**: a decided verdict is the verdict of every larger budget. -/
theorem check_mono {k' : ℕ} (le : k ≤ k') (decided : check F k s ≠ .undecided) :
    check F k' s = check F k s := by
  by_cases low : s ∈ lower F k
  · rw [check_eq_member_iff.mpr low, check_eq_member_iff.mpr (lower_mono F le low)]
  · by_cases up : s ∈ upper F k
    · exact absurd (check_undecided_iff.mpr ⟨low, up⟩) decided
    · rw [check_eq_nonmember_iff.mpr up,
        check_eq_nonmember_iff.mpr fun inside => up (upper_anti F le inside)]

/-- **The gap is never decided**: in the greatest fixed point and not in the least, at every
budget. -/
theorem check_gap (inGfp : s ∈ F.gfp) (notLfp : s ∉ F.lfp) (k : ℕ) : check F k s = .undecided :=
  check_undecided_iff.mpr ⟨fun low => notLfp (lower_subset_lfp F k low), gfp_subset_upper F k inGfp⟩

end Stages

/-! ## Plain bodies on image-finite systems -/

section Plain

variable {S : Type u} {Act : Type w}

/-- **Plain formulas**: no negation and no fixed point. -/
def plain : {n : ℕ} → Formula Act n → Bool
  | _, .tt => true
  | _, .ff => true
  | _, .var _ => true
  | _, .conj a b => plain a && plain b
  | _, .disj a b => plain a && plain b
  | _, .diamond _ a => plain a
  | _, .box _ a => plain a
  | _, .neg _ => false
  | _, .mu _ => false
  | _, .nu _ => false

theorem isPositiveIn_of_plain : ∀ {n : ℕ} (φ : Formula Act n), plain φ = true →
    ∀ i : Fin n, φ.isPositiveIn i true = true
  | _, .tt, _, _ => rfl
  | _, .ff, _, _ => rfl
  | _, .var _, _, _ => by simp [Formula.isPositiveIn]
  | _, .conj a b, p, i => by
      simp only [plain, Bool.and_eq_true] at p
      simp only [Formula.isPositiveIn, isPositiveIn_of_plain a p.1 i, isPositiveIn_of_plain b p.2 i,
        Bool.and_self]
  | _, .disj a b, p, i => by
      simp only [plain, Bool.and_eq_true] at p
      simp only [Formula.isPositiveIn, isPositiveIn_of_plain a p.1 i, isPositiveIn_of_plain b p.2 i,
        Bool.and_self]
  | _, .diamond _ a, p, i => isPositiveIn_of_plain a p i
  | _, .box _ a, p, i => isPositiveIn_of_plain a p i
  | _, .neg _, p, _ => by simp [plain] at p
  | _, .mu _, p, _ => by simp [plain] at p
  | _, .nu _, p, _ => by simp [plain] at p

/-- A plain formula reads its environment monotonically. -/
theorem sat_mono_of_plain (lts : LTS S Act) : ∀ {n : ℕ} (φ : Formula Act n), plain φ = true →
    ∀ {ρ ρ' : Env S n}, (∀ i, ρ i ⊆ ρ' i) → ∀ s, satisfies lts ρ φ s → satisfies lts ρ' φ s
  | _, .tt, _, _, _, _, _, holds => holds
  | _, .ff, _, _, _, _, _, holds => holds
  | _, .var i, _, _, _, le, _, holds => le i holds
  | _, .conj a b, p, _, _, le, s, holds => by
      simp only [plain, Bool.and_eq_true] at p
      exact ⟨sat_mono_of_plain lts a p.1 le s holds.1, sat_mono_of_plain lts b p.2 le s holds.2⟩
  | _, .disj a b, p, _, _, le, s, holds => by
      simp only [plain, Bool.and_eq_true] at p
      exact Or.imp (sat_mono_of_plain lts a p.1 le s) (sat_mono_of_plain lts b p.2 le s) holds
  | _, .diamond _ a, p, _, _, le, _, holds => by
      obtain ⟨t, step, there⟩ := holds
      exact ⟨t, step, sat_mono_of_plain lts a p le t there⟩
  | _, .box _ a, p, _, _, le, _, holds => fun t step => sat_mono_of_plain lts a p le t (holds t step)
  | _, .neg _, p, _, _, _, _, _ => by simp [plain] at p
  | _, .mu _, p, _, _, _, _, _ => by simp [plain] at p
  | _, .nu _, p, _, _, _, _, _ => by simp [plain] at p

/-- **Image-finite**: finitely many successors under each label. -/
def ImageFinite (lts : LTS S Act) : Prop := ∀ s a, (lts.successors s a).Finite

/-- The union of a family of environments. -/
def envUnion {n : ℕ} (family : ℕ → Env S n) : Env S n := fun i => ⋃ k, family k i

/-- The intersection of a family of environments. -/
def envInter {n : ℕ} (family : ℕ → Env S n) : Env S n := fun i => ⋂ k, family k i

theorem bound_of_finite {T : Set S} (finite : T.Finite) {P : S → ℕ → Prop}
    (each : ∀ t ∈ T, ∃ k, P t k) : ∃ K, ∀ t ∈ T, ∃ k ≤ K, P t k := by
  classical
  obtain ⟨K, hK⟩ := (finite.image fun t => if h : ∃ k, P t k then Classical.choose h else 0).bddAbove
  refine ⟨K, fun t inside => ?_⟩
  have h := each t inside
  refine ⟨if h : ∃ k, P t k then Classical.choose h else 0, hK ⟨t, inside, rfl⟩, ?_⟩
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- **A plain formula commutes with increasing unions on an image-finite system.** -/
theorem sat_union_of_plain {lts : LTS S Act} (finite : ImageFinite lts) :
    ∀ {n : ℕ} (φ : Formula Act n), plain φ = true → ∀ (family : ℕ → Env S n),
      (∀ k k', k ≤ k' → ∀ i, family k i ⊆ family k' i) →
      ∀ s, satisfies lts (envUnion family) φ s → ∃ k, satisfies lts (family k) φ s
  | _, .tt, _, _, _, _, _ => ⟨0, trivial⟩
  | _, .ff, _, _, _, _, holds => False.elim holds
  | _, .var _, _, _, _, _, holds => Set.mem_iUnion.mp holds
  | _, .conj a b, p, family, mono, s, holds => by
      simp only [plain, Bool.and_eq_true] at p
      obtain ⟨k₁, h₁⟩ := sat_union_of_plain finite a p.1 family mono s holds.1
      obtain ⟨k₂, h₂⟩ := sat_union_of_plain finite b p.2 family mono s holds.2
      exact ⟨max k₁ k₂, sat_mono_of_plain lts a p.1 (mono _ _ (le_max_left _ _)) s h₁,
        sat_mono_of_plain lts b p.2 (mono _ _ (le_max_right _ _)) s h₂⟩
  | _, .disj a b, p, family, mono, s, holds => by
      simp only [plain, Bool.and_eq_true] at p
      rcases holds with h | h
      · obtain ⟨k, hk⟩ := sat_union_of_plain finite a p.1 family mono s h
        exact ⟨k, Or.inl hk⟩
      · obtain ⟨k, hk⟩ := sat_union_of_plain finite b p.2 family mono s h
        exact ⟨k, Or.inr hk⟩
  | _, .diamond _ a, p, family, mono, _, holds => by
      obtain ⟨t, step, there⟩ := holds
      obtain ⟨k, hk⟩ := sat_union_of_plain finite a p family mono t there
      exact ⟨k, t, step, hk⟩
  | _, .box action a, p, family, mono, s, holds => by
      obtain ⟨K, bound⟩ := bound_of_finite (finite s action)
        (P := fun t k => satisfies lts (family k) a t)
        (fun t step => sat_union_of_plain finite a p family mono t (holds t step))
      refine ⟨K, fun t step => ?_⟩
      obtain ⟨k, le, hk⟩ := bound t step
      exact sat_mono_of_plain lts a p (mono _ _ le) t hk
  | _, .neg _, p, _, _, _, _ => by simp [plain] at p
  | _, .mu _, p, _, _, _, _ => by simp [plain] at p
  | _, .nu _, p, _, _, _, _ => by simp [plain] at p

/-- **A plain formula commutes with decreasing intersections on an image-finite system.** -/
theorem sat_inter_of_plain {lts : LTS S Act} (finite : ImageFinite lts) :
    ∀ {n : ℕ} (φ : Formula Act n), plain φ = true → ∀ (family : ℕ → Env S n),
      (∀ k k', k ≤ k' → ∀ i, family k' i ⊆ family k i) →
      ∀ s, (∀ k, satisfies lts (family k) φ s) → satisfies lts (envInter family) φ s
  | _, .tt, _, _, _, _, _ => trivial
  | _, .ff, _, _, _, _, all => False.elim (all 0)
  | _, .var _, _, _, _, _, all => Set.mem_iInter.mpr all
  | _, .conj a b, p, family, anti, s, all => by
      simp only [plain, Bool.and_eq_true] at p
      exact ⟨sat_inter_of_plain finite a p.1 family anti s fun k => (all k).1,
        sat_inter_of_plain finite b p.2 family anti s fun k => (all k).2⟩
  | _, .disj a b, p, family, anti, s, all => by
      simp only [plain, Bool.and_eq_true] at p
      by_cases left : ∀ k, satisfies lts (family k) a s
      · exact Or.inl (sat_inter_of_plain finite a p.1 family anti s left)
      · push Not at left
        obtain ⟨k₀, miss⟩ := left
        refine Or.inr (sat_inter_of_plain finite b p.2 family anti s fun k => ?_)
        have later : satisfies lts (family (max k k₀)) b s := by
          rcases all (max k k₀) with h | h
          · exact absurd (sat_mono_of_plain lts a p.1 (anti _ _ (le_max_right _ _)) s h) miss
          · exact h
        exact sat_mono_of_plain lts b p.2 (anti _ _ (le_max_left _ _)) s later
  | _, .diamond action a, p, family, anti, s, all => by
      by_contra missing
      have each : ∀ t ∈ lts.successors s action, ∃ k, ¬ satisfies lts (family k) a t := by
        intro t step
        by_contra always
        push Not at always
        exact missing ⟨t, step, sat_inter_of_plain finite a p family anti t always⟩
      obtain ⟨K, bound⟩ := bound_of_finite (finite s action) each
      obtain ⟨t, step, there⟩ := all K
      obtain ⟨k, le, miss⟩ := bound t step
      exact miss (sat_mono_of_plain lts a p (anti _ _ le) t there)
  | _, .box _ a, p, family, anti, _, all => fun t step =>
      sat_inter_of_plain finite a p family anti t fun k => all k t step
  | _, .neg _, p, _, _, _, _ => by simp [plain] at p
  | _, .mu _, p, _, _, _, _ => by simp [plain] at p
  | _, .nu _, p, _, _, _, _ => by simp [plain] at p

theorem extend_mono {n : ℕ} (ρ : Env S n) {X Y : Set S} (le : X ⊆ Y) (i : Fin (n + 1)) :
    ρ.extend X i ⊆ ρ.extend Y i := by
  unfold Env.extend
  split
  · exact le
  · exact subset_rfl

theorem extend_union {n : ℕ} (ρ : Env S n) (stages : ℕ → Set S) (i : Fin (n + 1)) (s : S) :
    s ∈ envUnion (fun k => ρ.extend (stages k)) i ↔ s ∈ ρ.extend (⋃ k, stages k) i := by
  by_cases zero : (i : ℕ) = 0
  · simp [envUnion, Env.extend, zero]
  · simp [envUnion, Env.extend, zero]

theorem extend_inter {n : ℕ} (ρ : Env S n) (stages : ℕ → Set S) (i : Fin (n + 1)) (s : S) :
    s ∈ envInter (fun k => ρ.extend (stages k)) i ↔ s ∈ ρ.extend (⋂ k, stages k) i := by
  by_cases zero : (i : ℕ) = 0
  · simp [envInter, Env.extend, zero]
  · simp [envInter, Env.extend, zero]

/-- **A least fixed point of a plain body is reached at stage ω on an image-finite system.** -/
theorem lfp_eq_iUnion_of_plain {lts : LTS S Act} (finite : ImageFinite lts) {n : ℕ} (ρ : Env S n)
    (body : Formula Act (n + 1)) (p : plain body = true) :
    (bodyOrderHom lts ρ body (isPositiveIn_of_plain body p 0)).lfp =
      ⋃ k, lower (bodyOrderHom lts ρ body (isPositiveIn_of_plain body p 0)) k := by
  apply Set.Subset.antisymm
  · apply OrderHom.lfp_le
    intro s inside
    have union : satisfies lts (envUnion fun k =>
        ρ.extend (lower (bodyOrderHom lts ρ body (isPositiveIn_of_plain body p 0)) k)) body s :=
      (satisfies_congr (fun _ _ _ => Iff.rfl) (fun i t => (extend_union ρ _ i t).symm) body s).mp
        inside
    obtain ⟨k, hk⟩ := sat_union_of_plain finite body p _
      (fun k k' le i => extend_mono ρ (lower_mono _ le) i) s union
    refine Set.mem_iUnion.mpr ⟨k + 1, ?_⟩
    rw [lower_succ]
    exact hk
  · exact Set.iUnion_subset fun k => lower_subset_lfp _ k

/-- **A greatest fixed point of a plain body is reached at stage ω on an image-finite system.** -/
theorem gfp_eq_iInter_of_plain {lts : LTS S Act} (finite : ImageFinite lts) {n : ℕ} (ρ : Env S n)
    (body : Formula Act (n + 1)) (p : plain body = true) :
    (bodyOrderHom lts ρ body (isPositiveIn_of_plain body p 0)).gfp =
      ⋂ k, upper (bodyOrderHom lts ρ body (isPositiveIn_of_plain body p 0)) k := by
  apply Set.Subset.antisymm
  · exact Set.subset_iInter fun k => gfp_subset_upper _ k
  · apply OrderHom.le_gfp
    intro s inside
    have all : ∀ k, satisfies lts ((fun k =>
        ρ.extend (upper (bodyOrderHom lts ρ body (isPositiveIn_of_plain body p 0)) k)) k) body s := by
      intro k
      have there := Set.mem_iInter.mp inside (k + 1)
      rw [upper_succ] at there
      exact there
    have inter := sat_inter_of_plain finite body p _
      (fun k k' le i => extend_mono ρ (upper_anti _ le) i) s all
    exact (satisfies_congr (fun _ _ _ => Iff.rfl) (fun i t => extend_inter ρ _ i t) body s).mp inter

variable {lts : LTS S Act}

/-- **Groundable**: on an image-finite system a state satisfies a least fixed point of a plain body
exactly when some finite unfolding finds it. -/
theorem satisfies_mu_iff_exists_stage (finite : ImageFinite lts) {n : ℕ} (ρ : Env S n)
    (body : Formula Act (n + 1)) (p : plain body = true) (s : S) :
    satisfies lts ρ (.mu body) s ↔
      ∃ k, s ∈ lower (bodyOrderHom lts ρ body (isPositiveIn_of_plain body p 0)) k := by
  rw [satisfies_mu_iff_mem_lfp lts ρ body (isPositiveIn_of_plain body p 0),
    lfp_eq_iUnion_of_plain finite ρ body p, Set.mem_iUnion]

/-- **Refutable**: on an image-finite system a state fails a greatest fixed point of a plain body
exactly when some finite unfolding excludes it. -/
theorem satisfies_nu_iff_forall_stage (finite : ImageFinite lts) {n : ℕ} (ρ : Env S n)
    (body : Formula Act (n + 1)) (p : plain body = true) (s : S) :
    satisfies lts ρ (.nu body) s ↔
      ∀ k, s ∈ upper (bodyOrderHom lts ρ body (isPositiveIn_of_plain body p 0)) k := by
  rw [satisfies_nu_iff_mem_gfp lts ρ body (isPositiveIn_of_plain body p 0),
    gfp_eq_iInter_of_plain finite ρ body p, Set.mem_iInter]

/-- **The check finds every member of a least fixed point** at some budget. -/
theorem check_complete_lfp (finite : ImageFinite lts) {n : ℕ} (ρ : Env S n)
    (body : Formula Act (n + 1)) (p : plain body = true) {s : S}
    (holds : satisfies lts ρ (.mu body) s) :
    ∃ k, check (bodyOrderHom lts ρ body (isPositiveIn_of_plain body p 0)) k s = .member := by
  obtain ⟨k, low⟩ := (satisfies_mu_iff_exists_stage finite ρ body p s).mp holds
  exact ⟨k, check_eq_member_iff.mpr low⟩

/-- **The check refutes every non-member of a greatest fixed point** at some budget. -/
theorem check_complete_gfp (finite : ImageFinite lts) {n : ℕ} (ρ : Env S n)
    (body : Formula Act (n + 1)) (p : plain body = true) {s : S}
    (fails : ¬ satisfies lts ρ (.nu body) s) :
    ∃ k, check (bodyOrderHom lts ρ body (isPositiveIn_of_plain body p 0)) k s = .nonmember := by
  rw [satisfies_nu_iff_forall_stage finite ρ body p s] at fails
  push Not at fails
  obtain ⟨k, up⟩ := fails
  exact ⟨k, check_eq_nonmember_iff.mpr up⟩

end Plain

/-! ## On the step -/

section Step

open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open NamesOnTheStep NamesOnTheStep.IssuingControls
open ProgramAdequacy StepSpan
open Distinctions.ParityBoundary FixpointTypes Ladder

/-- **The program "take one `T`" is image-finite on the nose**: it makes nothing, so a store's
successors are indexed by its present occurrences. -/
theorem countingKnowledge_imageFinite : ImageFinite (ltsOf countingKnowledge) := by
  intro C _
  refine ((Finset.finite_toSet C.present).image fun o =>
    (⟨C.equations ++ [(factT, o.1)], C.present \ {o}⟩ : Conf)).subset ?_
  intro C' step
  obtain ⟨o, present, rfl⟩ := succ_form step
  exact ⟨o, present, rfl⟩

theorem evenBody_plain : plain evenBody = true := rfl

/-- **The even reaches are groundable**: a store can stop after an even number of steps exactly when
a finite unfolding of `μX. [·]⊥ ∨ ⟨·⟩⟨·⟩X` finds it. -/
theorem evenReach_groundable (C : Conf) :
    C ∈ evenReach ↔ ∃ k, C ∈ lower (bodyOrderHom (ltsOf countingKnowledge)
      (atomEnv countingKnowledge evenReachFormula.atoms) evenBody
      (isPositiveIn_of_plain evenBody evenBody_plain 0)) k :=
  (evenReachFormula_holds C).symm.trans
    (satisfies_mu_iff_exists_stage countingKnowledge_imageFinite _ evenBody evenBody_plain C)

end Step

/-! ## Controls -/

section Controls

open OneLetterChain FixpointTypes

/-- `⟨·⟩X`: some step into `X`. -/
def stepBody : Formula Unit 1 := .diamond () (.var 0)

theorem chain_imageFinite : ImageFinite (chain ()) := by
  intro m _
  refine (Set.finite_singleton (m - 1)).subset ?_
  rintro m' ⟨-, rfl⟩
  show m' = m' + 1 - 1
  omega

/-- On the chain no state has an infinite run. -/
theorem chain_no_infinite_run (m : ℕ) : ¬ satisfies (chain ()) (fun _ => ∅) (.nu stepBody) m := by
  rintro ⟨X, member, post⟩
  have none : ∀ t, t ∉ X := by
    intro t
    induction t with
    | zero =>
        intro inX
        obtain ⟨_, ⟨_, impossible⟩, _⟩ := post 0 inX
        omega
    | succ t ih =>
        intro inX
        obtain ⟨t', ⟨_, same⟩, there⟩ := post (t + 1) inX
        obtain rfl : t' = t := by omega
        exact ih there
  exact none m member

theorem chain_upper (k : ℕ) : ∀ m, k ≤ m → m ∈ upper (bodyOrderHom (chain ()) (fun _ => ∅) stepBody rfl) k := by
  induction k with
  | zero => exact fun _ _ => mem_univ _
  | succ k ih =>
      intro m le
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      rw [upper_succ]
      exact ⟨m', ⟨rfl, rfl⟩, ih m' (by omega)⟩

/-- **A finite stage never confirms a greatest fixed point**: on the one-letter chain, which is
image-finite, no state has an infinite run, yet the state `k` passes the `k`-th upper stage of
`νX. ⟨·⟩X`, so the check is "undecided" there and never "member". -/
theorem chain_never_confirms (k : ℕ) :
    k ∈ upper (bodyOrderHom (chain ()) (fun _ => ∅) stepBody rfl) k ∧
      ¬ satisfies (chain ()) (fun _ => ∅) (.nu stepBody) k ∧
      check (bodyOrderHom (chain ()) (fun _ => ∅) stepBody rfl) k k ≠ .member :=
  ⟨chain_upper k k le_rfl, chain_no_infinite_run k, fun verdict =>
    chain_no_infinite_run k ((satisfies_nu_iff_mem_gfp (chain ()) _ stepBody rfl k).mpr
      (lfp_subset_gfp _ (check_member verdict)))⟩

open Mettapedia.GSLT.HennessyMilner.ImageFinitenessNecessary

/-- `[·]X`: every step into `X`. -/
def wellFoundedBody : Formula Unit 1 := .box () (.var 0)

/-- The tree's counterexample system, as a transition system. -/
abbrev branching := ltsOf hm

/-- The well-foundedness transformer there. -/
noncomputable abbrev wellFounded := bodyOrderHom branching (fun _ => ∅) wellFoundedBody rfl

theorem chain_lower {n k : ℕ} (low : St.chain n ∈ lower wellFounded k) : n < k := by
  induction k generalizing n with
  | zero => exact False.elim low
  | succ k ih =>
      rw [lower_succ] at low
      cases n with
      | zero => omega
      | succ n =>
          have := ih (low (St.chain n) (Step.chainDown n))
          omega

theorem left_not_lower (k : ℕ) : St.left ∉ lower wellFounded k := by
  cases k with
  | zero => exact fun low => False.elim low
  | succ k =>
      intro low
      rw [lower_succ] at low
      exact lt_irrefl k (chain_lower (low (St.chain k) (Step.leftChain k)))

theorem left_wellFounded : satisfies branching (fun _ => ∅) (.mu wellFoundedBody) St.left := by
  intro X closed
  have chains : ∀ n, St.chain n ∈ X := by
    intro n
    induction n with
    | zero =>
        apply closed
        intro t step
        cases step
    | succ n ih =>
        apply closed
        intro t step
        cases step
        exact ih
  apply closed
  intro t step
  cases step with
  | leftChain n => exact chains n

/-- **Without image-finiteness stage ω is not enough**: on the tree's counterexample to finitary
adequacy, the state that branches to chains of every finite length satisfies `μX. [·]X` and lies in
no finite lower stage, so the check answers "undecided" at every budget although it is a member. -/
theorem stage_omega_not_enough :
    satisfies branching (fun _ => ∅) (.mu wellFoundedBody) St.left ∧
      (∀ k, St.left ∉ lower wellFounded k) ∧ (∀ k, check wellFounded k St.left = .undecided) := by
  have inLfp : St.left ∈ wellFounded.lfp :=
    (satisfies_mu_iff_mem_lfp branching _ wellFoundedBody rfl St.left).mp left_wellFounded
  exact ⟨left_wellFounded, left_not_lower, fun k =>
    check_undecided_iff.mpr ⟨left_not_lower k, gfp_subset_upper _ k (lfp_subset_gfp _ inLfp)⟩⟩

end Controls

#print axioms lower_subset_lfp
#print axioms gfp_subset_upper
#print axioms check_member
#print axioms check_nonmember
#print axioms check_undecided_iff
#print axioms check_mono
#print axioms check_gap
#print axioms sat_union_of_plain
#print axioms sat_inter_of_plain
#print axioms lfp_eq_iUnion_of_plain
#print axioms gfp_eq_iInter_of_plain
#print axioms satisfies_mu_iff_exists_stage
#print axioms satisfies_nu_iff_forall_stage
#print axioms check_complete_lfp
#print axioms check_complete_gfp
#print axioms countingKnowledge_imageFinite
#print axioms evenReach_groundable
#print axioms chain_never_confirms
#print axioms stage_omega_not_enough

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.WhenTypesApply.Groundable
