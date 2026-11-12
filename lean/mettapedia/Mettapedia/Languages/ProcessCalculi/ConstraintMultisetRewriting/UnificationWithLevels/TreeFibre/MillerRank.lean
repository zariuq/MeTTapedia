import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerSteps
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSupport

/-!
# The rank of the Miller solver, and what re-reading keeps

**The rank** of a store is the pair
* the sum, over the unknowns occurring in its sides, of their arity plus one (`weight`);
* the number of equations.

Solving or projecting `X` removes it from the store (`occ_reread`: only the answer's own unknowns can appear in
its place), pruning lowers its arity, and deleting removes an equation. Each lowers the rank
(`weight_value_lt`, `weight_prune_lt`, `rank_delete`).

**What re-reading keeps** (`rereadSide_view`): every side of a Miller equation, re-read after an answer, is again a
Miller side or a rigid local, given that the answer's own re-reading of a side of `X` is one (`ValueShape`). The
three answers of the solver have this shape: a projection gives a rigid local (`project_shape`); `F x_σ` gives a
Miller side of `F` (`solve_shape`); `X' x_K` gives a Miller side of the re-declared `X` (`prune_shape`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

namespace Miller

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate

variable {Head L : Type} [UniverseLevel.LevelOrder L]

/-! ## Supports -/

section Supports

theorem support_lift_body {n m : Nat} (σ : Sub Head n m) {w : Fin m} {v' : Fin (n + 1)}
    (hw : w.succ ∈ (liftSub σ v').support) : ∃ v, v' = v.succ ∧ w ∈ (σ v).support := by
  cases v' using Fin.cases with
  | zero =>
      simp only [liftSub_zero, Tm.support, Finset.mem_singleton] at hw
      exact absurd hw (Fin.succ_ne_zero w)
  | succ v =>
      refine ⟨v, rfl, ?_⟩
      rw [liftSub_succ, ContextualDependentSupport.support_rename] at hw
      obtain ⟨u, hu, same⟩ := Finset.mem_image.mp hw
      have uw : u = w := Fin.succ_injective _ same
      rw [← uw]
      exact hu

/-- **What a substitution can bring into a support.** -/
theorem support_subst_sub {n : Nat} (t : Tm Head n) :
    ∀ {m : Nat} (σ : Sub Head n m) {w : Fin m}, w ∈ (Presentation.subst σ t).support →
      ∃ v ∈ t.support, w ∈ (σ v).support := by
  induction t with
  | var i => intro m σ w h; exact ⟨i, by simp [Tm.support], h⟩
  | const _ => intro m σ w h; simp [Presentation.subst, Tm.support] at h
  | head _ => intro m σ w h; simp [Presentation.subst, Tm.support] at h
  | pi A B ihA ihB =>
      intro m σ w h
      simp only [Presentation.subst, Tm.support, Finset.mem_union, mem_outerSupport] at h
      rcases h with h | h
      · obtain ⟨v, hv, hw⟩ := ihA σ h
        exact ⟨v, by simp [Tm.support, hv], hw⟩
      · obtain ⟨v', hv', hw⟩ := ihB (liftSub σ) h
        obtain ⟨v, rfl, hw'⟩ := support_lift_body σ hw
        exact ⟨v, by simp [Tm.support, hv'], hw'⟩
  | sigma A B ihA ihB =>
      intro m σ w h
      simp only [Presentation.subst, Tm.support, Finset.mem_union, mem_outerSupport] at h
      rcases h with h | h
      · obtain ⟨v, hv, hw⟩ := ihA σ h
        exact ⟨v, by simp [Tm.support, hv], hw⟩
      · obtain ⟨v', hv', hw⟩ := ihB (liftSub σ) h
        obtain ⟨v, rfl, hw'⟩ := support_lift_body σ hw
        exact ⟨v, by simp [Tm.support, hv'], hw'⟩
  | id A a b ihA iha ihb =>
      intro m σ w h
      simp only [Presentation.subst, Tm.support, Finset.mem_union] at h
      rcases h with (h | h) | h
      · obtain ⟨v, hv, hw⟩ := ihA σ h
        exact ⟨v, by simp [Tm.support, hv], hw⟩
      · obtain ⟨v, hv, hw⟩ := iha σ h
        exact ⟨v, by simp [Tm.support, hv], hw⟩
      · obtain ⟨v, hv, hw⟩ := ihb σ h
        exact ⟨v, by simp [Tm.support, hv], hw⟩
  | lam b ih =>
      intro m σ w h
      simp only [Presentation.subst, Tm.support, mem_outerSupport] at h
      obtain ⟨v', hv', hw⟩ := ih (liftSub σ) h
      obtain ⟨v, rfl, hw'⟩ := support_lift_body σ hw
      exact ⟨v, by simp [Tm.support, hv'], hw'⟩
  | app f a ihf iha =>
      intro m σ w h
      simp only [Presentation.subst, Tm.support, Finset.mem_union] at h
      rcases h with h | h
      · obtain ⟨v, hv, hw⟩ := ihf σ h
        exact ⟨v, by simp [Tm.support, hv], hw⟩
      · obtain ⟨v, hv, hw⟩ := iha σ h
        exact ⟨v, by simp [Tm.support, hv], hw⟩
  | pair a b iha ihb =>
      intro m σ w h
      simp only [Presentation.subst, Tm.support, Finset.mem_union] at h
      rcases h with h | h
      · obtain ⟨v, hv, hw⟩ := iha σ h
        exact ⟨v, by simp [Tm.support, hv], hw⟩
      · obtain ⟨v, hv, hw⟩ := ihb σ h
        exact ⟨v, by simp [Tm.support, hv], hw⟩
  | fst p ih =>
      intro m σ w h
      obtain ⟨v, hv, hw⟩ := ih σ h
      exact ⟨v, hv, hw⟩
  | snd p ih =>
      intro m σ w h
      obtain ⟨v, hv, hw⟩ := ih σ h
      exact ⟨v, hv, hw⟩
  | refl a ih =>
      intro m σ w h
      obtain ⟨v, hv, hw⟩ := ih σ h
      exact ⟨v, hv, hw⟩

theorem mem_support_lams : ∀ {n : Nat} (qs : List Head) (b : Tm Head (arity n qs)) (v : Fin n),
    v ∈ (lams qs b).support ↔ shift qs v ∈ b.support
  | _, [], _, _ => Iff.rfl
  | _, _ :: qs, b, v => by
      show v ∈ (Tm.lam (lams qs b)).support ↔ _
      simp only [Tm.support, mem_outerSupport]
      exact mem_support_lams qs b v.succ

theorem mem_support_apps {n : Nat} : ∀ (ts : List (Tm Head n)) (h : Tm Head n) (w : Fin n),
    w ∈ (apps h ts).support ↔ w ∈ h.support ∨ ∃ t ∈ ts, w ∈ t.support
  | [], h, w => by simp [apps]
  | t :: ts, h, w => by
      show w ∈ (apps (.app h t) ts).support ↔ _
      rw [mem_support_apps ts]
      simp only [Tm.support, Finset.mem_union, List.mem_cons, exists_eq_or_imp]
      tauto

/-- **A Miller side mentions exactly its unknown.** -/
theorem support_flexSide {N : Nat} (qs ps : List Head) (F : Fin N) (img : Fin ps.length → Fin qs.length) :
    (flexSide qs ps F img).support = {F} := by
  ext v
  unfold flexSide flexBody
  rw [mem_support_lams, mem_support_apps, Finset.mem_singleton]
  constructor
  · intro h
    rcases h with h | ⟨t, ht, h⟩
    · simp only [Tm.support, Finset.mem_singleton] at h
      exact shift_injective qs h
    · unfold spineArgs at ht
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht
      simp only [Tm.support, Finset.mem_singleton] at h
      exact absurd h.symm (loc_ne_shift qs (img j) v)
  · intro h
    subst h
    exact .inl (by simp [Tm.support])

/-- **A rigid local mentions no unknown.** -/
theorem support_localSide {N : Nat} (qs : List Head) (l : Fin qs.length) :
    (localSide qs l : Tm Head N).support = ∅ := by
  ext v
  unfold localSide
  rw [mem_support_lams]
  simp only [Tm.support, Finset.mem_singleton, Finset.notMem_empty, iff_false]
  intro h
  exact loc_ne_shift qs l v h.symm

/-- The re-read code of a side of `X` mentions only what the answer's value mentions. -/
theorem support_reread {N : Nat} (qs psX : List Head) (img : Fin psX.length → Fin qs.length)
    (val : Tm Head (arity N psX)) :
    (lams qs (Presentation.rename (sideRen qs psX img) val)).support ⊆ (lams psX val).support := by
  intro v h
  rw [mem_support_lams, ContextualDependentSupport.support_rename] at h
  obtain ⟨u, hu, same⟩ := Finset.mem_image.mp h
  rw [mem_support_lams]
  rcases index_cases psX u with ⟨w, rfl⟩ | ⟨j, rfl⟩
  · change spineRen psX (shift qs) _ (shift psX w) = shift qs v at same
    rw [spineRen_shift] at same
    rw [← shift_injective qs same]
    exact hu
  · change spineRen psX (shift qs) _ (loc psX j) = shift qs v at same
    rw [spineRen_loc] at same
    exact absurd same (loc_ne_shift qs (img j) v)

/-- **What an answer brings into a support.** -/
theorem support_answer {N : Nat} (X : Fin N) (psX : List Head) (val : Tm Head (arity N psX)) (t : Tm Head N) :
    (Presentation.subst (answerSub X psX val) t).support ⊆ t.support.erase X ∪ (lams psX val).support := by
  intro w h
  obtain ⟨v, hv, hw⟩ := support_subst_sub t _ h
  by_cases hvX : v = X
  · subst hvX
    rw [answerSub_self] at hw
    exact Finset.mem_union_right _ hw
  · rw [answerSub_ne X psX val hvX] at hw
    simp only [Tm.support, Finset.mem_singleton] at hw
    subst hw
    exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hvX, hv⟩)

end Supports

/-! ## The rank -/

section Rank

variable {S : Setting Head L}

/-- The unknowns occurring in the sides of a store. -/
def occ {Θ : Context S.R} : EquationStore (TotalTerm Θ) → Finset (Fin Θ.arity)
  | [] => ∅
  | e :: rest => e.1.2.code.support ∪ e.2.2.code.support ∪ occ rest

theorem mem_occ {Θ : Context S.R} {v : Fin Θ.arity} :
    ∀ {store : EquationStore (TotalTerm Θ)}, v ∈ occ store ↔
      ∃ e ∈ store, v ∈ e.1.2.code.support ∨ v ∈ e.2.2.code.support
  | [] => by simp [occ]
  | e :: rest => by
      simp only [occ, Finset.mem_union, List.mem_cons, exists_eq_or_imp]
      rw [mem_occ]

/-- The arity of a declared family. -/
def famArity {n : Nat} (t : Tm Head n) : Nat :=
  match readFam t with
  | some r => r.1.length
  | none => 0

theorem famArity_famCode {n : Nat} (ps : List Head) (c : Head) : famArity (famCode ps c : Tm Head n) = ps.length := by
  unfold famArity
  rw [readFam_famCode]

/-- **The weight**: the arities, plus one, of the occurring unknowns. -/
def weight {Θ : Context S.R} (store : EquationStore (TotalTerm Θ)) : Nat :=
  ∑ i ∈ occ store, (famArity (Ctx.lookup Θ.raw i) + 1)

/-- **The rank of the Miller solver.** -/
def millerRank {Γ : Context S.R} (store : EquationStore (TotalTerm Γ)) : Nat × Nat :=
  (weight store, store.length)

theorem rank_delete {Θ : Context S.R} (e : Equation (TotalTerm Θ)) (rest : EquationStore (TotalTerm Θ)) :
    ContextualDependentWorklist.Below (millerRank rest) (millerRank (e :: rest)) := by
  have sub : occ rest ⊆ occ (e :: rest) := fun v h => Finset.mem_union_right _ h
  have le : weight rest ≤ weight (e :: rest) := Finset.sum_le_sum_of_subset sub
  rcases Nat.lt_or_eq_of_le le with lt | eq
  · exact Prod.Lex.left _ _ lt
  · unfold millerRank
    rw [eq]
    exact Prod.Lex.right _ (Nat.lt_succ_self _)

variable [DecidableEq Head]

theorem rereadSide_type {Θ Θ' : Context S.R} {σ : Θ' ⟶ Θ} (A : AnswerData σ) (Y : TotalTerm Θ) {qs : List Head}
    {d : Head} (annotation : Y.1.code = famCode qs d) (universes : AllUniverses S.R qs) (hd : S.R.isUniverse d)
    (view : SideView (S := S) Θ.raw qs d Y.2.code) :
    (rereadSide A Y annotation universes hd view).1 = ((frames S.levels).act σ Y).1 := by
  unfold rereadSide
  split
  · split
    · rfl
    · rfl
  · rfl

theorem rereadSide_code {Θ Θ' : Context S.R} {σ : Θ' ⟶ Θ} (A : AnswerData σ) (Y : TotalTerm Θ) {qs : List Head}
    {d : Head} (annotation : Y.1.code = famCode qs d) (universes : AllUniverses S.R qs) (hd : S.R.isUniverse d)
    (view : SideView (S := S) Θ.raw qs d Y.2.code) :
    (rereadSide A Y annotation universes hd view).2.code = Presentation.subst σ.substitution Y.2.code ∨
      ∃ img : Fin A.psX.length → Fin qs.length,
        (rereadSide A Y annotation universes hd view).2.code =
          lams qs (Presentation.rename (sideRen qs A.psX img) A.val) := by
  cases view with
  | flex data below =>
      unfold rereadSide
      dsimp only
      by_cases h : data.unknown = A.X ∧ data.ps = A.psX
      · rw [dif_pos h]
        exact .inr ⟨_, rfl⟩
      · rw [dif_neg h]
        exact .inl rfl
  | rigid l side below => exact .inl rfl

variable [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]

/-- **Re-reading after an answer keeps only the answer's own unknowns in `X`'s place.** -/
theorem occ_reread {Θ : Context S.R} {families : Families Θ} {X : Fin Θ.arity} {ps' : List Head} {c' : Head}
    {universes' : AllUniverses S.R ps'} {hc' : S.R.isUniverse c'}
    (σ : redecl Θ families X ps' c' universes' hc' ⟶ Θ) (A : AnswerData σ)
    (hsub : ∀ t : Tm Head Θ.arity, Presentation.subst σ.substitution t =
      Presentation.subst (answerSub X A.psX A.val) t)
    (store : EquationStore (TotalTerm Θ)) :
    occ (rereadStore A store) ⊆ (occ (Θ := Θ) store).erase X ∪ (lams A.psX A.val).support := by
  intro v h
  obtain ⟨e', member, hv⟩ := mem_occ.mp h
  obtain ⟨e, eMember, rfl⟩ := List.mem_map.mp member
  have side : ∀ (code : Tm Head Θ.arity), code.support ⊆ (occ store) →
      (Presentation.subst σ.substitution code).support ⊆ (occ store).erase X ∪ (lams A.psX A.val).support := by
    intro code within w hw
    rw [hsub] at hw
    have := support_answer X A.psX A.val code hw
    rcases Finset.mem_union.mp this with h₁ | h₂
    · obtain ⟨ne, hw'⟩ := Finset.mem_erase.mp h₁
      exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨ne, within hw'⟩)
    · exact Finset.mem_union_right _ h₂
  have left : e.1.2.code.support ⊆ occ store := fun w hw => mem_occ.mpr ⟨e, eMember, .inl hw⟩
  have right : e.2.2.code.support ⊆ occ store := fun w hw => mem_occ.mpr ⟨e, eMember, .inr hw⟩
  have generic : ∀ (Y : TotalTerm Θ) {qs : List Head} {d : Head} (annotation : Y.1.code = famCode qs d)
      (universes : AllUniverses S.R qs) (hd : S.R.isUniverse d) (view : SideView (S := S) Θ.raw qs d Y.2.code),
      Y.2.code.support ⊆ occ store →
        (rereadSide A Y annotation universes hd view).2.code.support ⊆
          (occ store).erase X ∪ (lams A.psX A.val).support := by
    intro Y qs d annotation universes hd view within
    rcases rereadSide_code A Y annotation universes hd view with same | ⟨img, same⟩
    · rw [same]
      exact side _ within
    · rw [same]
      exact (support_reread qs A.psX img A.val).trans Finset.subset_union_right
  unfold rereadEq at hv
  cases hread : readEq (S := S) e with
  | none =>
      rw [hread] at hv
      rcases hv with hv | hv
      · exact side _ left hv
      · exact side _ right hv
  | some w =>
      rw [hread] at hv
      rcases hv with hv | hv
      · exact generic e.1 w.annotation_left w.universes w.universe_d w.left left hv
      · exact generic e.2 w.annotation_right w.universes w.universe_d w.right right hv

/-- **A value rule lowers the weight**: `X` occurs, and the answer's value mentions only other occurring
unknowns. -/
theorem weight_value_lt {Θ : Context S.R} {families : Families Θ} {X : Fin Θ.arity} {psX : List Head} {cX : Head}
    {universesX : AllUniverses S.R psX} {hcX : S.R.isUniverse cX}
    (σ : redecl Θ families X psX cX universesX hcX ⟶ Θ) (A : AnswerData σ)
    (hsub : ∀ t : Tm Head Θ.arity, Presentation.subst σ.substitution t =
      Presentation.subst (answerSub X A.psX A.val) t)
    (store : EquationStore (TotalTerm Θ)) (occurs : X ∈ occ store)
    (valOcc : (lams A.psX A.val).support ⊆ (occ (Θ := Θ) store).erase X) :
    weight (rereadStore A store) < weight store := by
  have sub : occ (rereadStore A store) ⊆ (occ (Θ := Θ) store).erase X := by
    intro v h
    rcases Finset.mem_union.mp (occ_reread σ A hsub store h) with h | h
    · exact h
    · exact valOcc h
  have arities : ∀ i ∈ (occ (Θ := Θ) store).erase X,
      famArity (Ctx.lookup (setFamAt Θ.raw X psX cX) i) = famArity (Ctx.lookup Θ.raw i) := by
    intro i member
    rw [lookup_setFamAt_ne Θ.raw X i psX cX (Finset.mem_erase.mp member).1]
  unfold weight
  calc ∑ i ∈ occ (rereadStore A store), (famArity (Ctx.lookup (setFamAt Θ.raw X psX cX) i) + 1)
      ≤ ∑ i ∈ (occ (Θ := Θ) store).erase X, (famArity (Ctx.lookup (setFamAt Θ.raw X psX cX) i) + 1) :=
        Finset.sum_le_sum_of_subset sub
    _ = ∑ i ∈ (occ (Θ := Θ) store).erase X, (famArity (Ctx.lookup Θ.raw i) + 1) :=
        Finset.sum_congr rfl fun i member => by rw [arities i member]
    _ < (famArity (Ctx.lookup Θ.raw X) + 1) +
          ∑ i ∈ (occ (Θ := Θ) store).erase X, (famArity (Ctx.lookup Θ.raw i) + 1) := by
        omega
    _ = ∑ i ∈ occ (Θ := Θ) store, (famArity (Ctx.lookup Θ.raw i) + 1) :=
        Finset.add_sum_erase (occ (Θ := Θ) store) (fun i => famArity (Ctx.lookup Θ.raw i) + 1) occurs

/-- **A pruning lowers the weight**: `X` occurs, its arity drops, and the answer mentions only `X`. -/
theorem weight_prune_lt {Θ : Context S.R} {families : Families Θ} {X : Fin Θ.arity} {psX ps' : List Head}
    {cX : Head} {universes' : AllUniverses S.R ps'} {hcX : S.R.isUniverse cX}
    (declared : Ctx.lookup Θ.raw X = famCode psX cX) (shorter : ps'.length < psX.length)
    (σ : redecl Θ families X ps' cX universes' hcX ⟶ Θ) (A : AnswerData σ)
    (hsub : ∀ t : Tm Head Θ.arity, Presentation.subst σ.substitution t =
      Presentation.subst (answerSub X A.psX A.val) t)
    (store : EquationStore (TotalTerm Θ)) (occurs : X ∈ occ store)
    (valOcc : (lams A.psX A.val).support ⊆ {X}) :
    weight (rereadStore A store) < weight store := by
  have sub : occ (rereadStore A store) ⊆ occ (Θ := Θ) store := by
    intro v h
    rcases Finset.mem_union.mp (occ_reread σ A hsub store h) with h | h
    · exact (Finset.mem_erase.mp h).2
    · rw [Finset.mem_singleton.mp (valOcc h)]
      exact occurs
  unfold weight
  calc ∑ i ∈ occ (rereadStore A store), (famArity (Ctx.lookup (setFamAt Θ.raw X ps' cX) i) + 1)
      ≤ ∑ i ∈ occ (Θ := Θ) store, (famArity (Ctx.lookup (setFamAt Θ.raw X ps' cX) i) + 1) :=
        Finset.sum_le_sum_of_subset sub
    _ < ∑ i ∈ occ (Θ := Θ) store, (famArity (Ctx.lookup Θ.raw i) + 1) := by
        apply Finset.sum_lt_sum
        · intro i _
          by_cases h : i = X
          · rw [h, lookup_setFamAt_self, declared, famArity_famCode, famArity_famCode]
            omega
          · rw [lookup_setFamAt_ne Θ.raw X i ps' cX h]
        · refine ⟨X, occurs, ?_⟩
          rw [lookup_setFamAt_self, declared, famArity_famCode, famArity_famCode]
          omega

end Rank

end Miller

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
