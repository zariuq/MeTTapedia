import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Fintype.Prod
import Mettapedia.GSLT.Causality.DoCalculus.TruncatedFactorization

/-!
# Front-door adjustment

On the smoking graph — an unobserved confounder `U`, smoking `S`, tar `T`,
and cancer `C`, with edges `U → S`, `U → C`, `S → T`, and `T → C` — the
effect of smoking on cancer is identified by the front-door formula

`P(c | do(s)) = Σ_t P(t | s) Σ_{s'} P(c | t, s') P(s')`.

The identity is for an arbitrary finite conditional table on a finite alphabet.
`P(s)` is required to be positive, and the tar table is required to be
positive on every smoking row: otherwise an intervention can select a row the
observational conditional never divides by. A vanishing smoking marginal
contributes nothing, and the `ℝ≥0∞` ratio is the observational conditional.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.DoCalculus

open Mettapedia.ProbabilityTheory.BayesianNetworks
open BayesianNetwork
open DirectedGraph
open scoped BigOperators ENNReal

variable {β : Type} [Fintype β] [DecidableEq β] [MeasurableSpace β]

/-- Smoking graph: confounder, smoking, tar, cancer. -/
inductive Smoke
  | u
  | s
  | t
  | c
  deriving DecidableEq

instance : Fintype Smoke where
  elems := {Smoke.u, Smoke.s, Smoke.t, Smoke.c}
  complete := by intro v; cases v <;> simp

/-- `U → S`, `U → C`, `S → T`, `T → C`. There is no direct edge `S → C`. -/
def smokeGraph : DirectedGraph Smoke where
  edges a b :=
    (a = .u ∧ b = .s) ∨ (a = .u ∧ b = .c) ∨ (a = .s ∧ b = .t) ∨ (a = .t ∧ b = .c)

instance : DecidableRel smokeGraph.edges := fun a b => by
  unfold smokeGraph
  infer_instance

/-- Rank increases along every edge. -/
def smokeRank : Smoke → ℕ
  | .u => 0
  | .s => 1
  | .t => 2
  | .c => 3

lemma smoke_edge_increases {a b : Smoke} (h : smokeGraph.edges a b) :
    smokeRank a < smokeRank b := by
  cases a <;> cases b <;> simp [smokeGraph, smokeRank] at h ⊢

lemma smoke_reachable_rank {a b : Smoke} (h : smokeGraph.Reachable a b) :
    smokeRank a ≤ smokeRank b := by
  induction h with
  | refl => exact le_rfl
  | step hedge _ ih => exact le_trans (Nat.le_of_lt (smoke_edge_increases hedge)) ih

/-- The smoking graph is acyclic. -/
lemma smokeAcyclic : smokeGraph.IsAcyclic := by
  intro v ⟨src, hedge, hreach⟩
  exact (lt_irrefl _) <|
    lt_of_lt_of_le (smoke_edge_increases hedge) (smoke_reachable_rank hreach)

/-- A configuration, written `(U, S, T, C)`. -/
def smokeOf (bu bs bt bc : β) : Smoke → β
  | .u => bu
  | .s => bs
  | .t => bt
  | .c => bc

omit [Fintype β] [DecidableEq β] [MeasurableSpace β] in
lemma coord_s (bu bs bt bc : β) : (smokeOf bu bs bt bc) .s = bs := rfl

omit [Fintype β] [DecidableEq β] [MeasurableSpace β] in
lemma coord_t (bu bs bt bc : β) : (smokeOf bu bs bt bc) .t = bt := rfl

omit [Fintype β] [DecidableEq β] [MeasurableSpace β] in
lemma coord_c (bu bs bt bc : β) : (smokeOf bu bs bt bc) .c = bc := rfl

/-- Configurations are four-tuples. -/
def smokeEquiv : (Smoke → β) ≃ β × β × β × β where
  toFun f := (f .u, f .s, f .t, f .c)
  invFun
    | (bu, bs, bt, bc) => smokeOf bu bs bt bc
  left_inv := by
    intro f
    ext v
    cases v <;> rfl
  right_inv := by
    rintro ⟨bu, bs, bt, bc⟩
    rfl

lemma sum_pair {α γ : Type} [Fintype α] [Fintype γ] (g : α × γ → ℝ≥0∞) :
    ∑ p, g p = ∑ a, ∑ c, g (a, c) := by
  rw [← Finset.univ_product_univ]
  exact Finset.sum_product (Finset.univ : Finset α) (Finset.univ : Finset γ) g

omit [DecidableEq β] [MeasurableSpace β] in
lemma sum_smoke (g : (Smoke → β) → ℝ≥0∞) :
    ∑ f, g f = ∑ bu, ∑ bs, ∑ bt, ∑ bc, g (smokeOf bu bs bt bc) := by
  rw [← Equiv.sum_comp smokeEquiv.symm g]
  simp_rw [sum_pair]
  rfl

lemma prod_smoke (g : Smoke → ℝ≥0∞) :
    ∏ v, g v = g .u * (g .s * (g .t * g .c)) := by
  have huniv : (Finset.univ : Finset Smoke) =
      insert .u (insert .s (insert .t {.c})) := by
    ext v
    cases v <;> simp
  rw [huniv, Finset.prod_insert (by simp), Finset.prod_insert (by simp),
    Finset.prod_insert (by simp), Finset.prod_singleton]

omit [MeasurableSpace β] in
lemma sum_fix (a0 : β) (g : β → ℝ≥0∞) :
    ∑ a, (if a = a0 then g a else 0) = g a0 := by
  simp

omit [Fintype β] [DecidableEq β] [MeasurableSpace β] in
lemma ite_and {P Q : Prop} [Decidable P] [Decidable Q] (a : ℝ≥0∞) :
    (if P ∧ Q then a else 0) = (if P then if Q then a else 0 else 0) := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

omit [Fintype β] [DecidableEq β] [MeasurableSpace β] in
lemma ite_and3 {P Q R : Prop} [Decidable P] [Decidable Q] [Decidable R] (a : ℝ≥0∞) :
    (if P ∧ Q ∧ R then a else 0) =
      (if P then if Q then if R then a else 0 else 0 else 0) := by
  by_cases hP : P <;> by_cases hQ : Q <;> by_cases hR : R <;> simp [hP, hQ, hR]

/-- `U` has no parents. -/
lemma smoke_no_parent_u (p : ParentIdx smokeGraph .u) : False := by
  have h := (mem_parentsFinset_iff smokeGraph p.val .u).1 p.property
  cases p.val <;> simp [smokeGraph] at h

/-- The only parent of smoking is the confounder. -/
lemma smoke_only_s (p : ParentIdx smokeGraph .s) : p.val = .u := by
  have h := (mem_parentsFinset_iff smokeGraph p.val .s).1 p.property
  simp only [smokeGraph] at h
  rcases h with ⟨h1, _⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩
  · exact h1
  · cases h2
  · cases h2
  · cases h2

/-- The only parent of tar is smoking. -/
lemma smoke_only_t (p : ParentIdx smokeGraph .t) : p.val = .s := by
  have h := (mem_parentsFinset_iff smokeGraph p.val .t).1 p.property
  simp only [smokeGraph] at h
  rcases h with ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨h1, _⟩ | ⟨_, h2⟩
  · cases h2
  · cases h2
  · exact h1
  · cases h2

/-- The parents of cancer are the confounder and tar. -/
lemma smoke_parent_c (p : ParentIdx smokeGraph .c) : p.val = .u ∨ p.val = .t := by
  have h := (mem_parentsFinset_iff smokeGraph p.val .c).1 p.property
  simp only [smokeGraph] at h
  rcases h with ⟨_, h2⟩ | ⟨h1, _⟩ | ⟨_, h2⟩ | ⟨h1, _⟩
  · cases h2
  · exact Or.inl h1
  · cases h2
  · exact Or.inr h1

/-- The empty parent row at `U`. -/
def rowU : ParentFun (β := β) smokeGraph .u :=
  fun p => (smoke_no_parent_u p).elim

/-- Smoking's parent row, read as the confounder's value. -/
def rowS (bu : β) : ParentFun (β := β) smokeGraph .s :=
  fun _ => bu

/-- Tar's parent row, read as smoking's value. -/
def rowT (bs : β) : ParentFun (β := β) smokeGraph .t :=
  fun _ => bs

/-- Cancer's parent row, read as `(U, T)`. -/
def rowC (bu bt : β) : ParentFun (β := β) smokeGraph .c :=
  fun p => if p.val = .u then bu else bt

omit [Fintype β] [DecidableEq β] [MeasurableSpace β] in
lemma parent_u (f : Smoke → β) :
    parentFunOf smokeGraph f .u = rowU := by
  ext p
  exact (smoke_no_parent_u p).elim

omit [Fintype β] [DecidableEq β] [MeasurableSpace β] in
lemma parent_s (bu bs bt bc : β) :
    parentFunOf smokeGraph (smokeOf bu bs bt bc) .s = rowS bu := by
  ext p
  simp [parentFunOf, smokeOf, rowS, smoke_only_s p]

omit [Fintype β] [DecidableEq β] [MeasurableSpace β] in
lemma parent_t (bu bs bt bc : β) :
    parentFunOf smokeGraph (smokeOf bu bs bt bc) .t = rowT bs := by
  ext p
  simp [parentFunOf, smokeOf, rowT, smoke_only_t p]

omit [Fintype β] [DecidableEq β] [MeasurableSpace β] in
lemma parent_c (bu bs bt bc : β) :
    parentFunOf smokeGraph (smokeOf bu bs bt bc) .c = rowC bu bt := by
  ext p
  cases smoke_parent_c p with
  | inl h => simp [parentFunOf, smokeOf, rowC, h]
  | inr h => simp [parentFunOf, smokeOf, rowC, h]

/-- Conditional weight of the confounder. -/
noncomputable def pu (cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT)
    (bu : β) : ℝ≥0∞ :=
  cptAt smokeGraph smokeAcyclic cpt .u rowU bu

/-- Conditional weight of smoking given the confounder. -/
noncomputable def ps (cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT)
    (bu bs : β) : ℝ≥0∞ :=
  cptAt smokeGraph smokeAcyclic cpt .s (rowS bu) bs

/-- Conditional weight of tar given smoking. -/
noncomputable def pt (cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT)
    (bs bt : β) : ℝ≥0∞ :=
  cptAt smokeGraph smokeAcyclic cpt .t (rowT bs) bt

/-- Conditional weight of cancer given the confounder and tar. -/
noncomputable def pc (cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT)
    (bu bt bc : β) : ℝ≥0∞ :=
  cptAt smokeGraph smokeAcyclic cpt .c (rowC bu bt) bc

omit [DecidableEq β] in
lemma sum_pu (cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT) :
    ∑ bu, pu cpt bu = 1 :=
  BayesianNetwork.DiscreteCPT.pmf_sum_eq_one _

omit [DecidableEq β] in
lemma sum_ps (cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT) (bu : β) :
    ∑ bs, ps cpt bu bs = 1 :=
  BayesianNetwork.DiscreteCPT.pmf_sum_eq_one _

omit [DecidableEq β] in
lemma sum_pt (cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT) (bs : β) :
    ∑ bt, pt cpt bs bt = 1 :=
  BayesianNetwork.DiscreteCPT.pmf_sum_eq_one _

omit [DecidableEq β] in
lemma sum_pc (cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT) (bu bt : β) :
    ∑ bc, pc cpt bu bt bc = 1 :=
  BayesianNetwork.DiscreteCPT.pmf_sum_eq_one _

omit [Fintype β] [DecidableEq β] in
lemma pu_ne_top (cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT) (bu : β) :
    pu cpt bu ≠ ∞ :=
  (cpt.cpt .u _).apply_ne_top bu

omit [Fintype β] [DecidableEq β] in
lemma ps_ne_top (cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT) (bu bs : β) :
    ps cpt bu bs ≠ ∞ :=
  (cpt.cpt .s _).apply_ne_top bs

omit [Fintype β] [DecidableEq β] in
lemma pt_ne_top (cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT) (bs bt : β) :
    pt cpt bs bt ≠ ∞ :=
  (cpt.cpt .t _).apply_ne_top bt

omit [Fintype β] [DecidableEq β] in
lemma pc_ne_top (cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT)
    (bu bt bc : β) : pc cpt bu bt bc ≠ ∞ :=
  (cpt.cpt .c _).apply_ne_top bc

omit [Fintype β] [DecidableEq β] in
lemma node_u (cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT)
    (bu bs bt bc : β) :
    DiscreteCPT.nodeProb cpt (smokeOf bu bs bt bc) .u = pu cpt bu := by
  rw [← cptAt_eq_nodeProb smokeGraph smokeAcyclic cpt (smokeOf bu bs bt bc) .u, parent_u]
  rfl

omit [Fintype β] [DecidableEq β] in
lemma node_s (cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT)
    (bu bs bt bc : β) :
    DiscreteCPT.nodeProb cpt (smokeOf bu bs bt bc) .s = ps cpt bu bs := by
  rw [← cptAt_eq_nodeProb smokeGraph smokeAcyclic cpt (smokeOf bu bs bt bc) .s, parent_s]
  rfl

omit [Fintype β] [DecidableEq β] in
lemma node_t (cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT)
    (bu bs bt bc : β) :
    DiscreteCPT.nodeProb cpt (smokeOf bu bs bt bc) .t = pt cpt bs bt := by
  rw [← cptAt_eq_nodeProb smokeGraph smokeAcyclic cpt (smokeOf bu bs bt bc) .t, parent_t]
  rfl

omit [Fintype β] [DecidableEq β] in
lemma node_c (cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT)
    (bu bs bt bc : β) :
    DiscreteCPT.nodeProb cpt (smokeOf bu bs bt bc) .c = pc cpt bu bt bc := by
  rw [← cptAt_eq_nodeProb smokeGraph smokeAcyclic cpt (smokeOf bu bs bt bc) .c, parent_c]
  rfl

omit [Fintype β] [DecidableEq β] in
/-- The joint is the product of the four conditional weights. -/
lemma joint_smoke (cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT)
    (bu bs bt bc : β) :
    cpt.jointWeight (smokeOf bu bs bt bc) =
      pu cpt bu * (ps cpt bu bs * (pt cpt bs bt * pc cpt bu bt bc)) := by
  unfold DiscreteCPT.jointWeight
  rw [prod_smoke]
  simp [node_u, node_s, node_t, node_c]

omit [Fintype β] [DecidableEq β] in
lemma joint_ne_top (cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT)
    (f : Smoke → β) : cpt.jointWeight f ≠ ∞ := by
  unfold DiscreteCPT.jointWeight DiscreteCPT.nodeProb
  exact ENNReal.prod_ne_top fun v _ => (cpt.cpt v _).apply_ne_top _

/-- `do(S = s0)`. -/
def doSmoke (s0 : β) : Smoke → Option β :=
  fun v => if v = .s then some s0 else none

omit [Fintype β] in
lemma trunc_u (cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT)
    (s0 bu bs bt bc : β) :
    truncatedFactor smokeGraph smokeAcyclic cpt (doSmoke s0) (smokeOf bu bs bt bc) .u =
      pu cpt bu := by
  have hne : Smoke.u ≠ Smoke.s := by decide
  simp [truncatedFactor, doSmoke, hne, cptAt_eq_nodeProb, node_u]

omit [Fintype β] in
lemma trunc_s (cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT)
    (s0 bu bs bt bc : β) :
    truncatedFactor smokeGraph smokeAcyclic cpt (doSmoke s0) (smokeOf bu bs bt bc) .s =
      if bs = s0 then 1 else 0 := by
  by_cases hbs : bs = s0 <;> simp [truncatedFactor, doSmoke, smokeOf, hbs]

omit [Fintype β] in
lemma trunc_t (cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT)
    (s0 bu bs bt bc : β) :
    truncatedFactor smokeGraph smokeAcyclic cpt (doSmoke s0) (smokeOf bu bs bt bc) .t =
      pt cpt bs bt := by
  have hne : Smoke.t ≠ Smoke.s := by decide
  simp [truncatedFactor, doSmoke, hne, cptAt_eq_nodeProb, node_t]

omit [Fintype β] in
lemma trunc_c (cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT)
    (s0 bu bs bt bc : β) :
    truncatedFactor smokeGraph smokeAcyclic cpt (doSmoke s0) (smokeOf bu bs bt bc) .c =
      pc cpt bu bt bc := by
  have hne : Smoke.c ≠ Smoke.s := by decide
  simp [truncatedFactor, doSmoke, hne, cptAt_eq_nodeProb, node_c]

omit [Fintype β] in
/-- Under `do(S = s0)` the smoking factor is an indicator and the smoking table drops out. -/
lemma trunc_smoke (cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT)
    (s0 bu bs bt bc : β) :
    truncatedWeight smokeGraph smokeAcyclic cpt (doSmoke s0) (smokeOf bu bs bt bc) =
      if bs = s0 then pu cpt bu * (pt cpt bs bt * pc cpt bu bt bc) else 0 := by
  unfold truncatedWeight
  rw [prod_smoke]
  simp [trunc_u, trunc_s, trunc_t, trunc_c]

/-- Mass of an event, as a finite sum of joint weights. -/
noncomputable def obs (cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT)
    (pred : (Smoke → β) → Prop) [DecidablePred pred] : ℝ≥0∞ :=
  ∑ f, if pred f then cpt.jointWeight f else 0

omit [DecidableEq β] in
lemma obs_ne_top (cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT)
    (pred : (Smoke → β) → Prop) [DecidablePred pred] : obs cpt pred ≠ ∞ := by
  unfold obs
  refine (ENNReal.sum_ne_top).2 fun f _ => ?_
  by_cases h : pred f
  · simpa [h] using joint_ne_top cpt f
  · simp [h]

omit [Fintype β] [DecidableEq β] [MeasurableSpace β] in
lemma mul_pc_right (w x y z : ℝ≥0∞) :
    w * (x * (y * z)) = (w * (x * y)) * z := by
  rw [← mul_assoc, ← mul_assoc, mul_assoc w x y]

omit [DecidableEq β] in
lemma sum_factor_pc (cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT)
    (bu bs bt : β) :
    (∑ bc, pu cpt bu * (ps cpt bu bs * (pt cpt bs bt * pc cpt bu bt bc))) =
      pu cpt bu * (ps cpt bu bs * pt cpt bs bt) := by
  simp_rw [mul_pc_right]
  rw [← Finset.mul_sum, sum_pc, mul_one]

omit [DecidableEq β] in
lemma sum_factor_pt (cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT)
    (bu bs : β) :
    (∑ bt, pu cpt bu * (ps cpt bu bs * pt cpt bs bt)) = pu cpt bu * ps cpt bu bs := by
  simp_rw [← mul_assoc]
  rw [← Finset.mul_sum, sum_pt, mul_one]

omit [Fintype β] in
/-- The smoking indicator, stated on the four coordinates rather than on `smokeOf`. -/
lemma summand_s (cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT)
    (bs0 bu bs bt bc : β) :
    (if (smokeOf bu bs bt bc) .s = bs0 then cpt.jointWeight (smokeOf bu bs bt bc) else 0) =
      if bs = bs0 then
        pu cpt bu * (ps cpt bu bs * (pt cpt bs bt * pc cpt bu bt bc)) else 0 := by
  by_cases h : (smokeOf bu bs bt bc) .s = bs0
  · have hbs : bs = bs0 := (coord_s bu bs bt bc).symm.trans h
    rw [if_pos h, if_pos hbs, joint_smoke]
  · have hbs : bs ≠ bs0 := fun hbs => h ((coord_s bu bs bt bc).trans hbs)
    rw [if_neg h, if_neg hbs]

omit [Fintype β] in
/-- The smoking-and-tar indicator, on coordinates. -/
lemma summand_st (cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT)
    (bs0 bt0 bu bs bt bc : β) :
    (if (smokeOf bu bs bt bc) .s = bs0 ∧ (smokeOf bu bs bt bc) .t = bt0 then
        cpt.jointWeight (smokeOf bu bs bt bc) else 0) =
      if bs = bs0 then if bt = bt0 then
        pu cpt bu * (ps cpt bu bs * (pt cpt bs bt * pc cpt bu bt bc)) else 0 else 0 := by
  by_cases hs : (smokeOf bu bs bt bc) .s = bs0
  · have hbs : bs = bs0 := (coord_s bu bs bt bc).symm.trans hs
    by_cases ht : (smokeOf bu bs bt bc) .t = bt0
    · have hbt : bt = bt0 := (coord_t bu bs bt bc).symm.trans ht
      rw [if_pos ⟨hs, ht⟩, if_pos hbs, if_pos hbt, joint_smoke]
    · have hbt : bt ≠ bt0 := fun hbt => ht ((coord_t bu bs bt bc).trans hbt)
      rw [if_neg (fun h => ht h.2), if_pos hbs, if_neg hbt]
  · have hbs : bs ≠ bs0 := fun hbs => hs ((coord_s bu bs bt bc).trans hbs)
    rw [if_neg (fun h => hs h.1), if_neg hbs]

omit [Fintype β] in
/-- The cancer-tar-smoking indicator, on coordinates. -/
lemma summand_cts (cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT)
    (bs0 bt0 bc0 bu bs bt bc : β) :
    (if (smokeOf bu bs bt bc) .c = bc0 ∧ (smokeOf bu bs bt bc) .t = bt0 ∧
        (smokeOf bu bs bt bc) .s = bs0 then
        cpt.jointWeight (smokeOf bu bs bt bc) else 0) =
      if bs = bs0 then if bt = bt0 then if bc = bc0 then
        pu cpt bu * (ps cpt bu bs * (pt cpt bs bt * pc cpt bu bt bc)) else 0 else 0 else 0 := by
  by_cases hs : (smokeOf bu bs bt bc) .s = bs0
  · have hbs : bs = bs0 := (coord_s bu bs bt bc).symm.trans hs
    by_cases ht : (smokeOf bu bs bt bc) .t = bt0
    · have hbt : bt = bt0 := (coord_t bu bs bt bc).symm.trans ht
      by_cases hc : (smokeOf bu bs bt bc) .c = bc0
      · have hbc : bc = bc0 := (coord_c bu bs bt bc).symm.trans hc
        rw [if_pos ⟨hc, ht, hs⟩, if_pos hbs, if_pos hbt, if_pos hbc, joint_smoke]
      · have hbc : bc ≠ bc0 := fun hbc => hc ((coord_c bu bs bt bc).trans hbc)
        rw [if_neg (fun h => hc h.1), if_pos hbs, if_pos hbt, if_neg hbc]
    · have hbt : bt ≠ bt0 := fun hbt => ht ((coord_t bu bs bt bc).trans hbt)
      rw [if_neg (fun h => ht h.2.1), if_pos hbs, if_neg hbt]
  · have hbs : bs ≠ bs0 := fun hbs => hs ((coord_s bu bs bt bc).trans hbs)
    rw [if_neg (fun h => hs h.2.2), if_neg hbs]

omit [Fintype β] in
/-- The cancer indicator of a truncated weight, on coordinates. -/
lemma summand_do (cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT)
    (s0 c0 bu bs bt bc : β) :
    (if (smokeOf bu bs bt bc) .c = c0 then
        truncatedWeight smokeGraph smokeAcyclic cpt (doSmoke s0) (smokeOf bu bs bt bc) else 0) =
      if bc = c0 then
        (if bs = s0 then pu cpt bu * (pt cpt bs bt * pc cpt bu bt bc) else 0) else 0 := by
  by_cases hc : (smokeOf bu bs bt bc) .c = c0
  · have hbc : bc = c0 := (coord_c bu bs bt bc).symm.trans hc
    rw [if_pos hc, if_pos hbc, trunc_smoke]
  · have hbc : bc ≠ c0 := fun hbc => hc ((coord_c bu bs bt bc).trans hbc)
    rw [if_neg hc, if_neg hbc]

lemma margS_expand (cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT) (bs0 : β) :
    obs cpt (fun f => f .s = bs0) = ∑ bu, pu cpt bu * ps cpt bu bs0 := by
  unfold obs
  rw [sum_smoke]
  simp_rw [summand_s cpt bs0]
  refine Finset.sum_congr rfl fun bu _ => ?_
  have hbc : ∀ bs bt,
      (∑ bc, if bs = bs0 then
          pu cpt bu * (ps cpt bu bs * (pt cpt bs bt * pc cpt bu bt bc)) else 0) =
        if bs = bs0 then pu cpt bu * (ps cpt bu bs * pt cpt bs bt) else 0 := by
    intro bs bt
    by_cases hbs : bs = bs0
    · simp_rw [if_pos hbs]
      exact sum_factor_pc cpt bu bs bt
    · simp [hbs]
  simp_rw [hbc]
  have hbt : ∀ bs,
      (∑ bt, if bs = bs0 then pu cpt bu * (ps cpt bu bs * pt cpt bs bt) else 0) =
        if bs = bs0 then pu cpt bu * ps cpt bu bs else 0 := by
    intro bs
    by_cases hbs : bs = bs0
    · simp_rw [if_pos hbs]
      exact sum_factor_pt cpt bu bs
    · simp [hbs]
  simp_rw [hbt]
  exact sum_fix bs0 fun bs => pu cpt bu * ps cpt bu bs

lemma massTS (cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT)
    (bs0 bt0 : β) :
    obs cpt (fun f => f .s = bs0 ∧ f .t = bt0) =
      pt cpt bs0 bt0 * obs cpt (fun f => f .s = bs0) := by
  rw [margS_expand]
  unfold obs
  rw [sum_smoke]
  simp_rw [summand_st cpt bs0 bt0]
  have hsum :
      (∑ bu, ∑ bs, ∑ bt, ∑ bc,
        if bs = bs0 then if bt = bt0 then
          pu cpt bu * (ps cpt bu bs * (pt cpt bs bt * pc cpt bu bt bc)) else 0 else 0) =
        ∑ bu, pu cpt bu * (ps cpt bu bs0 * pt cpt bs0 bt0) := by
    refine Finset.sum_congr rfl fun bu _ => ?_
    have hbc : ∀ bs bt,
        (∑ bc, if bs = bs0 then if bt = bt0 then
            pu cpt bu * (ps cpt bu bs * (pt cpt bs bt * pc cpt bu bt bc)) else 0 else 0) =
          if bs = bs0 then if bt = bt0 then
            pu cpt bu * (ps cpt bu bs * pt cpt bs bt) else 0 else 0 := by
      intro bs bt
      by_cases hbs : bs = bs0 <;> by_cases hbt : bt = bt0
      · simp_rw [if_pos hbs, if_pos hbt]
        exact sum_factor_pc cpt bu bs bt
      · simp [hbs, hbt]
      · simp [hbs]
      · simp [hbs]
    simp_rw [hbc]
    have hbt : ∀ bs,
        (∑ bt, if bs = bs0 then if bt = bt0 then
            pu cpt bu * (ps cpt bu bs * pt cpt bs bt) else 0 else 0) =
          if bs = bs0 then pu cpt bu * (ps cpt bu bs0 * pt cpt bs0 bt0) else 0 := by
      intro bs
      by_cases hbs : bs = bs0
      · simp_rw [if_pos hbs]
        rw [hbs]
        exact sum_fix bt0 fun bt => pu cpt bu * (ps cpt bu bs0 * pt cpt bs0 bt)
      · simp [hbs]
    simp_rw [hbt, sum_fix]
  rw [hsum]
  simp_rw [mul_comm (ps cpt _ _) (pt cpt bs0 bt0),
    mul_left_comm (pu cpt _) (pt cpt bs0 bt0), ← Finset.mul_sum] 

lemma massCTS (cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT)
    (bs0 bt0 bc0 : β) :
    obs cpt (fun f => f .c = bc0 ∧ f .t = bt0 ∧ f .s = bs0) =
      pt cpt bs0 bt0 * ∑ bu, pu cpt bu * (ps cpt bu bs0 * pc cpt bu bt0 bc0) := by
  unfold obs
  rw [sum_smoke]
  simp_rw [summand_cts cpt bs0 bt0 bc0]
  have hsum :
      (∑ bu, ∑ bs, ∑ bt, ∑ bc,
        if bs = bs0 then if bt = bt0 then if bc = bc0 then
          pu cpt bu * (ps cpt bu bs * (pt cpt bs bt * pc cpt bu bt bc)) else 0 else 0 else 0) =
        ∑ bu, pu cpt bu * (ps cpt bu bs0 * (pt cpt bs0 bt0 * pc cpt bu bt0 bc0)) := by
    refine Finset.sum_congr rfl fun bu _ => ?_
    have hbs : ∀ bs,
        (∑ bt, ∑ bc, if bs = bs0 then if bt = bt0 then if bc = bc0 then
            pu cpt bu * (ps cpt bu bs * (pt cpt bs bt * pc cpt bu bt bc)) else 0 else 0 else 0) =
          if bs = bs0 then
            pu cpt bu * (ps cpt bu bs0 * (pt cpt bs0 bt0 * pc cpt bu bt0 bc0)) else 0 := by
      intro bs
      by_cases hbs : bs = bs0
      · simp_rw [if_pos hbs]
        rw [hbs]
        have hbt : ∀ bt,
            (∑ bc, if bt = bt0 then if bc = bc0 then
                pu cpt bu * (ps cpt bu bs0 * (pt cpt bs0 bt * pc cpt bu bt bc)) else 0 else 0) =
              if bt = bt0 then
                pu cpt bu * (ps cpt bu bs0 * (pt cpt bs0 bt0 * pc cpt bu bt0 bc0)) else 0 := by
          intro bt
          by_cases hbt : bt = bt0
          · simp_rw [if_pos hbt]
            rw [hbt]
            exact sum_fix bc0 fun bc =>
              pu cpt bu * (ps cpt bu bs0 * (pt cpt bs0 bt0 * pc cpt bu bt0 bc))
          · simp [hbt]
        simp_rw [hbt, sum_fix]
      · simp [hbs]
    simp_rw [hbs, sum_fix]
  rw [hsum]
  have hcomm : ∀ bu,
      pu cpt bu * (ps cpt bu bs0 * (pt cpt bs0 bt0 * pc cpt bu bt0 bc0)) =
        pt cpt bs0 bt0 * (pu cpt bu * (ps cpt bu bs0 * pc cpt bu bt0 bc0)) := by
    intro bu
    rw [mul_left_comm (ps cpt bu bs0) (pt cpt bs0 bt0),
      mul_left_comm (pu cpt bu) (pt cpt bs0 bt0)]
  simp_rw [hcomm, ← Finset.mul_sum]

/-- Mass of `C = c0` under `do(S = s0)`. -/
noncomputable def doMass (cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT)
    (s0 c0 : β) : ℝ≥0∞ :=
  ∑ f, if f .c = c0 then
    truncatedWeight smokeGraph smokeAcyclic cpt (doSmoke s0) f else 0

lemma doMass_expand (cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT)
    (s0 c0 : β) :
    doMass cpt s0 c0 = ∑ bu, ∑ bt, pu cpt bu * (pt cpt s0 bt * pc cpt bu bt c0) := by
  unfold doMass
  rw [sum_smoke]
  simp_rw [summand_do cpt s0 c0]
  refine Finset.sum_congr rfl fun bu _ => ?_
  have hswap :
      (∑ bs, ∑ bt, ∑ bc,
        if bc = c0 then
          (if bs = s0 then pu cpt bu * (pt cpt bs bt * pc cpt bu bt bc) else 0) else 0) =
        ∑ bt, ∑ bs, ∑ bc,
          if bs = s0 then if bc = c0 then
            pu cpt bu * (pt cpt bs bt * pc cpt bu bt bc) else 0 else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun bs _ => Finset.sum_congr rfl fun bt _ =>
      Finset.sum_congr rfl fun bc _ => ?_
    by_cases hbs : bs = s0 <;> by_cases hbc : bc = c0 <;> simp [hbs, hbc]
  rw [hswap]
  refine Finset.sum_congr rfl fun bt _ => ?_
  have hbs : ∀ bs,
      (∑ bc, if bs = s0 then if bc = c0 then
          pu cpt bu * (pt cpt bs bt * pc cpt bu bt bc) else 0 else 0) =
        if bs = s0 then pu cpt bu * (pt cpt s0 bt * pc cpt bu bt c0) else 0 := by
    intro bs
    by_cases hbs : bs = s0
    · simp_rw [if_pos hbs]
      rw [hbs]
      exact sum_fix c0 fun bc => pu cpt bu * (pt cpt s0 bt * pc cpt bu bt bc)
    · simp [hbs]
  simp_rw [hbs]
  exact sum_fix s0 fun _ => pu cpt bu * (pt cpt s0 bt * pc cpt bu bt c0)

lemma ratio_term (cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT)
    (bs bt bc : β) (hpos : pt cpt bs bt ≠ 0) :
    (obs cpt (fun f => f .c = bc ∧ f .t = bt ∧ f .s = bs) /
        obs cpt (fun f => f .s = bs ∧ f .t = bt)) *
      obs cpt (fun f => f .s = bs) =
        ∑ bu, pu cpt bu * (ps cpt bu bs * pc cpt bu bt bc) := by
  rw [massCTS, massTS]
  set M : ℝ≥0∞ := obs cpt (fun f => f .s = bs)
  set I : ℝ≥0∞ := ∑ bu, pu cpt bu * (ps cpt bu bs * pc cpt bu bt bc)
  by_cases hM : M = 0
  · have hI : I = 0 := by
      unfold I
      have hM' : obs cpt (fun f => f .s = bs) = 0 := by simpa [M] using hM
      rw [margS_expand] at hM'
      have hterm :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun bu _ => bot_le (a := pu cpt bu * ps cpt bu bs))).1 hM'
      refine Finset.sum_eq_zero fun bu _ => ?_
      rw [← mul_assoc, hterm bu (Finset.mem_univ bu), zero_mul]
    simp [hM, hI]
  · have hMtop : M ≠ ∞ := by simpa [M] using obs_ne_top cpt (fun f => f .s = bs)
    rw [ENNReal.mul_div_mul_left I M hpos (pt_ne_top cpt bs bt),
      ENNReal.div_mul_cancel hM hMtop]

lemma inner_expand (cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT)
    (bt0 bc0 : β) (hposT : ∀ bs bt, pt cpt bs bt ≠ 0) :
    (∑ bs, (obs cpt (fun f => f .c = bc0 ∧ f .t = bt0 ∧ f .s = bs) /
        obs cpt (fun f => f .s = bs ∧ f .t = bt0)) *
        obs cpt (fun f => f .s = bs)) =
      ∑ bu, pu cpt bu * pc cpt bu bt0 bc0 := by
  simp_rw [ratio_term cpt _ bt0 bc0 (hposT _ bt0)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun bu _ => ?_
  have hre : ∀ bs,
      pu cpt bu * (ps cpt bu bs * pc cpt bu bt0 bc0) =
        (pu cpt bu * pc cpt bu bt0 bc0) * ps cpt bu bs := by
    intro bs
    rw [mul_comm (ps cpt bu bs) (pc cpt bu bt0 bc0), ← mul_assoc]
  simp_rw [hre, ← Finset.mul_sum, sum_ps, mul_one]

/-- **Front-door formula** for smoking, tar, and cancer.

`P(C = c0 | do(S = s0)) = Σ_t P(T = t | S = s0) Σ_{s'} P(C = c0 | T = t, S = s') P(S = s')`.

The ratios are the `ℝ≥0∞` quotients of the finite sums. The smoking marginal at
`s0` is positive, and every tar row is positive, so each quotient the
intervention can meet is the observational conditional. A smoking value of
marginal zero contributes zero on both readings, because in `ℝ≥0∞` the quotient
`0 / 0` is zero.
-/
theorem frontDoor (cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT)
    (s0 c0 : β)
    (hposS : obs cpt (fun f => f .s = s0) ≠ 0)
    (hposT : ∀ bs bt, pt cpt bs bt ≠ 0) :
    doMass cpt s0 c0 =
      ∑ bt, (obs cpt (fun f => f .s = s0 ∧ f .t = bt) /
          obs cpt (fun f => f .s = s0)) *
        (∑ bs, (obs cpt (fun f => f .c = c0 ∧ f .t = bt ∧ f .s = bs) /
            obs cpt (fun f => f .s = bs ∧ f .t = bt)) *
          obs cpt (fun f => f .s = bs)) := by
  rw [doMass_expand]
  have hdiv : ∀ bt,
      (pt cpt s0 bt * obs cpt (fun f => f .s = s0)) / obs cpt (fun f => f .s = s0) =
        pt cpt s0 bt :=
    fun bt => ENNReal.mul_div_cancel_right hposS (obs_ne_top cpt _)
  simp_rw [inner_expand cpt _ c0 hposT, massTS, hdiv]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun bt _ => ?_
  have hre : ∀ bu,
      pu cpt bu * (pt cpt s0 bt * pc cpt bu bt c0) =
        pt cpt s0 bt * (pu cpt bu * pc cpt bu bt c0) := by
    intro bu
    rw [mul_left_comm (pu cpt bu) (pt cpt s0 bt)]
  simp_rw [hre, ← Finset.mul_sum]

end Mettapedia.GSLT.Causality.DoCalculus
