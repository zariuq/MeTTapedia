import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mettapedia.GSLT.Causality.DoCalculus.ExchangeDelete
import Mettapedia.GSLT.Causality.DoCalculus.RegimeGraph

/-!
# Regime variables carry the do-calculus

An intervention on `Z` is conditioning on a regime parent. Each vertex `v` of
`Z` gains a parent `F_v` with two values. Idle keeps the conditional table.
The other value replaces that table by the point mass of the intervention.
The joint of `do(Z = z)` is the augmented joint conditioned on every regime
in `Z` taking that value, up to the positive finite prior of those regimes.
The observational joint is the same augmentation conditioned on idle.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.DoCalculus

open Mettapedia.ProbabilityTheory.BayesianNetworks
open Mettapedia.ProbabilityTheory.BayesianNetworks.DiscreteLocalMarkov
open BayesianNetwork
open DirectedGraph
open DSeparation
open MeasureTheory
open scoped BigOperators ENNReal

/-- Idle keeps the conditional table. `force` replaces it by a point mass. -/
inductive Regime where
  | idle
  | force
  deriving DecidableEq, Inhabited

instance : Fintype Regime where
  elems := {Regime.idle, Regime.force}
  complete r := by cases r <;> simp

instance : MeasurableSpace Regime := ⊤

def regimeBool : Regime ≃ Bool where
  toFun
    | .idle => false
    | .force => true
  invFun
    | false => .idle
    | true => .force
  left_inv r := by cases r <;> rfl
  right_inv b := by cases b <;> rfl

lemma half_sums : ∑ _r : Regime, (2 : ℝ≥0∞)⁻¹ = 1 := by
  have hswap : ∑ _r : Regime, (2 : ℝ≥0∞)⁻¹ = ∑ _b : Bool, (2 : ℝ≥0∞)⁻¹ := by
    symm
    exact Equiv.sum_comp regimeBool.symm fun _ => (2 : ℝ≥0∞)⁻¹
  rw [hswap, Fintype.sum_bool, ← two_mul]
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

noncomputable def halfRegime : PMF Regime :=
  PMF.ofFintype (fun _ => (2 : ℝ≥0∞)⁻¹) half_sums

variable {V : Type} [Fintype V] [DecidableEq V]

variable (β : Type) [Fintype β] [DecidableEq β] [Inhabited β] [MeasurableSpace β]
  [MeasurableSingletonClass β] [StandardBorelSpace β]

/-- Observed vertices keep the model alphabet. Regime vertices are binary. -/
abbrev augState : AugV V → Type
  | .obs _ => β
  | .regime _ => Regime

instance (a : AugV V) : Fintype (augState β a) := by
  cases a <;> infer_instance

instance (a : AugV V) : Inhabited (augState β a) := by
  cases a <;> infer_instance

instance (a : AugV V) : MeasurableSpace (augState β a) := by
  cases a <;> infer_instance

instance (a : AugV V) : MeasurableSingletonClass (augState β a) := by
  cases a <;> infer_instance

instance (a : AugV V) : StandardBorelSpace (augState β a) := by
  cases a <;> infer_instance

def obsOf (ω : ∀ a : AugV V, augState β a) : V → β :=
  fun v => ω (AugV.obs v)

def regimeOf (ω : ∀ a : AugV V, augState β a) : V → Regime :=
  fun v => ω (AugV.regime v)

def joinAug (p : (V → β) × (V → Regime)) : ∀ a : AugV V, augState β a
  | .obs v => p.1 v
  | .regime v => p.2 v

def augSplit : (∀ a : AugV V, augState β a) ≃ ((V → β) × (V → Regime)) where
  toFun ω := (obsOf β ω, regimeOf β ω)
  invFun := joinAug β
  left_inv ω := by
    funext a
    cases a <;> rfl
  right_inv p := by
    rcases p with ⟨_f, _r⟩
    rfl

variable (graph : DirectedGraph V) [DecidableRel graph.edges]
variable (hAcyclic : graph.IsAcyclic)

abbrev augNet (X Z : Finset V) : BayesianNetwork (AugV V) where
  graph := ga graph X Z
  acyclic := ga_acyclic graph hAcyclic X Z
  stateSpace := augState β
  measurableSpace := fun _ => inferInstance

instance (X Z : Finset V) :
    StandardBorelSpace ((augNet β graph hAcyclic X Z).JointSpace) :=
  StandardBorelSpace.pi_countable

omit [Fintype V] [Fintype β] [DecidableEq β] [Inhabited β]
  [MeasurableSingletonClass β] [StandardBorelSpace β] [DecidableRel graph.edges] in
lemma regimeParent_mem {X Z : Finset V} {v : V} (hvZ : v ∈ Z) (hvX : v ∉ X) :
    AugV.regime v ∈ (augNet β graph hAcyclic X Z).parents (AugV.obs v) := by
  have hedge := ga_regime_at graph X Z hvZ hvX
  simpa [BayesianNetwork.parents, DirectedGraph.parents] using hedge

def copiedAssign {X Z : Finset V} {v : V}
    (pa : (augNet β graph hAcyclic X Z).ParentAssignment (AugV.obs v))
    (hvX : v ∉ X) :
    (network (β := β) graph hAcyclic).ParentAssignment v :=
  fun u hu =>
    pa (AugV.obs u) <| by
      have hedge : graph.edges u v := by
        simpa [network, BayesianNetwork.parents, DirectedGraph.parents] using hu
      simpa [BayesianNetwork.parents, DirectedGraph.parents] using
        (ga_obs_edge graph X Z).2 ⟨hedge, hvX⟩

noncomputable def augCPT
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (X Z : Finset V) (x z : V → β) :
    (augNet β graph hAcyclic X Z).DiscreteCPT where
  cpt
    | .regime _, _ => halfRegime
    | .obs v, pa =>
        if hvX : v ∈ X then
          PMF.pure (x v)
        else if hvZ : v ∈ Z then
          if _hforce : pa (AugV.regime v) (regimeParent_mem β graph hAcyclic hvZ hvX) =
              Regime.force then
            PMF.pure (z v)
          else
            cpt.cpt v (copiedAssign β graph hAcyclic pa hvX)
        else
          cpt.cpt v (copiedAssign β graph hAcyclic pa hvX)

lemma aug_parts_disjoint :
    Disjoint (Finset.univ.image (AugV.obs : V → AugV V))
      (Finset.univ.image (AugV.regime : V → AugV V)) := by
  rw [Finset.disjoint_left]
  intro a hobs hreg
  rcases Finset.mem_image.mp hobs with ⟨_, _, rfl⟩
  rcases Finset.mem_image.mp hreg with ⟨_, _, h⟩
  cases h

lemma aug_univ :
    (Finset.univ : Finset (AugV V)) =
      Finset.univ.image AugV.obs ∪ Finset.univ.image AugV.regime := by
  ext a
  cases a <;> simp

omit [Fintype V] [DecidableEq V] in
lemma obs_injective {u v : V} (h : AugV.obs u = AugV.obs v) : u = v := by
  cases h
  rfl

omit [Fintype V] [DecidableEq V] in
lemma regime_injective {u v : V} (h : AugV.regime u = AugV.regime v) : u = v := by
  cases h
  rfl

lemma prod_aug (f : AugV V → ℝ≥0∞) :
    ∏ a, f a = (∏ v, f (AugV.obs v)) * (∏ v, f (AugV.regime v)) := by
  rw [aug_univ, Finset.prod_union aug_parts_disjoint]
  rw [Finset.prod_image (fun u _ v _ h => obs_injective h)]
  rw [Finset.prod_image (fun u _ v _ h => regime_injective h)]

omit [Fintype V] [Fintype β] [DecidableEq β] [Inhabited β]
  [MeasurableSingletonClass β] [StandardBorelSpace β] [DecidableRel graph.edges] in
lemma aug_regime_node
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (X Z : Finset V) (x z : V → β)
    (ω : (augNet β graph hAcyclic X Z).JointSpace) (v : V) :
    DiscreteCPT.nodeProb (augCPT β graph hAcyclic cpt X Z x z) ω (AugV.regime v) =
      (2 : ℝ≥0∞)⁻¹ := by
  unfold DiscreteCPT.nodeProb DiscreteCPT.parentAssignOfConfig augCPT halfRegime
  simp [PMF.ofFintype_apply]

omit [Fintype β] [DecidableEq β] [Inhabited β]
  [MeasurableSingletonClass β] [StandardBorelSpace β] [DecidableRel graph.edges] in
lemma aug_regime_prod
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (X Z : Finset V) (x z : V → β)
    (ω : (augNet β graph hAcyclic X Z).JointSpace) :
    ∏ v, DiscreteCPT.nodeProb (augCPT β graph hAcyclic cpt X Z x z) ω (AugV.regime v) =
      (2 : ℝ≥0∞)⁻¹ ^ Fintype.card V := by
  simp only [aug_regime_node β graph hAcyclic cpt X Z x z ω]
  rw [Finset.prod_const, Finset.card_univ]

omit [Fintype β] [Inhabited β] [MeasurableSingletonClass β] [StandardBorelSpace β] in
lemma aug_obs_force
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    {X Z : Finset V} (_hXZ : Disjoint X Z) (x z : V → β)
    (ω : (augNet β graph hAcyclic X Z).JointSpace)
    (hreg : ∀ v ∈ Z, regimeOf β ω v = Regime.force) (v : V) :
    DiscreteCPT.nodeProb (augCPT β graph hAcyclic cpt X Z x z) ω (AugV.obs v) =
      truncatedFactor graph hAcyclic cpt (doFinset (X ∪ Z) (mergeAssign X x z))
        (obsOf β ω) v := by
  simp only [DiscreteCPT.nodeProb, DiscreteCPT.parentAssignOfConfig, augCPT]
  by_cases hvX : v ∈ X
  · rw [dif_pos hvX, PMF.pure_apply, truncatedFactor,
      doFinset_eq_some (Finset.mem_union.mpr (Or.inl hvX))]
    simp [mergeAssign, hvX, obsOf]
  · by_cases hvZ : v ∈ Z
    · have hr : ω (AugV.regime v) = Regime.force := by
        simpa [regimeOf] using hreg v hvZ
      rw [dif_neg hvX, dif_pos hvZ]
      unfold copiedAssign DiscreteCPT.parentAssignOfConfig
      split
      · rw [PMF.pure_apply, truncatedFactor,
          doFinset_eq_some (Finset.mem_union.mpr (Or.inr hvZ))]
        have hzv : mergeAssign X x z v = z v := by
          unfold mergeAssign
          rw [if_neg hvX]
        by_cases hEq : ω (AugV.obs v) = z v
        · simp [obsOf, hzv, hEq]
        · have hnot : obsOf β ω v ≠ mergeAssign X x z v := by
            simpa [obsOf, hzv] using hEq
          simp [if_neg hEq, if_neg hnot]
      · rename_i hneg
        exact absurd hr hneg
    · have hnot : v ∉ X ∪ Z := by
        intro hmem
        rcases Finset.mem_union.mp hmem with hX | hZ
        · exact hvX hX
        · exact hvZ hZ
      rw [dif_neg hvX, dif_neg hvZ, truncatedFactor, doFinset_eq_none hnot]
      unfold cptAt
      congr

omit [Fintype β] [Inhabited β] [MeasurableSingletonClass β] [StandardBorelSpace β] in
lemma aug_obs_idle
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    {X Z : Finset V} (x z : V → β)
    (ω : (augNet β graph hAcyclic X Z).JointSpace)
    (hreg : ∀ v ∈ Z, regimeOf β ω v = Regime.idle) (v : V) :
    DiscreteCPT.nodeProb (augCPT β graph hAcyclic cpt X Z x z) ω (AugV.obs v) =
      truncatedFactor graph hAcyclic cpt (doFinset X x) (obsOf β ω) v := by
  simp only [DiscreteCPT.nodeProb, DiscreteCPT.parentAssignOfConfig, augCPT]
  by_cases hvX : v ∈ X
  · rw [dif_pos hvX, PMF.pure_apply, truncatedFactor, doFinset_eq_some hvX]
    by_cases hEq : ω (AugV.obs v) = x v
    · simp [obsOf, hEq]
    · simp [obsOf, hEq]
  · by_cases hvZ : v ∈ Z
    · have hr : ω (AugV.regime v) = Regime.idle := by
        simpa [regimeOf] using hreg v hvZ
      rw [dif_neg hvX, dif_pos hvZ]
      unfold copiedAssign DiscreteCPT.parentAssignOfConfig
      split
      · rename_i hforce
        rw [hr] at hforce
        cases hforce
      · rw [truncatedFactor, doFinset_eq_none hvX]
        unfold cptAt toParentAssignment parentFunOf obsOf
        rfl
    · rw [dif_neg hvX, dif_neg hvZ, truncatedFactor, doFinset_eq_none hvX]
      unfold cptAt
      congr

omit [Fintype β] [Inhabited β] [MeasurableSingletonClass β] [StandardBorelSpace β] in
lemma aug_weight_force
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    {X Z : Finset V} (hXZ : Disjoint X Z) (x z : V → β)
    (ω : (augNet β graph hAcyclic X Z).JointSpace)
    (hreg : ∀ v ∈ Z, regimeOf β ω v = Regime.force) :
    (augCPT β graph hAcyclic cpt X Z x z).jointWeight ω =
      (2 : ℝ≥0∞)⁻¹ ^ Fintype.card V *
        truncatedWeight graph hAcyclic cpt
          (doFinset (X ∪ Z) (mergeAssign X x z)) (obsOf β ω) := by
  unfold DiscreteCPT.jointWeight truncatedWeight
  rw [prod_aug]
  rw [aug_regime_prod β graph hAcyclic cpt X Z x z ω]
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  exact aug_obs_force β graph hAcyclic cpt hXZ x z ω hreg v

omit [Fintype β] [Inhabited β] [MeasurableSingletonClass β] [StandardBorelSpace β] in
lemma aug_weight_idle
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    {X Z : Finset V} (x z : V → β)
    (ω : (augNet β graph hAcyclic X Z).JointSpace)
    (hreg : ∀ v ∈ Z, regimeOf β ω v = Regime.idle) :
    (augCPT β graph hAcyclic cpt X Z x z).jointWeight ω =
      (2 : ℝ≥0∞)⁻¹ ^ Fintype.card V *
        truncatedWeight graph hAcyclic cpt (doFinset X x) (obsOf β ω) := by
  unfold DiscreteCPT.jointWeight truncatedWeight
  rw [prod_aug]
  rw [aug_regime_prod β graph hAcyclic cpt X Z x z ω]
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  exact aug_obs_idle β graph hAcyclic cpt x z ω hreg v

/-- Sum of the indicator of one fixed regime pattern on `Z`. -/
lemma regimePattern_mass (target : Regime) (Z : Finset V) :
    ∑ r : V → Regime, (if ∀ v ∈ Z, r v = target then (1 : ℝ≥0∞) else 0) ≠ 0 ∧
      ∑ r : V → Regime, (if ∀ v ∈ Z, r v = target then (1 : ℝ≥0∞) else 0) ≠ ⊤ := by
  let ind : (V → Regime) → ℝ≥0∞ :=
    fun r => if ∀ v ∈ Z, r v = target then 1 else 0
  let r0 : V → Regime := fun _ => target
  have hterm : ind r0 = 1 := by
    simp [ind, r0]
  have hge : (1 : ℝ≥0∞) ≤ ∑ r, ind r := by
    rw [← hterm]
    exact Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ r0)
  have hne0 : ∑ r, ind r ≠ 0 :=
    fun h0 => one_ne_zero (le_antisymm (hge.trans_eq h0) bot_le)
  have hle : ∑ r, ind r ≤ ∑ _ : V → Regime, (1 : ℝ≥0∞) := by
    refine Finset.sum_le_sum fun r _ => ?_
    simp only [ind]
    split_ifs
    · exact le_rfl
    · exact bot_le
  have htop : ∑ r, ind r ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ hle
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.one_ne_top
  exact ⟨hne0, htop⟩

lemma const_ne (Z : Finset V) (target : Regime) :
    let mass := ∑ r : V → Regime, (if ∀ v ∈ Z, r v = target then (1 : ℝ≥0∞) else 0)
    (2 : ℝ≥0∞)⁻¹ ^ Fintype.card V * mass ≠ 0 ∧
      (2 : ℝ≥0∞)⁻¹ ^ Fintype.card V * mass ≠ ⊤ := by
  intro mass
  have hmass := regimePattern_mass target Z
  have hbase0 : (2 : ℝ≥0∞)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr (by norm_num)
  have hbaseTop : (2 : ℝ≥0∞)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (by norm_num)
  have hpow0 : (2 : ℝ≥0∞)⁻¹ ^ Fintype.card V ≠ 0 := ENNReal.pow_ne_zero hbase0 _
  have hpowTop : (2 : ℝ≥0∞)⁻¹ ^ Fintype.card V ≠ ⊤ :=
    ENNReal.pow_ne_top_iff.mpr (Or.inl hbaseTop)
  exact ⟨mul_ne_zero hpow0 hmass.1, ENNReal.mul_ne_top hpowTop hmass.2⟩

omit [DecidableEq β] [MeasurableSingletonClass β] [DecidableRel graph.edges] in
lemma mem_assignEvent
    (X Z : Finset V) {S : Finset (AugV V)}
    (xS : ∀ p : ((S : Set (AugV V))),
      (augNet β graph hAcyclic X Z).stateSpace p.1)
    (ω : (augNet β graph hAcyclic X Z).JointSpace) :
    ω ∈ assignEvent (bn := augNet β graph hAcyclic X Z) S xS ↔
      restrictToSet (bn := augNet β graph hAcyclic X Z) (S : Set (AugV V)) ω = xS := by
  rw [assignEvent, eventOfConstraints_constraintsOfRestrict]
  simp [Set.mem_preimage, Set.mem_singleton_iff]

/-! ## Slice of the augmented joint -/

abbrev obsImage (S : Finset V) : Finset (AugV V) :=
  Finset.image AugV.obs S

abbrev regimeImage (Z : Finset V) : Finset (AugV V) :=
  Finset.image AugV.regime Z

/-- Read the anchor on observed coordinates. The regime branch is unused. -/
def obsRead (S : Finset V) (anchor : V → β)
    (p : ((obsImage S : Finset (AugV V)) : Set (AugV V))) : augState β p.1 :=
  match p.1 with
  | .obs v => anchor v
  | .regime _ => Regime.idle

/-- Read one regime value on the regime coordinates. The observed branch is unused. -/
def regimeRead (Z : Finset V) (target : Regime)
    (p : ((regimeImage Z : Finset (AugV V)) : Set (AugV V))) : augState β p.1 :=
  match p.1 with
  | .obs _ => default
  | .regime _ => target

omit [Fintype V] [Fintype β] [Inhabited β] [MeasurableSpace β]
  [MeasurableSingletonClass β] [StandardBorelSpace β] [DecidableRel graph.edges] hAcyclic in
lemma regime_mem_image {Z : Finset V} {v : V} :
    AugV.regime v ∈ regimeImage Z ↔ v ∈ Z := by
  constructor
  · intro hmem
    rcases Finset.mem_image.mp hmem with ⟨_, _, heq⟩
    cases heq
    assumption
  · intro hmem
    exact Finset.mem_image.mpr ⟨v, hmem, rfl⟩

omit [Fintype V] [Fintype β] [DecidableEq β] [Inhabited β]
  [MeasurableSingletonClass β] [StandardBorelSpace β] [DecidableRel graph.edges] in
lemma restrict_obs_iff (X Z S : Finset V) (anchor : V → β)
    (ω : (augNet β graph hAcyclic X Z).JointSpace) :
    restrictToSet (bn := augNet β graph hAcyclic X Z)
        ((obsImage S : Finset (AugV V)) : Set (AugV V)) ω = obsRead β S anchor ↔
      ∀ v ∈ S, obsOf β ω v = anchor v := by
  constructor
  · intro h v hv
    have hv' : AugV.obs v ∈ obsImage S := (obs_mem_image).2 hv
    have hfun := congrFun h ⟨AugV.obs v, Finset.mem_coe.mpr hv'⟩
    simpa [restrictToSet, obsRead, obsOf] using hfun
  · intro h
    ext p
    cases p with
    | mk a ha =>
        cases a with
        | obs v =>
            have hv : v ∈ S := (obs_mem_image).1 (Finset.mem_coe.mp ha)
            simp [restrictToSet, obsRead]
            simpa [obsOf] using h v hv
        | regime v =>
            rcases Finset.mem_image.mp (Finset.mem_coe.mp ha) with ⟨_, _, heq⟩
            cases heq

omit [Fintype V] [Fintype β] [DecidableEq β] [MeasurableSingletonClass β]
  [StandardBorelSpace β] [DecidableRel graph.edges] in
lemma restrict_regime_iff (X Z0 Z : Finset V) (target : Regime)
    (ω : (augNet β graph hAcyclic X Z0).JointSpace) :
    restrictToSet (bn := augNet β graph hAcyclic X Z0)
        ((regimeImage Z : Finset (AugV V)) : Set (AugV V)) ω =
      regimeRead β Z target ↔
      ∀ v ∈ Z, regimeOf β ω v = target := by
  constructor
  · intro h v hv
    have hv' : AugV.regime v ∈ regimeImage Z := (regime_mem_image (Z := Z)).2 hv
    have hfun := congrFun h ⟨AugV.regime v, Finset.mem_coe.mpr hv'⟩
    simpa [restrictToSet, regimeRead, regimeOf] using hfun
  · intro h
    ext p
    cases p with
    | mk a ha =>
        cases a with
        | regime v =>
            have hv : v ∈ Z := (regime_mem_image (Z := Z)).1 (Finset.mem_coe.mp ha)
            simp [restrictToSet, regimeRead]
            simpa [regimeOf] using h v hv
        | obs v =>
            rcases Finset.mem_image.mp (Finset.mem_coe.mp ha) with ⟨_, _, heq⟩
            cases heq

/-- Prior mass of one regime pattern on `Z`, including the free regimes. -/
noncomputable def regimeConst (Z : Finset V) (target : Regime) : ℝ≥0∞ :=
  (2 : ℝ≥0∞)⁻¹ ^ Fintype.card V *
    ∑ r : V → Regime, if ∀ v ∈ Z, r v = target then (1 : ℝ≥0∞) else 0

lemma regimeConst_spec (Z : Finset V) (target : Regime) :
    regimeConst Z target ≠ 0 ∧ regimeConst Z target ≠ ⊤ :=
  const_ne Z target

omit [DecidableEq β] [Inhabited β] [StandardBorelSpace β] [DecidableRel graph.edges] in
lemma measurable_aug (X Z : Finset V)
    (s : Set ((augNet β graph hAcyclic X Z).JointSpace)) : MeasurableSet s := by
  have hs : s = ⋃ ω ∈ s, {ω} := by
    ext ω
    simp
  rw [hs]
  exact MeasurableSet.biUnion (Set.toFinite s).countable fun ω _ =>
    measurableSet_singleton ω

omit [Inhabited β] [MeasurableSingletonClass β] [StandardBorelSpace β] in
lemma slice_sum_force
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    {X Z : Finset V} (hXZ : Disjoint X Z) (x z anchor : V → β) (S : Finset V) :
    (∑ ω : (augNet β graph hAcyclic X Z).JointSpace,
        if agreesOn S anchor (obsOf β ω) = true ∧
            ∀ v ∈ Z, regimeOf β ω v = Regime.force then
          (augCPT β graph hAcyclic cpt X Z x z).jointWeight ω else 0) =
      regimeConst Z Regime.force *
        truncSlice graph hAcyclic cpt
          (doFinset (X ∪ Z) (mergeAssign X x z)) S anchor := by
  let g : (augNet β graph hAcyclic X Z).JointSpace → ℝ≥0∞ := fun ω =>
    if agreesOn S anchor (obsOf β ω) = true ∧
        ∀ v ∈ Z, regimeOf β ω v = Regime.force then
      (augCPT β graph hAcyclic cpt X Z x z).jointWeight ω else 0
  have hre : ∑ ω, g ω =
      ∑ p : (V → β) × (V → Regime), g ((augSplit β).symm p) :=
    (Equiv.sum_comp (augSplit β).symm g).symm
  rw [hre, Fintype.sum_prod_type]
  have hterm : ∀ f r,
      g ((augSplit β).symm (f, r)) =
        (if agreesOn S anchor f = true then
          truncatedWeight graph hAcyclic cpt
            (doFinset (X ∪ Z) (mergeAssign X x z)) f else 0) *
        (if ∀ v ∈ Z, r v = Regime.force then (2 : ℝ≥0∞)⁻¹ ^ Fintype.card V else 0) := by
    intro f r
    rw [show (augSplit β).symm (f, r) = joinAug β (f, r) from rfl]
    by_cases hA : agreesOn S anchor f = true
    · by_cases hR : ∀ v ∈ Z, r v = Regime.force
      · have hreg : ∀ v ∈ Z, regimeOf β (joinAug β (f, r)) v = Regime.force := by
          intro v hv
          simpa [regimeOf, joinAug] using hR v hv
        have hobs : obsOf β (joinAug β (f, r)) = f := by
          funext v
          rfl
        have hcond :
            agreesOn S anchor (obsOf β (joinAug β (f, r))) = true ∧
              ∀ v ∈ Z, regimeOf β (joinAug β (f, r)) v = Regime.force :=
          ⟨by simpa [hobs] using hA, hreg⟩
        unfold g
        rw [if_pos hcond, if_pos hA, if_pos hR]
        have hw :=
          aug_weight_force β graph hAcyclic cpt hXZ x z (joinAug β (f, r)) hreg
        rw [hobs] at hw
        rw [hw, mul_comm]
      · have hnot : ¬ (agreesOn S anchor (obsOf β (joinAug β (f, r))) = true ∧
            ∀ v ∈ Z, regimeOf β (joinAug β (f, r)) v = Regime.force) := by
          intro hboth
          exact hR (fun v hv => by simpa [regimeOf, joinAug] using hboth.2 v hv)
        unfold g
        simp only [if_neg hnot, if_pos hA, if_neg hR, mul_zero]
    · have hnot : ¬ (agreesOn S anchor (obsOf β (joinAug β (f, r))) = true ∧
          ∀ v ∈ Z, regimeOf β (joinAug β (f, r)) v = Regime.force) := by
        intro hboth
        have hobs : obsOf β (joinAug β (f, r)) = f := by
          funext v
          rfl
        exact hA (by simpa [hobs] using hboth.1)
      unfold g
      simp only [if_neg hnot, if_neg hA, zero_mul]
  simp_rw [hterm]
  have hfac : ∀ f, (∑ r : V → Regime,
      (if agreesOn S anchor f = true then
        truncatedWeight graph hAcyclic cpt
          (doFinset (X ∪ Z) (mergeAssign X x z)) f else 0) *
      (if ∀ v ∈ Z, r v = Regime.force then (2 : ℝ≥0∞)⁻¹ ^ Fintype.card V else 0)) =
      (if agreesOn S anchor f = true then
        truncatedWeight graph hAcyclic cpt
          (doFinset (X ∪ Z) (mergeAssign X x z)) f else 0) *
      (∑ r : V → Regime, if ∀ v ∈ Z, r v = Regime.force then
        (2 : ℝ≥0∞)⁻¹ ^ Fintype.card V else 0) :=
    fun f => (Finset.mul_sum _ _ _).symm
  simp_rw [hfac]
  rw [← Finset.sum_mul]
  have hconst : ∑ r : V → Regime,
      (if ∀ v ∈ Z, r v = Regime.force then (2 : ℝ≥0∞)⁻¹ ^ Fintype.card V else 0) =
      regimeConst Z Regime.force := by
    unfold regimeConst
    have hscale : ∀ r : V → Regime,
        (if ∀ v ∈ Z, r v = Regime.force then (2 : ℝ≥0∞)⁻¹ ^ Fintype.card V else 0) =
          (2 : ℝ≥0∞)⁻¹ ^ Fintype.card V *
            (if ∀ v ∈ Z, r v = Regime.force then (1 : ℝ≥0∞) else 0) := by
      intro r
      by_cases hr : ∀ v ∈ Z, r v = Regime.force
      · simp [if_pos hr]
      · simp [if_neg hr]
    simp_rw [hscale, ← Finset.mul_sum]
  rw [hconst, mul_comm]
  unfold truncSlice
  rfl

omit [Inhabited β] [MeasurableSingletonClass β] [StandardBorelSpace β] in
lemma slice_sum_idle
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    {X Z : Finset V} (x z anchor : V → β) (S : Finset V) :
    (∑ ω : (augNet β graph hAcyclic X Z).JointSpace,
        if agreesOn S anchor (obsOf β ω) = true ∧
            ∀ v ∈ Z, regimeOf β ω v = Regime.idle then
          (augCPT β graph hAcyclic cpt X Z x z).jointWeight ω else 0) =
      regimeConst Z Regime.idle *
        truncSlice graph hAcyclic cpt (doFinset X x) S anchor := by
  let g : (augNet β graph hAcyclic X Z).JointSpace → ℝ≥0∞ := fun ω =>
    if agreesOn S anchor (obsOf β ω) = true ∧
        ∀ v ∈ Z, regimeOf β ω v = Regime.idle then
      (augCPT β graph hAcyclic cpt X Z x z).jointWeight ω else 0
  have hre : ∑ ω, g ω =
      ∑ p : (V → β) × (V → Regime), g ((augSplit β).symm p) :=
    (Equiv.sum_comp (augSplit β).symm g).symm
  rw [hre, Fintype.sum_prod_type]
  have hterm : ∀ f r,
      g ((augSplit β).symm (f, r)) =
        (if agreesOn S anchor f = true then
          truncatedWeight graph hAcyclic cpt (doFinset X x) f else 0) *
        (if ∀ v ∈ Z, r v = Regime.idle then (2 : ℝ≥0∞)⁻¹ ^ Fintype.card V else 0) := by
    intro f r
    rw [show (augSplit β).symm (f, r) = joinAug β (f, r) from rfl]
    by_cases hA : agreesOn S anchor f = true
    · by_cases hR : ∀ v ∈ Z, r v = Regime.idle
      · have hreg : ∀ v ∈ Z, regimeOf β (joinAug β (f, r)) v = Regime.idle := by
          intro v hv
          simpa [regimeOf, joinAug] using hR v hv
        have hobs : obsOf β (joinAug β (f, r)) = f := by
          funext v
          rfl
        have hcond :
            agreesOn S anchor (obsOf β (joinAug β (f, r))) = true ∧
              ∀ v ∈ Z, regimeOf β (joinAug β (f, r)) v = Regime.idle :=
          ⟨by simpa [hobs] using hA, hreg⟩
        unfold g
        rw [if_pos hcond, if_pos hA, if_pos hR]
        have hw :=
          aug_weight_idle β graph hAcyclic cpt (X := X) (Z := Z) x z
            (joinAug β (f, r)) hreg
        rw [hobs] at hw
        rw [hw, mul_comm]
      · have hnot : ¬ (agreesOn S anchor (obsOf β (joinAug β (f, r))) = true ∧
            ∀ v ∈ Z, regimeOf β (joinAug β (f, r)) v = Regime.idle) := by
          intro hboth
          exact hR (fun v hv => by simpa [regimeOf, joinAug] using hboth.2 v hv)
        unfold g
        simp only [if_neg hnot, if_pos hA, if_neg hR, mul_zero]
    · have hnot : ¬ (agreesOn S anchor (obsOf β (joinAug β (f, r))) = true ∧
          ∀ v ∈ Z, regimeOf β (joinAug β (f, r)) v = Regime.idle) := by
        intro hboth
        have hobs : obsOf β (joinAug β (f, r)) = f := by
          funext v
          rfl
        exact hA (by simpa [hobs] using hboth.1)
      unfold g
      simp only [if_neg hnot, if_neg hA, zero_mul]
  simp_rw [hterm]
  have hfac : ∀ f, (∑ r : V → Regime,
      (if agreesOn S anchor f = true then
        truncatedWeight graph hAcyclic cpt (doFinset X x) f else 0) *
      (if ∀ v ∈ Z, r v = Regime.idle then (2 : ℝ≥0∞)⁻¹ ^ Fintype.card V else 0)) =
      (if agreesOn S anchor f = true then
        truncatedWeight graph hAcyclic cpt (doFinset X x) f else 0) *
      (∑ r : V → Regime, if ∀ v ∈ Z, r v = Regime.idle then
        (2 : ℝ≥0∞)⁻¹ ^ Fintype.card V else 0) :=
    fun f => (Finset.mul_sum _ _ _).symm
  simp_rw [hfac, ← Finset.sum_mul]
  have hconst : ∑ r : V → Regime,
      (if ∀ v ∈ Z, r v = Regime.idle then (2 : ℝ≥0∞)⁻¹ ^ Fintype.card V else 0) =
      regimeConst Z Regime.idle := by
    unfold regimeConst
    have hscale : ∀ r : V → Regime,
        (if ∀ v ∈ Z, r v = Regime.idle then (2 : ℝ≥0∞)⁻¹ ^ Fintype.card V else 0) =
          (2 : ℝ≥0∞)⁻¹ ^ Fintype.card V *
            (if ∀ v ∈ Z, r v = Regime.idle then (1 : ℝ≥0∞) else 0) := by
      intro r
      by_cases hr : ∀ v ∈ Z, r v = Regime.idle
      · simp [if_pos hr]
      · simp [if_neg hr]
    simp_rw [hscale, ← Finset.mul_sum]
  rw [hconst, mul_comm]
  unfold truncSlice
  rfl

/-- Configurations that agree with `anchor` on `S` and carry one regime pattern. -/
def patternEvent (X Z S : Finset V) (anchor : V → β) (target : Regime) :
    Set ((augNet β graph hAcyclic X Z).JointSpace) :=
  assignEvent (bn := augNet β graph hAcyclic X Z) (obsImage S) (obsRead β S anchor) ∩
    assignEvent (bn := augNet β graph hAcyclic X Z) (regimeImage Z)
      (regimeRead β Z target)

omit [MeasurableSingletonClass β] [DecidableRel graph.edges] in
lemma mem_patternEvent (X Z S : Finset V) (anchor : V → β) (target : Regime)
    (ω : (augNet β graph hAcyclic X Z).JointSpace) :
    ω ∈ patternEvent β graph hAcyclic X Z S anchor target ↔
      agreesOn S anchor (obsOf β ω) = true ∧ ∀ v ∈ Z, regimeOf β ω v = target := by
  rw [patternEvent, Set.mem_inter_iff, mem_assignEvent, mem_assignEvent,
    restrict_obs_iff, restrict_regime_iff, agreesOn_eq_true_iff]

lemma measure_pattern_force
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    {X Z : Finset V} (hXZ : Disjoint X Z) (x z anchor : V → β) (S : Finset V) :
    (augCPT β graph hAcyclic cpt X Z x z).jointMeasure
        (patternEvent β graph hAcyclic X Z S anchor Regime.force) =
      regimeConst Z Regime.force *
        truncSlice graph hAcyclic cpt
          (doFinset (X ∪ Z) (mergeAssign X x z)) S anchor := by
  rw [DiscreteCPT.jointMeasure_apply_as_sum _
      (measurable_aug β graph hAcyclic X Z _)]
  have hmem : ∀ ω : (augNet β graph hAcyclic X Z).JointSpace,
      (ω ∈ patternEvent β graph hAcyclic X Z S anchor Regime.force) =
        (agreesOn S anchor (obsOf β ω) = true ∧
          ∀ v ∈ Z, regimeOf β ω v = Regime.force) := by
    intro ω
    simpa using mem_patternEvent β graph hAcyclic X Z S anchor Regime.force ω
  simp_rw [hmem]
  exact slice_sum_force β graph hAcyclic cpt hXZ x z anchor S

lemma measure_pattern_idle
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    {X Z : Finset V} (x z anchor : V → β) (S : Finset V) :
    (augCPT β graph hAcyclic cpt X Z x z).jointMeasure
        (patternEvent β graph hAcyclic X Z S anchor Regime.idle) =
      regimeConst Z Regime.idle *
        truncSlice graph hAcyclic cpt (doFinset X x) S anchor := by
  rw [DiscreteCPT.jointMeasure_apply_as_sum _
      (measurable_aug β graph hAcyclic X Z _)]
  have hmem : ∀ ω : (augNet β graph hAcyclic X Z).JointSpace,
      (ω ∈ patternEvent β graph hAcyclic X Z S anchor Regime.idle) =
        (agreesOn S anchor (obsOf β ω) = true ∧
          ∀ v ∈ Z, regimeOf β ω v = Regime.idle) := by
    intro ω
    simpa using mem_patternEvent β graph hAcyclic X Z S anchor Regime.idle ω
  simp_rw [hmem]
  exact slice_sum_idle β graph hAcyclic cpt x z anchor S

omit [Fintype β] [DecidableEq β] [Inhabited β] [MeasurableSingletonClass β]
  [StandardBorelSpace β] in
lemma zFactor_le_one
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT) (Z : Finset V) (f : V → β) :
    zFactor graph hAcyclic cpt Z f ≤ 1 := by
  unfold zFactor
  induction Z using Finset.induction with
  | empty => simp
  | insert v Z hv ih =>
      rw [Finset.prod_insert hv]
      have hle : cptAt graph hAcyclic cpt v (parentFunOf graph f v) (f v) ≤ 1 := by
        simpa [cptAt] using
          PMF.coe_le_one (cpt.cpt v (toParentAssignment graph hAcyclic v
            (parentFunOf graph f v))) (f v)
      exact (mul_le_mul_left hle _).trans (by rw [one_mul]; exact ih)

omit [Fintype β] [Inhabited β] [MeasurableSingletonClass β] [StandardBorelSpace β] in
lemma truncWeight_doX_le_doXZ
    {X Z : Finset V} (hdisj : Disjoint X Z)
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (x z f : V → β) (hz : ∀ v ∈ Z, f v = z v) :
    truncatedWeight graph hAcyclic cpt (doFinset X x) f ≤
      truncatedWeight graph hAcyclic cpt (doFinset (X ∪ Z) (mergeAssign X x z)) f := by
  have hmul :=
    truncatedWeight_mul_zFactor graph hAcyclic hdisj cpt x z f hz
  rw [hmul]
  exact (mul_le_mul_of_nonneg_left (zFactor_le_one β graph hAcyclic cpt Z f)
    zero_le).trans (by rw [mul_one])

omit [Inhabited β] [MeasurableSingletonClass β] [StandardBorelSpace β] in
lemma truncSlice_doX_le_doXZ
    {X Z : Finset V} (hdisj : Disjoint X Z)
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (x z anchor : V → β) (hz : ∀ v ∈ Z, anchor v = z v)
    {S : Finset V} (hZS : Z ⊆ S) :
    truncSlice graph hAcyclic cpt (doFinset X x) S anchor ≤
      truncSlice graph hAcyclic cpt
        (doFinset (X ∪ Z) (mergeAssign X x z)) S anchor := by
  unfold truncSlice
  refine Finset.sum_le_sum fun f _ => ?_
  cases hbit : agreesOn S anchor f with
  | false => simp
  | true =>
      have hall : ∀ v ∈ S, f v = anchor v := (agreesOn_eq_true_iff).mp hbit
      have hzf : ∀ v ∈ Z, f v = z v :=
        fun v hv => (hall v (hZS hv)).trans (hz v hv)
      exact truncWeight_doX_le_doXZ β graph hAcyclic hdisj cpt x z f hzf

omit [Inhabited β] [MeasurableSingletonClass β] [StandardBorelSpace β] in
lemma truncSlice_doXZ_ne_zero_of_doX
    {X Z : Finset V} (hdisj : Disjoint X Z)
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (x z anchor : V → β) (hz : ∀ v ∈ Z, anchor v = z v)
    {S : Finset V} (hZS : Z ⊆ S)
    (hpos : truncSlice graph hAcyclic cpt (doFinset X x) S anchor ≠ 0) :
    truncSlice graph hAcyclic cpt
      (doFinset (X ∪ Z) (mergeAssign X x z)) S anchor ≠ 0 := by
  intro h0
  have hle := truncSlice_doX_le_doXZ β graph hAcyclic hdisj cpt x z anchor hz hZS
  exact hpos (le_antisymm (hle.trans_eq h0) bot_le)

/-! ## Rules 2 and 3 -/

omit [Fintype V] [Fintype β] [DecidableEq β] [Inhabited β] [MeasurableSpace β]
  [MeasurableSingletonClass β] [StandardBorelSpace β] [DecidableRel graph.edges] in
lemma obs_regime_images_disjoint (S T : Finset V) :
    Disjoint (obsImage S) (regimeImage T) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  rcases Finset.mem_image.mp ha with ⟨_, _, rfl⟩
  rcases Finset.mem_image.mp hb with ⟨_, _, h⟩
  cases h

omit [Fintype V] [DecidableEq V] [Fintype β] [DecidableEq β] [Inhabited β]
  [MeasurableSpace β] [MeasurableSingletonClass β] [StandardBorelSpace β]
  [DecidableRel graph.edges] hAcyclic in
private lemma active_pair {G : DirectedGraph V} {C : Set V} {p : List V}
    (hact : ActiveTrail G C p) (hlen : p.length = 2) :
    ∃ (u vNode : V) (_hedge : UndirectedEdge G u vNode), p = [u, vNode] :=
  ActiveTrail.rec
    (motive := fun trail _ => trail.length = 2 →
      ∃ (u vNode : V) (_hedge : UndirectedEdge G u vNode), trail = [u, vNode])
    (fun vtx hlen1 => by
      have : ([vtx] : List V).length = 1 := rfl
      omega)
    (fun {u vNode} hedge _ => ⟨u, vNode, hedge, rfl⟩)
    (fun {a b c} {rest} _ _ _ _ _ hlen3 => by
      have : 3 ≤ (a :: b :: c :: rest).length := by simp
      omega)
    hact hlen

omit [Fintype V] [DecidableEq V] [Fintype β] [DecidableEq β] [Inhabited β]
  [MeasurableSpace β] [MeasurableSingletonClass β] [StandardBorelSpace β]
  graph [DecidableRel graph.edges] hAcyclic in
private lemma active_last_triple {G : DirectedGraph V} {C : Set V} {p : List V}
    (hact : ActiveTrail G C p) (hlen : 3 ≤ p.length) :
    ∃ (a b c : V) (hab : UndirectedEdge G a b) (hbc : UndirectedEdge G b c)
      (hac : a ≠ c),
      IsActive G C ⟨a, b, c, hab, hbc, hac⟩ ∧
        p.getLast? = some c ∧ p.dropLast.getLast? = some b := by
  obtain ⟨a, b, c, rest, hab, hbc, hac, rfl, hAct, hTail⟩ :=
    active_cons_of_long hact hlen
  cases rest with
  | nil =>
      exact ⟨a, b, c, hab, hbc, hac, hAct, by simp [List.getLast?],
        by simp [List.dropLast, List.getLast?]⟩
  | cons d rest =>
      have hlen' : 3 ≤ (b :: c :: d :: rest).length := by simp
      rcases active_last_triple hTail hlen' with
        ⟨a', b', c', hab', hbc', hac', hAct', hc, hb⟩
      exact ⟨a', b', c', hab', hbc', hac', hAct',
        by simpa [List.getLast?] using hc,
        by simpa [List.dropLast, List.getLast?] using hb⟩
termination_by p.length

omit [Fintype V] [DecidableEq V] [Fintype β] [DecidableEq β] [Inhabited β]
  [MeasurableSpace β] [MeasurableSingletonClass β] [StandardBorelSpace β]
  [DecidableRel graph.edges] in
lemma gout_no_leave {X Z : Finset V} {u v : V} (hu : u ∈ Z) :
    ¬ (gout graph X Z).edges u v :=
  fun h => h.2 hu

omit [Fintype V] [Fintype β] [DecidableEq β] [Inhabited β] [MeasurableSpace β]
  [MeasurableSingletonClass β] [StandardBorelSpace β] [DecidableRel graph.edges] in
lemma gout_enter_parent
    {X Z W : Finset V}
    (hparents : ∀ v ∈ Z, ∀ u, graph.edges u v → u ∈ X ∪ Z ∪ W)
    {u v : V} (hv : v ∈ Z) (hedge : (gout graph X Z).edges u v) :
    u ∈ X ∪ W := by
  have huZ : u ∉ Z := hedge.2
  have hgx : (gx graph X).edges u v := hedge.1
  have hmem := hparents v hv u hgx.1
  rcases Finset.mem_union.mp hmem with hXZ | hW
  · rcases Finset.mem_union.mp hXZ with hX | hZ
    · exact Finset.mem_union.mpr (Or.inl hX)
    · exact absurd hZ huZ
  · exact Finset.mem_union.mpr (Or.inr hW)

omit [Fintype V] [Fintype β] [DecidableEq β] [Inhabited β] [MeasurableSpace β]
  [MeasurableSingletonClass β] [StandardBorelSpace β] [DecidableRel graph.edges] in
lemma slice_of_trimmed (X Y Z W : Finset V) :
    X ∪ (Y \ (X ∪ Z ∪ W)) ∪ Z ∪ W = X ∪ Y ∪ Z ∪ W := by
  set S := X ∪ Z ∪ W with hS
  have hcomm : X ∪ (Y \ S) ∪ Z ∪ W = (Y \ S) ∪ S := by
    ext v
    simp only [Finset.mem_union, hS]
    tauto
  rw [hcomm, Finset.sdiff_union_self_eq_union]
  ext v
  simp only [Finset.mem_union, hS]
  tauto

omit [Fintype V] [DecidableRel graph.edges] in
/-- In the rule-2 mutilation, a parent of `Z` that also lies in `X ∪ W` blocks
every trail out of `Y \ (X ∪ Z ∪ W)`. -/
theorem dsep_gout_of_parents
    {X Y Z W : Finset V}
    (hparents : ∀ v ∈ Z, ∀ u, graph.edges u v → u ∈ X ∪ Z ∪ W)
    (acyclic : graph.IsAcyclic) :
    DSeparatedFull (gout graph X Z)
      (((Y \ (X ∪ Z ∪ W)) : Finset V) : Set V)
      ((Z : Finset V) : Set V)
      (((X ∪ W) : Finset V) : Set V) := by
  intro y0 hy0 z0 hz0 hyz htrail
  rcases htrail with ⟨p, hp, hpe, hact⟩
  have hyNot : y0 ∉ X ∪ Z ∪ W := (Finset.mem_sdiff.mp (Finset.mem_coe.mp hy0)).2
  have hyZ : y0 ∉ Z := fun h =>
    hyNot (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr h))))
  have hyXW : y0 ∉ X ∪ W := fun h =>
    hyNot (by
      rcases Finset.mem_union.mp h with hX | hW
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hX)))
      · exact Finset.mem_union.mpr (Or.inr hW))
  have hends := pathEndpoints_head_last hp
  have hjoin : some (p.head hp, p.getLast hp) = some (y0, z0) := by
    rw [← hends, hpe]
  have hyHead : p.head hp = y0 := (Prod.ext_iff.mp (by injection hjoin)).1
  have hzLast : p.getLast hp = z0 := (Prod.ext_iff.mp (by injection hjoin)).2
  have hzMem : z0 ∈ p := by
    rw [← hzLast]
    exact List.getLast_mem hp
  rcases firstHit_of_mem Z hzMem (Finset.mem_coe.mp hz0) with ⟨front, hit, back, hfh⟩
  have hspec := firstHit_spec Z p
  simp only [hfh] at hspec
  rcases hspec with ⟨hpEq, hhit, _hfront⟩
  let C : Set V := ((X ∪ W : Finset V) : Set V)
  have htake := activeTrail_take hact (front.length + 1) (by omega) (by
    have hlen : p.length = front.length + back.length + 1 := by
      simp [hpEq, List.length_append]
      omega
    omega)
  have hqTake := take_firstHit hfh
  rw [hqTake] at htake
  have hfrontNe : front ≠ [] := by
    intro hnil
    have hhd : p.head hp = hit := by
      subst hnil
      subst hpEq
      rfl
    exact hyZ (hyHead.symm.trans hhd ▸ hhit)
  let q : List V := front ++ [hit]
  have hq : ActiveTrail (gout graph X Z) C q := htake
  have hqNe : q ≠ [] := by simp [q]
  have hqHead : q.head hqNe = y0 := by
    cases front with
    | nil => exact absurd rfl hfrontNe
    | cons a as =>
        have hph : p.head hp = a := by
          subst hpEq
          rfl
        have hqh : q.head hqNe = a := by
          unfold q
          rfl
        exact hqh.trans (hph.symm.trans hyHead)
  have hqLast : q.getLast hqNe = hit :=
    (List.getLast_congr hqNe
      (List.append_ne_nil_of_right_ne_nil front (List.cons_ne_nil hit []))
      (by simp [q])).trans (List.getLast_append_singleton front)
  by_cases hshort : q.length = 2
  · rcases active_pair hq hshort with ⟨u, vNode, hedge, hqEq⟩
    have hpair : front ++ [hit] = [u, vNode] := by simpa [q] using hqEq
    have hlen1 : front.length = 1 := by
      have happ : (front ++ [hit]).length = front.length + 1 := by
        simp [List.length_append]
      have htwo : (front ++ [hit]).length = 2 := hshort
      omega
    rcases List.length_eq_one_iff.mp hlen1 with ⟨a, ha⟩
    have hlists : [a, hit] = [u, vNode] := by simpa [ha] using hpair
    have haU : a = u := by
      injection hlists
    have hvU : hit = vNode := by
      injection hlists with _ hrest
      injection hrest
    have hhead : q.head hqNe = a := by simp [q, ha, List.head_cons]
    have hu : u = y0 := haU.symm.trans (hhead.symm.trans hqHead)
    have hv : vNode = hit := hvU.symm
    have hdir : (gout graph X Z).edges u vNode := by
      rcases hedge with hdir | hrev
      · exact hdir
      · exact absurd hrev (gout_no_leave graph (hv ▸ hhit))
    have hparent := gout_enter_parent graph hparents (hv ▸ hhit) hdir
    exact hyXW (hu ▸ hparent)
  · have hge : 2 ≤ q.length := by
      have hlen : q.length = front.length + 1 := by simp [q, List.length_append]
      have hpos : 1 ≤ front.length := by
        cases front with
        | nil => exact absurd rfl hfrontNe
        | cons _ _ => simp
      omega
    have hlong : 3 ≤ q.length := by omega
    rcases active_last_triple hq hlong with
      ⟨a, pred, last, hab, hbc, hac, hAct, hlast, hpred⟩
    have hlastEq : last = hit := by
      have hsome : q.getLast? = some hit := by
        rw [List.getLast?_eq_getLast_of_ne_nil hqNe]
        exact congrArg some hqLast
      exact Option.some.inj (hlast.symm.trans hsome)
    have hdir : (gout graph X Z).edges pred last := by
      rcases hbc with hdir | hrev
      · exact hdir
      · exact absurd hrev (gout_no_leave graph (hlastEq ▸ hhit))
    have hparent := gout_enter_parent graph hparents (hlastEq ▸ hhit) hdir
    have hnon : IsNonCollider (gout graph X Z) ⟨a, pred, last, hab, hbc, hac⟩ :=
      noncollider_of_out (gout_acyclic graph acyclic X Z)
        (hab := hab) (hbc := hbc) (hac := hac) (Or.inr hdir)
    have havoid :=
      active_nonCollider_not_in_Z (gout graph X Z) C ⟨a, pred, last, hab, hbc, hac⟩
        hAct hnon
    exact havoid (by
      simp only [C]
      exact Finset.mem_coe.mpr hparent)

/-- **Rule 2.** Separation of `Y` from `Z` given `X ∪ W` in the graph with the
arrows into `X` and out of `Z` deleted is `Y ⫫ F_Z | X, Z, W` in the regime
augmentation. The resulting conditional masses are the g-formula ratios.
Positivity is the `do(X)` mass of `X ∪ Z ∪ W`; the `do(X ∪ Z)` denominator
follows because each intervened factor is at most one. -/
theorem rule2_regime
    {X Y Z W : Finset V}
    (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (hsep : DSeparatedFull (gout graph X Z) (Y : Set V) (Z : Set V)
      ((X ∪ W : Finset V) : Set V))
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (x z anchor : V → β)
    (hz : ∀ v ∈ Z, anchor v = z v)
    (hpos : truncSlice graph hAcyclic cpt (doFinset X x) (X ∪ Z ∪ W) anchor ≠ 0) :
    truncSlice graph hAcyclic cpt (doFinset (X ∪ Z) (mergeAssign X x z))
        (X ∪ Y ∪ Z ∪ W) anchor /
      truncSlice graph hAcyclic cpt (doFinset (X ∪ Z) (mergeAssign X x z))
        (X ∪ Z ∪ W) anchor =
    truncSlice graph hAcyclic cpt (doFinset X x) (X ∪ Y ∪ Z ∪ W) anchor /
      truncSlice graph hAcyclic cpt (doFinset X x) (X ∪ Z ∪ W) anchor := by
  let bn := augNet β graph hAcyclic X Z
  let cptA := augCPT β graph hAcyclic cpt X Z x z
  let μ := cptA.jointMeasure
  let Yo := obsImage Y
  let Zr := regimeImage Z
  let Co := obsImage (X ∪ Z ∪ W)
  let numS : Finset V := X ∪ Y ∪ Z ∪ W
  let denS : Finset V := X ∪ Z ∪ W
  have hci : CondIndepVertices bn μ (Yo : Set (AugV V)) (Zr : Set (AugV V))
      (Co : Set (AugV V)) := by
    have hsepA := dsep_regime_rule2 graph hAcyclic hYZ hsep
    have hover :
        ((Yo : Set (AugV V)) ∩ (Zr : Set (AugV V))) ⊆ (Co : Set (AugV V)) := by
      intro a ha
      exact False.elim <|
        Finset.disjoint_left.mp (obs_regime_images_disjoint Y Z)
          (Finset.mem_coe.mp ha.1) (Finset.mem_coe.mp ha.2)
    have hYo : AugV.obs '' (Y : Set V) = (Yo : Set (AugV V)) := by
      simp [Yo, obsImage, Finset.coe_image]
    have hZr : AugV.regime '' (Z : Set V) = (Zr : Set (AugV V)) := by
      simp [Zr, regimeImage, Finset.coe_image]
    have hCo : AugV.obs '' ((X ∪ Z ∪ W : Finset V) : Set V) =
        (Co : Set (AugV V)) := by
      simp [Co, obsImage, Finset.coe_image]
    rw [hYo, hZr, hCo] at hsepA
    exact dsep_implies_condIndepVertices (bn := bn) (μ := μ) hover hsepA
  have hZS : Z ⊆ denS := by
    intro v hv
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hv)))
  have hposZ :=
    truncSlice_doXZ_ne_zero_of_doX β graph hAcyclic hXZ cpt x z anchor hz hZS hpos
  have hconstF := regimeConst_spec Z Regime.force
  have hconstI := regimeConst_spec Z Regime.idle
  have hdenF : μ (patternEvent β graph hAcyclic X Z denS anchor Regime.force) ≠ 0 := by
    rw [measure_pattern_force β graph hAcyclic cpt hXZ x z anchor denS]
    exact mul_ne_zero hconstF.1 hposZ
  have hdenI : μ (patternEvent β graph hAcyclic X Z denS anchor Regime.idle) ≠ 0 := by
    rw [measure_pattern_idle β graph hAcyclic cpt x z anchor denS]
    exact mul_ne_zero hconstI.1 hpos
  have hforceEq :
      patternEvent β graph hAcyclic X Z numS anchor Regime.force =
        assignEvent (bn := bn) Yo (obsRead β Y anchor) ∩
          assignEvent (bn := bn) Zr (regimeRead β Z Regime.force) ∩
          assignEvent (bn := bn) Co (obsRead β denS anchor) := by
    ext ω
    rw [mem_patternEvent, Set.mem_inter_iff, Set.mem_inter_iff,
      mem_assignEvent, mem_assignEvent, mem_assignEvent,
      restrict_obs_iff, restrict_regime_iff, restrict_obs_iff, agreesOn_eq_true_iff]
    constructor
    · intro h
      refine ⟨⟨?_, h.2⟩, ?_⟩
      · intro v hv
        exact h.1 v (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
          (Or.inl (Finset.mem_union.mpr (Or.inr hv))))))
      · intro v hv
        exact h.1 v (by
          rcases Finset.mem_union.mp hv with hXZ | hW
          · rcases Finset.mem_union.mp hXZ with hX | hZ
            · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
                (Or.inl (Finset.mem_union.mpr (Or.inl hX)))))
            · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hZ)))
          · exact Finset.mem_union.mpr (Or.inr hW))
    · intro h
      refine ⟨?_, h.1.2⟩
      intro v hv
      rcases Finset.mem_union.mp hv with hYZW | hW
      · rcases Finset.mem_union.mp hYZW with hYZ | hZ
        · rcases Finset.mem_union.mp hYZ with hX | hY
          · exact h.2 v (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hX))))
          · exact h.1.1 v hY
        · exact h.2 v (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hZ))))
      · exact h.2 v (Finset.mem_union.mpr (Or.inr hW))
  have hidleEq :
      patternEvent β graph hAcyclic X Z numS anchor Regime.idle =
        assignEvent (bn := bn) Yo (obsRead β Y anchor) ∩
          assignEvent (bn := bn) Zr (regimeRead β Z Regime.idle) ∩
          assignEvent (bn := bn) Co (obsRead β denS anchor) := by
    ext ω
    rw [mem_patternEvent, Set.mem_inter_iff, Set.mem_inter_iff,
      mem_assignEvent, mem_assignEvent, mem_assignEvent,
      restrict_obs_iff, restrict_regime_iff, restrict_obs_iff, agreesOn_eq_true_iff]
    constructor
    · intro h
      refine ⟨⟨?_, h.2⟩, ?_⟩
      · intro v hv
        exact h.1 v (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
          (Or.inl (Finset.mem_union.mpr (Or.inr hv))))))
      · intro v hv
        exact h.1 v (by
          rcases Finset.mem_union.mp hv with hXZ | hW
          · rcases Finset.mem_union.mp hXZ with hX | hZ
            · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
                (Or.inl (Finset.mem_union.mpr (Or.inl hX)))))
            · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hZ)))
          · exact Finset.mem_union.mpr (Or.inr hW))
    · intro h
      refine ⟨?_, h.1.2⟩
      intro v hv
      rcases Finset.mem_union.mp hv with hYZW | hW
      · rcases Finset.mem_union.mp hYZW with hYZ | hZ
        · rcases Finset.mem_union.mp hYZ with hX | hY
          · exact h.2 v (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hX))))
          · exact h.1.1 v hY
        · exact h.2 v (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hZ))))
      · exact h.2 v (Finset.mem_union.mpr (Or.inr hW))
  have hdenForceEq :
      patternEvent β graph hAcyclic X Z denS anchor Regime.force =
        assignEvent (bn := bn) Zr (regimeRead β Z Regime.force) ∩
          assignEvent (bn := bn) Co (obsRead β denS anchor) := by
    ext ω
    rw [mem_patternEvent, Set.mem_inter_iff, mem_assignEvent, mem_assignEvent,
      restrict_regime_iff, restrict_obs_iff, agreesOn_eq_true_iff]
    constructor
    · intro h
      exact ⟨h.2, h.1⟩
    · intro h
      exact ⟨h.2, h.1⟩
  have hdenIdleEq :
      patternEvent β graph hAcyclic X Z denS anchor Regime.idle =
        assignEvent (bn := bn) Zr (regimeRead β Z Regime.idle) ∩
          assignEvent (bn := bn) Co (obsRead β denS anchor) := by
    ext ω
    rw [mem_patternEvent, Set.mem_inter_iff, mem_assignEvent, mem_assignEvent,
      restrict_regime_iff, restrict_obs_iff, agreesOn_eq_true_iff]
    constructor
    · intro h
      exact ⟨h.2, h.1⟩
    · intro h
      exact ⟨h.2, h.1⟩
  have hCIforce :=
    condIndepVertices_condMass (bn := bn) (μ := μ) Yo Zr Co
      (obsRead β Y anchor) (regimeRead β Z Regime.force) (obsRead β denS anchor)
      hci (by simpa [hdenForceEq] using hdenF)
  have hCIidle :=
    condIndepVertices_condMass (bn := bn) (μ := μ) Yo Zr Co
      (obsRead β Y anchor) (regimeRead β Z Regime.idle) (obsRead β denS anchor)
      hci (by simpa [hdenIdleEq] using hdenI)
  have hratio := hCIforce.trans hCIidle.symm
  rw [← hforceEq, ← hidleEq, ← hdenForceEq, ← hdenIdleEq] at hratio
  rw [measure_pattern_force β graph hAcyclic cpt hXZ x z anchor numS,
    measure_pattern_force β graph hAcyclic cpt hXZ x z anchor denS,
    measure_pattern_idle β graph hAcyclic cpt x z anchor numS,
    measure_pattern_idle β graph hAcyclic cpt x z anchor denS] at hratio
  rw [ENNReal.mul_div_mul_left _ _ hconstF.1 hconstF.2,
    ENNReal.mul_div_mul_left _ _ hconstI.1 hconstI.2] at hratio
  exact hratio

/-- **Rule 3.** Separation of `Y` from `Z` given `X ∪ W` in the graph with the
arrows into `X` and into `Z(W)` deleted is `Y ⫫ F_Z | X, W`. Both denominator
masses are hypotheses: the idle conditional uses `do(X)`, and the forced
conditional uses `do(X, Z)`. -/
theorem rule3_regime
    {X Y Z W : Finset V}
    (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) (hWZ : Disjoint W Z)
    (hsep : DSeparatedFull (g3 graph X Z W) (Y : Set V) (Z : Set V)
      ((X ∪ W : Finset V) : Set V))
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (x z anchor : V → β)
    (hpos : truncSlice graph hAcyclic cpt (doFinset X x) (X ∪ W) anchor ≠ 0)
    (hposZ : truncSlice graph hAcyclic cpt
      (doFinset (X ∪ Z) (mergeAssign X x z)) (X ∪ W) anchor ≠ 0) :
    truncSlice graph hAcyclic cpt (doFinset (X ∪ Z) (mergeAssign X x z))
        (X ∪ Y ∪ W) anchor /
      truncSlice graph hAcyclic cpt
        (doFinset (X ∪ Z) (mergeAssign X x z)) (X ∪ W) anchor =
    truncSlice graph hAcyclic cpt (doFinset X x) (X ∪ Y ∪ W) anchor /
      truncSlice graph hAcyclic cpt (doFinset X x) (X ∪ W) anchor := by
  let bn := augNet β graph hAcyclic X Z
  let cptA := augCPT β graph hAcyclic cpt X Z x z
  let μ := cptA.jointMeasure
  let Yo := obsImage Y
  let Zr := regimeImage Z
  let Co := obsImage (X ∪ W)
  let numS : Finset V := X ∪ Y ∪ W
  let denS : Finset V := X ∪ W
  have hci : CondIndepVertices bn μ (Yo : Set (AugV V)) (Zr : Set (AugV V))
      (Co : Set (AugV V)) := by
    have hsepA := dsep_regime_rule3 graph hAcyclic hXZ hYZ hWZ hsep
    have hover :
        ((Yo : Set (AugV V)) ∩ (Zr : Set (AugV V))) ⊆ (Co : Set (AugV V)) := by
      intro a ha
      exact False.elim <|
        Finset.disjoint_left.mp (obs_regime_images_disjoint Y Z)
          (Finset.mem_coe.mp ha.1) (Finset.mem_coe.mp ha.2)
    have hYo : AugV.obs '' (Y : Set V) = (Yo : Set (AugV V)) := by
      simp [Yo, obsImage, Finset.coe_image]
    have hZr : AugV.regime '' (Z : Set V) = (Zr : Set (AugV V)) := by
      simp [Zr, regimeImage, Finset.coe_image]
    have hCo : AugV.obs '' ((X ∪ W : Finset V) : Set V) =
        (Co : Set (AugV V)) := by
      simp [Co, obsImage, Finset.coe_image]
    rw [hYo, hZr, hCo] at hsepA
    exact dsep_implies_condIndepVertices (bn := bn) (μ := μ) hover hsepA
  have hconstF := regimeConst_spec Z Regime.force
  have hconstI := regimeConst_spec Z Regime.idle
  have hdenF : μ (patternEvent β graph hAcyclic X Z denS anchor Regime.force) ≠ 0 := by
    rw [measure_pattern_force β graph hAcyclic cpt hXZ x z anchor denS]
    exact mul_ne_zero hconstF.1 hposZ
  have hdenI : μ (patternEvent β graph hAcyclic X Z denS anchor Regime.idle) ≠ 0 := by
    rw [measure_pattern_idle β graph hAcyclic cpt x z anchor denS]
    exact mul_ne_zero hconstI.1 hpos
  have hforceEq :
      patternEvent β graph hAcyclic X Z numS anchor Regime.force =
        assignEvent (bn := bn) Yo (obsRead β Y anchor) ∩
          assignEvent (bn := bn) Zr (regimeRead β Z Regime.force) ∩
          assignEvent (bn := bn) Co (obsRead β denS anchor) := by
    ext ω
    rw [mem_patternEvent, Set.mem_inter_iff, Set.mem_inter_iff,
      mem_assignEvent, mem_assignEvent, mem_assignEvent,
      restrict_obs_iff, restrict_regime_iff, restrict_obs_iff, agreesOn_eq_true_iff]
    constructor
    · intro h
      refine ⟨⟨?_, h.2⟩, ?_⟩
      · intro v hv
        exact h.1 v (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hv))))
      · intro v hv
        rcases Finset.mem_union.mp hv with hX | hW
        · exact h.1 v (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hX))))
        · exact h.1 v (Finset.mem_union.mpr (Or.inr hW))
    · intro h
      refine ⟨?_, h.1.2⟩
      intro v hv
      rcases Finset.mem_union.mp hv with hXY | hW
      · rcases Finset.mem_union.mp hXY with hX | hY
        · exact h.2 v (Finset.mem_union.mpr (Or.inl hX))
        · exact h.1.1 v hY
      · exact h.2 v (Finset.mem_union.mpr (Or.inr hW))
  have hidleEq :
      patternEvent β graph hAcyclic X Z numS anchor Regime.idle =
        assignEvent (bn := bn) Yo (obsRead β Y anchor) ∩
          assignEvent (bn := bn) Zr (regimeRead β Z Regime.idle) ∩
          assignEvent (bn := bn) Co (obsRead β denS anchor) := by
    ext ω
    rw [mem_patternEvent, Set.mem_inter_iff, Set.mem_inter_iff,
      mem_assignEvent, mem_assignEvent, mem_assignEvent,
      restrict_obs_iff, restrict_regime_iff, restrict_obs_iff, agreesOn_eq_true_iff]
    constructor
    · intro h
      refine ⟨⟨?_, h.2⟩, ?_⟩
      · intro v hv
        exact h.1 v (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hv))))
      · intro v hv
        rcases Finset.mem_union.mp hv with hX | hW
        · exact h.1 v (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hX))))
        · exact h.1 v (Finset.mem_union.mpr (Or.inr hW))
    · intro h
      refine ⟨?_, h.1.2⟩
      intro v hv
      rcases Finset.mem_union.mp hv with hXY | hW
      · rcases Finset.mem_union.mp hXY with hX | hY
        · exact h.2 v (Finset.mem_union.mpr (Or.inl hX))
        · exact h.1.1 v hY
      · exact h.2 v (Finset.mem_union.mpr (Or.inr hW))
  have hdenForceEq :
      patternEvent β graph hAcyclic X Z denS anchor Regime.force =
        assignEvent (bn := bn) Zr (regimeRead β Z Regime.force) ∩
          assignEvent (bn := bn) Co (obsRead β denS anchor) := by
    ext ω
    rw [mem_patternEvent, Set.mem_inter_iff, mem_assignEvent, mem_assignEvent,
      restrict_regime_iff, restrict_obs_iff, agreesOn_eq_true_iff]
    constructor
    · intro h
      exact ⟨h.2, h.1⟩
    · intro h
      exact ⟨h.2, h.1⟩
  have hdenIdleEq :
      patternEvent β graph hAcyclic X Z denS anchor Regime.idle =
        assignEvent (bn := bn) Zr (regimeRead β Z Regime.idle) ∩
          assignEvent (bn := bn) Co (obsRead β denS anchor) := by
    ext ω
    rw [mem_patternEvent, Set.mem_inter_iff, mem_assignEvent, mem_assignEvent,
      restrict_regime_iff, restrict_obs_iff, agreesOn_eq_true_iff]
    constructor
    · intro h
      exact ⟨h.2, h.1⟩
    · intro h
      exact ⟨h.2, h.1⟩
  have hCIforce :=
    condIndepVertices_condMass (bn := bn) (μ := μ) Yo Zr Co
      (obsRead β Y anchor) (regimeRead β Z Regime.force) (obsRead β denS anchor)
      hci (by simpa [hdenForceEq] using hdenF)
  have hCIidle :=
    condIndepVertices_condMass (bn := bn) (μ := μ) Yo Zr Co
      (obsRead β Y anchor) (regimeRead β Z Regime.idle) (obsRead β denS anchor)
      hci (by simpa [hdenIdleEq] using hdenI)
  have hratio := hCIforce.trans hCIidle.symm
  rw [← hforceEq, ← hidleEq, ← hdenForceEq, ← hdenIdleEq] at hratio
  rw [measure_pattern_force β graph hAcyclic cpt hXZ x z anchor numS,
    measure_pattern_force β graph hAcyclic cpt hXZ x z anchor denS,
    measure_pattern_idle β graph hAcyclic cpt x z anchor numS,
    measure_pattern_idle β graph hAcyclic cpt x z anchor denS] at hratio
  rw [ENNReal.mul_div_mul_left _ _ hconstF.1 hconstF.2,
    ENNReal.mul_div_mul_left _ _ hconstI.1 hconstI.2] at hratio
  exact hratio

/-- The parent condition is the special case of rule 2 on
`Y \ (X ∪ Z ∪ W)`. That deletion does not change the summed coordinates. -/
theorem rule2_parents_of_regime
    {X Y Z W : Finset V}
    (hdisj : Disjoint X Z)
    (hparents : ∀ v ∈ Z, ∀ u, graph.edges u v → u ∈ X ∪ Z ∪ W)
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (x z anchor : V → β)
    (hz : ∀ v ∈ Z, anchor v = z v)
    (hpos : truncSlice graph hAcyclic cpt (doFinset X x) (X ∪ Z ∪ W) anchor ≠ 0) :
    truncSlice graph hAcyclic cpt (doFinset (X ∪ Z) (mergeAssign X x z))
        (X ∪ Y ∪ Z ∪ W) anchor /
      truncSlice graph hAcyclic cpt (doFinset (X ∪ Z) (mergeAssign X x z))
        (X ∪ Z ∪ W) anchor =
    truncSlice graph hAcyclic cpt (doFinset X x) (X ∪ Y ∪ Z ∪ W) anchor /
      truncSlice graph hAcyclic cpt (doFinset X x) (X ∪ Z ∪ W) anchor := by
  let Y' : Finset V := Y \ (X ∪ Z ∪ W)
  have hYZ : Disjoint Y' Z := by
    rw [Finset.disjoint_left]
    intro v hv hvZ
    exact (Finset.mem_sdiff.mp hv).2
      (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hvZ))))
  have hsep : DSeparatedFull (gout graph X Z) (Y' : Set V) (Z : Set V)
      ((X ∪ W : Finset V) : Set V) := by
    simpa [Y'] using
      dsep_gout_of_parents graph hparents hAcyclic (Y := Y) (X := X) (Z := Z) (W := W)
  have hrule :=
    rule2_regime (β := β) (graph := graph) (hAcyclic := hAcyclic)
      hdisj hYZ hsep cpt x z anchor hz hpos
  have hslice : X ∪ Y' ∪ Z ∪ W = X ∪ Y ∪ Z ∪ W := by
    ext v
    simp only [Finset.mem_union, Finset.mem_sdiff, Y']
    tauto
  rw [hslice] at hrule
  exact hrule

omit [Fintype V] [DecidableEq V] [Fintype β] [DecidableEq β] [Inhabited β]
  [MeasurableSpace β] [MeasurableSingletonClass β] [StandardBorelSpace β]
  [DecidableRel graph.edges] in
lemma zWitness_eq_zOf (X Z W : Finset V) :
    zWitness graph X Z W = zOf graph X Z W := by
  unfold zWitness zOf gx
  rfl

omit [Fintype V] [DecidableEq V] [Fintype β] [DecidableEq β] [Inhabited β]
  [MeasurableSpace β] [MeasurableSingletonClass β] [StandardBorelSpace β]
  [DecidableRel graph.edges] in
lemma g3_eq_deleteIncoming_z {X Z W : Finset V}
    (h : zWitness graph X Z W = ((Z : Finset V) : Set V)) :
    g3 graph X Z W = deleteIncoming (gx graph X) Z := by
  ext u v
  simp [g3, deleteIncoming, deleteIncomingSet, h]

/-- No outside child makes `Z(W) = Z`, so rule 3's separation holds, and the
two denominators agree. -/
theorem rule3_no_external_of_regime
    {X Y Z W : Finset V}
    (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) (hWZ : Disjoint W Z)
    (hout0 : ∀ u ∈ Z, ∀ v, graph.edges u v → v ∈ X ∪ Z)
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (x z anchor : V → β)
    (hpos : truncSlice graph hAcyclic cpt (doFinset X x) (X ∪ W) anchor ≠ 0) :
    truncSlice graph hAcyclic cpt (doFinset (X ∪ Z) (mergeAssign X x z))
        (X ∪ Y ∪ W) anchor /
      truncSlice graph hAcyclic cpt
        (doFinset (X ∪ Z) (mergeAssign X x z)) (X ∪ W) anchor =
    truncSlice graph hAcyclic cpt (doFinset X x) (X ∪ Y ∪ W) anchor /
      truncSlice graph hAcyclic cpt (doFinset X x) (X ∪ W) anchor ∧
    truncSlice graph hAcyclic cpt
      (doFinset (X ∪ Z) (mergeAssign X x z)) (X ∪ W) anchor ≠ 0 := by
  have hzw : zWitness graph X Z W = ((Z : Finset V) : Set V) := by
    rw [zWitness_eq_zOf graph X Z W]
    exact zOf_eq_of_no_external_child graph hout0 hWZ
  have hg : g3 graph X Z W = deleteIncoming (deleteIncoming graph X) Z := by
    simpa [gx] using g3_eq_deleteIncoming_z graph hzw
  have hsep0 :=
    rule3_isolated_separated graph hout0 ((Y : Finset V) : Set V)
      (((X ∪ W : Finset V) : Set V))
  have hsep : DSeparatedFull (g3 graph X Z W) (Y : Set V) (Z : Set V)
      ((X ∪ W : Finset V) : Set V) := by
    simpa [hg] using hsep0
  have hSZ : Disjoint (X ∪ W) Z := by
    rw [Finset.disjoint_union_left]
    exact ⟨hXZ, hWZ⟩
  have hden :=
    truncSlice_no_external_child graph hAcyclic hXZ hSZ hout0 cpt x z anchor
  have hposZ : truncSlice graph hAcyclic cpt
      (doFinset (X ∪ Z) (mergeAssign X x z)) (X ∪ W) anchor ≠ 0 := by
    rw [hden]
    exact hpos
  refine ⟨?_, hposZ⟩
  exact rule3_regime (β := β) (graph := graph) (hAcyclic := hAcyclic)
    hXZ hYZ hWZ hsep cpt x z anchor hpos hposZ

end Mettapedia.GSLT.Causality.DoCalculus
