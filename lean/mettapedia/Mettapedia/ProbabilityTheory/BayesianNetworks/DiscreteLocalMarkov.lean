import Mettapedia.ProbabilityTheory.BayesianNetworks.DiscreteLocalMarkov.BlockFactorization

open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace Mettapedia.ProbabilityTheory.BayesianNetworks.DiscreteLocalMarkov

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (bn : BayesianNetwork V)
variable [∀ v : V, Fintype (bn.stateSpace v)]
variable [∀ v : V, Nonempty (bn.stateSpace v)]
variable [∀ v : V, StandardBorelSpace (bn.stateSpace v)]

open BayesianNetwork DiscreteCPT DirectedGraph

noncomputable def parentsRestrict (v : V) :
    bn.JointSpace → (∀ p : {x // x ∈ (bn.graph.parents v : Set V)}, bn.stateSpace p.1) :=
  restrictToSet (bn := bn) (bn.graph.parents v)

lemma measurableSet_parents_preimage
    (v : V) {s : Set bn.JointSpace}
    (hs : MeasurableSet[bn.measurableSpaceOfVertices (bn.graph.parents v)] s) :
    ∃ S : Set (∀ p : {x // x ∈ (bn.graph.parents v : Set V)}, bn.stateSpace p.1),
      MeasurableSet S ∧ s = (parentsRestrict (bn := bn) v) ⁻¹' S := by
  classical
  -- Rewrite the parent sigma-algebra as a comap, then use measurableSet_comap.
  have hs' :
      MeasurableSet[
        MeasurableSpace.comap (parentsRestrict (bn := bn) v) (by infer_instance)] s := by
    simpa [parentsRestrict,
      measurableSpaceOfVertices_eq_comap_restrict (bn := bn) (bn.graph.parents v)] using hs
  rcases (MeasurableSpace.measurableSet_comap).1 hs' with ⟨S, hS, hpre⟩
  exact ⟨S, hS, hpre.symm⟩

abbrev ParentAssign (v : V) :=
  ∀ p : {x // x ∈ (bn.graph.parents v : Set V)}, bn.stateSpace p.1

def parentFiber (v : V) (c : ParentAssign (bn := bn) v) : Set bn.JointSpace :=
  (parentsRestrict (bn := bn) v) ⁻¹' {c}

lemma mem_parentFiber_iff
    (v : V) (c : ParentAssign (bn := bn) v) (ω : bn.JointSpace) :
    ω ∈ parentFiber (bn := bn) v c ↔ (parentsRestrict (bn := bn) v ω) = c := by
  rfl

lemma parentFiber_disjoint
    (v : V) (c₁ c₂ : ParentAssign (bn := bn) v) (h : c₁ ≠ c₂) :
    Disjoint (parentFiber (bn := bn) v c₁) (parentFiber (bn := bn) v c₂) := by
  classical
  refine Set.disjoint_left.mpr ?_
  intro ω hω₁ hω₂
  have h1 : parentsRestrict (bn := bn) v ω = c₁ := by
    simpa [parentFiber] using hω₁
  have h2 : parentsRestrict (bn := bn) v ω = c₂ := by
    simpa [parentFiber] using hω₂
  exact h (h1.symm.trans h2)

lemma parents_preimage_eq_iUnion
    (v : V) (S : Set (ParentAssign (bn := bn) v)) :
    (parentsRestrict (bn := bn) v) ⁻¹' S =
      ⋃ c : ParentAssign (bn := bn) v,
        (if c ∈ S then parentFiber (bn := bn) v c else (∅ : Set bn.JointSpace)) := by
  classical
  ext ω
  constructor
  · intro hω
    have hmem : parentsRestrict (bn := bn) v ω ∈ S := hω
    refine Set.mem_iUnion.mpr ?_
    refine ⟨parentsRestrict (bn := bn) v ω, ?_⟩
    by_cases h : parentsRestrict (bn := bn) v ω ∈ S
    · simp [parentFiber, h]
    · exact (h hmem).elim
  · intro hω
    rcases Set.mem_iUnion.mp hω with ⟨c, hc⟩
    by_cases h : c ∈ S
    · have hc' : ω ∈ parentFiber (bn := bn) v c := by
        simpa [h] using hc
      have hEq : parentsRestrict (bn := bn) v ω = c := by
        simpa [parentFiber] using hc'
      simpa [hEq] using h
    · have hempty : False := by
        have : ω ∈ (∅ : Set bn.JointSpace) := by
          simpa [h] using hc
        simpa using this
      exact hempty.elim

lemma measurable_parentFiber
    (v : V) [MeasurableSingletonClass (ParentAssign (bn := bn) v)]
    (c : ParentAssign (bn := bn) v) :
    @MeasurableSet _ MeasurableSpace.pi (parentFiber (bn := bn) v c) := by
  -- `parentsRestrict` is measurable on `JointSpace` with `MeasurableSpace.pi`,
  -- and fibers are preimages of singleton sets.
  have hle :
      MeasurableSpace.comap (parentsRestrict (bn := bn) v) (by infer_instance) ≤
        (MeasurableSpace.pi : MeasurableSpace bn.JointSpace) := by
    simpa [parentsRestrict,
      measurableSpaceOfVertices_eq_comap_restrict (bn := bn) (bn.graph.parents v)] using
      (bn.measurableSpaceOfVertices_le (bn.graph.parents v))
  have hmeas : Measurable (parentsRestrict (bn := bn) v) :=
    Measurable.of_comap_le hle
  simpa [parentFiber] using hmeas (measurableSet_singleton (x := c))

lemma measurable_parentFiber_vertices
    (v : V) [MeasurableSingletonClass (ParentAssign (bn := bn) v)]
    (c : ParentAssign (bn := bn) v) :
    MeasurableSet[bn.measurableSpaceOfVertices (bn.graph.parents v)]
      (parentFiber (bn := bn) v c) := by
  -- parentFiber is a singleton preimage under parentsRestrict, i.e. measurable in the
  -- parent-generated sigma-algebra by the comap characterization.
  have hcomap :
      MeasurableSet[
        MeasurableSpace.comap (parentsRestrict (bn := bn) v) (by infer_instance)]
        (parentFiber (bn := bn) v c) := by
    refine (MeasurableSpace.measurableSet_comap).2 ?_
    exact ⟨({c} : Set (ParentAssign (bn := bn) v)), measurableSet_singleton (x := c), rfl⟩
  simpa [parentsRestrict,
    measurableSpaceOfVertices_eq_comap_restrict (bn := bn) (bn.graph.parents v)]
    using hcomap

lemma setIntegral_parents_preimage
    (μ : Measure bn.JointSpace) [IsFiniteMeasure μ]
    (v : V) [MeasurableSingletonClass (ParentAssign (bn := bn) v)]
    (S : Set (ParentAssign (bn := bn) v)) (f : bn.JointSpace → ℝ)
    (hf : Integrable f μ) :
    ∫ x in (parentsRestrict (bn := bn) v) ⁻¹' S, f x ∂μ =
      ∑ c : ParentAssign (bn := bn) v,
        if c ∈ S then ∫ x in parentFiber (bn := bn) v c, f x ∂μ else 0 := by
  classical
  have hrepr := parents_preimage_eq_iUnion (bn := bn) v S
  rw [hrepr]
  have hMeas :
      ∀ c : ParentAssign (bn := bn) v,
        @MeasurableSet _ MeasurableSpace.pi
          (if c ∈ S then parentFiber (bn := bn) v c else (∅ : Set bn.JointSpace)) := by
    intro c
    by_cases hc : c ∈ S
    · simpa [hc] using measurable_parentFiber (bn := bn) v c
    · simp [hc]
  have hDisj :
      Pairwise (fun c1 c2 : ParentAssign (bn := bn) v =>
        Disjoint
          (if c1 ∈ S then parentFiber (bn := bn) v c1 else (∅ : Set bn.JointSpace))
          (if c2 ∈ S then parentFiber (bn := bn) v c2 else (∅ : Set bn.JointSpace))) := by
    intro c1 c2 hne
    by_cases hc1 : c1 ∈ S
    · by_cases hc2 : c2 ∈ S
      · simpa [hc1, hc2] using parentFiber_disjoint (bn := bn) v c1 c2 hne
      · simp [hc2]
    · simp [hc1]
  have hInt :
      ∀ c : ParentAssign (bn := bn) v,
        IntegrableOn (f := f)
          (if c ∈ S then parentFiber (bn := bn) v c else (∅ : Set bn.JointSpace)) μ := by
    intro c
    exact hf.integrableOn
  have hUnion :
      ∫ x in ⋃ c : ParentAssign (bn := bn) v,
          (if c ∈ S then parentFiber (bn := bn) v c else (∅ : Set bn.JointSpace)), f x ∂μ
        = ∑ c : ParentAssign (bn := bn) v,
            ∫ x in (if c ∈ S then parentFiber (bn := bn) v c else (∅ : Set bn.JointSpace)),
              f x ∂μ :=
    MeasureTheory.integral_iUnion_fintype
      (μ := μ) (f := f)
      (s := fun c : ParentAssign (bn := bn) v =>
        if c ∈ S then parentFiber (bn := bn) v c else (∅ : Set bn.JointSpace))
      hMeas hDisj hInt
  have hSum :
      (∑ c : ParentAssign (bn := bn) v,
          ∫ x in (if c ∈ S then parentFiber (bn := bn) v c else (∅ : Set bn.JointSpace)),
            f x ∂μ)
      = ∑ c : ParentAssign (bn := bn) v,
          if c ∈ S then ∫ x in parentFiber (bn := bn) v c, f x ∂μ else 0 := by
    refine Finset.sum_congr rfl ?_
    intro c _
    by_cases hc : c ∈ S <;> simp [hc]
  exact hUnion.trans hSum

/-- Decompose a single-vertex preimage as a finite union of `eventEq` slices. -/
lemma vertex_preimage_eq_iUnion_eventEq
    (v : V) (S : Set (bn.stateSpace v)) :
    (fun ω : bn.JointSpace => ω v) ⁻¹' S =
      ⋃ a : bn.stateSpace v,
        (if a ∈ S then eventEq (bn := bn) v a else (∅ : Set bn.JointSpace)) := by
  classical
  ext ω
  constructor
  · intro hω
    refine Set.mem_iUnion.mpr ?_
    refine ⟨ω v, ?_⟩
    by_cases hS : ω v ∈ S
    · simp [eventEq, hS]
    · exact (hS hω).elim
  · intro hω
    rcases Set.mem_iUnion.mp hω with ⟨a, ha⟩
    by_cases hS : a ∈ S
    · have : ω ∈ eventEq (bn := bn) v a := by simpa [hS] using ha
      have hv : ω v = a := by simpa [eventEq] using this
      simpa [hv] using hS
    · have : ω ∈ (∅ : Set bn.JointSpace) := by simpa [hS] using ha
      exact False.elim (by simpa using this)

/-- Distinct `eventEq` slices on the same vertex are disjoint. -/
lemma eventEq_disjoint_of_ne
    (v : V) {a₁ a₂ : bn.stateSpace v} (h : a₁ ≠ a₂) :
    Disjoint (eventEq (bn := bn) v a₁) (eventEq (bn := bn) v a₂) := by
  refine Set.disjoint_left.mpr ?_
  intro ω h1 h2
  have hv1 : ω v = a₁ := by simpa [eventEq] using h1
  have hv2 : ω v = a₂ := by simpa [eventEq] using h2
  exact h (hv1.symm.trans hv2)

/-- Set-integral decomposition over single-vertex fibers. -/
lemma setIntegral_vertex_preimage
    (μ : Measure bn.JointSpace) [IsFiniteMeasure μ]
    (v : V) [∀ v, MeasurableSingletonClass (bn.stateSpace v)]
    (S : Set (bn.stateSpace v)) (f : bn.JointSpace → ℝ)
    (hf : Integrable f μ) :
    ∫ x in (fun ω : bn.JointSpace => ω v) ⁻¹' S, f x ∂μ =
      ∑ a : bn.stateSpace v,
        if a ∈ S then ∫ x in eventEq (bn := bn) v a, f x ∂μ else 0 := by
  classical
  rw [vertex_preimage_eq_iUnion_eventEq (bn := bn) v S]
  have hMeas :
      ∀ a : bn.stateSpace v,
        @MeasurableSet _ MeasurableSpace.pi
          (if a ∈ S then eventEq (bn := bn) v a else (∅ : Set bn.JointSpace)) := by
    intro a
    by_cases ha : a ∈ S
    · simpa [ha] using measurable_eventEq (bn := bn) v a
    · simp [ha]
  have hDisj :
      Pairwise (fun a1 a2 : bn.stateSpace v =>
        Disjoint
          (if a1 ∈ S then eventEq (bn := bn) v a1 else (∅ : Set bn.JointSpace))
          (if a2 ∈ S then eventEq (bn := bn) v a2 else (∅ : Set bn.JointSpace))) := by
    intro a1 a2 hne
    by_cases h1 : a1 ∈ S
    · by_cases h2 : a2 ∈ S
      · simpa [h1, h2] using eventEq_disjoint_of_ne (bn := bn) v (a₁ := a1) (a₂ := a2) hne
      · simp [h2]
    · simp [h1]
  have hInt :
      ∀ a : bn.stateSpace v,
        IntegrableOn (f := f)
          (if a ∈ S then eventEq (bn := bn) v a else (∅ : Set bn.JointSpace)) μ := by
    intro _; exact hf.integrableOn
  have hUnion :
      ∫ x in ⋃ a : bn.stateSpace v,
          (if a ∈ S then eventEq (bn := bn) v a else (∅ : Set bn.JointSpace)), f x ∂μ
        =
      ∑ a : bn.stateSpace v,
          ∫ x in (if a ∈ S then eventEq (bn := bn) v a else (∅ : Set bn.JointSpace)),
            f x ∂μ :=
    MeasureTheory.integral_iUnion_fintype
      (μ := μ) (f := f)
      (s := fun a : bn.stateSpace v =>
        if a ∈ S then eventEq (bn := bn) v a else (∅ : Set bn.JointSpace))
      hMeas hDisj hInt
  have hSum :
      (∑ a : bn.stateSpace v,
          ∫ x in (if a ∈ S then eventEq (bn := bn) v a else (∅ : Set bn.JointSpace)), f x ∂μ)
      =
      ∑ a : bn.stateSpace v,
          if a ∈ S then ∫ x in eventEq (bn := bn) v a, f x ∂μ else 0 := by
    refine Finset.sum_congr rfl ?_
    intro a _
    by_cases ha : a ∈ S <;> simp [ha]
  exact hUnion.trans hSum

lemma jointMeasure_parentFiber_inter_as_sum
    (cpt : bn.DiscreteCPT)
    [∀ v, MeasurableSingletonClass (bn.stateSpace v)]
    (v : V) [MeasurableSingletonClass (ParentAssign (bn := bn) v)]
    (c : ParentAssign (bn := bn) v)
    {S : Set bn.JointSpace}
    (hS : @MeasurableSet _ MeasurableSpace.pi S) :
    cpt.jointMeasure (S ∩ parentFiber (bn := bn) v c) =
      ∑ x : bn.JointSpace,
        if x ∈ S ∩ parentFiber (bn := bn) v c then cpt.jointWeight x else 0 := by
  classical
  simpa using
    (BayesianNetwork.DiscreteCPT.jointMeasure_apply_as_sum
      (bn := bn) (cpt := cpt) (S := S ∩ parentFiber (bn := bn) v c)
      (hS.inter (measurable_parentFiber (bn := bn) v c)))

private lemma prod_erase_split_descendants
    (cpt : bn.DiscreteCPT) (v : V) (x : bn.JointSpace) :
    (∏ w ∈ Finset.univ.erase v, cpt.nodeProb x w)
      =
    (∏ w ∈ (Finset.univ.filter (fun w => w ∉ bn.graph.descendants v ∧ w ≠ v)),
      cpt.nodeProb x w) *
    (∏ d ∈ (Finset.univ.filter (fun d => d ∈ bn.graph.descendants v)),
      cpt.nodeProb x d) := by
  have hsplit :=
    Finset.prod_filter_mul_prod_filter_not
      (s := Finset.univ.erase v)
      (p := fun w => w ∈ bn.graph.descendants v)
      (f := fun w => cpt.nodeProb x w)
  have hdesc :
      (Finset.univ.erase v).filter (fun w => w ∈ bn.graph.descendants v)
        =
      Finset.univ.filter (fun d => d ∈ bn.graph.descendants v) := by
    ext w
    constructor
    · intro hw
      exact by simpa using (Finset.mem_filter.mp hw).2
    · intro hw
      have hw_desc : w ∈ bn.graph.descendants v := (Finset.mem_filter.mp hw).2
      have hw_ne : w ≠ v := by
        rcases hw_desc with ⟨_, hw_ne⟩
        exact hw_ne
      exact Finset.mem_filter.mpr ⟨by simpa [hw_ne], hw_desc⟩
  have hnotdesc :
      (Finset.univ.erase v).filter (fun w => w ∉ bn.graph.descendants v)
        =
      Finset.univ.filter (fun w => w ∉ bn.graph.descendants v ∧ w ≠ v) := by
    ext w
    constructor
    · intro hw
      rcases Finset.mem_filter.mp hw with ⟨hw_erase, hw_not_desc⟩
      have hw_ne : w ≠ v := (Finset.mem_erase.mp hw_erase).1
      exact Finset.mem_filter.mpr ⟨by simp, ⟨hw_not_desc, hw_ne⟩⟩
    · intro hw
      rcases Finset.mem_filter.mp hw with ⟨_, hw_pred⟩
      rcases hw_pred with ⟨hw_not_desc, hw_ne⟩
      exact Finset.mem_filter.mpr ⟨by simpa [hw_ne], hw_not_desc⟩
  calc
    (∏ w ∈ Finset.univ.erase v, cpt.nodeProb x w)
        =
      (∏ d ∈ (Finset.univ.erase v).filter (fun w => w ∈ bn.graph.descendants v),
        cpt.nodeProb x d) *
      (∏ w ∈ (Finset.univ.erase v).filter (fun w => w ∉ bn.graph.descendants v),
        cpt.nodeProb x w) := by
          simpa [mul_comm] using hsplit.symm
    _ =
      (∏ d ∈ Finset.univ.filter (fun d => d ∈ bn.graph.descendants v),
        cpt.nodeProb x d) *
      (∏ w ∈ Finset.univ.filter (fun w => w ∉ bn.graph.descendants v ∧ w ≠ v),
        cpt.nodeProb x w) := by
          simp [hdesc, hnotdesc]
    _ =
      (∏ w ∈ Finset.univ.filter (fun w => w ∉ bn.graph.descendants v ∧ w ≠ v),
        cpt.nodeProb x w) *
      (∏ d ∈ Finset.univ.filter (fun d => d ∈ bn.graph.descendants v),
        cpt.nodeProb x d) := by
          ring

private lemma jointWeight_split_descendants
    (cpt : bn.DiscreteCPT) (v : V) (x : bn.JointSpace) :
    cpt.jointWeight x
      =
    cpt.nodeProb x v *
      (∏ w ∈ (Finset.univ.filter (fun w => w ∉ bn.graph.descendants v ∧ w ≠ v)),
        cpt.nodeProb x w) *
      (∏ d ∈ (Finset.univ.filter (fun d => d ∈ bn.graph.descendants v)),
        cpt.nodeProb x d) := by
  calc
    cpt.jointWeight x
        = cpt.nodeProb x v * ∏ w ∈ Finset.univ.erase v, cpt.nodeProb x w := by
            simpa using jointWeight_factor_single (bn := bn) (cpt := cpt) v x
    _ =
      cpt.nodeProb x v *
      ((∏ w ∈ (Finset.univ.filter (fun w => w ∉ bn.graph.descendants v ∧ w ≠ v)),
          cpt.nodeProb x w) *
        (∏ d ∈ (Finset.univ.filter (fun d => d ∈ bn.graph.descendants v)),
          cpt.nodeProb x d)) := by
            simp [prod_erase_split_descendants (bn := bn) (cpt := cpt) (v := v) (x := x)]
    _ =
      cpt.nodeProb x v *
      (∏ w ∈ (Finset.univ.filter (fun w => w ∉ bn.graph.descendants v ∧ w ≠ v)),
        cpt.nodeProb x w) *
      (∏ d ∈ (Finset.univ.filter (fun d => d ∈ bn.graph.descendants v)),
        cpt.nodeProb x d) := by
          ring

/-! ### Descendant-sum helper

These lemmas are used to collapse sums over descendant assignments in the
fiber-screening proof. They isolate the dependence on `x_v` and the ND-part
from the descendant product, which telescopes to 1.
-/

theorem descendant_not_parent
    (v d : V) (hd : d ∈ bn.graph.descendants v) : d ∉ bn.graph.parents v := by
  intro hdpar
  rcases hd with ⟨hvd, _hvd_ne⟩
  exact bn.acyclic d ⟨v, hdpar, hvd⟩

theorem nodeProb_patch_descendants_at_v
    (cpt : bn.DiscreteCPT) (v : V) (D : Finset V)
    (hD_desc : ∀ d, d ∈ D → d ∈ bn.graph.descendants v)
    (x : bn.JointSpace) (xD : ∀ d : ↥D, bn.stateSpace d) :
    cpt.nodeProb (patchConfig bn x D xD) v = cpt.nodeProb x v := by
  have hv_not_desc : v ∉ bn.graph.descendants v := by
    intro hv
    rcases hv with ⟨_hvv, hvne⟩
    exact hvne rfl
  exact nodeProb_patch_descendants_irrelevant bn cpt v v D hD_desc x xD hv_not_desc

private lemma sum_descendants_jointWeight
    (cpt : bn.DiscreteCPT) (v : V) (x : bn.JointSpace) (D : Finset V)
    (hD_desc : ∀ d, d ∈ D → d ∈ bn.graph.descendants v)
    (hD : D = Finset.univ.filter (fun d => d ∈ bn.graph.descendants v)) :
    (∑ xD : (∀ d : ↥D, bn.stateSpace d),
        cpt.jointWeight (patchConfig bn x D xD))
      =
      cpt.nodeProb x v *
        (∏ w ∈ (Finset.univ.filter (fun w => w ∉ bn.graph.descendants v ∧ w ≠ v)),
          cpt.nodeProb x w) := by
  classical
  have hnode_v :
      ∀ xD : (∀ d : ↥D, bn.stateSpace d),
        cpt.nodeProb (patchConfig bn x D xD) v = cpt.nodeProb x v := by
    intro xD
    exact nodeProb_patch_descendants_at_v bn cpt v D hD_desc x xD
  have hprod_nd :
      ∀ xD : (∀ d : ↥D, bn.stateSpace d),
        (∏ w ∈ (Finset.univ.filter (fun w => w ∉ bn.graph.descendants v ∧ w ≠ v)),
            cpt.nodeProb (patchConfig bn x D xD) w)
          =
        (∏ w ∈ (Finset.univ.filter (fun w => w ∉ bn.graph.descendants v ∧ w ≠ v)),
            cpt.nodeProb x w) := by
    intro xD
    exact prod_notDescNotSelf_patch_descendants_irrelevant bn cpt v D hD_desc x xD
  set cconst :=
    cpt.nodeProb x v *
      (∏ w ∈ (Finset.univ.filter (fun w => w ∉ bn.graph.descendants v ∧ w ≠ v)),
          cpt.nodeProb x w)
  calc
    (∑ xD : (∀ d : ↥D, bn.stateSpace d),
        cpt.jointWeight (patchConfig bn x D xD))
        =
      ∑ xD : (∀ d : ↥D, bn.stateSpace d),
        cconst *
          (∏ d ∈ (Finset.univ.filter (fun d => d ∈ bn.graph.descendants v)),
              cpt.nodeProb (patchConfig bn x D xD) d) := by
        refine Finset.sum_congr rfl ?_
        intro xD _
        have hsplit := jointWeight_split_descendants (bn := bn) (cpt := cpt) (v := v)
          (x := patchConfig bn x D xD)
        -- Replace the v-part and ND-part by constants using hnode_v and hprod_nd
        -- and keep descendant product as-is.
        simpa [hnode_v xD, hprod_nd xD, cconst, mul_assoc, mul_left_comm, mul_comm] using hsplit
    _ =
      cconst *
        ∑ xD : (∀ d : ↥D, bn.stateSpace d),
          (∏ d : ↥D, cpt.nodeProb (patchConfig bn x D xD) d) := by
        -- rewrite the descendant product using hD, then pull out constants
        have hD' :
            (Finset.univ.filter (fun d => d ∈ bn.graph.descendants v)) = D := by
          simpa using hD.symm
        have hprod_desc :
            ∀ xD : (∀ d : ↥D, bn.stateSpace d),
              (∏ d ∈ D, cpt.nodeProb (patchConfig bn x D xD) d)
                =
              ∏ d : ↥D, cpt.nodeProb (patchConfig bn x D xD) d := by
          intro xD
          -- product over the finset equals product over the attached subtype
          simpa using (Finset.prod_attach (s := D)
            (f := fun d => cpt.nodeProb (patchConfig bn x D xD) d)).symm
        -- now pull out constants from the sum
        -- rewrite the product inside the sum to a product over the subtype
        have hsum_rewrite :
            (∑ xD : (∀ d : ↥D, bn.stateSpace d),
                cconst *
                  (∏ d ∈ (Finset.univ.filter (fun d => d ∈ bn.graph.descendants v)),
                      cpt.nodeProb (patchConfig bn x D xD) d))
              =
            ∑ xD : (∀ d : ↥D, bn.stateSpace d),
              cconst * (∏ d : ↥D, cpt.nodeProb (patchConfig bn x D xD) d) := by
          refine Finset.sum_congr rfl ?_
          intro xD _
          simp [hD', hprod_desc xD, cconst, mul_assoc]
        -- pull out constants
        calc
          (∑ xD : (∀ d : ↥D, bn.stateSpace d),
              cconst *
                (∏ d ∈ (Finset.univ.filter (fun d => d ∈ bn.graph.descendants v)),
                    cpt.nodeProb (patchConfig bn x D xD) d))
              =
            ∑ xD : (∀ d : ↥D, bn.stateSpace d),
              cconst * (∏ d : ↥D, cpt.nodeProb (patchConfig bn x D xD) d) := by
                exact hsum_rewrite
          _ = cconst *
              ∑ xD : (∀ d : ↥D, bn.stateSpace d),
                (∏ d : ↥D, cpt.nodeProb (patchConfig bn x D xD) d) := by
                -- pull cconst out of the sum
                simp [Finset.mul_sum, mul_assoc, cconst]
    _ =
      cpt.nodeProb x v *
        (∏ w ∈ (Finset.univ.filter (fun w => w ∉ bn.graph.descendants v ∧ w ≠ v)),
            cpt.nodeProb x w) * 1 := by
        -- telescoping sum on descendants
        have htel := telescoping_sum (bn := bn) (cpt := cpt) (D := D) (x := x)
        -- rewrite the sum to 1, then simp
        have htel' := congrArg (fun t => cconst * t) htel
        simpa [cconst, mul_assoc, mul_left_comm, mul_comm] using htel'
    _ =
      cpt.nodeProb x v *
        (∏ w ∈ (Finset.univ.filter (fun w => w ∉ bn.graph.descendants v ∧ w ≠ v)),
            cpt.nodeProb x w) := by
        simp

/-! ### Reindex bridge: split `JointSpace` into descendant/non-descendant coordinates

These helpers provide the concrete reindexing bridge needed by the fiber-screening step:
`JointSpace` is split via `Equiv.piEquivPiSubtypeProd`, and descendant assignments are
connected to the finite `patchConfig` representation used by `sum_descendants_jointWeight`.
-/

private noncomputable def descSetToFin
    (v : V)
    (xD : ∀ d : {d // d ∈ bn.graph.descendants v}, bn.stateSpace d) :
    ∀ d : ↥(Finset.univ.filter (fun d => d ∈ bn.graph.descendants v)), bn.stateSpace d :=
  fun d => xD ⟨d.1, (Finset.mem_filter.mp d.2).2⟩

private noncomputable def descFinToSet
    (v : V)
    (xD : ∀ d : ↥(Finset.univ.filter (fun d => d ∈ bn.graph.descendants v)), bn.stateSpace d) :
    ∀ d : {d // d ∈ bn.graph.descendants v}, bn.stateSpace d :=
  fun d => xD ⟨d.1, Finset.mem_filter.mpr ⟨Finset.mem_univ d.1, d.2⟩⟩

private noncomputable def descAssignEquiv
    (v : V) :
    (∀ d : {d // d ∈ bn.graph.descendants v}, bn.stateSpace d) ≃
      (∀ d : ↥(Finset.univ.filter (fun d => d ∈ bn.graph.descendants v)), bn.stateSpace d) where
  toFun := descSetToFin (bn := bn) v
  invFun := descFinToSet (bn := bn) v
  left_inv := by
    intro xD
    funext d
    simp [descSetToFin, descFinToSet]
  right_inv := by
    intro xD
    funext d
    simp [descSetToFin, descFinToSet]

private noncomputable def baseFromNonDesc
    (v : V)
    (xND : ∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n) :
    bn.JointSpace :=
  fun u =>
    if hu : u ∈ bn.graph.descendants v then
      Classical.choice (inferInstance : Nonempty (bn.stateSpace u))
    else
      xND ⟨u, hu⟩

private noncomputable def mergeDescNonDesc
    (v : V)
    (xND : ∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n)
    (xD : ∀ d : {d // d ∈ bn.graph.descendants v}, bn.stateSpace d) :
    bn.JointSpace :=
  patchConfig bn
    (baseFromNonDesc (bn := bn) v xND)
    (Finset.univ.filter (fun d => d ∈ bn.graph.descendants v))
    (descSetToFin (bn := bn) v xD)

private lemma piEquiv_descendants_symm_eq_merge
    (v : V)
    (xD : ∀ d : {d // d ∈ bn.graph.descendants v}, bn.stateSpace d)
    (xND : ∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n) :
    (Equiv.piEquivPiSubtypeProd (p := fun d : V => d ∈ bn.graph.descendants v)
      (β := fun d : V => bn.stateSpace d)).symm (xD, xND)
      =
    mergeDescNonDesc (bn := bn) v xND xD := by
  funext u
  by_cases hu : u ∈ bn.graph.descendants v
  · have hDmem : u ∈ Finset.univ.filter (fun d => d ∈ bn.graph.descendants v) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, hu⟩
    calc
      (Equiv.piEquivPiSubtypeProd (p := fun d : V => d ∈ bn.graph.descendants v)
          (β := fun d : V => bn.stateSpace d)).symm (xD, xND) u
          = xD ⟨u, hu⟩ := by
              simp [Equiv.piEquivPiSubtypeProd, hu]
      _ =
        patchConfig bn
          (baseFromNonDesc (bn := bn) v xND)
          (Finset.univ.filter (fun d => d ∈ bn.graph.descendants v))
          (descSetToFin (bn := bn) v xD) u := by
            simp [patchConfig_inside (bn := bn)
              (x := baseFromNonDesc (bn := bn) v xND)
              (D := Finset.univ.filter (fun d => d ∈ bn.graph.descendants v))
              (xD := descSetToFin (bn := bn) v xD)
              (v := u) hDmem, descSetToFin]
  · have hDnot : u ∉ Finset.univ.filter (fun d => d ∈ bn.graph.descendants v) := by
      intro hmem
      exact hu (Finset.mem_filter.mp hmem).2
    calc
      (Equiv.piEquivPiSubtypeProd (p := fun d : V => d ∈ bn.graph.descendants v)
          (β := fun d : V => bn.stateSpace d)).symm (xD, xND) u
          = xND ⟨u, hu⟩ := by
              simp [Equiv.piEquivPiSubtypeProd, hu]
      _ =
        patchConfig bn
          (baseFromNonDesc (bn := bn) v xND)
          (Finset.univ.filter (fun d => d ∈ bn.graph.descendants v))
          (descSetToFin (bn := bn) v xD) u := by
            simp [patchConfig_outside (bn := bn)
              (x := baseFromNonDesc (bn := bn) v xND)
              (D := Finset.univ.filter (fun d => d ∈ bn.graph.descendants v))
              (xD := descSetToFin (bn := bn) v xD)
              (v := u) hDnot, baseFromNonDesc, hu]

private lemma sum_reindex_desc_nonDesc
    (v : V) (f : bn.JointSpace → ENNReal) :
    (∑ x : bn.JointSpace, f x)
      =
    ∑ xD : (∀ d : {d // d ∈ bn.graph.descendants v}, bn.stateSpace d),
      ∑ xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n),
        f (mergeDescNonDesc (bn := bn) v xND xD) := by
  classical
  let e :
      bn.JointSpace ≃
        (∀ d : {d // d ∈ bn.graph.descendants v}, bn.stateSpace d) ×
          (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n) :=
    Equiv.piEquivPiSubtypeProd (p := fun d : V => d ∈ bn.graph.descendants v)
      (β := fun d : V => bn.stateSpace d)
  calc
    (∑ x : bn.JointSpace, f x)
        =
      ∑ p :
          (∀ d : {d // d ∈ bn.graph.descendants v}, bn.stateSpace d) ×
            (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n),
        f (e.symm p) := by
          refine Fintype.sum_equiv e f (fun p => f (e.symm p)) ?_
          intro x
          simpa [e] using congrArg f ((Equiv.symm_apply_apply e x).symm)
    _ =
      ∑ xD : (∀ d : {d // d ∈ bn.graph.descendants v}, bn.stateSpace d),
        ∑ xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n),
          f (e.symm (xD, xND)) := by
            simpa using
              (Fintype.sum_prod_type
                (f := fun p :
                    (∀ d : {d // d ∈ bn.graph.descendants v}, bn.stateSpace d) ×
                      (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n) =>
                  f (e.symm p)))
    _ =
      ∑ xD : (∀ d : {d // d ∈ bn.graph.descendants v}, bn.stateSpace d),
        ∑ xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n),
          f (mergeDescNonDesc (bn := bn) v xND xD) := by
            refine Finset.sum_congr rfl ?_
            intro xD _
            refine Finset.sum_congr rfl ?_
            intro xND _
            simpa [e] using congrArg f
              (piEquiv_descendants_symm_eq_merge (bn := bn) (v := v) (xD := xD) (xND := xND))

private lemma sum_descendants_jointWeight_over_nonDesc
    (cpt : bn.DiscreteCPT) (v : V)
    (xND : ∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n) :
    (∑ xD : (∀ d : {d // d ∈ bn.graph.descendants v}, bn.stateSpace d),
        cpt.jointWeight (mergeDescNonDesc (bn := bn) v xND xD))
      =
    cpt.nodeProb (baseFromNonDesc (bn := bn) v xND) v *
      (∏ w ∈ (Finset.univ.filter (fun w => w ∉ bn.graph.descendants v ∧ w ≠ v)),
        cpt.nodeProb (baseFromNonDesc (bn := bn) v xND) w) := by
  classical
  have hD_desc :
      ∀ d, d ∈ (Finset.univ.filter (fun d => d ∈ bn.graph.descendants v)) →
        d ∈ bn.graph.descendants v := by
    intro d hd
    exact (Finset.mem_filter.mp hd).2
  calc
    (∑ xD : (∀ d : {d // d ∈ bn.graph.descendants v}, bn.stateSpace d),
        cpt.jointWeight (mergeDescNonDesc (bn := bn) v xND xD))
        =
      ∑ xD : (∀ d : ↥(Finset.univ.filter (fun d => d ∈ bn.graph.descendants v)), bn.stateSpace d),
        cpt.jointWeight
          (patchConfig bn
            (baseFromNonDesc (bn := bn) v xND)
            (Finset.univ.filter (fun d => d ∈ bn.graph.descendants v))
            xD) := by
              calc
                (∑ xD : (∀ d : {d // d ∈ bn.graph.descendants v}, bn.stateSpace d),
                    cpt.jointWeight (mergeDescNonDesc (bn := bn) v xND xD))
                    =
                  ∑ xD :
                      (∀ d : ↥(Finset.univ.filter (fun d => d ∈ bn.graph.descendants v)),
                        bn.stateSpace d),
                    cpt.jointWeight
                      (mergeDescNonDesc (bn := bn) v xND
                        ((descAssignEquiv (bn := bn) v).symm xD)) := by
                          refine Fintype.sum_equiv (descAssignEquiv (bn := bn) v)
                            (fun xD =>
                              cpt.jointWeight (mergeDescNonDesc (bn := bn) v xND xD))
                            (fun xD =>
                              cpt.jointWeight
                                (mergeDescNonDesc (bn := bn) v xND
                                  ((descAssignEquiv (bn := bn) v).symm xD))) ?_
                          intro xD
                          rfl
                _ =
                  ∑ xD :
                      (∀ d : ↥(Finset.univ.filter (fun d => d ∈ bn.graph.descendants v)),
                        bn.stateSpace d),
                    cpt.jointWeight
                      (patchConfig bn
                        (baseFromNonDesc (bn := bn) v xND)
                        (Finset.univ.filter (fun d => d ∈ bn.graph.descendants v))
                        xD) := by
                          refine Finset.sum_congr rfl ?_
                          intro xD _
                          have hround :
                              descSetToFin (bn := bn) v ((descAssignEquiv (bn := bn) v).symm xD)
                                = xD := by
                            exact
                              (Equiv.apply_symm_apply (descAssignEquiv (bn := bn) v) xD)
                          simp [mergeDescNonDesc, hround]
    _ =
      cpt.nodeProb (baseFromNonDesc (bn := bn) v xND) v *
        (∏ w ∈ (Finset.univ.filter (fun w => w ∉ bn.graph.descendants v ∧ w ≠ v)),
          cpt.nodeProb (baseFromNonDesc (bn := bn) v xND) w) := by
            simpa using
              (sum_descendants_jointWeight (bn := bn) (cpt := cpt) (v := v)
                (x := baseFromNonDesc (bn := bn) v xND)
                (D := Finset.univ.filter (fun d => d ∈ bn.graph.descendants v))
                hD_desc rfl)

private lemma sum_jointWeight_reindex_and_collapse
    (cpt : bn.DiscreteCPT) (v : V) :
    (∑ x : bn.JointSpace, cpt.jointWeight x)
      =
    ∑ xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n),
      cpt.nodeProb (baseFromNonDesc (bn := bn) v xND) v *
        (∏ w ∈ (Finset.univ.filter (fun w => w ∉ bn.graph.descendants v ∧ w ≠ v)),
          cpt.nodeProb (baseFromNonDesc (bn := bn) v xND) w) := by
  classical
  calc
    (∑ x : bn.JointSpace, cpt.jointWeight x)
        =
      ∑ xD : (∀ d : {d // d ∈ bn.graph.descendants v}, bn.stateSpace d),
        ∑ xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n),
          cpt.jointWeight (mergeDescNonDesc (bn := bn) v xND xD) := by
            exact sum_reindex_desc_nonDesc (bn := bn) (v := v) (f := cpt.jointWeight)
    _ =
      ∑ xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n),
        ∑ xD : (∀ d : {d // d ∈ bn.graph.descendants v}, bn.stateSpace d),
          cpt.jointWeight (mergeDescNonDesc (bn := bn) v xND xD) := by
            simpa using
              (Finset.sum_comm
                (f := fun xD
                    (xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n)) =>
                  cpt.jointWeight (mergeDescNonDesc (bn := bn) v xND xD)))
    _ =
      ∑ xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n),
        cpt.nodeProb (baseFromNonDesc (bn := bn) v xND) v *
          (∏ w ∈ (Finset.univ.filter (fun w => w ∉ bn.graph.descendants v ∧ w ≠ v)),
            cpt.nodeProb (baseFromNonDesc (bn := bn) v xND) w) := by
              refine Finset.sum_congr rfl ?_
              intro xND _
              exact sum_descendants_jointWeight_over_nonDesc (bn := bn) (cpt := cpt)
                (v := v) xND

private lemma sum_descendants_jointWeight_over_nonDesc_if
    (cpt : bn.DiscreteCPT) (v : V)
    (xND : ∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n)
    (P : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n) → Prop) :
    (∑ xD : (∀ d : {d // d ∈ bn.graph.descendants v}, bn.stateSpace d),
        (if P xND then cpt.jointWeight (mergeDescNonDesc (bn := bn) v xND xD) else 0))
      =
    if P xND then
      cpt.nodeProb (baseFromNonDesc (bn := bn) v xND) v *
        (∏ w ∈ (Finset.univ.filter (fun w => w ∉ bn.graph.descendants v ∧ w ≠ v)),
          cpt.nodeProb (baseFromNonDesc (bn := bn) v xND) w)
    else 0 := by
  by_cases hP : P xND
  · simp [hP, sum_descendants_jointWeight_over_nonDesc]
  · simp [hP]

private lemma sum_jointWeight_reindex_and_collapse_of_desc_irrel
    (cpt : bn.DiscreteCPT) (v : V)
    (Q : bn.JointSpace → Prop)
    (P : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n) → Prop)
    (hQP :
      ∀ xND xD,
        Q (mergeDescNonDesc (bn := bn) v xND xD) ↔ P xND) :
    (∑ x : bn.JointSpace, if Q x then cpt.jointWeight x else 0)
      =
    ∑ xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n),
      if P xND then
        cpt.nodeProb (baseFromNonDesc (bn := bn) v xND) v *
          (∏ w ∈ (Finset.univ.filter (fun w => w ∉ bn.graph.descendants v ∧ w ≠ v)),
            cpt.nodeProb (baseFromNonDesc (bn := bn) v xND) w)
      else 0 := by
  classical
  calc
    (∑ x : bn.JointSpace, if Q x then cpt.jointWeight x else 0)
        =
      ∑ xD : (∀ d : {d // d ∈ bn.graph.descendants v}, bn.stateSpace d),
        ∑ xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n),
          (if Q (mergeDescNonDesc (bn := bn) v xND xD)
            then cpt.jointWeight (mergeDescNonDesc (bn := bn) v xND xD) else 0) := by
            exact sum_reindex_desc_nonDesc (bn := bn) (v := v)
              (f := fun x => if Q x then cpt.jointWeight x else 0)
    _ =
      ∑ xD : (∀ d : {d // d ∈ bn.graph.descendants v}, bn.stateSpace d),
        ∑ xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n),
          (if P xND
            then cpt.jointWeight (mergeDescNonDesc (bn := bn) v xND xD) else 0) := by
            refine Finset.sum_congr rfl ?_
            intro xD _
            refine Finset.sum_congr rfl ?_
            intro xND _
            by_cases hP : P xND
            · have hQ : Q (mergeDescNonDesc (bn := bn) v xND xD) := (hQP xND xD).2 hP
              simp [hP, hQ]
            · have hQ : ¬ Q (mergeDescNonDesc (bn := bn) v xND xD) := by
                intro hQ
                exact hP ((hQP xND xD).1 hQ)
              simp [hP, hQ]
    _ =
      ∑ xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n),
        ∑ xD : (∀ d : {d // d ∈ bn.graph.descendants v}, bn.stateSpace d),
          (if P xND
            then cpt.jointWeight (mergeDescNonDesc (bn := bn) v xND xD) else 0) := by
            simpa using
              (Finset.sum_comm
                (f := fun xD
                    (xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n)) =>
                  if P xND then cpt.jointWeight (mergeDescNonDesc (bn := bn) v xND xD) else 0))
    _ =
      ∑ xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n),
        if P xND then
          cpt.nodeProb (baseFromNonDesc (bn := bn) v xND) v *
            (∏ w ∈ (Finset.univ.filter (fun w => w ∉ bn.graph.descendants v ∧ w ≠ v)),
              cpt.nodeProb (baseFromNonDesc (bn := bn) v xND) w)
        else 0 := by
          refine Finset.sum_congr rfl ?_
          intro xND _
          simpa using
            (sum_descendants_jointWeight_over_nonDesc_if (bn := bn) (cpt := cpt) (v := v)
              (xND := xND) (P := P))

/-- Per-parent-fiber screening identity for a discrete CPT joint measure.

This is the algebraic core behind the local-Markov proof and a reusable finite
bridge for later BN soundness work: once the parent assignment `c` is fixed,
the event determined by `v` and the event determined by
`ND(v) \ (Pa(v) ∪ {v})` multiply over the parent fiber `F_c`. -/
theorem jointMeasure_parentFiber_screening_mul
    (cpt : bn.DiscreteCPT) (v : V)
    (B : Set bn.JointSpace)
    (hB : MeasurableSet[bn.measurableSpaceOfVertices ({v} : Set V)] B)
    (t₂ : Set bn.JointSpace)
    (ht₂ : MeasurableSet[bn.measurableSpaceOfVertices
            (bn.nonDescendantsExceptParentsAndSelf v)] t₂)
    (c : ParentAssign (bn := bn) v) :
    cpt.jointMeasure (((B ∩ t₂)) ∩ parentFiber (bn := bn) v c) *
      cpt.jointMeasure (parentFiber (bn := bn) v c)
      =
      cpt.jointMeasure (B ∩ parentFiber (bn := bn) v c) *
      cpt.jointMeasure (t₂ ∩ parentFiber (bn := bn) v c) := by
  -- Reduce measurable sets to finite coordinate-restriction preimages.
  rcases measurableSet_singleton_preimage (bn := bn) (v := v) (s := B) hB with
    ⟨SB, hSB, hBpre⟩
  rcases measurableSet_vertices_preimage (bn := bn)
    (S := bn.nonDescendantsExceptParentsAndSelf v) (s := t₂) ht₂ with
    ⟨SND, hSND, ht₂pre⟩
  subst hBpre
  subst ht₂pre
  let F : Set bn.JointSpace := parentFiber (bn := bn) v c
  have hB_pi : @MeasurableSet _ MeasurableSpace.pi ((fun ω : bn.JointSpace => ω v) ⁻¹' SB) := by
    exact (measurable_pi_apply v) hSB
  have hRestr_meas : Measurable (restrictToSet (bn := bn) (bn.nonDescendantsExceptParentsAndSelf v)) := by
    have hle :
        MeasurableSpace.comap
          (restrictToSet (bn := bn) (bn.nonDescendantsExceptParentsAndSelf v))
          (by infer_instance)
          ≤ (MeasurableSpace.pi : MeasurableSpace bn.JointSpace) := by
      simpa [measurableSpaceOfVertices_eq_comap_restrict (bn := bn)
        (bn.nonDescendantsExceptParentsAndSelf v)] using
        (bn.measurableSpaceOfVertices_le (bn.nonDescendantsExceptParentsAndSelf v))
    exact Measurable.of_comap_le hle
  have ht₂_pi :
      @MeasurableSet _ MeasurableSpace.pi
        ((restrictToSet (bn := bn) (bn.nonDescendantsExceptParentsAndSelf v)) ⁻¹' SND) := by
    exact hRestr_meas hSND
  have hBt₂_pi :
      @MeasurableSet _ MeasurableSpace.pi
        (((fun ω : bn.JointSpace => ω v) ⁻¹' SB) ∩
         ((restrictToSet (bn := bn) (bn.nonDescendantsExceptParentsAndSelf v)) ⁻¹' SND)) := by
    exact hB_pi.inter ht₂_pi
  have hμ_BtF :
      cpt.jointMeasure ((((fun ω : bn.JointSpace => ω v) ⁻¹' SB) ∩
        ((restrictToSet (bn := bn) (bn.nonDescendantsExceptParentsAndSelf v)) ⁻¹' SND)) ∩ F) =
      ∑ x : bn.JointSpace,
        if x ∈ ((((fun ω : bn.JointSpace => ω v) ⁻¹' SB) ∩
          ((restrictToSet (bn := bn) (bn.nonDescendantsExceptParentsAndSelf v)) ⁻¹' SND)) ∩ F)
        then cpt.jointWeight x else 0 := by
    simpa [F] using
      (jointMeasure_parentFiber_inter_as_sum (bn := bn) (cpt := cpt) (v := v) (c := c)
        (S := (((fun ω : bn.JointSpace => ω v) ⁻¹' SB) ∩
          ((restrictToSet (bn := bn) (bn.nonDescendantsExceptParentsAndSelf v)) ⁻¹' SND)))
        hBt₂_pi)
  have hμ_BF :
      cpt.jointMeasure (((fun ω : bn.JointSpace => ω v) ⁻¹' SB) ∩ F) =
      ∑ x : bn.JointSpace,
        if x ∈ (((fun ω : bn.JointSpace => ω v) ⁻¹' SB) ∩ F) then cpt.jointWeight x else 0 := by
    simpa [F] using
      (jointMeasure_parentFiber_inter_as_sum (bn := bn) (cpt := cpt) (v := v) (c := c)
        (S := ((fun ω : bn.JointSpace => ω v) ⁻¹' SB)) hB_pi)
  have hμ_t₂F :
      cpt.jointMeasure
        (((restrictToSet (bn := bn) (bn.nonDescendantsExceptParentsAndSelf v)) ⁻¹' SND) ∩ F) =
      ∑ x : bn.JointSpace,
        if x ∈ (((restrictToSet (bn := bn) (bn.nonDescendantsExceptParentsAndSelf v)) ⁻¹' SND) ∩ F)
        then cpt.jointWeight x else 0 := by
    simpa [F] using
      (jointMeasure_parentFiber_inter_as_sum (bn := bn) (cpt := cpt) (v := v) (c := c)
        (S := ((restrictToSet (bn := bn) (bn.nonDescendantsExceptParentsAndSelf v)) ⁻¹' SND))
        ht₂_pi)
  have hμ_F :
      cpt.jointMeasure F =
      ∑ x : bn.JointSpace, if x ∈ F then cpt.jointWeight x else 0 := by
    simpa [F] using
      (jointMeasure_parentFiber_inter_as_sum (bn := bn) (cpt := cpt) (v := v) (c := c)
        (S := (Set.univ : Set bn.JointSpace)) MeasurableSet.univ)
  let Bset : Set bn.JointSpace := ((fun ω : bn.JointSpace => ω v) ⁻¹' SB)
  let Tset : Set bn.JointSpace :=
    ((restrictToSet (bn := bn) (bn.nonDescendantsExceptParentsAndSelf v)) ⁻¹' SND)
  let S_BtF : Set bn.JointSpace := (Bset ∩ Tset) ∩ F
  let S_BF : Set bn.JointSpace := Bset ∩ F
  let S_t₂F : Set bn.JointSpace := Tset ∩ F
  let P_BtF :
      (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n) → Prop :=
    fun xND => baseFromNonDesc (bn := bn) v xND ∈ S_BtF
  let P_BF :
      (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n) → Prop :=
    fun xND => baseFromNonDesc (bn := bn) v xND ∈ S_BF
  let P_t₂F :
      (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n) → Prop :=
    fun xND => baseFromNonDesc (bn := bn) v xND ∈ S_t₂F
  let P_F :
      (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n) → Prop :=
    fun xND => baseFromNonDesc (bn := bn) v xND ∈ F
  let A :
      (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n) → ENNReal :=
    fun xND =>
      cpt.nodeProb (baseFromNonDesc (bn := bn) v xND) v *
        (∏ w ∈ (Finset.univ.filter (fun w => w ∉ bn.graph.descendants v ∧ w ≠ v)),
          cpt.nodeProb (baseFromNonDesc (bn := bn) v xND) w)
  have hv_not_desc : v ∉ bn.graph.descendants v := by
    intro hv
    rcases hv with ⟨_, hv_ne⟩
    exact hv_ne rfl
  have hmerge_eq_base_of_not_desc :
      ∀ (xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n))
        (xD : (∀ d : {d // d ∈ bn.graph.descendants v}, bn.stateSpace d))
        (u : V),
        u ∉ bn.graph.descendants v →
          mergeDescNonDesc (bn := bn) v xND xD u = baseFromNonDesc (bn := bn) v xND u := by
    intro xND xD u hu
    have hu_not_memD : u ∉ Finset.univ.filter (fun d => d ∈ bn.graph.descendants v) := by
      intro huD
      exact hu ((Finset.mem_filter.mp huD).2)
    simpa [mergeDescNonDesc] using
      (patchConfig_outside (bn := bn)
        (x := baseFromNonDesc (bn := bn) v xND)
        (D := Finset.univ.filter (fun d => d ∈ bn.graph.descendants v))
        (xD := descSetToFin (bn := bn) v xD)
        (v := u) hu_not_memD)
  have hmerge_eq_base_at_v :
      ∀ (xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n))
        (xD : (∀ d : {d // d ∈ bn.graph.descendants v}, bn.stateSpace d)),
        mergeDescNonDesc (bn := bn) v xND xD v = baseFromNonDesc (bn := bn) v xND v := by
    intro xND xD
    exact hmerge_eq_base_of_not_desc xND xD v hv_not_desc
  have hmerge_eq_base_on_restrictND :
      ∀ (xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n))
        (xD : (∀ d : {d // d ∈ bn.graph.descendants v}, bn.stateSpace d)),
        restrictToSet (bn := bn) (bn.nonDescendantsExceptParentsAndSelf v)
          (mergeDescNonDesc (bn := bn) v xND xD)
          =
        restrictToSet (bn := bn) (bn.nonDescendantsExceptParentsAndSelf v)
          (baseFromNonDesc (bn := bn) v xND) := by
    intro xND xD
    funext u
    have hu_not_desc : u.1 ∉ bn.graph.descendants v := by
      have hu_mem : u.1 ∈ bn.nonDescendantsExceptParentsAndSelf v := u.2
      have hu_mem' :
          u.1 ∉ bn.graph.descendants v ∧ u.1 ∉ bn.graph.parents v ∪ ({v} : Set V) := by
        simpa [BayesianNetwork.nonDescendantsExceptParentsAndSelf, Set.mem_diff] using hu_mem
      exact hu_mem'.1
    exact hmerge_eq_base_of_not_desc xND xD u.1 hu_not_desc
  have hmerge_eq_base_on_parents :
      ∀ (xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n))
        (xD : (∀ d : {d // d ∈ bn.graph.descendants v}, bn.stateSpace d)),
        parentsRestrict (bn := bn) v (mergeDescNonDesc (bn := bn) v xND xD)
          =
        parentsRestrict (bn := bn) v (baseFromNonDesc (bn := bn) v xND) := by
    intro xND xD
    funext p
    have hp_not_desc : p.1 ∉ bn.graph.descendants v := by
      intro hp_desc
      exact (descendant_not_parent (bn := bn) (v := v) (d := p.1) hp_desc) p.2
    exact hmerge_eq_base_of_not_desc xND xD p.1 hp_not_desc
  have hQP_BtF :
      ∀ xND xD,
        ((mergeDescNonDesc (bn := bn) v xND xD) ∈ S_BtF) ↔ P_BtF xND := by
    intro xND xD
    have hB :
        ((mergeDescNonDesc (bn := bn) v xND xD) ∈ Bset) ↔
          ((baseFromNonDesc (bn := bn) v xND) ∈ Bset) := by
      simp [Bset, hmerge_eq_base_at_v xND xD]
    have hT :
        ((mergeDescNonDesc (bn := bn) v xND xD) ∈ Tset) ↔
          ((baseFromNonDesc (bn := bn) v xND) ∈ Tset) := by
      simp [Tset, hmerge_eq_base_on_restrictND xND xD]
    have hFm :
        ((mergeDescNonDesc (bn := bn) v xND xD) ∈ F) ↔
          ((baseFromNonDesc (bn := bn) v xND) ∈ F) := by
      simp [F, parentFiber, hmerge_eq_base_on_parents xND xD]
    simp [P_BtF, S_BtF, Set.mem_inter_iff, hB, hT, hFm]
  have hQP_BF :
      ∀ xND xD,
        ((mergeDescNonDesc (bn := bn) v xND xD) ∈ S_BF) ↔ P_BF xND := by
    intro xND xD
    have hB :
        ((mergeDescNonDesc (bn := bn) v xND xD) ∈ Bset) ↔
          ((baseFromNonDesc (bn := bn) v xND) ∈ Bset) := by
      simp [Bset, hmerge_eq_base_at_v xND xD]
    have hFm :
        ((mergeDescNonDesc (bn := bn) v xND xD) ∈ F) ↔
          ((baseFromNonDesc (bn := bn) v xND) ∈ F) := by
      simp [F, parentFiber, hmerge_eq_base_on_parents xND xD]
    simp [P_BF, S_BF, Set.mem_inter_iff, hB, hFm]
  have hQP_t₂F :
      ∀ xND xD,
        ((mergeDescNonDesc (bn := bn) v xND xD) ∈ S_t₂F) ↔ P_t₂F xND := by
    intro xND xD
    have hT :
        ((mergeDescNonDesc (bn := bn) v xND xD) ∈ Tset) ↔
          ((baseFromNonDesc (bn := bn) v xND) ∈ Tset) := by
      simp [Tset, hmerge_eq_base_on_restrictND xND xD]
    have hFm :
        ((mergeDescNonDesc (bn := bn) v xND xD) ∈ F) ↔
          ((baseFromNonDesc (bn := bn) v xND) ∈ F) := by
      simp [F, parentFiber, hmerge_eq_base_on_parents xND xD]
    simp [P_t₂F, S_t₂F, Set.mem_inter_iff, hT, hFm]
  have hQP_F :
      ∀ xND xD,
        ((mergeDescNonDesc (bn := bn) v xND xD) ∈ F) ↔ P_F xND := by
    intro xND xD
    have hFm :
        ((mergeDescNonDesc (bn := bn) v xND xD) ∈ F) ↔
          ((baseFromNonDesc (bn := bn) v xND) ∈ F) := by
      simp [F, parentFiber, hmerge_eq_base_on_parents xND xD]
    simpa [P_F] using hFm
  have hsum_BtF :
      (∑ x : bn.JointSpace, if x ∈ S_BtF then cpt.jointWeight x else 0)
        =
      ∑ xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n),
        if P_BtF xND then A xND else 0 := by
    classical
    convert
      (sum_jointWeight_reindex_and_collapse_of_desc_irrel
        (bn := bn) (cpt := cpt) (v := v)
        (Q := fun x => x ∈ S_BtF) (P := P_BtF) hQP_BtF) using 1
    · refine Finset.sum_congr rfl ?_
      intro x _
      by_cases h : x ∈ S_BtF <;> simp [h]
    · simp [A]
  have hsum_BF :
      (∑ x : bn.JointSpace, if x ∈ S_BF then cpt.jointWeight x else 0)
        =
      ∑ xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n),
        if P_BF xND then A xND else 0 := by
    classical
    convert
      (sum_jointWeight_reindex_and_collapse_of_desc_irrel
        (bn := bn) (cpt := cpt) (v := v)
        (Q := fun x => x ∈ S_BF) (P := P_BF) hQP_BF) using 1
    · refine Finset.sum_congr rfl ?_
      intro x _
      by_cases h : x ∈ S_BF <;> simp [h]
    · simp [A]
  have hsum_t₂F :
      (∑ x : bn.JointSpace, if x ∈ S_t₂F then cpt.jointWeight x else 0)
        =
      ∑ xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n),
        if P_t₂F xND then A xND else 0 := by
    classical
    convert
      (sum_jointWeight_reindex_and_collapse_of_desc_irrel
        (bn := bn) (cpt := cpt) (v := v)
        (Q := fun x => x ∈ S_t₂F) (P := P_t₂F) hQP_t₂F) using 1
    · refine Finset.sum_congr rfl ?_
      intro x _
      by_cases h : x ∈ S_t₂F <;> simp [h]
    · simp [A]
  have hsum_F :
      (∑ x : bn.JointSpace, if x ∈ F then cpt.jointWeight x else 0)
        =
      ∑ xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n),
        if P_F xND then A xND else 0 := by
    simpa [A] using
      (sum_jointWeight_reindex_and_collapse_of_desc_irrel
        (bn := bn) (cpt := cpt) (v := v)
        (Q := fun x => x ∈ F) (P := P_F) hQP_F)
  have hμ_BtF_ND :
      cpt.jointMeasure S_BtF
        =
      ∑ xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n),
        if P_BtF xND then A xND else 0 := by
    calc
      cpt.jointMeasure S_BtF
          = ∑ x : bn.JointSpace, if x ∈ S_BtF then cpt.jointWeight x else 0 := by
              simpa [S_BtF, Bset, Tset, Set.inter_assoc] using hμ_BtF
      _ = ∑ xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n),
            if P_BtF xND then A xND else 0 := hsum_BtF
  have hμ_BF_ND :
      cpt.jointMeasure S_BF
        =
      ∑ xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n),
        if P_BF xND then A xND else 0 := by
    calc
      cpt.jointMeasure S_BF
          = ∑ x : bn.JointSpace, if x ∈ S_BF then cpt.jointWeight x else 0 := by
              simpa [S_BF, Bset] using hμ_BF
      _ = ∑ xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n),
            if P_BF xND then A xND else 0 := hsum_BF
  have hμ_t₂F_ND :
      cpt.jointMeasure S_t₂F
        =
      ∑ xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n),
        if P_t₂F xND then A xND else 0 := by
    calc
      cpt.jointMeasure S_t₂F
          = ∑ x : bn.JointSpace, if x ∈ S_t₂F then cpt.jointWeight x else 0 := by
              simpa [S_t₂F, Tset] using hμ_t₂F
      _ = ∑ xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n),
            if P_t₂F xND then A xND else 0 := hsum_t₂F
  have hμ_F_ND :
      cpt.jointMeasure F
        =
      ∑ xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n),
        if P_F xND then A xND else 0 := by
    calc
      cpt.jointMeasure F
          = ∑ x : bn.JointSpace, if x ∈ F then cpt.jointWeight x else 0 := hμ_F
      _ = ∑ xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n),
            if P_F xND then A xND else 0 := hsum_F
  let NDIdx := {n // n ∉ bn.graph.descendants v}
  let xvIdx : NDIdx := ⟨v, hv_not_desc⟩
  let XRest := (∀ n : {n : NDIdx // n ≠ xvIdx}, bn.stateSpace n.1.1)
  let eND :
      (∀ n : NDIdx, bn.stateSpace n.1) ≃ (bn.stateSpace v × XRest) :=
    Equiv.piSplitAt xvIdx (fun n : NDIdx => bn.stateSpace n.1)
  have hsum_split_xND :
      ∀ f : (∀ n : NDIdx, bn.stateSpace n.1) → ENNReal,
        (∑ xND : (∀ n : NDIdx, bn.stateSpace n.1), f xND)
          =
        ∑ a : bn.stateSpace v,
          ∑ xrest : XRest,
            f (eND.symm (a, xrest)) := by
    intro f
    classical
    calc
      (∑ xND : (∀ n : NDIdx, bn.stateSpace n.1), f xND)
          =
        ∑ p : bn.stateSpace v × XRest, f (eND.symm p) := by
          refine Fintype.sum_equiv eND f (fun p => f (eND.symm p)) ?_
          intro xND
          simp
      _ =
        ∑ a : bn.stateSpace v,
          ∑ xrest : XRest, f (eND.symm (a, xrest)) := by
            simpa using
              (Fintype.sum_prod_type
                (f := fun p : bn.stateSpace v × XRest => f (eND.symm p)))
  have hμ_BtF_split :
      cpt.jointMeasure S_BtF
        =
      ∑ a : bn.stateSpace v,
        ∑ xrest : XRest,
          if P_BtF (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0 := by
    rw [hμ_BtF_ND]
    simpa using
      (hsum_split_xND
        (f := fun xND : (∀ n : NDIdx, bn.stateSpace n.1) =>
          if P_BtF xND then A xND else 0))
  have hμ_BF_split :
      cpt.jointMeasure S_BF
        =
      ∑ a : bn.stateSpace v,
        ∑ xrest : XRest,
          if P_BF (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0 := by
    rw [hμ_BF_ND]
    simpa using
      (hsum_split_xND
        (f := fun xND : (∀ n : NDIdx, bn.stateSpace n.1) =>
          if P_BF xND then A xND else 0))
  have hμ_t₂F_split :
      cpt.jointMeasure S_t₂F
        =
      ∑ a : bn.stateSpace v,
        ∑ xrest : XRest,
          if P_t₂F (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0 := by
    rw [hμ_t₂F_ND]
    simpa using
      (hsum_split_xND
        (f := fun xND : (∀ n : NDIdx, bn.stateSpace n.1) =>
          if P_t₂F xND then A xND else 0))
  have hμ_F_split :
      cpt.jointMeasure F
        =
      ∑ a : bn.stateSpace v,
        ∑ xrest : XRest,
          if P_F (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0 := by
    rw [hμ_F_ND]
    simpa using
      (hsum_split_xND
        (f := fun xND : (∀ n : NDIdx, bn.stateSpace n.1) =>
          if P_F xND then A xND else 0))
  let paC : bn.ParentAssignment v := fun u hu => c ⟨u, hu⟩
  let qB : ENNReal := ∑ a : bn.stateSpace v, if a ∈ SB then cpt.cpt v paC a else 0
  let a0 : bn.stateSpace v := Classical.choice (inferInstance : Nonempty (bn.stateSpace v))
  let xND0 : XRest → (∀ n : NDIdx, bn.stateSpace n.1) := fun xrest => eND.symm (a0, xrest)
  let x0 : XRest → bn.JointSpace := fun xrest => baseFromNonDesc (bn := bn) v (xND0 xrest)
  let R : XRest → ENNReal := fun xrest =>
    ∏ w ∈ (Finset.univ.filter (fun w => w ∉ bn.graph.descendants v ∧ w ≠ v)),
      cpt.nodeProb (x0 xrest) w
  let PF0 : XRest → Prop := fun xrest => P_F (xND0 xrest)
  let PT0 : XRest → Prop := fun xrest => P_t₂F (xND0 xrest)

  have hparents_update_v :
      ∀ (x : bn.JointSpace) (a : bn.stateSpace v),
        parentsRestrict (bn := bn) v (Function.update x v a)
          =
        parentsRestrict (bn := bn) v x := by
    intro x a
    funext p
    have hp_ne : p.1 ≠ v := by
      intro hp
      exact not_self_parent (bn := bn) v (by simpa [hp] using p.2)
    simp [parentsRestrict, restrictToSet, Function.update_of_ne hp_ne]

  have hv_not_ND : v ∉ bn.nonDescendantsExceptParentsAndSelf v := by
    intro hv_mem
    have hv_mem' :
        v ∉ bn.graph.descendants v ∧ v ∉ bn.graph.parents v ∪ ({v} : Set V) := by
      simpa [BayesianNetwork.nonDescendantsExceptParentsAndSelf, Set.mem_diff] using hv_mem
    exact hv_mem'.2 (Set.mem_union_right _ rfl)

  have hrestrictND_update :
      ∀ (x : bn.JointSpace) (a : bn.stateSpace v),
        restrictToSet (bn := bn) (bn.nonDescendantsExceptParentsAndSelf v) (Function.update x v a)
          =
        restrictToSet (bn := bn) (bn.nonDescendantsExceptParentsAndSelf v) x := by
    intro x a
    funext u
    have hu_ne : u.1 ≠ v := by
      intro hu
      apply hv_not_ND
      simpa [hu] using u.2
    simp [restrictToSet, Function.update_of_ne hu_ne]

  have hxND_update :
      ∀ (a : bn.stateSpace v) (xrest : XRest),
        eND.symm (a, xrest) = Function.update (xND0 xrest) xvIdx a := by
    intro a xrest
    funext n
    by_cases hn : n = xvIdx
    · subst hn
      have hpair : eND (eND.symm (a, xrest)) = (a, xrest) :=
        Equiv.apply_symm_apply eND (a, xrest)
      have hfst : (eND (eND.symm (a, xrest))).1 = a := congrArg Prod.fst hpair
      simpa [eND] using hfst
    · have h1 : (eND.symm (a, xrest)) n = xrest ⟨n, hn⟩ := by
        have hpair : eND (eND.symm (a, xrest)) = (a, xrest) :=
          Equiv.apply_symm_apply eND (a, xrest)
        have hsnd :
            (eND (eND.symm (a, xrest))).2 ⟨n, hn⟩ = xrest ⟨n, hn⟩ :=
          congrArg (fun g => g ⟨n, hn⟩) (congrArg Prod.snd hpair)
        simpa [eND] using hsnd
      have h2 : (xND0 xrest) n = xrest ⟨n, hn⟩ := by
        have hpair : eND (eND.symm (a0, xrest)) = (a0, xrest) :=
          Equiv.apply_symm_apply eND (a0, xrest)
        have hsnd :
            (eND (eND.symm (a0, xrest))).2 ⟨n, hn⟩ = xrest ⟨n, hn⟩ :=
          congrArg (fun g => g ⟨n, hn⟩) (congrArg Prod.snd hpair)
        simpa [xND0, eND] using hsnd
      simp [Function.update_of_ne hn, h1, h2]

  have hbase_update :
      ∀ (a : bn.stateSpace v) (xrest : XRest),
        baseFromNonDesc (bn := bn) v (eND.symm (a, xrest))
          =
        Function.update (x0 xrest) v a := by
    intro a xrest
    funext u
    by_cases hu_desc : u ∈ bn.graph.descendants v
    · have huv_ne : u ≠ v := by
        intro huv
        subst huv
        exact hv_not_desc hu_desc
      simp [baseFromNonDesc, x0, xND0, hu_desc, Function.update_of_ne huv_ne]
    · have hu_not_desc : u ∉ bn.graph.descendants v := hu_desc
      by_cases huv : u = v
      · subst huv
        have hxv : (eND.symm (a, xrest)) xvIdx = a := by
          simpa [Function.update_self] using
            congrArg (fun f => f xvIdx) (hxND_update a xrest)
        simpa [baseFromNonDesc, x0, xND0, hv_not_desc, xvIdx]
          using hxv
      · have hidx_ne : (⟨u, hu_not_desc⟩ : NDIdx) ≠ xvIdx := by
          intro h
          apply huv
          exact congrArg Subtype.val h
        have hx :
            (eND.symm (a, xrest)) ⟨u, hu_not_desc⟩
              =
            (xND0 xrest) ⟨u, hu_not_desc⟩ := by
          have hx' := congrArg (fun f => f ⟨u, hu_not_desc⟩) (hxND_update a xrest)
          simp [Function.update_of_ne hidx_ne] at hx'
          exact hx'
        have hx0 :
            (x0 xrest) u = (xND0 xrest) ⟨u, hu_not_desc⟩ := by
          simp [x0, baseFromNonDesc, hu_not_desc]
        simp [baseFromNonDesc, hu_not_desc, Function.update_of_ne huv, hx, hx0]

  have hP_F_indep :
      ∀ (a : bn.stateSpace v) (xrest : XRest),
        P_F (eND.symm (a, xrest)) ↔ PF0 xrest := by
    intro a xrest
    constructor
    · intro h
      have hpar_upd :
          parentsRestrict (bn := bn) v (Function.update (x0 xrest) v a) = c := by
        simpa [hbase_update a xrest, F, parentFiber, P_F] using h
      have hpar0 :
          parentsRestrict (bn := bn) v (x0 xrest) = c := by
        simpa [hparents_update_v (x := x0 xrest) (a := a)] using hpar_upd
      simpa [PF0, P_F, x0, xND0, F, parentFiber]
        using hpar0
    · intro h
      have hpar0 :
          parentsRestrict (bn := bn) v (x0 xrest) = c := by
        simpa [PF0, P_F, x0, xND0, F, parentFiber] using h
      have hpar_upd :
          parentsRestrict (bn := bn) v (Function.update (x0 xrest) v a) = c := by
        simpa [hparents_update_v (x := x0 xrest) (a := a)] using hpar0
      simpa [hbase_update a xrest, F, parentFiber, P_F] using hpar_upd

  have hP_t₂F_implies_P_F :
      ∀ xND, P_t₂F xND → P_F xND := by
    intro xND h
    have hmem : baseFromNonDesc (bn := bn) v xND ∈ S_t₂F := by
      simpa [P_t₂F] using h
    exact hmem.2

  have hP_t₂F_indep :
      ∀ (a : bn.stateSpace v) (xrest : XRest),
        P_t₂F (eND.symm (a, xrest)) ↔ PT0 xrest := by
    intro a xrest
    let xnew : bn.JointSpace := baseFromNonDesc (bn := bn) v (eND.symm (a, xrest))
    have hT_indep : xnew ∈ Tset ↔ x0 xrest ∈ Tset := by
      dsimp [xnew, Tset]
      change
        restrictToSet (bn := bn) (bn.nonDescendantsExceptParentsAndSelf v)
          (baseFromNonDesc (bn := bn) v (eND.symm (a, xrest))) ∈ SND
          ↔
        restrictToSet (bn := bn) (bn.nonDescendantsExceptParentsAndSelf v) (x0 xrest) ∈ SND
      rw [hbase_update a xrest]
      simp [hrestrictND_update (x := x0 xrest) (a := a)]
    have hF_indep : xnew ∈ F ↔ x0 xrest ∈ F := by
      simpa [xnew, PF0, P_F, x0, xND0] using hP_F_indep a xrest
    have hS : xnew ∈ S_t₂F ↔ x0 xrest ∈ S_t₂F := by
      simp [S_t₂F, Set.mem_inter_iff, hT_indep, hF_indep]
    simpa [P_t₂F, PT0, xnew, xND0] using hS

  have hP_BF_split :
      ∀ (a : bn.stateSpace v) (xrest : XRest),
        P_BF (eND.symm (a, xrest)) ↔ (a ∈ SB ∧ PF0 xrest) := by
    intro a xrest
    let xnew : bn.JointSpace := baseFromNonDesc (bn := bn) v (eND.symm (a, xrest))
    have hB_mem : xnew ∈ Bset ↔ a ∈ SB := by
      dsimp [xnew, Bset]
      rw [hbase_update a xrest]
      simp
    have hF_mem : xnew ∈ F ↔ PF0 xrest := by
      simpa [xnew, P_F] using hP_F_indep a xrest
    simp [P_BF, xnew, S_BF, Set.mem_inter_iff, hB_mem, hF_mem]

  have hP_BtF_split :
      ∀ (a : bn.stateSpace v) (xrest : XRest),
        P_BtF (eND.symm (a, xrest)) ↔ (a ∈ SB ∧ PT0 xrest) := by
    intro a xrest
    let xnew : bn.JointSpace := baseFromNonDesc (bn := bn) v (eND.symm (a, xrest))
    have hB_mem : xnew ∈ Bset ↔ a ∈ SB := by
      dsimp [xnew, Bset]
      rw [hbase_update a xrest]
      simp
    have hT2_mem : xnew ∈ S_t₂F ↔ PT0 xrest := by
      simpa [xnew, P_t₂F] using hP_t₂F_indep a xrest
    have hTF : xnew ∈ Tset ∩ F ↔ PT0 xrest := by
      simpa [S_t₂F, Set.mem_inter_iff] using hT2_mem
    have hBt : xnew ∈ S_BtF ↔ (a ∈ SB ∧ PT0 xrest) := by
      constructor
      · intro hx
        have hxB : xnew ∈ Bset := hx.1.1
        have hxTF : xnew ∈ Tset ∩ F := ⟨hx.1.2, hx.2⟩
        exact ⟨hB_mem.mp hxB, hTF.mp hxTF⟩
      · intro h
        rcases h with ⟨ha, hpt⟩
        have hxB : xnew ∈ Bset := hB_mem.mpr ha
        have hxTF : xnew ∈ Tset ∩ F := hTF.mpr hpt
        exact ⟨⟨hxB, hxTF.1⟩, hxTF.2⟩
    simpa [P_BtF, xnew] using hBt

  have hnodeProb_eq_cpt :
      ∀ (a : bn.stateSpace v) (xrest : XRest),
        PF0 xrest →
          cpt.nodeProb (Function.update (x0 xrest) v a) v = cpt.cpt v paC a := by
    intro a xrest hPF
    have hpar0 : parentsRestrict (bn := bn) v (x0 xrest) = c := by
      simpa [PF0, P_F, x0, xND0, F, parentFiber] using hPF
    have hpar_upd : parentsRestrict (bn := bn) v (Function.update (x0 xrest) v a) = c := by
      simpa [hparents_update_v (x := x0 xrest) (a := a)] using hpar0
    have hpa_cfg : cpt.parentAssignOfConfig (Function.update (x0 xrest) v a) v = paC := by
      funext u hu
      have hcomp := congrArg (fun p => p ⟨u, hu⟩) hpar_upd
      simpa [parentsRestrict, restrictToSet, DiscreteCPT.parentAssignOfConfig, paC] using hcomp
    calc
      cpt.nodeProb (Function.update (x0 xrest) v a) v
          = cpt.cpt v (cpt.parentAssignOfConfig (Function.update (x0 xrest) v a) v)
              ((Function.update (x0 xrest) v a) v) := rfl
      _ = cpt.cpt v paC a := by simp [hpa_cfg, paC]

  have hA_decomp :
      ∀ (a : bn.stateSpace v) (xrest : XRest),
        A (eND.symm (a, xrest))
          =
        cpt.nodeProb (Function.update (x0 xrest) v a) v * R xrest := by
    intro a xrest
    have hprod :
        (∏ w ∈ (Finset.univ.filter (fun w => w ∉ bn.graph.descendants v ∧ w ≠ v)),
          cpt.nodeProb (Function.update (x0 xrest) v a) w)
          =
        R xrest := by
      simpa [R] using
        (prod_notDescNotSelf_independent_of_xv (bn := bn) (cpt := cpt)
          (v := v) (x := x0 xrest) (a := a))
    simp [A, x0, hprod, hbase_update a xrest]

  have hsum_cpt_row : ∑ a : bn.stateSpace v, cpt.cpt v paC a = 1 := by
    simpa using pmf_sum_eq_one (cpt.cpt v paC)

  have hμ_BtF_split' :
      cpt.jointMeasure S_BtF
        =
      ∑ xrest : XRest,
        ∑ a : bn.stateSpace v,
          if P_BtF (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0 := by
    calc
      cpt.jointMeasure S_BtF
          =
        ∑ a : bn.stateSpace v,
          ∑ xrest : XRest,
            if P_BtF (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0 := hμ_BtF_split
      _ =
        ∑ xrest : XRest,
          ∑ a : bn.stateSpace v,
            if P_BtF (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0 := by
              simpa using
                (Finset.sum_comm
                  (f := fun a : bn.stateSpace v =>
                    fun xrest : XRest =>
                      if P_BtF (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0))

  have hμ_BF_split' :
      cpt.jointMeasure S_BF
        =
      ∑ xrest : XRest,
        ∑ a : bn.stateSpace v,
          if P_BF (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0 := by
    calc
      cpt.jointMeasure S_BF
          =
        ∑ a : bn.stateSpace v,
          ∑ xrest : XRest,
            if P_BF (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0 := hμ_BF_split
      _ =
        ∑ xrest : XRest,
          ∑ a : bn.stateSpace v,
            if P_BF (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0 := by
              simpa using
                (Finset.sum_comm
                  (f := fun a : bn.stateSpace v =>
                    fun xrest : XRest =>
                      if P_BF (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0))

  have hμ_t₂F_split' :
      cpt.jointMeasure S_t₂F
        =
      ∑ xrest : XRest,
        ∑ a : bn.stateSpace v,
          if P_t₂F (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0 := by
    calc
      cpt.jointMeasure S_t₂F
          =
        ∑ a : bn.stateSpace v,
          ∑ xrest : XRest,
            if P_t₂F (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0 := hμ_t₂F_split
      _ =
        ∑ xrest : XRest,
          ∑ a : bn.stateSpace v,
            if P_t₂F (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0 := by
              simpa using
                (Finset.sum_comm
                  (f := fun a : bn.stateSpace v =>
                    fun xrest : XRest =>
                      if P_t₂F (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0))

  have hμ_F_split' :
      cpt.jointMeasure F
        =
      ∑ xrest : XRest,
        ∑ a : bn.stateSpace v,
          if P_F (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0 := by
    calc
      cpt.jointMeasure F
          =
        ∑ a : bn.stateSpace v,
          ∑ xrest : XRest,
            if P_F (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0 := hμ_F_split
      _ =
        ∑ xrest : XRest,
          ∑ a : bn.stateSpace v,
            if P_F (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0 := by
              simpa using
                (Finset.sum_comm
                  (f := fun a : bn.stateSpace v =>
                    fun xrest : XRest =>
                      if P_F (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0))

  have hInner_F :
      ∀ xrest : XRest,
        (∑ a : bn.stateSpace v,
          if P_F (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0)
          =
        if PF0 xrest then R xrest else 0 := by
    intro xrest
    by_cases hPF : PF0 xrest
    · have hPFa : ∀ a : bn.stateSpace v, P_F (eND.symm (a, xrest)) := by
        intro a
        exact (hP_F_indep a xrest).2 hPF
      calc
        (∑ a : bn.stateSpace v,
          if P_F (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0)
            = ∑ a : bn.stateSpace v, A (eND.symm (a, xrest)) := by
                simp [hPFa]
        _ = ∑ a : bn.stateSpace v,
              cpt.nodeProb (Function.update (x0 xrest) v a) v * R xrest := by
                refine Finset.sum_congr rfl ?_
                intro a _
                simpa using hA_decomp a xrest
        _ = (∑ a : bn.stateSpace v, cpt.nodeProb (Function.update (x0 xrest) v a) v) * R xrest := by
              simpa using
                (Finset.sum_mul
                  (s := (Finset.univ : Finset (bn.stateSpace v)))
                  (f := fun a : bn.stateSpace v =>
                    cpt.nodeProb (Function.update (x0 xrest) v a) v)
                  (a := R xrest)).symm
        _ = (∑ a : bn.stateSpace v, cpt.cpt v paC a) * R xrest := by
              refine congrArg (fun z => z * R xrest) ?_
              refine Finset.sum_congr rfl ?_
              intro a _
              exact hnodeProb_eq_cpt a xrest hPF
        _ = R xrest := by simp [hsum_cpt_row]
        _ = if PF0 xrest then R xrest else 0 := by simp [hPF]
    · have hPFa : ∀ a : bn.stateSpace v, ¬ P_F (eND.symm (a, xrest)) := by
        intro a h
        exact hPF ((hP_F_indep a xrest).1 h)
      simp [hPFa, hPF]

  have hInner_t₂F :
      ∀ xrest : XRest,
        (∑ a : bn.stateSpace v,
          if P_t₂F (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0)
          =
        if PT0 xrest then R xrest else 0 := by
    intro xrest
    by_cases hPT : PT0 xrest
    · have hPF : PF0 xrest := by
        exact hP_t₂F_implies_P_F (xND := xND0 xrest) (by simpa [PT0] using hPT)
      have hPTa : ∀ a : bn.stateSpace v, P_t₂F (eND.symm (a, xrest)) := by
        intro a
        exact (hP_t₂F_indep a xrest).2 hPT
      calc
        (∑ a : bn.stateSpace v,
          if P_t₂F (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0)
            = ∑ a : bn.stateSpace v, A (eND.symm (a, xrest)) := by
                simp [hPTa]
        _ = ∑ a : bn.stateSpace v,
              cpt.nodeProb (Function.update (x0 xrest) v a) v * R xrest := by
                refine Finset.sum_congr rfl ?_
                intro a _
                simpa using hA_decomp a xrest
        _ = (∑ a : bn.stateSpace v, cpt.nodeProb (Function.update (x0 xrest) v a) v) * R xrest := by
              simpa using
                (Finset.sum_mul
                  (s := (Finset.univ : Finset (bn.stateSpace v)))
                  (f := fun a : bn.stateSpace v =>
                    cpt.nodeProb (Function.update (x0 xrest) v a) v)
                  (a := R xrest)).symm
        _ = (∑ a : bn.stateSpace v, cpt.cpt v paC a) * R xrest := by
              refine congrArg (fun z => z * R xrest) ?_
              refine Finset.sum_congr rfl ?_
              intro a _
              exact hnodeProb_eq_cpt a xrest hPF
        _ = R xrest := by simp [hsum_cpt_row]
        _ = if PT0 xrest then R xrest else 0 := by simp [hPT]
    · have hPTa : ∀ a : bn.stateSpace v, ¬ P_t₂F (eND.symm (a, xrest)) := by
        intro a h
        exact hPT ((hP_t₂F_indep a xrest).1 h)
      simp [hPTa, hPT]

  have hInner_BF :
      ∀ xrest : XRest,
        (∑ a : bn.stateSpace v,
          if P_BF (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0)
          =
        if PF0 xrest then qB * R xrest else 0 := by
    intro xrest
    by_cases hPF : PF0 xrest
    · have hBFa :
          ∀ a : bn.stateSpace v,
            P_BF (eND.symm (a, xrest)) ↔ a ∈ SB := by
        intro a
        simpa [hPF, and_assoc] using hP_BF_split a xrest
      calc
        (∑ a : bn.stateSpace v,
          if P_BF (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0)
            = ∑ a : bn.stateSpace v,
                if a ∈ SB then A (eND.symm (a, xrest)) else 0 := by
                  refine Finset.sum_congr rfl ?_
                  intro a _
                  by_cases ha : a ∈ SB <;> simp [hBFa a, ha]
        _ = ∑ a : bn.stateSpace v,
              if a ∈ SB then cpt.cpt v paC a * R xrest else 0 := by
                refine Finset.sum_congr rfl ?_
                intro a _
                by_cases ha : a ∈ SB
                · simp [ha, hA_decomp a xrest, hnodeProb_eq_cpt a xrest hPF]
                · simp [ha]
        _ = (∑ a : bn.stateSpace v, if a ∈ SB then cpt.cpt v paC a else 0) * R xrest := by
              simpa using
                (Finset.sum_mul
                  (s := (Finset.univ : Finset (bn.stateSpace v)))
                  (f := fun a : bn.stateSpace v => if a ∈ SB then cpt.cpt v paC a else 0)
                  (a := R xrest)).symm
        _ = qB * R xrest := by simp [qB]
        _ = if PF0 xrest then qB * R xrest else 0 := by simp [hPF]
    · have hBFa : ∀ a : bn.stateSpace v, ¬ P_BF (eND.symm (a, xrest)) := by
        intro a h
        exact hPF (hP_BF_split a xrest |>.1 h |>.2)
      simp [hBFa, hPF]

  have hInner_BtF :
      ∀ xrest : XRest,
        (∑ a : bn.stateSpace v,
          if P_BtF (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0)
          =
        if PT0 xrest then qB * R xrest else 0 := by
    intro xrest
    by_cases hPT : PT0 xrest
    · have hPF : PF0 xrest := by
        exact hP_t₂F_implies_P_F (xND := xND0 xrest) (by simpa [PT0] using hPT)
      have hBtFa :
          ∀ a : bn.stateSpace v,
            P_BtF (eND.symm (a, xrest)) ↔ a ∈ SB := by
        intro a
        simpa [hPT, and_assoc] using hP_BtF_split a xrest
      calc
        (∑ a : bn.stateSpace v,
          if P_BtF (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0)
            = ∑ a : bn.stateSpace v,
                if a ∈ SB then A (eND.symm (a, xrest)) else 0 := by
                  refine Finset.sum_congr rfl ?_
                  intro a _
                  by_cases ha : a ∈ SB <;> simp [hBtFa a, ha]
        _ = ∑ a : bn.stateSpace v,
              if a ∈ SB then cpt.cpt v paC a * R xrest else 0 := by
                refine Finset.sum_congr rfl ?_
                intro a _
                by_cases ha : a ∈ SB
                · simp [ha, hA_decomp a xrest, hnodeProb_eq_cpt a xrest hPF]
                · simp [ha]
        _ = (∑ a : bn.stateSpace v, if a ∈ SB then cpt.cpt v paC a else 0) * R xrest := by
              simpa using
                (Finset.sum_mul
                  (s := (Finset.univ : Finset (bn.stateSpace v)))
                  (f := fun a : bn.stateSpace v => if a ∈ SB then cpt.cpt v paC a else 0)
                  (a := R xrest)).symm
        _ = qB * R xrest := by simp [qB]
        _ = if PT0 xrest then qB * R xrest else 0 := by simp [hPT]
    · have hBtFa : ∀ a : bn.stateSpace v, ¬ P_BtF (eND.symm (a, xrest)) := by
        intro a h
        exact hPT (hP_BtF_split a xrest |>.1 h |>.2)
      simp [hBtFa, hPT]

  have hμ_F_as :
      cpt.jointMeasure F = ∑ xrest : XRest, if PF0 xrest then R xrest else 0 := by
    calc
      cpt.jointMeasure F
          =
        ∑ xrest : XRest,
          ∑ a : bn.stateSpace v,
            if P_F (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0 := hμ_F_split'
      _ = ∑ xrest : XRest, if PF0 xrest then R xrest else 0 := by
            refine Finset.sum_congr rfl ?_
            intro xrest _
            exact hInner_F xrest

  have hμ_t₂F_as :
      cpt.jointMeasure S_t₂F = ∑ xrest : XRest, if PT0 xrest then R xrest else 0 := by
    calc
      cpt.jointMeasure S_t₂F
          =
        ∑ xrest : XRest,
          ∑ a : bn.stateSpace v,
            if P_t₂F (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0 := hμ_t₂F_split'
      _ = ∑ xrest : XRest, if PT0 xrest then R xrest else 0 := by
            refine Finset.sum_congr rfl ?_
            intro xrest _
            exact hInner_t₂F xrest

  have hμ_BF_as :
      cpt.jointMeasure S_BF = ∑ xrest : XRest, if PF0 xrest then qB * R xrest else 0 := by
    calc
      cpt.jointMeasure S_BF
          =
        ∑ xrest : XRest,
          ∑ a : bn.stateSpace v,
            if P_BF (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0 := hμ_BF_split'
      _ = ∑ xrest : XRest, if PF0 xrest then qB * R xrest else 0 := by
            refine Finset.sum_congr rfl ?_
            intro xrest _
            exact hInner_BF xrest

  have hμ_BtF_as :
      cpt.jointMeasure S_BtF = ∑ xrest : XRest, if PT0 xrest then qB * R xrest else 0 := by
    calc
      cpt.jointMeasure S_BtF
          =
        ∑ xrest : XRest,
          ∑ a : bn.stateSpace v,
            if P_BtF (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0 := hμ_BtF_split'
      _ = ∑ xrest : XRest, if PT0 xrest then qB * R xrest else 0 := by
            refine Finset.sum_congr rfl ?_
            intro xrest _
            exact hInner_BtF xrest

  have hμ_BF_q :
      cpt.jointMeasure S_BF = qB * cpt.jointMeasure F := by
    calc
      cpt.jointMeasure S_BF = ∑ xrest : XRest, if PF0 xrest then qB * R xrest else 0 := hμ_BF_as
      _ = ∑ xrest : XRest, qB * (if PF0 xrest then R xrest else 0) := by
            refine Finset.sum_congr rfl ?_
            intro xrest _
            by_cases hPF : PF0 xrest <;> simp [hPF]
      _ = qB * (∑ xrest : XRest, if PF0 xrest then R xrest else 0) := by
            simpa using
              (Finset.mul_sum
                (a := qB) (s := (Finset.univ : Finset XRest))
                (f := fun xrest : XRest => if PF0 xrest then R xrest else 0)).symm
      _ = qB * cpt.jointMeasure F := by rw [hμ_F_as]

  have hμ_BtF_q :
      cpt.jointMeasure S_BtF = qB * cpt.jointMeasure S_t₂F := by
    calc
      cpt.jointMeasure S_BtF = ∑ xrest : XRest, if PT0 xrest then qB * R xrest else 0 := hμ_BtF_as
      _ = ∑ xrest : XRest, qB * (if PT0 xrest then R xrest else 0) := by
            refine Finset.sum_congr rfl ?_
            intro xrest _
            by_cases hPT : PT0 xrest <;> simp [hPT]
      _ = qB * (∑ xrest : XRest, if PT0 xrest then R xrest else 0) := by
            simpa using
              (Finset.mul_sum
                (a := qB) (s := (Finset.univ : Finset XRest))
                (f := fun xrest : XRest => if PT0 xrest then R xrest else 0)).symm
      _ = qB * cpt.jointMeasure S_t₂F := by rw [hμ_t₂F_as]

  have hfinal :
      cpt.jointMeasure S_BtF * cpt.jointMeasure F
        =
      cpt.jointMeasure S_BF * cpt.jointMeasure S_t₂F := by
    calc
      cpt.jointMeasure S_BtF * cpt.jointMeasure F
          = (qB * cpt.jointMeasure S_t₂F) * cpt.jointMeasure F := by
              rw [hμ_BtF_q]
      _ = qB * (cpt.jointMeasure S_t₂F * cpt.jointMeasure F) := by
            simp [mul_assoc]
      _ = qB * (cpt.jointMeasure F * cpt.jointMeasure S_t₂F) := by
            simp [mul_comm]
      _ = (qB * cpt.jointMeasure F) * cpt.jointMeasure S_t₂F := by
            simp [mul_assoc]
      _ = cpt.jointMeasure S_BF * cpt.jointMeasure S_t₂F := by
            rw [hμ_BF_q]
  simpa [S_BtF, S_BF, S_t₂F, Bset, Tset, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm]
    using hfinal


/- BN factorization CI on parent fibers: for B ∈ m_v and f = t₂.indicator 1 with t₂ ∈ m_{ND'},
    on each parent fiber F_c the joint weight factors as nodeProb(v,x_v,c) · Ψ(x_{ND'},c)
    after marginalizing descendants (telescoping_sum). This product structure gives:
    μ[B.indicator 1 * f | m_pa] =ᵃᵉ μ[B.indicator 1 | m_pa] * μ[f | m_pa]

    Proof: On fiber F_c, w(x) = nodeProb(v, x_v, c) · Ψ(x_{ND'}, c) · Σ_desc(→1).
    Since nodeProb(v) depends only on x_v,c and Ψ depends only on x_{ND'},c:
    μ(B∩t₂∩F_c) · μ(F_c) = μ(B∩F_c) · μ(t₂∩F_c). Summing over fibers gives CI. -/
/-- Event-level conditional-expectation factorization for the discrete BN local-Markov core.

For an event `B` depending only on `v` and an event `t₂` depending only on
`ND(v) \ (Pa(v) ∪ {v})`, conditioning on the parent σ-algebra makes the
indicator product split. This packages the discrete parent-fiber screening
algebra into a reusable public theorem. -/
theorem condExp_indicator_mul_of_parent_screening
    (cpt : bn.DiscreteCPT) (v : V)
    (B : Set bn.JointSpace)
    (hB : MeasurableSet[bn.measurableSpaceOfVertices ({v} : Set V)] B)
    (t₂ : Set bn.JointSpace)
    (ht₂ : MeasurableSet[bn.measurableSpaceOfVertices
            (bn.nonDescendantsExceptParentsAndSelf v)] t₂) :
    cpt.jointMeasure[B.indicator (fun _ => (1 : ℝ)) * t₂.indicator (fun _ => (1 : ℝ)) |
      bn.measurableSpaceOfVertices (bn.graph.parents v)] =ᵐ[cpt.jointMeasure]
    cpt.jointMeasure[B.indicator (fun _ => (1 : ℝ)) |
      bn.measurableSpaceOfVertices (bn.graph.parents v)] *
    cpt.jointMeasure[t₂.indicator (fun _ => (1 : ℝ)) |
      bn.measurableSpaceOfVertices (bn.graph.parents v)] := by
  -- On each parent fiber F_c, w(x) factors as nodeProb(v, x_v, c) · Ψ(x_{ND'}, c)
  -- after marginalizing descendants. Since B depends only on x_v and t₂ on x_{ND'},
  -- the sums factor, giving CI.
  -- Proof: characterize μ[g|m_pa]*μ[f|m_pa] as a condExp via its integral identity.
  -- The integral condition ∫_s (prod) dμ = ∫_s (g*f) dμ on each parent fiber F_c
  -- follows from the BN product factorization: p(x)|_{F_c} = φ(x_v) · ψ(x_{ND'})
  -- (after marginalizing descendants via telescoping_sum), making g and f independent.
  set μ := cpt.jointMeasure with hμ_def
  set m_pa := bn.measurableSpaceOfVertices (bn.graph.parents v) with hm_pa_def
  set f := t₂.indicator (fun _ => (1 : ℝ)) with hf_def
  set g := B.indicator (fun _ => (1 : ℝ)) with hg_def
  have hm_pa_le : m_pa ≤ MeasurableSpace.pi := bn.measurableSpaceOfVertices_le _
  haveI hsf : SigmaFinite (μ.trim hm_pa_le) :=
    BayesianNetwork.sigmaFinite_trim_of_le bn μ m_pa hm_pa_le
  have hB_pi : @MeasurableSet _ MeasurableSpace.pi B :=
    (bn.measurableSpaceOfVertices_le _) _ hB
  have ht₂_pi : @MeasurableSet _ MeasurableSpace.pi t₂ :=
    (bn.measurableSpaceOfVertices_le _) _ ht₂
  have hf_int : Integrable f μ := (integrable_const 1).indicator ht₂_pi
  have hg_int : Integrable g μ := (integrable_const 1).indicator hB_pi
  have hgf_eq : g * f = (B ∩ t₂).indicator (fun _ => (1 : ℝ)) := by
    ext x; simp only [g, f, Pi.mul_apply, Set.indicator, Set.mem_inter_iff]
    split_ifs <;> simp_all
  have hgf_int : Integrable (g * f) μ := by
    rw [hgf_eq]; exact (integrable_const 1).indicator (hB_pi.inter ht₂_pi)
  -- Product of condExps: m_pa-measurable, integrable (bounded by 1)
  have hprod_sm : StronglyMeasurable[m_pa] (μ[g | m_pa] * μ[f | m_pa]) :=
    stronglyMeasurable_condExp.mul stronglyMeasurable_condExp
  have hg_bnd := condExp_indicator_norm_le_one bn μ hm_pa_le B hB_pi
  have hf_bnd := condExp_indicator_norm_le_one bn μ hm_pa_le t₂ ht₂_pi
  have hprod_int : Integrable (μ[g | m_pa] * μ[f | m_pa]) μ := by
    apply (integrable_const (1 : ℝ)).mono'
    · exact (stronglyMeasurable_condExp.mono hm_pa_le).aestronglyMeasurable.mul
        (stronglyMeasurable_condExp.mono hm_pa_le).aestronglyMeasurable
    · filter_upwards [hg_bnd, hf_bnd] with x hgx hfx
      simp only [Pi.mul_apply, norm_mul]
      exact le_trans (mul_le_mul hgx hfx (norm_nonneg _) zero_le_one) (by norm_num)
  -- Characterize via ae_eq_condExp: need ∫_s prod dμ = ∫_s g*f dμ for all s ∈ m_pa
  symm
  exact ae_eq_condExp_of_forall_setIntegral_eq hm_pa_le hgf_int
    (fun s _ _ => hprod_int.integrableOn)
    (fun s hs _ => by
      -- Represent `s` as a preimage under the parent-restriction map, then
      -- reduce the integral equality to parent-fiber equalities.
      rcases measurableSet_parents_preimage (bn := bn) v hs with ⟨S, hS, hs_eq⟩
      subst hs_eq
      have hL :=
        setIntegral_parents_preimage (bn := bn) (μ := μ) v S
          (μ[g | m_pa] * μ[f | m_pa]) hprod_int
      have hR :=
        setIntegral_parents_preimage (bn := bn) (μ := μ) v S (g * f) hgf_int
      -- It remains to prove the per-fiber identity:
      --   ∫_{F_c} μ[g|m_pa] * μ[f|m_pa] dμ = ∫_{F_c} g*f dμ
      -- for each parent assignment `c`.
      have hFiber :
          ∀ c : ParentAssign (bn := bn) v,
            ∫ x in parentFiber (bn := bn) v c, (μ[g | m_pa] * μ[f | m_pa]) x ∂μ
              = ∫ x in parentFiber (bn := bn) v c, (g * f) x ∂μ := by
        intro c
        let F : Set bn.JointSpace := parentFiber (bn := bn) v c
        have hF_meas : @MeasurableSet _ MeasurableSpace.pi F := by
          simpa [F] using measurable_parentFiber (bn := bn) v c
        have hF_meas_mpa : MeasurableSet[m_pa] F := by
          simpa [F, hm_pa_def] using measurable_parentFiber_vertices (bn := bn) v c
        by_cases hμF0 : μ F = 0
        · have hrestrict0 : μ.restrict F = 0 := Measure.restrict_zero_set hμF0
          calc
            ∫ x in parentFiber (bn := bn) v c, (μ[g | m_pa] * μ[f | m_pa]) x ∂μ
                = ∫ x in F, (μ[g | m_pa] * μ[f | m_pa]) x ∂μ := by rfl
            _ = 0 := by simp [MeasureTheory.integral_zero_measure, hrestrict0]
            _ = ∫ x in F, (g * f) x ∂μ := by simp [MeasureTheory.integral_zero_measure, hrestrict0]
            _ = ∫ x in parentFiber (bn := bn) v c, (g * f) x ∂μ := by rfl
        · have hFne : F.Nonempty := by
            by_contra hne
            have hE : F = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
            exact hμF0 (by simpa [hE] using (MeasureTheory.measure_empty (μ := μ)))
          rcases hFne with ⟨ω0, hω0⟩
          have hconst_g :
              (fun x => (μ[g | m_pa]) x) =ᵐ[μ.restrict F] fun _ => (μ[g | m_pa]) ω0 := by
            refine (MeasureTheory.ae_restrict_iff' hF_meas).2 ?_
            refine Filter.Eventually.of_forall ?_
            intro x hx
            have hPx : parentsRestrict (bn := bn) v x = c := by
              simpa [F, parentFiber] using hx
            have hP0 : parentsRestrict (bn := bn) v ω0 = c := by
              simpa [F, parentFiber] using hω0
            exact measurable_const_on_fiber_set (bn := bn) (S := (bn.graph.parents v : Set V))
              (f := fun z => (μ[g | m_pa]) z)
              ((stronglyMeasurable_condExp (μ := μ) (m := m_pa) (f := g)).measurable)
              (by simpa [parentsRestrict] using hPx.trans hP0.symm)
          have hconst_f :
              (fun x => (μ[f | m_pa]) x) =ᵐ[μ.restrict F] fun _ => (μ[f | m_pa]) ω0 := by
            refine (MeasureTheory.ae_restrict_iff' hF_meas).2 ?_
            refine Filter.Eventually.of_forall ?_
            intro x hx
            have hPx : parentsRestrict (bn := bn) v x = c := by
              simpa [F, parentFiber] using hx
            have hP0 : parentsRestrict (bn := bn) v ω0 = c := by
              simpa [F, parentFiber] using hω0
            exact measurable_const_on_fiber_set (bn := bn) (S := (bn.graph.parents v : Set V))
              (f := fun z => (μ[f | m_pa]) z)
              ((stronglyMeasurable_condExp (μ := μ) (m := m_pa) (f := f)).measurable)
              (by simpa [parentsRestrict] using hPx.trans hP0.symm)
          have hconst_prod :
              (fun x => (μ[g | m_pa] * μ[f | m_pa]) x) =ᵐ[μ.restrict F]
                fun _ => (μ[g | m_pa]) ω0 * (μ[f | m_pa]) ω0 := by
            filter_upwards [hconst_g, hconst_f] with x hgx hfx
            simp [hgx, hfx]
          have hLconst :
              ∫ x in F, (μ[g | m_pa] * μ[f | m_pa]) x ∂μ
                = ((μ[g | m_pa]) ω0 * (μ[f | m_pa]) ω0) * μ.real F := by
            exact setIntegral_const_on (bn := bn) (μ := μ) (s := F) hF_meas _ hconst_prod
          have hGconst :
              ∫ x in F, (μ[g | m_pa]) x ∂μ = (μ[g | m_pa]) ω0 * μ.real F := by
            exact setIntegral_const_on (bn := bn) (μ := μ) (s := F) hF_meas _ hconst_g
          have hFconst :
              ∫ x in F, (μ[f | m_pa]) x ∂μ = (μ[f | m_pa]) ω0 * μ.real F := by
            exact setIntegral_const_on (bn := bn) (μ := μ) (s := F) hF_meas _ hconst_f
          have hGset :
              ∫ x in F, (μ[g | m_pa]) x ∂μ = ∫ x in F, g x ∂μ := by
            exact (MeasureTheory.setIntegral_condExp
              (hm := hm_pa_le) (μ := μ) (f := g) hg_int hF_meas_mpa)
          have hFset :
              ∫ x in F, (μ[f | m_pa]) x ∂μ = ∫ x in F, f x ∂μ := by
            exact (MeasureTheory.setIntegral_condExp
              (hm := hm_pa_le) (μ := μ) (f := f) hf_int hF_meas_mpa)
          have hInt_g :
              ∫ x in F, g x ∂μ = μ.real (B ∩ F) := by
            calc
              ∫ x in F, g x ∂μ
                  = ∫ x in F, (B.indicator (fun _ : bn.JointSpace => (1 : ℝ))) x ∂μ := by
                      rfl
              _ = ∫ x in F ∩ B, (fun _ : bn.JointSpace => (1 : ℝ)) x ∂μ := by
                    simpa using
                      (MeasureTheory.setIntegral_indicator (μ := μ) (s := F)
                        (t := B) (f := fun _ : bn.JointSpace => (1 : ℝ)) hB_pi)
              _ = μ.real (F ∩ B) := by
                    simpa using
                      (MeasureTheory.setIntegral_const (μ := μ) (s := F ∩ B)
                        (c := (1 : ℝ)))
              _ = μ.real (B ∩ F) := by simp [Set.inter_comm]
          have hInt_f :
              ∫ x in F, f x ∂μ = μ.real (t₂ ∩ F) := by
            calc
              ∫ x in F, f x ∂μ
                  = ∫ x in F, (t₂.indicator (fun _ : bn.JointSpace => (1 : ℝ))) x ∂μ := by
                      rfl
              _ = ∫ x in F ∩ t₂, (fun _ : bn.JointSpace => (1 : ℝ)) x ∂μ := by
                    simpa using
                      (MeasureTheory.setIntegral_indicator (μ := μ) (s := F)
                        (t := t₂) (f := fun _ : bn.JointSpace => (1 : ℝ)) ht₂_pi)
              _ = μ.real (F ∩ t₂) := by
                    simpa using
                      (MeasureTheory.setIntegral_const (μ := μ) (s := F ∩ t₂)
                        (c := (1 : ℝ)))
              _ = μ.real (t₂ ∩ F) := by simp [Set.inter_comm]
          have hInt_gf :
              ∫ x in F, (g * f) x ∂μ = μ.real ((B ∩ t₂) ∩ F) := by
            calc
              ∫ x in F, (g * f) x ∂μ
                  = ∫ x in F, ((B ∩ t₂).indicator (fun _ : bn.JointSpace => (1 : ℝ))) x ∂μ := by
                      rw [hgf_eq]
              _ = ∫ x in F ∩ (B ∩ t₂), (fun _ : bn.JointSpace => (1 : ℝ)) x ∂μ := by
                    simpa using
                      (MeasureTheory.setIntegral_indicator (μ := μ) (s := F)
                        (t := (B ∩ t₂)) (f := fun _ : bn.JointSpace => (1 : ℝ))
                        (hB_pi.inter ht₂_pi))
              _ = μ.real (F ∩ (B ∩ t₂)) := by
                    simpa using
                      (MeasureTheory.setIntegral_const (μ := μ) (s := F ∩ (B ∩ t₂))
                        (c := (1 : ℝ)))
              _ = μ.real ((B ∩ t₂) ∩ F) := by
                    simp [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm]
          have hscreen : μ ((B ∩ t₂) ∩ F) * μ F = μ (B ∩ F) * μ (t₂ ∩ F) := by
            simpa [μ, F, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using
              jointMeasure_parentFiber_screening_mul
                (bn := bn) (cpt := cpt) (v := v) (B := B) (hB := hB)
                (t₂ := t₂) (ht₂ := ht₂) c
          have hscreen_real :
              μ.real ((B ∩ t₂) ∩ F) * μ.real F = μ.real (B ∩ F) * μ.real (t₂ ∩ F) := by
            have htoReal := congrArg ENNReal.toReal hscreen
            simpa [Measure.real, ENNReal.toReal_mul,
              MeasureTheory.measure_ne_top (μ := μ) (s := ((B ∩ t₂) ∩ F)),
              MeasureTheory.measure_ne_top (μ := μ) (s := F),
              MeasureTheory.measure_ne_top (μ := μ) (s := (B ∩ F)),
              MeasureTheory.measure_ne_top (μ := μ) (s := (t₂ ∩ F))] using htoReal
          have hGF : (μ[g | m_pa]) ω0 * μ.real F = μ.real (B ∩ F) := by
            calc
              (μ[g | m_pa]) ω0 * μ.real F = ∫ x in F, (μ[g | m_pa]) x ∂μ := by
                simpa [hGconst] using hGconst.symm
              _ = ∫ x in F, g x ∂μ := hGset
              _ = μ.real (B ∩ F) := hInt_g
          have hFF : (μ[f | m_pa]) ω0 * μ.real F = μ.real (t₂ ∩ F) := by
            calc
              (μ[f | m_pa]) ω0 * μ.real F = ∫ x in F, (μ[f | m_pa]) x ∂μ := by
                simpa [hFconst] using hFconst.symm
              _ = ∫ x in F, f x ∂μ := hFset
              _ = μ.real (t₂ ∩ F) := hInt_f
          have hmul :
              (((μ[g | m_pa]) ω0 * (μ[f | m_pa]) ω0) * μ.real F) * μ.real F
                = (μ.real ((B ∩ t₂) ∩ F)) * μ.real F := by
            calc
              (((μ[g | m_pa]) ω0 * (μ[f | m_pa]) ω0) * μ.real F) * μ.real F
                  = ((μ[g | m_pa]) ω0 * μ.real F) * ((μ[f | m_pa]) ω0 * μ.real F) := by
                      ring
              _ = μ.real (B ∩ F) * μ.real (t₂ ∩ F) := by
                    simp [hGF, hFF]
              _ = (μ.real ((B ∩ t₂) ∩ F)) * μ.real F := by
                    simpa [mul_comm, mul_left_comm, mul_assoc] using hscreen_real.symm
          have hmain :
              ((μ[g | m_pa]) ω0 * (μ[f | m_pa]) ω0) * μ.real F
                = μ.real ((B ∩ t₂) ∩ F) := by
            have hF0 : μ.real F ≠ 0 := by
              intro h0
              have hzero_or_top : μ F = 0 ∨ μ F = ⊤ := by
                exact (ENNReal.toReal_eq_zero_iff (μ F)).1 (by simpa [Measure.real] using h0)
              have : μ F = 0 := by
                rcases hzero_or_top with hzero | htop
                · exact hzero
                · exact (MeasureTheory.measure_ne_top (μ := μ) (s := F) htop).elim
              exact hμF0 this
            exact mul_right_cancel₀ hF0 hmul
          calc
            ∫ x in F, (μ[g | m_pa] * μ[f | m_pa]) x ∂μ
                = ((μ[g | m_pa]) ω0 * (μ[f | m_pa]) ω0) * μ.real F := hLconst
            _ = μ.real ((B ∩ t₂) ∩ F) := hmain
            _ = ∫ x in F, (g * f) x ∂μ := by
                  symm
                  exact hInt_gf
      calc
        ∫ x in (parentsRestrict (bn := bn) v) ⁻¹' S, (μ[g | m_pa] * μ[f | m_pa]) x ∂μ
            = ∑ c : ParentAssign (bn := bn) v,
                if c ∈ S then
                  ∫ x in parentFiber (bn := bn) v c, (μ[g | m_pa] * μ[f | m_pa]) x ∂μ
                else 0 := hL
        _ = ∑ c : ParentAssign (bn := bn) v,
              if c ∈ S then
                ∫ x in parentFiber (bn := bn) v c, (g * f) x ∂μ
              else 0 := by
              refine Finset.sum_congr rfl ?_
              intro c _
              by_cases hc : c ∈ S
              · simp [hc]
                exact hFiber c
              · simp [hc]
        _ = ∫ x in (parentsRestrict (bn := bn) v) ⁻¹' S, (g * f) x ∂μ := hR.symm)
    hprod_sm.aestronglyMeasurable

/-- Key BN-specific lemma: conditioning on vertex v gives no additional information
    about non-descendants beyond what the parents provide.

    This is the heart of the local Markov property for Bayesian networks.
    The proof uses the BN product factorization: on each parent fiber F_c,
    the weight factors as φ_v(x_v,c) · φ_ND(x_{ND'},c) after marginalizing
    descendants (via telescoping_sum). Since the ratio μ(t₂∩F_{c,a})/μ(F_{c,a})
    is independent of a (the v-value), adding v to the conditioning doesn't change
    the conditional expectation of t₂. -/
theorem condExp_ndesc_indep_of_vertex
    (cpt : bn.DiscreteCPT) (v : V)
    (t₂ : Set bn.JointSpace)
    (ht₂ : MeasurableSet[bn.measurableSpaceOfVertices
            (bn.nonDescendantsExceptParentsAndSelf v)] t₂) :
    (cpt.jointMeasure)⟦t₂ |
      bn.measurableSpaceOfVertices (bn.graph.parents v) ⊔
      bn.measurableSpaceOfVertices ({v} : Set V)⟧ =ᵐ[cpt.jointMeasure]
    (cpt.jointMeasure)⟦t₂ | bn.measurableSpaceOfVertices (bn.graph.parents v)⟧ := by
  -- Strategy: use ae_eq_condExp_of_forall_setIntegral_eq to show
  -- μ[f|m_pa] is a version of μ[f|m_pav], where f = 1_{t₂}.
  set μ := cpt.jointMeasure with hμ_def
  set m_pa := bn.measurableSpaceOfVertices (bn.graph.parents v) with hm_pa_def
  set m_v := bn.measurableSpaceOfVertices ({v} : Set V) with hm_v_def
  set m_pav := m_pa ⊔ m_v with hm_pav_def
  set f : bn.JointSpace → ℝ := t₂.indicator (fun _ => 1) with hf_def
  have hm_pa_le : m_pa ≤ MeasurableSpace.pi := bn.measurableSpaceOfVertices_le _
  have hm_pav_le : m_pav ≤ MeasurableSpace.pi :=
    sup_le hm_pa_le (bn.measurableSpaceOfVertices_le _)
  haveI : SigmaFinite (μ.trim hm_pav_le) :=
    BayesianNetwork.sigmaFinite_trim_of_le bn μ m_pav hm_pav_le
  have ht₂_pi : @MeasurableSet _ MeasurableSpace.pi t₂ :=
    (bn.measurableSpaceOfVertices_le _) _ ht₂
  have hf_int : Integrable f μ := (integrable_const 1).indicator ht₂_pi
  -- μ[f|m_pa] is m_pav-strongly measurable (since m_pa ≤ m_pav)
  have hm_pa_le_pav : m_pa ≤ m_pav := le_sup_left
  have hg_sm : AEStronglyMeasurable[m_pav] (μ[f | m_pa]) μ :=
    (stronglyMeasurable_condExp (m := m_pa)).mono hm_pa_le_pav |>.aestronglyMeasurable
  -- μ[f|m_pa] is integrable on any set
  have hg_int : ∀ s, MeasurableSet[m_pav] s → μ s < ⊤ → IntegrableOn (μ[f | m_pa]) s μ :=
    fun _ _ _ => integrable_condExp.integrableOn
  -- KEY: integral condition on all m_pav-measurable sets
  have hg_eq : ∀ s, MeasurableSet[m_pav] s → μ s < ⊤ →
      ∫ x in s, (μ[f | m_pa]) x ∂μ = ∫ x in s, f x ∂μ := by
    intro s hs _
    -- Use Dynkin π-λ theorem (induction_on_inter) to extend from π-system generators
    -- π-system: {A ∩ B | A ∈ m_pa, B ∈ m_v}
    let π : Set (Set bn.JointSpace) :=
      {t | ∃ A B, MeasurableSet[m_pa] A ∧ MeasurableSet[m_v] B ∧ t = A ∩ B}
    -- m_pav = generateFrom π
    have h_gen : m_pav = MeasurableSpace.generateFrom π := by
      apply le_antisymm
      · apply sup_le
        · intro t ht
          exact MeasurableSpace.measurableSet_generateFrom
            ⟨t, Set.univ, ht, MeasurableSet.univ, (Set.inter_univ t).symm⟩
        · intro t ht
          exact MeasurableSpace.measurableSet_generateFrom
            ⟨Set.univ, t, MeasurableSet.univ, ht, (Set.univ_inter t).symm⟩
      · exact MeasurableSpace.generateFrom_le fun t ⟨A, B, hA, hB, ht_eq⟩ => by
          subst ht_eq
          exact MeasurableSet.inter (hm_pa_le_pav _ hA) ((le_sup_right : m_v ≤ m_pav) _ hB)
    -- π is a π-system
    have h_pi : IsPiSystem π := by
      intro s₁ ⟨A₁, B₁, hA₁, hB₁, hs₁⟩ s₂ ⟨A₂, B₂, hA₂, hB₂, hs₂⟩ _
      exact ⟨A₁ ∩ A₂, B₁ ∩ B₂, hA₁.inter hA₂, hB₁.inter hB₂, by
        subst hs₁; subst hs₂; ext x; simp [Set.mem_inter_iff]; tauto⟩
    -- SigmaFinite for m_pa (needed for setIntegral_condExp)
    haveI hsf_pa : SigmaFinite (μ.trim hm_pa_le) :=
      BayesianNetwork.sigmaFinite_trim_of_le bn μ m_pa hm_pa_le
    -- Apply Dynkin theorem
    have h_dynkin := MeasurableSpace.induction_on_inter h_gen h_pi
      (C := fun s _ => ∫ x in s, (μ[f | m_pa]) x ∂μ = ∫ x in s, f x ∂μ)
      (by simp) -- C(∅)
      (by -- C(basic): for A ∩ B ∈ π — BN factorization gives CI on parent fibers
        intro t ⟨A, B, hA, hB, ht_eq⟩; subst ht_eq
        have hB_pi : @MeasurableSet _ MeasurableSpace.pi B :=
          (bn.measurableSpaceOfVertices_le _) _ hB
        -- Use the CI lemma
        have hci := condExp_indicator_mul_of_parent_screening bn cpt v B hB t₂ ht₂
        -- hci : μ[g * f | m_pa] =ᵃᵉ μ[g | m_pa] * μ[f | m_pa]
        -- where g = B.indicator 1
        set g := B.indicator (fun _ => (1 : ℝ)) with hg_def
        have hg_int : Integrable g μ := (integrable_const 1).indicator hB_pi
        -- g * f = (B ∩ t₂).indicator 1
        have hgf_eq : g * f = (B ∩ t₂).indicator (fun _ => (1 : ℝ)) := by
          ext x; simp only [g, f, hg_def, hf_def, Pi.mul_apply, Set.indicator,
            Set.mem_inter_iff]; split_ifs <;> simp_all
        have hgf_int : Integrable (g * f) μ := by
          rw [hgf_eq]; exact (integrable_const 1).indicator (hB_pi.inter ht₂_pi)
        -- Key identity: g * μ[f|m_pa] = μ[f|m_pa] * g (commute for pull-out)
        have hgce_int : Integrable (g * fun x => (μ[f|m_pa]) x) μ := by
          have heq : g * (fun x => (μ[f|m_pa]) x) =
              B.indicator (fun x => (μ[f|m_pa]) x) := by
            ext x; simp [g, Set.indicator, Pi.mul_apply]
          rw [heq]; exact (integrable_condExp (m := m_pa)).indicator hB_pi
        -- Convert ∫_{A∩B} to ∫_A via setIntegral_indicator
        rw [← setIntegral_indicator hB_pi, ← setIntegral_indicator hB_pi]
        -- Rewrite B.indicator h as g * h
        have h_ind_rhs : (fun x => B.indicator f x) = g * f := by
          ext x; simp only [Set.indicator_apply, Pi.mul_apply, g]
          split_ifs <;> simp
        have h_ind_lhs : (fun x => B.indicator (fun x => (μ[f|m_pa]) x) x) =
            (g * fun x => (μ[f|m_pa]) x) := by
          ext x; simp only [Set.indicator_apply, Pi.mul_apply, g]
          split_ifs <;> simp
        rw [h_ind_lhs, h_ind_rhs]
        -- Goal: ∫_A (g * μ[f|m_pa]) dμ = ∫_A (g * f) dμ
        -- Step 1: RHS = ∫_A μ[g*f|m_pa] dμ (by setIntegral_condExp.symm)
        rw [(setIntegral_condExp hm_pa_le hgf_int hA).symm]
        -- Step 2: LHS = ∫_A μ[g*μ[f|m_pa]|m_pa] dμ (by setIntegral_condExp.symm)
        rw [show ∫ x in A, (g * fun x => (μ[f|m_pa]) x) x ∂μ =
            ∫ x in A, (μ[g * fun x => (μ[f|m_pa]) x | m_pa]) x ∂μ from
          (setIntegral_condExp hm_pa_le hgce_int hA).symm]
        -- Goal: ∫_A μ[g*μ[f|m_pa]|m_pa] dμ = ∫_A μ[g*f|m_pa] dμ
        -- Step 3: By pull-out, μ[g*μ[f|m_pa]|m_pa] =ᵃᵉ μ[f|m_pa]*μ[g|m_pa]
        -- (since μ[f|m_pa] is m_pa-strongly-measurable)
        have hce_bnd := condExp_indicator_norm_le_one bn μ hm_pa_le t₂ ht₂_pi
        have h_pullout : μ[g * (fun x => (μ[f|m_pa]) x) | m_pa] =ᵐ[μ]
            (fun x => (μ[f|m_pa]) x) * μ[g | m_pa] := by
          have hcomm : g * (fun x => (μ[f|m_pa]) x) =
              (fun x => (μ[f|m_pa]) x) * g := mul_comm _ _
          rw [hcomm]
          exact condExp_stronglyMeasurable_mul_of_bound hm_pa_le
            stronglyMeasurable_condExp hg_int 1 hce_bnd
        -- Step 4: By CI, μ[g*f|m_pa] =ᵃᵉ μ[g|m_pa]*μ[f|m_pa]
        -- Both =ᵃᵉ μ[f|m_pa]*μ[g|m_pa] (by mul_comm)
        have h_ci_comm : μ[g * f | m_pa] =ᵐ[μ]
            (fun x => (μ[f|m_pa]) x) * μ[g | m_pa] := by
          exact hci.trans (Filter.EventuallyEq.of_eq (mul_comm _ _))
        -- Both integrands are a.e. equal:
        -- μ[g * μ[f|m_pa] | m_pa] =ᵃᵉ μ[f|m_pa] * μ[g|m_pa] =ᵃᵉ μ[g * f | m_pa]
        -- So their integrals over A are equal
        exact setIntegral_congr_ae (hm_pa_le _ hA)
          ((h_pullout.trans h_ci_comm.symm).mono (fun x hx => fun _ => hx)))
      (by -- C(complement): C(t) → C(tᶜ)
        intro t ht hCt
        have ht_pi : @MeasurableSet _ MeasurableSpace.pi t := hm_pav_le _ ht
        have h_total : ∫ x, (μ[f | m_pa]) x ∂μ = ∫ x, f x ∂μ :=
          integral_condExp hm_pa_le
        have hg_int' : Integrable (fun x => (μ[f | m_pa]) x : bn.JointSpace → ℝ) μ :=
          integrable_condExp (m := m_pa)
        have hg_add := integral_add_compl ht_pi hg_int'
        have hf_add := integral_add_compl ht_pi hf_int
        linarith)
      (by -- C(countable disjoint union)
        intro g_seq hd hm hC
        have hg_meas : ∀ i, @MeasurableSet _ MeasurableSpace.pi (g_seq i) :=
          fun i => hm_pav_le _ (hm i)
        have h1 : ∫ x in ⋃ i, g_seq i, (μ[f | m_pa]) x ∂μ =
            ∑' i, ∫ x in g_seq i, (μ[f | m_pa]) x ∂μ :=
          integral_iUnion hg_meas hd integrable_condExp.integrableOn
        have h2 : ∫ x in ⋃ i, g_seq i, f x ∂μ =
            ∑' i, ∫ x in g_seq i, f x ∂μ :=
          integral_iUnion hg_meas hd hf_int.integrableOn
        rw [h1, h2]
        exact tsum_congr hC)
    exact h_dynkin s hs
  exact (ae_eq_condExp_of_forall_setIntegral_eq hm_pav_le hf_int hg_int hg_eq hg_sm).symm

/-- The local Markov property holds for discrete CPT joint measures.

    Uses the tower/pull-out proof:
    1. Pull-out on m_pa⊔m_v: μ[1_{t₁}·1_{t₂}|m_pav] =ᵐ 1_{t₁}·μ[1_{t₂}|m_pav]
    2. BN factorization: μ[1_{t₂}|m_pav] =ᵐ μ[1_{t₂}|m_pa]
    3. Tower: μ[μ[·|m_pav]|m_pa] =ᵐ μ[·|m_pa]
    4. Pull-out on m_pa: μ[μ[f₂|m_pa]·1_{t₁}|m_pa] =ᵐ μ[f₂|m_pa]·μ[1_{t₁}|m_pa]
-/
theorem discrete_localMarkovCondition
    (cpt : bn.DiscreteCPT) (v : V) :
    LocalMarkovCondition bn cpt.jointMeasure v := by
  rw [LocalMarkovCondition, condIndep_iff]
  · intro t₁ t₂ ht₁ ht₂
    let m_pa := bn.measurableSpaceOfVertices (bn.graph.parents v)
    let m_pav := m_pa ⊔ bn.measurableSpaceOfVertices ({v} : Set V)
    have hm_pa_le : m_pa ≤ MeasurableSpace.pi := bn.measurableSpaceOfVertices_le _
    have hm_pav_le : m_pav ≤ MeasurableSpace.pi :=
      sup_le hm_pa_le (bn.measurableSpaceOfVertices_le _)
    haveI hsf : SigmaFinite (cpt.jointMeasure.trim hm_pav_le) :=
      BayesianNetwork.sigmaFinite_trim_of_le bn cpt.jointMeasure m_pav hm_pav_le
    have ht₁_pi : @MeasurableSet _ MeasurableSpace.pi t₁ :=
      (bn.measurableSpaceOfVertices_le _) _ ht₁
    have ht₂_pi : @MeasurableSet _ MeasurableSpace.pi t₂ :=
      (bn.measurableSpaceOfVertices_le _) _ ht₂
    -- Indicator functions
    let f₁ := t₁.indicator (fun _ => (1 : ℝ))
    let f₂ := t₂.indicator (fun _ => (1 : ℝ))
    have hf₁_int : Integrable f₁ cpt.jointMeasure :=
      (integrable_const (1 : ℝ)).indicator ht₁_pi
    have hf₂_int : Integrable f₂ cpt.jointMeasure :=
      (integrable_const (1 : ℝ)).indicator ht₂_pi
    -- Step 1: 1_{t₁∩t₂} = f₁ * f₂
    have hind : (t₁ ∩ t₂).indicator (fun _ => (1 : ℝ)) = f₁ * f₂ := by
      ext ω; simp only [f₁, f₂, Set.indicator, Pi.mul_apply, Set.mem_inter_iff]
      split_ifs <;> simp_all
    -- Step 2: Pull-out on m_pav: μ[f₁*f₂|m_pav] =ᵐ f₁ * μ[f₂|m_pav]
    have hf₁_sm : StronglyMeasurable[m_pav] f₁ :=
      (stronglyMeasurable_const.indicator ht₁).mono le_sup_right
    have hf₁_bnd : ∀ᵐ ω ∂cpt.jointMeasure, ‖f₁ ω‖ ≤ 1 := by
      filter_upwards with ω; simp only [f₁, Set.indicator]; split_ifs <;> simp
    have h2 : cpt.jointMeasure[(t₁ ∩ t₂).indicator (fun _ => (1:ℝ)) | m_pav] =ᵐ[cpt.jointMeasure]
        f₁ * cpt.jointMeasure[f₂ | m_pav] :=
      (condExp_congr_ae (Filter.EventuallyEq.of_eq hind)).trans
        (condExp_stronglyMeasurable_mul_of_bound hm_pav_le hf₁_sm hf₂_int 1 hf₁_bnd)
    -- Step 3: BN factorization: μ[f₂|m_pav] =ᵐ μ[f₂|m_pa]
    have h3 := condExp_ndesc_indep_of_vertex bn cpt v t₂ ht₂
    -- Step 4: Combine 2+3: μ[1_{t₁∩t₂}|m_pav] =ᵐ f₁ * μ[f₂|m_pa]
    have h4 := h2.trans (Filter.EventuallyEq.mul (Filter.EventuallyEq.refl _ f₁) h3)
    -- Step 5: Tower + condition: μ[1_{t₁∩t₂}|m_pa] =ᵐ μ[f₁*μ[f₂|m_pa]|m_pa]
    have h5 : cpt.jointMeasure[(t₁ ∩ t₂).indicator (fun _ => (1:ℝ)) | m_pa]
        =ᵐ[cpt.jointMeasure]
        cpt.jointMeasure[f₁ * cpt.jointMeasure[f₂ | m_pa] | m_pa] :=
      (condExp_condExp_of_le (m₁ := m_pa) (m₂ := m_pav) le_sup_left hm_pav_le).symm.trans
        (condExp_congr_ae h4)
    -- Step 6: Pull-out on m_pa: μ[g*f₁|m_pa] =ᵐ g*μ[f₁|m_pa] where g = μ[f₂|m_pa]
    have hce_bnd := condExp_indicator_norm_le_one bn cpt.jointMeasure hm_pa_le t₂ ht₂_pi
    have h6 : cpt.jointMeasure[f₁ * cpt.jointMeasure[f₂ | m_pa] | m_pa]
        =ᵐ[cpt.jointMeasure]
        cpt.jointMeasure[f₁ | m_pa] * cpt.jointMeasure[f₂ | m_pa] := by
      have hcomm : f₁ * cpt.jointMeasure[f₂ | m_pa] =
          cpt.jointMeasure[f₂ | m_pa] * f₁ := mul_comm _ _
      rw [hcomm]
      exact (condExp_stronglyMeasurable_mul_of_bound hm_pa_le
        stronglyMeasurable_condExp hf₁_int 1 hce_bnd).trans
        (Filter.EventuallyEq.of_eq (mul_comm _ _))
    exact h5.trans h6
  · exact bn.measurableSpaceOfVertices_le _
  · exact bn.measurableSpaceOfVertices_le _

/-- Reduced-core discrete conditional independence for concrete events:
an event depending only on `v` is conditionally independent of an event
depending only on `ND(v) \ (Pa(v) ∪ {v})`, given the parent coordinates. -/
theorem jointMeasure_condIndepSet_of_vertex_nonDesc_given_parents
    (cpt : bn.DiscreteCPT) (v : V)
    {B t₂ : Set bn.JointSpace}
    (hB : MeasurableSet[bn.measurableSpaceOfVertices ({v} : Set V)] B)
    (ht₂ : MeasurableSet[bn.measurableSpaceOfVertices
            (bn.nonDescendantsExceptParentsAndSelf v)] t₂) :
    ProbabilityTheory.CondIndepSet
      (m' := bn.measurableSpaceOfVertices (bn.graph.parents v))
      (hm' := measurableSpaceOfVertices_le (bn := bn) (bn.graph.parents v))
      B t₂ cpt.jointMeasure := by
  have hmarkov : LocalMarkovCondition bn cpt.jointMeasure v :=
    discrete_localMarkovCondition (bn := bn) cpt v
  have hsets :=
    (ProbabilityTheory.condIndep_iff_forall_condIndepSet
      (m' := bn.measurableSpaceOfVertices (bn.graph.parents v))
      (m₁ := bn.measurableSpaceOfVertices ({v} : Set V))
      (m₂ := bn.measurableSpaceOfVertices (bn.nonDescendantsExceptParentsAndSelf v))
      (hm' := measurableSpaceOfVertices_le (bn := bn) (bn.graph.parents v))
      (μ := cpt.jointMeasure)).1 (by
        simpa [LocalMarkovCondition] using hmarkov)
  exact hsets B t₂ hB ht₂

/-- Reduced-core discrete conditional independence remains valid after
intersecting the singleton-left and non-descendant-right events with additional
parent-measurable events. This is the first non-singleton event-level bridge we
need for parent-enriched reduced-core arguments. -/
theorem jointMeasure_condIndepSet_of_parent_inter_vertex_parent_inter_nonDesc_given_parents
    (cpt : bn.DiscreteCPT) (v : V)
    {u B w t₂ : Set bn.JointSpace}
    (hu : MeasurableSet[bn.measurableSpaceOfVertices (bn.graph.parents v)] u)
    (hB : MeasurableSet[bn.measurableSpaceOfVertices ({v} : Set V)] B)
    (hw : MeasurableSet[bn.measurableSpaceOfVertices (bn.graph.parents v)] w)
    (ht₂ : MeasurableSet[bn.measurableSpaceOfVertices
            (bn.nonDescendantsExceptParentsAndSelf v)] t₂) :
    ProbabilityTheory.CondIndepSet
      (m' := bn.measurableSpaceOfVertices (bn.graph.parents v))
      (hm' := measurableSpaceOfVertices_le (bn := bn) (bn.graph.parents v))
      (u ∩ B) (w ∩ t₂) cpt.jointMeasure := by
  have hB_meas :
      MeasurableSet B :=
    (measurableSpaceOfVertices_le (bn := bn) ({v} : Set V)) _ hB
  have ht₂_meas :
      MeasurableSet t₂ :=
    (measurableSpaceOfVertices_le (bn := bn)
      (bn.nonDescendantsExceptParentsAndSelf v)) _ ht₂
  have hbase :
      ProbabilityTheory.CondIndepSet
        (m' := bn.measurableSpaceOfVertices (bn.graph.parents v))
        (hm' := measurableSpaceOfVertices_le (bn := bn) (bn.graph.parents v))
        B t₂ cpt.jointMeasure :=
    jointMeasure_condIndepSet_of_vertex_nonDesc_given_parents
      (bn := bn) cpt v hB ht₂
  have hleft :
      ProbabilityTheory.CondIndepSet
        (m' := bn.measurableSpaceOfVertices (bn.graph.parents v))
        (hm' := measurableSpaceOfVertices_le (bn := bn) (bn.graph.parents v))
        (u ∩ B) t₂ cpt.jointMeasure :=
    condIndepSet_inter_left_of_measurable
      (bn := bn) (μ := cpt.jointMeasure) (Z := bn.graph.parents v)
      hu hB_meas ht₂_meas hbase
  have huB_meas : MeasurableSet (u ∩ B) :=
    ((measurableSpaceOfVertices_le (bn := bn) (bn.graph.parents v)) _ hu).inter hB_meas
  simpa [Set.inter_comm] using
    (condIndepSet_inter_right_of_measurable
      (bn := bn) (μ := cpt.jointMeasure) (Z := bn.graph.parents v)
      huB_meas ht₂_meas hw hleft)

/-- Discrete local Markov, lifted directly from the concrete event theorem to the
vertex-generated σ-algebras for `{v}` and `ND(v) \ (Pa(v) ∪ {v})`. -/
theorem jointMeasure_condIndepVertices_of_vertex_nonDesc_given_parents
    (cpt : bn.DiscreteCPT) (v : V) :
    CondIndepVertices
      bn cpt.jointMeasure ({v} : Set V)
      (bn.nonDescendantsExceptParentsAndSelf v) (bn.graph.parents v) := by
  unfold CondIndepVertices
  exact
    (ProbabilityTheory.condIndep_iff_forall_condIndepSet
      (m' := bn.measurableSpaceOfVertices (bn.graph.parents v))
      (m₁ := bn.measurableSpaceOfVertices ({v} : Set V))
      (m₂ := bn.measurableSpaceOfVertices (bn.nonDescendantsExceptParentsAndSelf v))
      (hm' := measurableSpaceOfVertices_le (bn := bn) (bn.graph.parents v))
      (μ := cpt.jointMeasure)).2
      (fun s t hs ht =>
        jointMeasure_condIndepSet_of_vertex_nonDesc_given_parents
          (bn := bn) cpt v hs ht)

/-- Parent coordinates can be freely added to both sides of the reduced-core
discrete local-Markov statement, because they are already measurable in the
conditioning σ-algebra. -/
theorem jointMeasure_condIndepVertices_of_parentset_union_vertex_nonDesc_given_parents
    (cpt : bn.DiscreteCPT) (v : V) {U W : Set V}
    (hU : U ⊆ bn.graph.parents v)
    (hW : W ⊆ bn.graph.parents v) :
    CondIndepVertices
      bn cpt.jointMeasure (U ∪ ({v} : Set V))
      (W ∪ bn.nonDescendantsExceptParentsAndSelf v) (bn.graph.parents v) := by
  have hbase :
      CondIndepVertices
        bn cpt.jointMeasure ({v} : Set V)
        (bn.nonDescendantsExceptParentsAndSelf v) (bn.graph.parents v) :=
    jointMeasure_condIndepVertices_of_vertex_nonDesc_given_parents
      (bn := bn) cpt v
  have hleft :
      CondIndepVertices
        bn cpt.jointMeasure (U ∪ ({v} : Set V))
        (bn.nonDescendantsExceptParentsAndSelf v) (bn.graph.parents v) :=
    condIndepVertices_union_left_of_subset_conditioning
      (bn := bn) (μ := cpt.jointMeasure)
      (U := U) (X := ({v} : Set V))
      (Y := bn.nonDescendantsExceptParentsAndSelf v)
      (Z := bn.graph.parents v) hU hbase
  exact
    condIndepVertices_union_right_of_subset_conditioning
      (bn := bn) (μ := cpt.jointMeasure)
      (X := U ∪ ({v} : Set V))
      (U := W) (Y := bn.nonDescendantsExceptParentsAndSelf v)
      (Z := bn.graph.parents v) hW hleft

/-- Set-level reduced-core discrete soundness for parent-enriched singleton blocks:
arbitrary events measurable in `σ(U ∪ {v})` and `σ(W ∪ ND(v)\(Pa(v)∪{v}))`
are conditionally independent given `σ(Pa(v))` whenever `U,W ⊆ Pa(v)`. -/
theorem jointMeasure_condIndepSet_of_parentset_union_vertex_parentset_union_nonDesc_given_parents
    (cpt : bn.DiscreteCPT) (v : V) {U W : Set V}
    (hU : U ⊆ bn.graph.parents v)
    (hW : W ⊆ bn.graph.parents v)
    {s t : Set bn.JointSpace}
    (hs : MeasurableSet[bn.measurableSpaceOfVertices (U ∪ ({v} : Set V))] s)
    (ht : MeasurableSet[bn.measurableSpaceOfVertices
            (W ∪ bn.nonDescendantsExceptParentsAndSelf v)] t) :
    ProbabilityTheory.CondIndepSet
      (m' := bn.measurableSpaceOfVertices (bn.graph.parents v))
      (hm' := measurableSpaceOfVertices_le (bn := bn) (bn.graph.parents v))
      s t cpt.jointMeasure := by
  have hCI :
      CondIndepVertices
        bn cpt.jointMeasure (U ∪ ({v} : Set V))
        (W ∪ bn.nonDescendantsExceptParentsAndSelf v) (bn.graph.parents v) :=
    jointMeasure_condIndepVertices_of_parentset_union_vertex_nonDesc_given_parents
      (bn := bn) cpt v hU hW
  exact
    (ProbabilityTheory.condIndep_iff_forall_condIndepSet
      (m' := bn.measurableSpaceOfVertices (bn.graph.parents v))
      (m₁ := bn.measurableSpaceOfVertices (U ∪ ({v} : Set V)))
      (m₂ := bn.measurableSpaceOfVertices (W ∪ bn.nonDescendantsExceptParentsAndSelf v))
      (hm' := measurableSpaceOfVertices_le (bn := bn) (bn.graph.parents v))
      (μ := cpt.jointMeasure)).1 (by
        simpa [CondIndepVertices] using hCI) s t hs ht

/-- Reduced-core discrete soundness for a parent-enriched singleton-left block:
if the only non-conditioned left vertex is `v`, then d-separation from `Y`
given `Pa(v)` is enough to invoke the discrete local-Markov bridge. -/
theorem dsepFull_parentset_union_singleton_left_parentset_condIndepVertices
    (cpt : bn.DiscreteCPT) {v : V} {U Y : Set V}
    (hU : U ⊆ bn.graph.parents v)
    (hXY : (U ∪ ({v} : Set V)) ∩ Y ⊆ bn.graph.parents v)
    (hdsep :
      Mettapedia.ProbabilityTheory.BayesianNetworks.DSeparation.DSeparatedFull
        bn.graph (U ∪ ({v} : Set V)) Y (bn.graph.parents v)) :
    CondIndepVertices
      bn cpt.jointMeasure (U ∪ ({v} : Set V)) Y (bn.graph.parents v) := by
  have hSubset :
      Y \ bn.graph.parents v ⊆ bn.nonDescendantsExceptParentsAndSelf v :=
    dsepFull_parentset_union_singleton_left_parentset_subset_nonDescendantsExceptParentsAndSelf
      (bn := bn) (v := v) hXY hdsep
  have hCore :
      CondIndepVertices
        bn cpt.jointMeasure (U ∪ ({v} : Set V))
        ((Y ∩ bn.graph.parents v) ∪ bn.nonDescendantsExceptParentsAndSelf v)
        (bn.graph.parents v) :=
    jointMeasure_condIndepVertices_of_parentset_union_vertex_nonDesc_given_parents
      (bn := bn) cpt v hU (by
        intro y hy
        exact hy.2)
  have hY :
      Y ⊆ (Y ∩ bn.graph.parents v) ∪ bn.nonDescendantsExceptParentsAndSelf v := by
    intro y hy
    by_cases hyPa : y ∈ bn.graph.parents v
    · exact Or.inl ⟨hy, hyPa⟩
    · exact Or.inr (hSubset ⟨hy, hyPa⟩)
  exact condIndepVertices_of_le_right (bn := bn) (μ := cpt.jointMeasure) hY hCore

/-- Event-level form of the parent-enriched singleton-left reduced-core
d-separation bridge. This is the concrete measurable-event theorem that the
broader disjoint-core route will want to reuse. -/
theorem dsepFull_parentset_union_singleton_left_parentset_condIndepSet
    (cpt : bn.DiscreteCPT) {v : V} {U Y : Set V}
    (hU : U ⊆ bn.graph.parents v)
    (hXY : (U ∪ ({v} : Set V)) ∩ Y ⊆ bn.graph.parents v)
    (hdsep :
      Mettapedia.ProbabilityTheory.BayesianNetworks.DSeparation.DSeparatedFull
        bn.graph (U ∪ ({v} : Set V)) Y (bn.graph.parents v))
    {s t : Set bn.JointSpace}
    (hs : MeasurableSet[bn.measurableSpaceOfVertices (U ∪ ({v} : Set V))] s)
    (ht : MeasurableSet[bn.measurableSpaceOfVertices Y] t) :
    ProbabilityTheory.CondIndepSet
      (m' := bn.measurableSpaceOfVertices (bn.graph.parents v))
      (hm' := measurableSpaceOfVertices_le (bn := bn) (bn.graph.parents v))
      s t cpt.jointMeasure := by
  have hCI :
      CondIndepVertices
        bn cpt.jointMeasure (U ∪ ({v} : Set V)) Y (bn.graph.parents v) :=
    dsepFull_parentset_union_singleton_left_parentset_condIndepVertices
      (bn := bn) cpt hU hXY hdsep
  exact
    (ProbabilityTheory.condIndep_iff_forall_condIndepSet
      (m' := bn.measurableSpaceOfVertices (bn.graph.parents v))
      (m₁ := bn.measurableSpaceOfVertices (U ∪ ({v} : Set V)))
      (m₂ := bn.measurableSpaceOfVertices Y)
      (hm' := measurableSpaceOfVertices_le (bn := bn) (bn.graph.parents v))
      (μ := cpt.jointMeasure)).1 (by
        simpa [CondIndepVertices] using hCI) s t hs ht

/-- If every pair of `eventOfConstraints` atoms over `X` and `Y` is conditionally
independent given `σ(Z)`, then the full vertex-generated σ-algebras over `X` and
`Y` are conditionally independent given `σ(Z)`. This packages the final lift
from atomic block identities to the public `CondIndepVertices` API. -/
theorem condIndepVertices_of_condIndepSet_constraintAtoms
    (μ : Measure bn.JointSpace) [IsFiniteMeasure μ]
    [∀ v, MeasurableSingletonClass (bn.stateSpace v)]
    {X Y Z : Set V}
    (hatom :
      ∀ xX : (∀ p : X, bn.stateSpace p.1),
        ∀ xY : (∀ p : Y, bn.stateSpace p.1),
          ProbabilityTheory.CondIndepSet
            (m' := bn.measurableSpaceOfVertices Z)
            (hm' := measurableSpaceOfVertices_le (bn := bn) Z)
            (eventOfConstraints (bn := bn)
              (constraintsOfRestrict (bn := bn) X xX))
            (eventOfConstraints (bn := bn)
              (constraintsOfRestrict (bn := bn) Y xY))
            μ) :
    CondIndepVertices bn μ X Y Z := by
  let mZ : MeasurableSpace bn.JointSpace := bn.measurableSpaceOfVertices Z
  let mX : MeasurableSpace bn.JointSpace := bn.measurableSpaceOfVertices X
  let mY : MeasurableSpace bn.JointSpace := bn.measurableSpaceOfVertices Y
  let atomX : (∀ p : X, bn.stateSpace p.1) → Set bn.JointSpace :=
    fun xX => eventOfConstraints (bn := bn)
      (constraintsOfRestrict (bn := bn) X xX)
  let atomY : (∀ p : Y, bn.stateSpace p.1) → Set bn.JointSpace :=
    fun xY => eventOfConstraints (bn := bn)
      (constraintsOfRestrict (bn := bn) Y xY)
  let p : Set (Set bn.JointSpace) :=
    {a | a = ∅ ∨ ∃ xX : (∀ q : X, bn.stateSpace q.1), a = atomX xX}
  let q : Set (Set bn.JointSpace) :=
    {b | b = ∅ ∨ ∃ xY : (∀ r : Y, bn.stateSpace r.1), b = atomY xY}
  have hmZ : mZ ≤ (MeasurableSpace.pi : MeasurableSpace bn.JointSpace) :=
    measurableSpaceOfVertices_le (bn := bn) Z
  have hmX : mX ≤ (MeasurableSpace.pi : MeasurableSpace bn.JointSpace) :=
    measurableSpaceOfVertices_le (bn := bn) X
  have hmY : mY ≤ (MeasurableSpace.pi : MeasurableSpace bn.JointSpace) :=
    measurableSpaceOfVertices_le (bn := bn) Y
  have hAtomX_meas :
      ∀ xX : (∀ p : X, bn.stateSpace p.1),
        MeasurableSet[mX] (atomX xX) := by
    intro xX
    have hcomap :
        MeasurableSet[
          MeasurableSpace.comap (restrictToSet (bn := bn) X) (by infer_instance)]
          (atomX xX) := by
      refine (MeasurableSpace.measurableSet_comap).2 ?_
      refine ⟨{xX}, by simp, ?_⟩
      exact (eventOfConstraints_constraintsOfRestrict (bn := bn) X xX).symm
    simpa [mX, measurableSpaceOfVertices_eq_comap_restrict (bn := bn) X,
      atomX] using hcomap
  have hAtomY_meas :
      ∀ xY : (∀ p : Y, bn.stateSpace p.1),
        MeasurableSet[mY] (atomY xY) := by
    intro xY
    have hcomap :
        MeasurableSet[
          MeasurableSpace.comap (restrictToSet (bn := bn) Y) (by infer_instance)]
          (atomY xY) := by
      refine (MeasurableSpace.measurableSet_comap).2 ?_
      refine ⟨{xY}, by simp, ?_⟩
      exact (eventOfConstraints_constraintsOfRestrict (bn := bn) Y xY).symm
    simpa [mY, measurableSpaceOfVertices_eq_comap_restrict (bn := bn) Y,
      atomY] using hcomap
  have hp_pi : IsPiSystem p := by
    intro a ha b hb hab
    rcases ha with rfl | ⟨xX, rfl⟩
    · simpa using hab
    · rcases hb with rfl | ⟨yX, rfl⟩
      · simpa [p] using hab
      · by_cases hxy : xX = yX
        · right
          refine ⟨xX, ?_⟩
          subst hxy
          ext ω
          simp [atomX]
        · left
          ext ω
          have hdisj :
              Disjoint
                (eventOfConstraints (bn := bn)
                  (constraintsOfRestrict (bn := bn) X xX))
                (eventOfConstraints (bn := bn)
                  (constraintsOfRestrict (bn := bn) X yX)) :=
            eventOfConstraints_constraintsOfRestrict_disjoint
              (bn := bn) X hxy
          have hempty : ω ∉ atomX xX ∩ atomX yX := by
            intro hω
            exact Set.disjoint_left.mp hdisj hω.1 hω.2
          simp [atomX, hempty]
  have hq_pi : IsPiSystem q := by
    intro a ha b hb hab
    rcases ha with rfl | ⟨xY, rfl⟩
    · simpa using hab
    · rcases hb with rfl | ⟨yY, rfl⟩
      · simpa [q] using hab
      · by_cases hxy : xY = yY
        · right
          refine ⟨xY, ?_⟩
          subst hxy
          ext ω
          simp [atomY]
        · left
          ext ω
          have hdisj :
              Disjoint
                (eventOfConstraints (bn := bn)
                  (constraintsOfRestrict (bn := bn) Y xY))
                (eventOfConstraints (bn := bn)
                  (constraintsOfRestrict (bn := bn) Y yY)) :=
            eventOfConstraints_constraintsOfRestrict_disjoint
              (bn := bn) Y hxy
          have hempty : ω ∉ atomY xY ∩ atomY yY := by
            intro hω
            exact Set.disjoint_left.mp hdisj hω.1 hω.2
          simp [atomY, hempty]
  have hp_meas : ∀ a ∈ p, @MeasurableSet _ MeasurableSpace.pi a := by
    intro a ha
    rcases ha with rfl | ⟨xX, rfl⟩
    · simpa using (MeasurableSet.empty : @MeasurableSet _ MeasurableSpace.pi ∅)
    · exact hmX _ (hAtomX_meas xX)
  have hq_meas : ∀ b ∈ q, @MeasurableSet _ MeasurableSpace.pi b := by
    intro b hb
    rcases hb with rfl | ⟨xY, rfl⟩
    · simpa using (MeasurableSet.empty : @MeasurableSet _ MeasurableSpace.pi ∅)
    · exact hmY _ (hAtomY_meas xY)
  have hp_generate : MeasurableSpace.generateFrom p = mX := by
    apply le_antisymm
    · apply MeasurableSpace.generateFrom_le
      intro a ha
      rcases ha with rfl | ⟨xX, rfl⟩
      · simpa [mX] using (MeasurableSet.empty : MeasurableSet[MeasurableSpace.pi] ∅)
      · exact hAtomX_meas xX
    · intro s hs
      rcases measurableSet_vertices_preimage (bn := bn) (S := X) (s := s) hs with
        ⟨T, hT, rfl⟩
      rw [vertices_preimage_eq_iUnion_eventOfConstraints (bn := bn) X T]
      apply MeasurableSet.iUnion
      intro xX
      by_cases hxX : xX ∈ T
      · have hmem :
            (if xX ∈ T then atomX xX else (∅ : Set bn.JointSpace)) ∈ p := by
          right
          refine ⟨xX, ?_⟩
          simp [hxX, atomX]
        exact MeasurableSpace.measurableSet_generateFrom hmem
      · have hmem :
            (if xX ∈ T then atomX xX else (∅ : Set bn.JointSpace)) ∈ p := by
          left
          simp [hxX]
        simpa [hxX] using MeasurableSpace.measurableSet_generateFrom hmem
  have hq_generate : MeasurableSpace.generateFrom q = mY := by
    apply le_antisymm
    · apply MeasurableSpace.generateFrom_le
      intro b hb
      rcases hb with rfl | ⟨xY, rfl⟩
      · simpa [mY] using (MeasurableSet.empty : MeasurableSet[MeasurableSpace.pi] ∅)
      · exact hAtomY_meas xY
    · intro t ht
      rcases measurableSet_vertices_preimage (bn := bn) (S := Y) (s := t) ht with
        ⟨T, hT, rfl⟩
      rw [vertices_preimage_eq_iUnion_eventOfConstraints (bn := bn) Y T]
      apply MeasurableSet.iUnion
      intro xY
      by_cases hxY : xY ∈ T
      · have hmem :
            (if xY ∈ T then atomY xY else (∅ : Set bn.JointSpace)) ∈ q := by
          right
          refine ⟨xY, ?_⟩
          simp [hxY, atomY]
        exact MeasurableSpace.measurableSet_generateFrom hmem
      · have hmem :
            (if xY ∈ T then atomY xY else (∅ : Set bn.JointSpace)) ∈ q := by
          left
          simp [hxY]
        simpa [hxY] using MeasurableSpace.measurableSet_generateFrom hmem
  have hpq :
      ProbabilityTheory.CondIndepSets (m' := mZ) (hm' := hmZ) p q μ := by
    rw [ProbabilityTheory.condIndepSets_iff
      (m' := mZ) (hm' := hmZ) (s1 := p) (s2 := q) hp_meas hq_meas (μ := μ)]
    intro a b ha hb
    rcases ha with rfl | ⟨xX, rfl⟩
    · exact
        (ProbabilityTheory.condIndepSet_iff
          (m' := mZ) (hm' := hmZ) (s := (∅ : Set bn.JointSpace)) (t := b)
          (show @MeasurableSet _ MeasurableSpace.pi (∅ : Set bn.JointSpace) from by simp)
          (hq_meas b hb) (μ := μ)).1
        (condIndepSet_of_measurable_left
          (bn := bn) (μ := μ) (Z := Z)
          (show @MeasurableSet _ mZ (∅ : Set bn.JointSpace) from by simp)
          (hq_meas b hb))
    · rcases hb with rfl | ⟨xY, rfl⟩
      · exact
          (ProbabilityTheory.condIndepSet_iff
            (m' := mZ) (hm' := hmZ) (s := atomX xX) (t := (∅ : Set bn.JointSpace))
            (hmX _ (hAtomX_meas xX))
            (show @MeasurableSet _ MeasurableSpace.pi (∅ : Set bn.JointSpace) from by simp)
            (μ := μ)).1
          (condIndepSet_of_measurable_right
            (bn := bn) (μ := μ) (Z := Z)
            (hmX _ (hAtomX_meas xX))
            (show @MeasurableSet _ mZ (∅ : Set bn.JointSpace) from by simp))
      · exact
          (ProbabilityTheory.condIndepSet_iff
            (m' := mZ) (hm' := hmZ) (s := atomX xX) (t := atomY xY)
            (hmX _ (hAtomX_meas xX)) (hmY _ (hAtomY_meas xY)) (μ := μ)).1
          (by simpa [atomX, atomY] using hatom xX xY)
  have hsup :
      ProbabilityTheory.CondIndep
        (m' := mZ) (m₁ := MeasurableSpace.generateFrom p)
        (m₂ := MeasurableSpace.generateFrom q)
        (hm' := hmZ) μ :=
    ProbabilityTheory.CondIndepSets.condIndep'
      (m' := mZ) (hm' := hmZ)
      hp_meas hq_meas hp_pi hq_pi hpq
  simpa [CondIndepVertices, mZ, mX, mY, hp_generate, hq_generate] using hsup

/-- The `X`- and `Y`-reachable moral-ancestral blocks are conditionally
independent given `Z` for the discrete CPT joint measure. This packages the
block-atom `CondIndepSet` theorem into the vertex-level API. -/
theorem jointMeasure_reachableBlocks_condIndepVertices
    [∀ v, MeasurableSingletonClass (bn.stateSpace v)]
    (cpt : bn.DiscreteCPT) (X Y Z : Set V)
    (hirr : ∀ v : V, ¬bn.graph.edges v v)
    (hXY : Disjoint X Y)
    (hSep : DSeparation.SeparatedInMoralAncestral bn.graph X Y Z) :
    CondIndepVertices bn cpt.jointMeasure
      (DSeparation.xReachableBlock bn.graph X Y Z)
      (DSeparation.yReachableBlock bn.graph X Y Z)
      Z := by
  refine condIndepVertices_of_condIndepSet_constraintAtoms
      (bn := bn) (μ := cpt.jointMeasure)
      (X := DSeparation.xReachableBlock bn.graph X Y Z)
      (Y := DSeparation.yReachableBlock bn.graph X Y Z)
      (Z := Z) ?_
  intro xX xY
  simpa using
    jointMeasure_blockConstraint_condIndepSet
      (bn := bn) (cpt := cpt) X Y Z hirr hXY hSep xX xY

/-- Disjoint-core d-separation soundness for discrete CPT joint measures. -/
theorem jointMeasure_dsepFull_disjoint_core_condIndepVertices
    [∀ v, MeasurableSingletonClass (bn.stateSpace v)]
    (cpt : bn.DiscreteCPT)
    {X Y Z : Set V}
    (hXY : Disjoint X Y)
    (hdsep : DSeparation.DSeparatedFull bn.graph X Y Z) :
    CondIndepVertices bn cpt.jointMeasure X Y Z := by
  have hirr : ∀ v : V, ¬bn.graph.edges v v := by
    intro v hvv
    exact bn.acyclic v ⟨v, hvv, DirectedGraph.reachable_refl bn.graph v⟩
  have hSep :
      DSeparation.SeparatedInMoralAncestral bn.graph X Y Z :=
    (DSeparation.dsepFull_iff_separatedInMoralAncestral
      bn.graph X Y Z bn.acyclic hirr).1 hdsep
  have hBlocks :
      CondIndepVertices bn cpt.jointMeasure
        (DSeparation.xReachableBlock bn.graph X Y Z)
        (DSeparation.yReachableBlock bn.graph X Y Z)
        Z :=
    jointMeasure_reachableBlocks_condIndepVertices
      (bn := bn) (cpt := cpt) X Y Z hirr hXY hSep
  have hsubX : X \ Z ⊆ DSeparation.xReachableBlock bn.graph X Y Z := by
    intro x hx
    refine ⟨
      DSeparation.endpoint_in_relevantOutsideConditioning_X bn.graph X Y Z hx.1 hx.2,
      x, hx.1, hx.2, ?_⟩
    exact DirectedGraph.reachable_refl
      (DSeparation.moralAncestralWithoutConditioning bn.graph X Y Z) x
  have hsubY : Y \ Z ⊆ DSeparation.yReachableBlock bn.graph X Y Z := by
    intro y hy
    refine ⟨
      DSeparation.endpoint_in_relevantOutsideConditioning_Y bn.graph X Y Z hy.1 hy.2,
      y, hy.1, hy.2, ?_⟩
    exact DirectedGraph.reachable_refl
      (DSeparation.moralAncestralWithoutConditioning bn.graph X Y Z) y
  have hCore :
      CondIndepVertices bn cpt.jointMeasure (X \ Z) (Y \ Z) Z :=
    condIndepVertices_of_le_right (bn := bn) (μ := cpt.jointMeasure) hsubY
      (condIndepVertices_of_le_left (bn := bn) (μ := cpt.jointMeasure) hsubX hBlocks)
  exact
    (condIndepVertices_iff_diff_conditioning
      (bn := bn) (μ := cpt.jointMeasure) (X := X) (Y := Y) (Z := Z)).2 hCore

instance discrete_hasLocalMarkovProperty
    (cpt : bn.DiscreteCPT) :
    HasLocalMarkovProperty bn cpt.jointMeasure where
  markov_condition := discrete_localMarkovCondition bn cpt

/-- Discrete CPT joint measures satisfy the full d-separation soundness
interface. -/
instance discrete_dSeparationSoundness
    [∀ v, MeasurableSingletonClass (bn.stateSpace v)]
    (cpt : bn.DiscreteCPT) :
    DSeparationSoundness bn cpt.jointMeasure where
  dsep_condIndep := by
    intro X Y Z hXYZ hdsep
    exact dsep_condIndep_of_disjoint_core
      (bn := bn) (μ := cpt.jointMeasure)
      (hcore := fun {_X _Y _Z} hdisj hdsepCore =>
        jointMeasure_dsepFull_disjoint_core_condIndepVertices
          (bn := bn) (cpt := cpt) (X := _X) (Y := _Y) (Z := _Z) hdisj hdsepCore)
      hXYZ hdsep

end Mettapedia.ProbabilityTheory.BayesianNetworks.DiscreteLocalMarkov
