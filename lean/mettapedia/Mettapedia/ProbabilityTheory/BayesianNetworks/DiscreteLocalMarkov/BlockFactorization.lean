import Mettapedia.ProbabilityTheory.BayesianNetworks.DiscreteLocalMarkov.Core

open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace Mettapedia.ProbabilityTheory.BayesianNetworks.DiscreteLocalMarkov

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (bn : BayesianNetwork V)
variable [∀ v : V, Fintype (bn.stateSpace v)]
variable [∀ v : V, Nonempty (bn.stateSpace v)]

open BayesianNetwork DiscreteCPT DirectedGraph

/-! ## HasLocalMarkovProperty instance for discrete CPTs

The factorization lemmas above prove the mathematical content: nodeProb for w ∈ ND(v)\Pa(v)\{v}
is independent of x_v. The bridge to Mathlib's `CondIndep` requires reducing to the
algebraic CI condition on parent fibers, then using the BN product factorization and
the telescoping sum to verify it.

Proof strategy (tower property + pull-out):

Given: t₁ is m_v-measurable, t₂ is m_ND-measurable.
Show: μ⟦t₁ ∩ t₂ | m_pa⟧ =ᵐ μ⟦t₁ | m_pa⟧ * μ⟦t₂ | m_pa⟧

Step 1: 1_{t₁∩t₂} = 1_{t₁} · 1_{t₂} (indicator multiplication)
Step 2: μ⟦f | m_pa⟧ =ᵐ μ⟦μ⟦f | m_pa ⊔ m_v⟧ | m_pa⟧ (tower property, m_pa ≤ m_pa ⊔ m_v)
Step 3: μ⟦1_{t₁}·1_{t₂} | m_pa ⊔ m_v⟧ =ᵐ 1_{t₁} · μ⟦1_{t₂} | m_pa ⊔ m_v⟧
         (pull-out: 1_{t₁} is (m_pa ⊔ m_v)-measurable since m_v ≤ m_pa ⊔ m_v)
Step 4: μ⟦1_{t₂} | m_pa ⊔ m_v⟧ =ᵐ μ⟦1_{t₂} | m_pa⟧
         ← BN FACTORIZATION: knowing x_v gives no info about ND' given Pa(v).
         On each parent-vertex fiber F_{c,a}, the marginal weight factors as
         φ_v(a,c) · φ_ND(x_{ND'},c), with the descendant sum = 1 (telescoping_sum).
         So P(t₂|Pa=c,v=a) = P(t₂|Pa=c) — the ratio is independent of a.
Step 5: μ⟦1_{t₁} · μ⟦1_{t₂}|m_pa⟧ | m_pa⟧ =ᵐ μ⟦1_{t₁}|m_pa⟧ · μ⟦1_{t₂}|m_pa⟧
         (pull-out: μ⟦1_{t₂}|m_pa⟧ is m_pa-measurable)

The only non-standard step is Step 4, which encapsulates the BN factorization.
The algebraic CI: μ(t₂∩F_c∩B) · μ(F_c) = μ(t₂∩F_c) · μ(F_c∩B) for m_v-meas B
follows from the factored weight after summing out descendants (telescoping_sum). -/

variable [∀ v : V, StandardBorelSpace (bn.stateSpace v)]

/-- Helper: condExp of an indicator is bounded by 1 in norm a.e. -/
lemma condExp_indicator_norm_le_one
    (μ : Measure bn.JointSpace) [IsFiniteMeasure μ]
    {m' : MeasurableSpace bn.JointSpace} (hm' : m' ≤ MeasurableSpace.pi)
    [SigmaFinite (μ.trim hm')]
    (s : Set bn.JointSpace) (hs : @MeasurableSet _ MeasurableSpace.pi s) :
    ∀ᵐ ω ∂μ, ‖(μ[s.indicator (fun _ => (1 : ℝ)) | m']) ω‖ ≤ 1 := by
  have hint : Integrable (s.indicator fun _ => (1 : ℝ)) μ :=
    (integrable_const (1 : ℝ)).indicator hs
  have h_ind_le : (s.indicator fun _ => (1 : ℝ)) ≤ᵐ[μ] fun _ => (1 : ℝ) :=
    Filter.Eventually.of_forall fun ω => by
      simp only [Set.indicator_apply]; split_ifs <;> norm_num
  have h_mono : (μ[s.indicator (fun _ => (1 : ℝ)) | m']) ≤ᵐ[μ] (μ[fun _ => (1 : ℝ) | m']) :=
    condExp_mono hint (integrable_const (1 : ℝ)) h_ind_le
  have h_const : (μ[fun _ => (1 : ℝ) | m']) = fun _ => (1 : ℝ) :=
    condExp_of_stronglyMeasurable hm' stronglyMeasurable_const (integrable_const _)
  have h_le : (μ[s.indicator (fun _ => (1 : ℝ)) | m']) ≤ᵐ[μ] fun _ => (1 : ℝ) := by
    have := h_const ▸ h_mono; exact this
  have h_ge : (0 : bn.JointSpace → ℝ) ≤ᵐ[μ] (μ[s.indicator (fun _ => (1 : ℝ)) | m']) :=
    condExp_nonneg (Filter.Eventually.of_forall fun ω => by
      simp only [Set.indicator_apply]; split_ifs <;> norm_num)
  filter_upwards [h_le, h_ge] with ω hle hge
  rw [Real.norm_eq_abs, abs_le]
  simp only [Pi.zero_apply] at hge
  exact ⟨by linarith, hle⟩

/-! ### Parent-fiber decomposition helpers

These lemmas let us treat any `m_pa`-measurable set as the preimage of a set of
parent assignments via the restriction map. They will be used to decompose
integrals over parent fibers in the BN CI proof below.
-/

lemma measurableSet_vertices_preimage
    (S : Set V) {s : Set bn.JointSpace}
    (hs : MeasurableSet[bn.measurableSpaceOfVertices S] s) :
    ∃ T : Set (∀ p : S, bn.stateSpace p),
      MeasurableSet T ∧ s = (restrictToSet (bn := bn) S) ⁻¹' T := by
  have hs' :
      MeasurableSet[
        MeasurableSpace.comap (restrictToSet (bn := bn) S) (by infer_instance)] s := by
    rw [measurableSpaceOfVertices_eq_comap_restrict (bn := bn) S] at hs
    exact hs
  rcases (MeasurableSpace.measurableSet_comap).1 hs' with ⟨T, hT, hpre⟩
  exact ⟨T, hT, hpre.symm⟩

lemma measurableSet_singleton_preimage
    (v : V) {s : Set bn.JointSpace}
    (hs : MeasurableSet[bn.measurableSpaceOfVertices ({v} : Set V)] s) :
    ∃ T : Set (bn.stateSpace v), MeasurableSet T ∧ s = (fun ω : bn.JointSpace => ω v) ⁻¹' T := by
  have hs' :
      MeasurableSet[
        MeasurableSpace.comap (fun ω : bn.JointSpace => ω v) (by infer_instance)] s := by
    rw [measurableSpaceOfVertices_singleton (bn := bn) v] at hs
    exact hs
  rcases (MeasurableSpace.measurableSet_comap).1 hs' with ⟨T, hT, hpre⟩
  exact ⟨T, hT, hpre.symm⟩

/-! ### Constraint atoms for arbitrary vertex blocks

The next global BN soundness target will need an atom-level statement for
constraint events on separated endpoint blocks. We keep that target as a source
comment rather than an unproved declaration:

`μ(event(cx ++ cy ++ cz)) * μ(event(cz)) = μ(event(cx ++ cz)) * μ(event(cy ++ cz))`

for constraint lists supported on disjoint `X`, `Y`, and conditioning block `Z`.
The lemmas below expose `eventOfConstraints` as the atomic generators of
`measurableSpaceOfVertices S`.
-/

/-- Enumerate a restriction assignment as a concrete constraint list. -/
noncomputable def constraintsOfRestrict (S : Set V)
    (xS : ∀ p : S, bn.stateSpace p.1) : List (Σ v : V, bn.stateSpace v) :=
  ((Finset.univ : Finset S).toList).map (fun p => (⟨p.1, xS p⟩ : Σ v : V, bn.stateSpace v))

/-- The constraint list built from a restriction assignment cuts out exactly the
singleton fiber of that assignment. -/
lemma eventOfConstraints_constraintsOfRestrict
    (S : Set V) (xS : ∀ p : S, bn.stateSpace p.1) :
    eventOfConstraints (bn := bn) (constraintsOfRestrict (bn := bn) S xS) =
      (restrictToSet (bn := bn) S) ⁻¹' ({xS} : Set (∀ p : S, bn.stateSpace p.1)) := by
  classical
  ext ω
  constructor
  · intro hω
    ext p
    have hpMem : p ∈ ((Finset.univ : Finset S).toList) := by
      simp
    have hcMem :
        (⟨p.1, xS p⟩ : Σ v : V, bn.stateSpace v) ∈
          constraintsOfRestrict (bn := bn) S xS := by
      simpa [constraintsOfRestrict] using
        (List.mem_map.2 ⟨p, hpMem, rfl⟩)
    exact hω _ hcMem
  · intro hω c hc
    have hc' : ∃ p : S, (⟨p.1, xS p⟩ : Σ v : V, bn.stateSpace v) = c := by
      simpa [constraintsOfRestrict] using hc
    rcases hc' with ⟨p, hpEq⟩
    subst hpEq
    exact congrFun hω p

/-- Distinct block assignments yield disjoint constraint atoms. -/
lemma eventOfConstraints_constraintsOfRestrict_disjoint
    (S : Set V) {xS yS : ∀ p : S, bn.stateSpace p.1}
    (hxy : xS ≠ yS) :
    Disjoint
      (eventOfConstraints (bn := bn) (constraintsOfRestrict (bn := bn) S xS))
      (eventOfConstraints (bn := bn) (constraintsOfRestrict (bn := bn) S yS)) := by
  refine Set.disjoint_left.mpr ?_
  intro ω hx hy
  have hx' : restrictToSet (bn := bn) S ω = xS := by
    simpa [eventOfConstraints_constraintsOfRestrict (bn := bn) S xS] using hx
  have hy' : restrictToSet (bn := bn) S ω = yS := by
    simpa [eventOfConstraints_constraintsOfRestrict (bn := bn) S yS] using hy
  exact hxy (hx'.symm.trans hy')

/-- A constraint atom over `S` is measurable in the vertex σ-algebra `σ(S)`. -/
lemma measurable_eventOfConstraints_constraintsOfRestrict_vertices
    [∀ v, MeasurableSingletonClass (bn.stateSpace v)]
    (S : Set V) (xS : ∀ p : S, bn.stateSpace p.1) :
    MeasurableSet[bn.measurableSpaceOfVertices S]
      (eventOfConstraints (bn := bn) (constraintsOfRestrict (bn := bn) S xS)) := by
  have hcomap :
      MeasurableSet[
        MeasurableSpace.comap (restrictToSet (bn := bn) S) (by infer_instance)]
        (eventOfConstraints (bn := bn) (constraintsOfRestrict (bn := bn) S xS)) := by
    rw [eventOfConstraints_constraintsOfRestrict (bn := bn) S xS]
    exact (MeasurableSpace.measurableSet_comap).2 ⟨{xS}, by simp, rfl⟩
  rw [measurableSpaceOfVertices_eq_comap_restrict (bn := bn) S]
  exact hcomap

/-- Conditional expectations with respect to `σ(S)` are constant on each
constraint atom fixing the coordinates in `S`. -/
lemma condExp_ae_eq_const_on_constraintsOfRestrict
    [∀ v, MeasurableSingletonClass (bn.stateSpace v)]
    (μ : Measure bn.JointSpace) [IsFiniteMeasure μ]
    (S : Set V) (xS : ∀ p : S, bn.stateSpace p.1)
    (s : Set bn.JointSpace) {ω0 : bn.JointSpace}
    (hω0 : restrictToSet (bn := bn) S ω0 = xS) :
    (fun ω : bn.JointSpace =>
      MeasureTheory.condExp
        (bn.measurableSpaceOfVertices S) μ
        (s.indicator fun _ : bn.JointSpace => (1 : ℝ))
        ω)
      =ᵐ[μ.restrict
        (eventOfConstraints (bn := bn) (constraintsOfRestrict (bn := bn) S xS))]
    (fun _ : bn.JointSpace =>
      MeasureTheory.condExp
        (bn.measurableSpaceOfVertices S) μ
        (s.indicator fun _ : bn.JointSpace => (1 : ℝ))
        ω0) := by
  refine (MeasureTheory.ae_restrict_iff' ?_).2 ?_
  · exact measurable_eventOfConstraints (bn := bn)
      (constraintsOfRestrict (bn := bn) S xS)
  refine Filter.Eventually.of_forall ?_
  intro ω hω
  apply measurable_const_on_fiber_set (bn := bn) (S := S)
  · exact (stronglyMeasurable_condExp (μ := μ)
      (m := bn.measurableSpaceOfVertices S)
      (f := (s.indicator fun _ => (1 : ℝ)))).measurable
  · have hωS : restrictToSet (bn := bn) S ω = xS := by
      simpa [eventOfConstraints_constraintsOfRestrict (bn := bn) S xS] using hω
    exact hωS.trans hω0.symm

/-- Any event measurable in `σ(S)` is a finite union of constraint atoms. -/
lemma vertices_preimage_eq_iUnion_eventOfConstraints
    (S : Set V) (T : Set (∀ p : S, bn.stateSpace p.1)) :
    (restrictToSet (bn := bn) S) ⁻¹' T =
      ⋃ xS : (∀ p : S, bn.stateSpace p.1),
        (if xS ∈ T then
          eventOfConstraints (bn := bn) (constraintsOfRestrict (bn := bn) S xS)
        else (∅ : Set bn.JointSpace)) := by
  classical
  ext ω
  constructor
  · intro hω
    refine Set.mem_iUnion.2 ?_
    refine ⟨restrictToSet (bn := bn) S ω, ?_⟩
    by_cases hT : restrictToSet (bn := bn) S ω ∈ T
    · simpa [hT, eventOfConstraints_constraintsOfRestrict (bn := bn) S
        (restrictToSet (bn := bn) S ω)] using hω
    · exact (hT hω).elim
  · intro hω
    rcases Set.mem_iUnion.1 hω with ⟨xS, hxS⟩
    by_cases hT : xS ∈ T
    · have hx :
          ω ∈ eventOfConstraints (bn := bn) (constraintsOfRestrict (bn := bn) S xS) := by
        simpa [hT] using hxS
      have hEq : restrictToSet (bn := bn) S ω = xS := by
        simpa [eventOfConstraints_constraintsOfRestrict (bn := bn) S xS] using hx
      simpa [hEq] using hT
    · have hempty : False := by
        have : ω ∈ (∅ : Set bn.JointSpace) := by
          simpa [hT] using hxS
        simpa using this
      exact hempty.elim

/-- Direct measure decomposition over block-constraint atoms. -/
lemma measure_vertices_preimage_eq_sum
    (μ : Measure bn.JointSpace)
    (S : Set V) [∀ v, MeasurableSingletonClass (bn.stateSpace v)]
    (T : Set (∀ p : S, bn.stateSpace p.1)) :
    μ ((restrictToSet (bn := bn) S) ⁻¹' T) =
      ∑ xS : (∀ p : S, bn.stateSpace p.1),
        if xS ∈ T then
          μ (eventOfConstraints (bn := bn) (constraintsOfRestrict (bn := bn) S xS))
        else 0 := by
  classical
  rw [vertices_preimage_eq_iUnion_eventOfConstraints (bn := bn) S T]
  have hMeas :
      ∀ xS : (∀ p : S, bn.stateSpace p.1),
        MeasurableSet
          (if xS ∈ T then
            eventOfConstraints (bn := bn) (constraintsOfRestrict (bn := bn) S xS)
          else (∅ : Set bn.JointSpace)) := by
    intro xS
    by_cases hxS : xS ∈ T
    · simpa [hxS] using
        measurable_eventOfConstraints (bn := bn)
          (constraintsOfRestrict (bn := bn) S xS)
    · simp [hxS]
  have hDisj :
      Pairwise (fun xS yS : (∀ p : S, bn.stateSpace p.1) =>
        Disjoint
          (if xS ∈ T then
            eventOfConstraints (bn := bn) (constraintsOfRestrict (bn := bn) S xS)
          else (∅ : Set bn.JointSpace))
          (if yS ∈ T then
            eventOfConstraints (bn := bn) (constraintsOfRestrict (bn := bn) S yS)
          else (∅ : Set bn.JointSpace))) := by
    intro xS yS hne
    by_cases hxS : xS ∈ T
    · by_cases hyS : yS ∈ T
      · simpa [hxS, hyS] using
          eventOfConstraints_constraintsOfRestrict_disjoint
            (bn := bn) S (xS := xS) (yS := yS) hne
      · simp [hyS]
    · simp [hxS]
  have hUnion :
      μ (⋃ xS : (∀ p : S, bn.stateSpace p.1),
          (if xS ∈ T then
            eventOfConstraints (bn := bn) (constraintsOfRestrict (bn := bn) S xS)
          else (∅ : Set bn.JointSpace)))
        =
      ∑' xS : (∀ p : S, bn.stateSpace p.1),
        μ (if xS ∈ T then
          eventOfConstraints (bn := bn) (constraintsOfRestrict (bn := bn) S xS)
        else (∅ : Set bn.JointSpace)) :=
    MeasureTheory.measure_iUnion hDisj hMeas
  calc
    μ (⋃ xS : (∀ p : S, bn.stateSpace p.1),
        (if xS ∈ T then
          eventOfConstraints (bn := bn) (constraintsOfRestrict (bn := bn) S xS)
        else (∅ : Set bn.JointSpace))) =
      ∑' xS : (∀ p : S, bn.stateSpace p.1),
        μ (if xS ∈ T then
          eventOfConstraints (bn := bn) (constraintsOfRestrict (bn := bn) S xS)
        else (∅ : Set bn.JointSpace)) := hUnion
    _ =
      ∑ xS : (∀ p : S, bn.stateSpace p.1),
        μ (if xS ∈ T then
          eventOfConstraints (bn := bn) (constraintsOfRestrict (bn := bn) S xS)
        else (∅ : Set bn.JointSpace)) := by
          rw [tsum_fintype]
    _ =
      ∑ xS : (∀ p : S, bn.stateSpace p.1),
        if xS ∈ T then
          μ (eventOfConstraints (bn := bn) (constraintsOfRestrict (bn := bn) S xS))
        else 0 := by
          refine Finset.sum_congr rfl ?_
          intro xS _
          by_cases hxS : xS ∈ T <;> simp [hxS]

/-- Set-integral decomposition over block-constraint atoms. -/
lemma setIntegral_vertices_preimage
    (μ : Measure bn.JointSpace) [IsFiniteMeasure μ]
    (S : Set V) [∀ v, MeasurableSingletonClass (bn.stateSpace v)]
    (T : Set (∀ p : S, bn.stateSpace p.1)) (f : bn.JointSpace → ℝ)
    (hf : Integrable f μ) :
    ∫ x in (restrictToSet (bn := bn) S) ⁻¹' T, f x ∂μ =
      ∑ xS : (∀ p : S, bn.stateSpace p.1),
        if xS ∈ T then
          ∫ x in eventOfConstraints (bn := bn) (constraintsOfRestrict (bn := bn) S xS), f x ∂μ
        else 0 := by
  classical
  rw [vertices_preimage_eq_iUnion_eventOfConstraints (bn := bn) S T]
  have hMeas :
      ∀ xS : (∀ p : S, bn.stateSpace p.1),
        @MeasurableSet _ MeasurableSpace.pi
          (if xS ∈ T then
            eventOfConstraints (bn := bn) (constraintsOfRestrict (bn := bn) S xS)
          else (∅ : Set bn.JointSpace)) := by
    intro xS
    by_cases hxS : xS ∈ T
    · simpa [hxS] using
        measurable_eventOfConstraints (bn := bn)
          (constraintsOfRestrict (bn := bn) S xS)
    · simp [hxS]
  have hDisj :
      Pairwise (fun xS yS : (∀ p : S, bn.stateSpace p.1) =>
        Disjoint
          (if xS ∈ T then
            eventOfConstraints (bn := bn) (constraintsOfRestrict (bn := bn) S xS)
          else (∅ : Set bn.JointSpace))
          (if yS ∈ T then
            eventOfConstraints (bn := bn) (constraintsOfRestrict (bn := bn) S yS)
          else (∅ : Set bn.JointSpace))) := by
    intro xS yS hne
    by_cases hxS : xS ∈ T
    · by_cases hyS : yS ∈ T
      · simpa [hxS, hyS] using
          eventOfConstraints_constraintsOfRestrict_disjoint
            (bn := bn) S (xS := xS) (yS := yS) hne
      · simp [hyS]
    · simp [hxS]
  have hInt :
      ∀ xS : (∀ p : S, bn.stateSpace p.1),
        IntegrableOn (f := f)
          (if xS ∈ T then
            eventOfConstraints (bn := bn) (constraintsOfRestrict (bn := bn) S xS)
          else (∅ : Set bn.JointSpace)) μ := by
    intro xS
    exact hf.integrableOn
  have hUnion :
      ∫ x in ⋃ xS : (∀ p : S, bn.stateSpace p.1),
          (if xS ∈ T then
            eventOfConstraints (bn := bn) (constraintsOfRestrict (bn := bn) S xS)
          else (∅ : Set bn.JointSpace)), f x ∂μ
        =
      ∑ xS : (∀ p : S, bn.stateSpace p.1),
        ∫ x in (if xS ∈ T then
          eventOfConstraints (bn := bn) (constraintsOfRestrict (bn := bn) S xS)
        else (∅ : Set bn.JointSpace)), f x ∂μ :=
    MeasureTheory.integral_iUnion_fintype
      (μ := μ) (f := f)
      (s := fun xS : (∀ p : S, bn.stateSpace p.1) =>
        if xS ∈ T then
          eventOfConstraints (bn := bn) (constraintsOfRestrict (bn := bn) S xS)
        else (∅ : Set bn.JointSpace))
      hMeas hDisj hInt
  have hSum :
      (∑ xS : (∀ p : S, bn.stateSpace p.1),
          ∫ x in (if xS ∈ T then
            eventOfConstraints (bn := bn) (constraintsOfRestrict (bn := bn) S xS)
          else (∅ : Set bn.JointSpace)), f x ∂μ)
        =
      ∑ xS : (∀ p : S, bn.stateSpace p.1),
        if xS ∈ T then
          ∫ x in eventOfConstraints (bn := bn) (constraintsOfRestrict (bn := bn) S xS), f x ∂μ
        else 0 := by
    refine Finset.sum_congr rfl ?_
    intro xS _
    by_cases hxS : xS ∈ T <;> simp [hxS]
  exact hUnion.trans hSum

/-! ### Relevant / irrelevant reindexing for block atoms -/

private noncomputable def irrSetToFin
    (X Y Z : Set V)
    (xI : ∀ d : {d // d ∉ DSeparation.relevantVertices bn.graph X Y Z}, bn.stateSpace d) :
    ∀ d : ↥(irrelevantHeadFinset bn X Y Z), bn.stateSpace d :=
  fun d => xI ⟨d.1, (Finset.mem_filter.mp d.2).2⟩

private noncomputable def irrFinToSet
    (X Y Z : Set V)
    (xI : ∀ d : ↥(irrelevantHeadFinset bn X Y Z), bn.stateSpace d) :
    ∀ d : {d // d ∉ DSeparation.relevantVertices bn.graph X Y Z}, bn.stateSpace d :=
  fun d => xI ⟨d.1, Finset.mem_filter.mpr ⟨Finset.mem_univ d.1, d.2⟩⟩

private noncomputable def irrAssignEquiv
    (X Y Z : Set V) :
    (∀ d : {d // d ∉ DSeparation.relevantVertices bn.graph X Y Z}, bn.stateSpace d) ≃
      (∀ d : ↥(irrelevantHeadFinset bn X Y Z), bn.stateSpace d) where
  toFun := irrSetToFin (bn := bn) X Y Z
  invFun := irrFinToSet (bn := bn) X Y Z
  left_inv := by
    intro xI
    funext d
    simp [irrSetToFin, irrFinToSet]
  right_inv := by
    intro xI
    funext d
    simp [irrSetToFin, irrFinToSet]

private noncomputable def baseFromRelevant
    (X Y Z : Set V)
    (xR : ∀ r : {r // r ∈ DSeparation.relevantVertices bn.graph X Y Z}, bn.stateSpace r) :
    bn.JointSpace :=
  fun u =>
    if hu : u ∈ DSeparation.relevantVertices bn.graph X Y Z then
      xR ⟨u, hu⟩
    else
      Classical.choice (inferInstance : Nonempty (bn.stateSpace u))

private noncomputable def mergeRelevantIrrelevant
    (X Y Z : Set V)
    (xR : ∀ r : {r // r ∈ DSeparation.relevantVertices bn.graph X Y Z}, bn.stateSpace r)
    (xI : ∀ d : {d // d ∉ DSeparation.relevantVertices bn.graph X Y Z}, bn.stateSpace d) :
    bn.JointSpace :=
  patchConfig bn
    (baseFromRelevant (bn := bn) X Y Z xR)
    (irrelevantHeadFinset bn X Y Z)
    (irrSetToFin (bn := bn) X Y Z xI)

private lemma mergeRelevantIrrelevant_restrict_relevant
    (X Y Z : Set V)
    (xR : ∀ r : {r // r ∈ DSeparation.relevantVertices bn.graph X Y Z}, bn.stateSpace r)
    (xI : ∀ d : {d // d ∉ DSeparation.relevantVertices bn.graph X Y Z}, bn.stateSpace d) :
    restrictToSet (bn := bn) (DSeparation.relevantVertices bn.graph X Y Z)
      (mergeRelevantIrrelevant (bn := bn) X Y Z xR xI) = xR := by
  funext r
  have hr_not_mem :
      r.1 ∉ irrelevantHeadFinset bn X Y Z := by
    intro hrI
    exact (Finset.mem_filter.mp hrI).2 r.2
  calc
    restrictToSet (bn := bn) (DSeparation.relevantVertices bn.graph X Y Z)
        (mergeRelevantIrrelevant (bn := bn) X Y Z xR xI) r
        =
      mergeRelevantIrrelevant (bn := bn) X Y Z xR xI r.1 := rfl
    _ =
      baseFromRelevant (bn := bn) X Y Z xR r.1 := by
        simpa [mergeRelevantIrrelevant] using
          (patchConfig_outside (bn := bn)
            (x := baseFromRelevant (bn := bn) X Y Z xR)
            (D := irrelevantHeadFinset bn X Y Z)
            (xD := irrSetToFin (bn := bn) X Y Z xI)
            (v := r.1) hr_not_mem)
    _ = xR r := by
      simp [baseFromRelevant, r.2]

private lemma piEquiv_relevant_symm_eq_merge
    (X Y Z : Set V)
    (xR : ∀ r : {r // r ∈ DSeparation.relevantVertices bn.graph X Y Z}, bn.stateSpace r)
    (xI : ∀ d : {d // d ∉ DSeparation.relevantVertices bn.graph X Y Z}, bn.stateSpace d) :
    (Equiv.piEquivPiSubtypeProd
      (p := fun d : V => d ∈ DSeparation.relevantVertices bn.graph X Y Z)
      (β := fun d : V => bn.stateSpace d)).symm (xR, xI)
      =
    mergeRelevantIrrelevant (bn := bn) X Y Z xR xI := by
  funext u
  by_cases hu : u ∈ DSeparation.relevantVertices bn.graph X Y Z
  · have hu_not_mem :
        u ∉ irrelevantHeadFinset bn X Y Z := by
      intro huI
      exact (Finset.mem_filter.mp huI).2 hu
    calc
      (Equiv.piEquivPiSubtypeProd
          (p := fun d : V => d ∈ DSeparation.relevantVertices bn.graph X Y Z)
          (β := fun d : V => bn.stateSpace d)).symm (xR, xI) u
          = xR ⟨u, hu⟩ := by
              simp [Equiv.piEquivPiSubtypeProd, hu]
      _ =
        mergeRelevantIrrelevant (bn := bn) X Y Z xR xI u := by
          simp [mergeRelevantIrrelevant, baseFromRelevant,
            patchConfig_outside (bn := bn)
              (x := baseFromRelevant (bn := bn) X Y Z xR)
              (D := irrelevantHeadFinset bn X Y Z)
              (xD := irrSetToFin (bn := bn) X Y Z xI)
              (v := u) hu_not_mem, hu]
  · have hu_mem :
        u ∈ irrelevantHeadFinset bn X Y Z := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, hu⟩
    calc
      (Equiv.piEquivPiSubtypeProd
          (p := fun d : V => d ∈ DSeparation.relevantVertices bn.graph X Y Z)
          (β := fun d : V => bn.stateSpace d)).symm (xR, xI) u
          = xI ⟨u, hu⟩ := by
              simp [Equiv.piEquivPiSubtypeProd, hu]
      _ =
        mergeRelevantIrrelevant (bn := bn) X Y Z xR xI u := by
          simp [mergeRelevantIrrelevant,
            patchConfig_inside (bn := bn)
              (x := baseFromRelevant (bn := bn) X Y Z xR)
              (D := irrelevantHeadFinset bn X Y Z)
              (xD := irrSetToFin (bn := bn) X Y Z xI)
              (v := u) hu_mem, irrSetToFin]

private lemma sum_reindex_relevant_irrelevant
    (X Y Z : Set V) (f : bn.JointSpace → ENNReal) :
    (∑ x : bn.JointSpace, f x)
      =
    ∑ xR : (∀ r : {r // r ∈ DSeparation.relevantVertices bn.graph X Y Z}, bn.stateSpace r),
      ∑ xI : (∀ d : {d // d ∉ DSeparation.relevantVertices bn.graph X Y Z}, bn.stateSpace d),
        f (mergeRelevantIrrelevant (bn := bn) X Y Z xR xI) := by
  classical
  let e :
      bn.JointSpace ≃
        (∀ r : {r // r ∈ DSeparation.relevantVertices bn.graph X Y Z}, bn.stateSpace r) ×
          (∀ d : {d // d ∉ DSeparation.relevantVertices bn.graph X Y Z}, bn.stateSpace d) :=
    Equiv.piEquivPiSubtypeProd
      (p := fun d : V => d ∈ DSeparation.relevantVertices bn.graph X Y Z)
      (β := fun d : V => bn.stateSpace d)
  calc
    (∑ x : bn.JointSpace, f x)
        =
      ∑ p :
          (∀ r : {r // r ∈ DSeparation.relevantVertices bn.graph X Y Z}, bn.stateSpace r) ×
            (∀ d : {d // d ∉ DSeparation.relevantVertices bn.graph X Y Z}, bn.stateSpace d),
        f (e.symm p) := by
          refine Fintype.sum_equiv e f (fun p => f (e.symm p)) ?_
          intro x
          simpa [e] using congrArg f ((Equiv.symm_apply_apply e x).symm)
    _ =
      ∑ xR : (∀ r : {r // r ∈ DSeparation.relevantVertices bn.graph X Y Z}, bn.stateSpace r),
        ∑ xI : (∀ d : {d // d ∉ DSeparation.relevantVertices bn.graph X Y Z}, bn.stateSpace d),
          f (e.symm (xR, xI)) := by
            simpa using
              (Fintype.sum_prod_type
                (f := fun p :
                    (∀ r : {r // r ∈ DSeparation.relevantVertices bn.graph X Y Z},
                      bn.stateSpace r) ×
                      (∀ d : {d // d ∉ DSeparation.relevantVertices bn.graph X Y Z},
                        bn.stateSpace d) =>
                  f (e.symm p)))
    _ =
      ∑ xR : (∀ r : {r // r ∈ DSeparation.relevantVertices bn.graph X Y Z}, bn.stateSpace r),
        ∑ xI : (∀ d : {d // d ∉ DSeparation.relevantVertices bn.graph X Y Z}, bn.stateSpace d),
          f (mergeRelevantIrrelevant (bn := bn) X Y Z xR xI) := by
            refine Finset.sum_congr rfl ?_
            intro xR _
            refine Finset.sum_congr rfl ?_
            intro xI _
            simpa [e] using congrArg f
              (piEquiv_relevant_symm_eq_merge (bn := bn) X Y Z xR xI)

/-- The joint-weight sum over a single atom on the full relevant vertex set
collapses to the product of the relevant block factors. -/
theorem jointWeight_sum_indicator_relevantAtom_eq_relevantBlockProducts
    (cpt : bn.DiscreteCPT) (X Y Z : Set V)
    (hirr : ∀ v : V, ¬bn.graph.edges v v)
    (hXY : Disjoint X Y)
    (hSep : DSeparation.SeparatedInMoralAncestral bn.graph X Y Z)
    (xR : ∀ r : {r // r ∈ DSeparation.relevantVertices bn.graph X Y Z}, bn.stateSpace r) :
    (∑ x : bn.JointSpace,
        if restrictToSet (bn := bn) (DSeparation.relevantVertices bn.graph X Y Z) x = xR then
          cpt.jointWeight x
        else 0)
      =
      (∏ v ∈ relevantHeadXFinset bn X Y Z,
          cpt.nodeProb (baseFromRelevant (bn := bn) X Y Z xR) v) *
        ((∏ v ∈ relevantHeadYFinset bn X Y Z,
            cpt.nodeProb (baseFromRelevant (bn := bn) X Y Z xR) v) *
          ((∏ v ∈ relevantHeadResidualFinset bn X Y Z,
              cpt.nodeProb (baseFromRelevant (bn := bn) X Y Z xR) v) *
            ∏ v ∈ relevantHeadConditioningFinset bn X Y Z,
              cpt.nodeProb (baseFromRelevant (bn := bn) X Y Z xR) v)) := by
  classical
  rw [sum_reindex_relevant_irrelevant (bn := bn) X Y Z
    (f := fun x : bn.JointSpace =>
      if restrictToSet (bn := bn) (DSeparation.relevantVertices bn.graph X Y Z) x = xR then
        cpt.jointWeight x
      else 0)]
  have hAtom :
      ∀ xR' xI,
        (if
            restrictToSet (bn := bn) (DSeparation.relevantVertices bn.graph X Y Z)
              (mergeRelevantIrrelevant (bn := bn) X Y Z xR' xI) = xR
          then cpt.jointWeight (mergeRelevantIrrelevant (bn := bn) X Y Z xR' xI)
          else 0)
          =
        if xR' = xR then
          cpt.jointWeight (mergeRelevantIrrelevant (bn := bn) X Y Z xR xI)
        else 0 := by
    intro xR' xI
    have hRestr :
        restrictToSet (bn := bn) (DSeparation.relevantVertices bn.graph X Y Z)
          (mergeRelevantIrrelevant (bn := bn) X Y Z xR' xI) = xR' :=
      mergeRelevantIrrelevant_restrict_relevant (bn := bn) X Y Z xR' xI
    by_cases hx : xR' = xR
    · subst hx
      simp [hRestr]
    · simp [hRestr, hx]
  calc
    (∑ xR' : (∀ r : {r // r ∈ DSeparation.relevantVertices bn.graph X Y Z}, bn.stateSpace r),
        ∑ xI : (∀ d : {d // d ∉ DSeparation.relevantVertices bn.graph X Y Z}, bn.stateSpace d),
          if
              restrictToSet (bn := bn) (DSeparation.relevantVertices bn.graph X Y Z)
                (mergeRelevantIrrelevant (bn := bn) X Y Z xR' xI) = xR
            then cpt.jointWeight (mergeRelevantIrrelevant (bn := bn) X Y Z xR' xI)
            else 0)
        =
      ∑ xR' : (∀ r : {r // r ∈ DSeparation.relevantVertices bn.graph X Y Z}, bn.stateSpace r),
        ∑ xI : (∀ d : {d // d ∉ DSeparation.relevantVertices bn.graph X Y Z}, bn.stateSpace d),
          if xR' = xR then
            cpt.jointWeight (mergeRelevantIrrelevant (bn := bn) X Y Z xR xI)
          else 0 := by
            refine Finset.sum_congr rfl ?_
            intro xR' _
            refine Finset.sum_congr rfl ?_
            intro xI _
            exact hAtom xR' xI
    _ =
      ∑ xI : (∀ d : {d // d ∉ DSeparation.relevantVertices bn.graph X Y Z}, bn.stateSpace d),
        cpt.jointWeight (mergeRelevantIrrelevant (bn := bn) X Y Z xR xI) := by
          simp
    _ =
      ∑ xI : (∀ d : ↥(irrelevantHeadFinset bn X Y Z), bn.stateSpace d),
        cpt.jointWeight
          (patchConfig bn
            (baseFromRelevant (bn := bn) X Y Z xR)
            (irrelevantHeadFinset bn X Y Z) xI) := by
              refine Fintype.sum_equiv (irrAssignEquiv (bn := bn) X Y Z)
                (fun xI =>
                  cpt.jointWeight (mergeRelevantIrrelevant (bn := bn) X Y Z xR xI))
                (fun xI =>
                  cpt.jointWeight
                    (patchConfig bn
                      (baseFromRelevant (bn := bn) X Y Z xR)
                      (irrelevantHeadFinset bn X Y Z) xI)) ?_
              intro xI
              rfl
    _ =
      (∏ v ∈ relevantHeadXFinset bn X Y Z,
          cpt.nodeProb (baseFromRelevant (bn := bn) X Y Z xR) v) *
        ((∏ v ∈ relevantHeadYFinset bn X Y Z,
            cpt.nodeProb (baseFromRelevant (bn := bn) X Y Z xR) v) *
          ((∏ v ∈ relevantHeadResidualFinset bn X Y Z,
              cpt.nodeProb (baseFromRelevant (bn := bn) X Y Z xR) v) *
            ∏ v ∈ relevantHeadConditioningFinset bn X Y Z,
              cpt.nodeProb (baseFromRelevant (bn := bn) X Y Z xR) v)) := by
                simpa [mergeRelevantIrrelevant] using
                  sum_irrelevant_jointWeight_eq_relevantBlockProducts
                    (bn := bn) (cpt := cpt) X Y Z hirr hXY hSep
                    (baseFromRelevant (bn := bn) X Y Z xR)

/-- The joint measure of a single atom on the full relevant vertex set collapses
to the product of the relevant block factors. -/
theorem jointMeasure_relevantAtom_eq_relevantBlockProducts
    [∀ v, MeasurableSingletonClass (bn.stateSpace v)]
    (cpt : bn.DiscreteCPT) (X Y Z : Set V)
    (hirr : ∀ v : V, ¬bn.graph.edges v v)
    (hXY : Disjoint X Y)
    (hSep : DSeparation.SeparatedInMoralAncestral bn.graph X Y Z)
    (xR : ∀ r : {r // r ∈ DSeparation.relevantVertices bn.graph X Y Z}, bn.stateSpace r) :
    cpt.jointMeasure
      (eventOfConstraints (bn := bn)
        (constraintsOfRestrict (bn := bn)
          (DSeparation.relevantVertices bn.graph X Y Z) xR))
      =
      (∏ v ∈ relevantHeadXFinset bn X Y Z,
          cpt.nodeProb (baseFromRelevant (bn := bn) X Y Z xR) v) *
        ((∏ v ∈ relevantHeadYFinset bn X Y Z,
            cpt.nodeProb (baseFromRelevant (bn := bn) X Y Z xR) v) *
          ((∏ v ∈ relevantHeadResidualFinset bn X Y Z,
              cpt.nodeProb (baseFromRelevant (bn := bn) X Y Z xR) v) *
            ∏ v ∈ relevantHeadConditioningFinset bn X Y Z,
              cpt.nodeProb (baseFromRelevant (bn := bn) X Y Z xR) v)) := by
  have hμ :=
    DiscreteCPT.jointMeasure_eventOfConstraints (bn := bn) (cpt := cpt)
      (constraintsOfRestrict (bn := bn)
        (DSeparation.relevantVertices bn.graph X Y Z) xR)
  have hsum :
      (∑ x : bn.JointSpace,
          if x ∈ (restrictToSet (bn := bn)
            (DSeparation.relevantVertices bn.graph X Y Z)) ⁻¹' ({xR} : Set
              (∀ r : {r // r ∈ DSeparation.relevantVertices bn.graph X Y Z},
                bn.stateSpace r.1))
          then cpt.jointWeight x else 0)
        =
      (∏ v ∈ relevantHeadXFinset bn X Y Z,
          cpt.nodeProb (baseFromRelevant (bn := bn) X Y Z xR) v) *
        ((∏ v ∈ relevantHeadYFinset bn X Y Z,
            cpt.nodeProb (baseFromRelevant (bn := bn) X Y Z xR) v) *
          ((∏ v ∈ relevantHeadResidualFinset bn X Y Z,
              cpt.nodeProb (baseFromRelevant (bn := bn) X Y Z xR) v) *
            ∏ v ∈ relevantHeadConditioningFinset bn X Y Z,
              cpt.nodeProb (baseFromRelevant (bn := bn) X Y Z xR) v)) := by
    simpa [Set.mem_preimage, Set.mem_singleton_iff] using
      (jointWeight_sum_indicator_relevantAtom_eq_relevantBlockProducts
        (bn := bn) (cpt := cpt) X Y Z hirr hXY hSep xR)
  calc
    cpt.jointMeasure
        (eventOfConstraints (bn := bn)
          (constraintsOfRestrict (bn := bn)
            (DSeparation.relevantVertices bn.graph X Y Z) xR))
        =
      cpt.jointMeasure
        ((restrictToSet (bn := bn) (DSeparation.relevantVertices bn.graph X Y Z)) ⁻¹'
          ({xR} : Set
            (∀ r : {r // r ∈ DSeparation.relevantVertices bn.graph X Y Z},
              bn.stateSpace r.1))) := by
                rw [eventOfConstraints_constraintsOfRestrict
                  (bn := bn) (DSeparation.relevantVertices bn.graph X Y Z) xR]
    _ =
      ∑ x : bn.JointSpace,
        if x ∈ (restrictToSet (bn := bn)
          (DSeparation.relevantVertices bn.graph X Y Z)) ⁻¹' ({xR} : Set
            (∀ r : {r // r ∈ DSeparation.relevantVertices bn.graph X Y Z},
              bn.stateSpace r.1))
        then cpt.jointWeight x else 0 := by
          simpa [eventOfConstraints_constraintsOfRestrict
            (bn := bn) (DSeparation.relevantVertices bn.graph X Y Z) xR]
            using hμ
    _ = _ := hsum

private def xBlockToRelevant
    (X Y Z : Set V)
    (p : {v // v ∈ DSeparation.xReachableBlock bn.graph X Y Z}) :
    {r // r ∈ DSeparation.relevantVertices bn.graph X Y Z} :=
  ⟨p.1, p.2.1.1⟩

private def yBlockToRelevant
    (X Y Z : Set V)
    (p : {v // v ∈ DSeparation.yReachableBlock bn.graph X Y Z}) :
    {r // r ∈ DSeparation.relevantVertices bn.graph X Y Z} :=
  ⟨p.1, p.2.1.1⟩

private def zToRelevant
    (X Y Z : Set V)
    (p : Z) :
    {r // r ∈ DSeparation.relevantVertices bn.graph X Y Z} :=
  ⟨p.1, DSeparation.z_in_relevant bn.graph X Y Z p.2⟩

private def residualBlockToRelevant
    (X Y Z : Set V)
    (p : {v // v ∈ DSeparation.residualBlock bn.graph X Y Z}) :
    {r // r ∈ DSeparation.relevantVertices bn.graph X Y Z} :=
  ⟨p.1, p.2.1.1⟩

private def relevantToResidual
    (X Y Z : Set V)
    (r : {r // r ∈ DSeparation.relevantVertices bn.graph X Y Z})
    (hx : r.1 ∉ DSeparation.xReachableBlock bn.graph X Y Z)
    (hy : r.1 ∉ DSeparation.yReachableBlock bn.graph X Y Z)
    (hz : r.1 ∉ Z) :
    {u // u ∈ DSeparation.residualBlock bn.graph X Y Z} :=
  ⟨r.1, ⟨⟨r.2, hz⟩, by simp [hx, hy]⟩⟩

private def relevantAssignmentsMatchingBlocks
    (X Y Z : Set V)
    (xX : ∀ p : {v // v ∈ DSeparation.xReachableBlock bn.graph X Y Z}, bn.stateSpace p.1)
    (xY : ∀ p : {v // v ∈ DSeparation.yReachableBlock bn.graph X Y Z}, bn.stateSpace p.1)
    (xZ : ∀ p : Z, bn.stateSpace p.1) :
    Set (∀ r : {r // r ∈ DSeparation.relevantVertices bn.graph X Y Z}, bn.stateSpace r.1) :=
  {xR |
    (∀ p : {v // v ∈ DSeparation.xReachableBlock bn.graph X Y Z},
      xR (xBlockToRelevant (bn := bn) X Y Z p) = xX p) ∧
    (∀ p : {v // v ∈ DSeparation.yReachableBlock bn.graph X Y Z},
      xR (yBlockToRelevant (bn := bn) X Y Z p) = xY p) ∧
    (∀ p : Z,
      xR (zToRelevant (bn := bn) X Y Z p) = xZ p)}

private noncomputable def mergeRelevantFromBlockAssignments
    (X Y Z : Set V)
    (xX : ∀ p : {v // v ∈ DSeparation.xReachableBlock bn.graph X Y Z}, bn.stateSpace p.1)
    (xY : ∀ p : {v // v ∈ DSeparation.yReachableBlock bn.graph X Y Z}, bn.stateSpace p.1)
    (xU : ∀ p : {v // v ∈ DSeparation.residualBlock bn.graph X Y Z}, bn.stateSpace p.1)
    (xZ : ∀ p : Z, bn.stateSpace p.1) :
    ∀ r : {r // r ∈ DSeparation.relevantVertices bn.graph X Y Z}, bn.stateSpace r.1 :=
  fun r =>
    if hx : r.1 ∈ DSeparation.xReachableBlock bn.graph X Y Z then
      xX ⟨r.1, hx⟩
    else if hy : r.1 ∈ DSeparation.yReachableBlock bn.graph X Y Z then
      xY ⟨r.1, hy⟩
    else if hz : r.1 ∈ Z then
      xZ ⟨r.1, hz⟩
    else
      xU (relevantToResidual (bn := bn) X Y Z r hx hy hz)

private noncomputable def residualAssignmentOfRelevant
    (X Y Z : Set V)
    (xR : ∀ r : {r // r ∈ DSeparation.relevantVertices bn.graph X Y Z}, bn.stateSpace r.1) :
    ∀ p : {v // v ∈ DSeparation.residualBlock bn.graph X Y Z}, bn.stateSpace p.1 :=
  fun p => xR (residualBlockToRelevant (bn := bn) X Y Z p)

private theorem mergeRelevantFromBlockAssignments_mem_matchingBlocks
    (X Y Z : Set V)
    (hXY : Disjoint X Y)
    (hSep : DSeparation.SeparatedInMoralAncestral bn.graph X Y Z)
    (xX : ∀ p : {v // v ∈ DSeparation.xReachableBlock bn.graph X Y Z}, bn.stateSpace p.1)
    (xY : ∀ p : {v // v ∈ DSeparation.yReachableBlock bn.graph X Y Z}, bn.stateSpace p.1)
    (xU : ∀ p : {v // v ∈ DSeparation.residualBlock bn.graph X Y Z}, bn.stateSpace p.1)
    (xZ : ∀ p : Z, bn.stateSpace p.1) :
    mergeRelevantFromBlockAssignments (bn := bn) X Y Z xX xY xU xZ ∈
      relevantAssignmentsMatchingBlocks (bn := bn) X Y Z xX xY xZ := by
  refine ⟨?_, ?_, ?_⟩
  · intro p
    simp [mergeRelevantFromBlockAssignments, xBlockToRelevant, p.2]
  · intro p
    have hp_not_x : p.1 ∉ DSeparation.xReachableBlock bn.graph X Y Z := by
      intro hpX
      exact (Set.disjoint_left.mp
        (DSeparation.xReachableBlock_disjoint_yReachableBlock
          bn.graph X Y Z hXY hSep)) hpX p.2
    simp [mergeRelevantFromBlockAssignments, yBlockToRelevant, hp_not_x, p.2]
  · intro p
    have hp_not_x : p.1 ∉ DSeparation.xReachableBlock bn.graph X Y Z := by
      intro hpX
      exact hpX.1.2 p.2
    have hp_not_y : p.1 ∉ DSeparation.yReachableBlock bn.graph X Y Z := by
      intro hpY
      exact hpY.1.2 p.2
    simp [mergeRelevantFromBlockAssignments, zToRelevant, hp_not_x, hp_not_y, p.2]

private theorem residualAssignmentOfRelevant_mergeRelevantFromBlockAssignments
    (X Y Z : Set V)
    (xX : ∀ p : {v // v ∈ DSeparation.xReachableBlock bn.graph X Y Z}, bn.stateSpace p.1)
    (xY : ∀ p : {v // v ∈ DSeparation.yReachableBlock bn.graph X Y Z}, bn.stateSpace p.1)
    (xU : ∀ p : {v // v ∈ DSeparation.residualBlock bn.graph X Y Z}, bn.stateSpace p.1)
    (xZ : ∀ p : Z, bn.stateSpace p.1) :
    residualAssignmentOfRelevant (bn := bn) X Y Z
      (mergeRelevantFromBlockAssignments (bn := bn) X Y Z xX xY xU xZ)
      =
    xU := by
  funext p
  have hp_not_x : p.1 ∉ DSeparation.xReachableBlock bn.graph X Y Z := by
    exact fun hx => p.2.2 (Or.inl hx)
  have hp_not_y : p.1 ∉ DSeparation.yReachableBlock bn.graph X Y Z := by
    exact fun hy => p.2.2 (Or.inr hy)
  have hp_not_z : p.1 ∉ Z := p.2.1.2
  simp [residualAssignmentOfRelevant, residualBlockToRelevant, mergeRelevantFromBlockAssignments,
    residualBlockToRelevant, relevantToResidual, hp_not_x, hp_not_y, hp_not_z]

private theorem mergeRelevantFromBlockAssignments_residualAssignmentOfRelevant
    (X Y Z : Set V)
    (hXY : Disjoint X Y)
    (hSep : DSeparation.SeparatedInMoralAncestral bn.graph X Y Z)
    (xX : ∀ p : {v // v ∈ DSeparation.xReachableBlock bn.graph X Y Z}, bn.stateSpace p.1)
    (xY : ∀ p : {v // v ∈ DSeparation.yReachableBlock bn.graph X Y Z}, bn.stateSpace p.1)
    (xZ : ∀ p : Z, bn.stateSpace p.1)
    (xR : ∀ r : {r // r ∈ DSeparation.relevantVertices bn.graph X Y Z}, bn.stateSpace r.1)
    (hxR : xR ∈ relevantAssignmentsMatchingBlocks (bn := bn) X Y Z xX xY xZ) :
    mergeRelevantFromBlockAssignments (bn := bn) X Y Z xX xY
      (residualAssignmentOfRelevant (bn := bn) X Y Z xR) xZ
      =
    xR := by
  funext r
  rcases hxR with ⟨hx, hy, hz⟩
  by_cases hrX : r.1 ∈ DSeparation.xReachableBlock bn.graph X Y Z
  · simpa [mergeRelevantFromBlockAssignments, hrX, xBlockToRelevant] using
      (hx ⟨r.1, hrX⟩).symm
  · by_cases hrY : r.1 ∈ DSeparation.yReachableBlock bn.graph X Y Z
    have hrY_not_x : r.1 ∉ DSeparation.xReachableBlock bn.graph X Y Z := by
      intro hrX'
      exact (Set.disjoint_left.mp
        (DSeparation.xReachableBlock_disjoint_yReachableBlock
          bn.graph X Y Z hXY hSep)) hrX' hrY
    · simpa [mergeRelevantFromBlockAssignments, hrX, hrY, yBlockToRelevant] using
        (hy ⟨r.1, hrY⟩).symm
    · by_cases hrZ : r.1 ∈ Z
      · simpa [mergeRelevantFromBlockAssignments, hrX, hrY, hrZ, zToRelevant] using
          (hz ⟨r.1, hrZ⟩).symm
      · simp [mergeRelevantFromBlockAssignments, hrX, hrY, hrZ,
          residualAssignmentOfRelevant, residualBlockToRelevant, relevantToResidual]

private noncomputable def residualMatchingEquiv
    (X Y Z : Set V)
    (hXY : Disjoint X Y)
    (hSep : DSeparation.SeparatedInMoralAncestral bn.graph X Y Z)
    (xX : ∀ p : {v // v ∈ DSeparation.xReachableBlock bn.graph X Y Z}, bn.stateSpace p.1)
    (xY : ∀ p : {v // v ∈ DSeparation.yReachableBlock bn.graph X Y Z}, bn.stateSpace p.1)
    (xZ : ∀ p : Z, bn.stateSpace p.1) :
    (∀ p : {v // v ∈ DSeparation.residualBlock bn.graph X Y Z}, bn.stateSpace p.1) ≃
      {xR // xR ∈ relevantAssignmentsMatchingBlocks (bn := bn) X Y Z xX xY xZ} where
  toFun := fun xU =>
    ⟨mergeRelevantFromBlockAssignments (bn := bn) X Y Z xX xY xU xZ,
      mergeRelevantFromBlockAssignments_mem_matchingBlocks
        (bn := bn) X Y Z hXY hSep xX xY xU xZ⟩
  invFun := fun xR =>
    residualAssignmentOfRelevant (bn := bn) X Y Z xR.1
  left_inv := by
    intro xU
    exact residualAssignmentOfRelevant_mergeRelevantFromBlockAssignments
      (bn := bn) X Y Z xX xY xU xZ
  right_inv := by
    intro xR
    apply Subtype.ext
    exact mergeRelevantFromBlockAssignments_residualAssignmentOfRelevant
      (bn := bn) X Y Z hXY hSep xX xY xZ xR.1 xR.2

/-- The intersection of the `X`-block, `Y`-block, and conditioning atoms is
exactly the preimage of the set of relevant assignments that match those three
block restrictions. -/
theorem blockConstraint_inter_eq_relevantPreimage
    (X Y Z : Set V)
    (xX : ∀ p : {v // v ∈ DSeparation.xReachableBlock bn.graph X Y Z}, bn.stateSpace p.1)
    (xY : ∀ p : {v // v ∈ DSeparation.yReachableBlock bn.graph X Y Z}, bn.stateSpace p.1)
    (xZ : ∀ p : Z, bn.stateSpace p.1) :
    eventOfConstraints (bn := bn)
        (constraintsOfRestrict (bn := bn)
          (DSeparation.xReachableBlock bn.graph X Y Z) xX)
      ∩
        (eventOfConstraints (bn := bn)
          (constraintsOfRestrict (bn := bn)
            (DSeparation.yReachableBlock bn.graph X Y Z) xY)
        ∩
          eventOfConstraints (bn := bn)
            (constraintsOfRestrict (bn := bn) Z xZ))
      =
    (restrictToSet (bn := bn) (DSeparation.relevantVertices bn.graph X Y Z)) ⁻¹'
      relevantAssignmentsMatchingBlocks (bn := bn) X Y Z xX xY xZ := by
  ext ω
  constructor
  · intro hω
    rcases hω with ⟨hxω, hyzω⟩
    rcases hyzω with ⟨hyω, hzω⟩
    change
      relevantAssignmentsMatchingBlocks (bn := bn) X Y Z xX xY xZ
        (restrictToSet (bn := bn) (DSeparation.relevantVertices bn.graph X Y Z) ω)
    refine ⟨?_, ?_, ?_⟩
    · have hxRestr :
        restrictToSet (bn := bn) (DSeparation.xReachableBlock bn.graph X Y Z) ω = xX := by
          simpa [eventOfConstraints_constraintsOfRestrict
            (bn := bn) (DSeparation.xReachableBlock bn.graph X Y Z) xX] using hxω
      intro p
      simpa [xBlockToRelevant, restrictToSet] using congrFun hxRestr p
    · have hyRestr :
        restrictToSet (bn := bn) (DSeparation.yReachableBlock bn.graph X Y Z) ω = xY := by
          simpa [eventOfConstraints_constraintsOfRestrict
            (bn := bn) (DSeparation.yReachableBlock bn.graph X Y Z) xY] using hyω
      intro p
      simpa [yBlockToRelevant, restrictToSet] using congrFun hyRestr p
    · have hzRestr : restrictToSet (bn := bn) Z ω = xZ := by
        simpa [eventOfConstraints_constraintsOfRestrict (bn := bn) Z xZ] using hzω
      intro p
      simpa [zToRelevant, restrictToSet] using congrFun hzRestr p
  · intro hω
    change
      relevantAssignmentsMatchingBlocks (bn := bn) X Y Z xX xY xZ
        (restrictToSet (bn := bn) (DSeparation.relevantVertices bn.graph X Y Z) ω) at hω
    rcases hω with ⟨hx, hy, hz⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa [eventOfConstraints_constraintsOfRestrict
        (bn := bn) (DSeparation.xReachableBlock bn.graph X Y Z) xX] using! funext hx
    · simpa [eventOfConstraints_constraintsOfRestrict
        (bn := bn) (DSeparation.yReachableBlock bn.graph X Y Z) xY] using! funext hy
    · simpa [eventOfConstraints_constraintsOfRestrict
        (bn := bn) Z xZ] using! funext hz

/-- A block atom over the `X`-reachable side, `Y`-reachable side, and
conditioning set is a finite disjoint sum of full relevant atoms. -/
theorem jointMeasure_blockConstraint_eq_sum_relevantAtoms
    [∀ v, MeasurableSingletonClass (bn.stateSpace v)]
    (cpt : bn.DiscreteCPT) (X Y Z : Set V)
    (xX : ∀ p : {v // v ∈ DSeparation.xReachableBlock bn.graph X Y Z}, bn.stateSpace p.1)
    (xY : ∀ p : {v // v ∈ DSeparation.yReachableBlock bn.graph X Y Z}, bn.stateSpace p.1)
    (xZ : ∀ p : Z, bn.stateSpace p.1) :
    cpt.jointMeasure
      (eventOfConstraints (bn := bn)
          (constraintsOfRestrict (bn := bn)
            (DSeparation.xReachableBlock bn.graph X Y Z) xX)
        ∩
          (eventOfConstraints (bn := bn)
            (constraintsOfRestrict (bn := bn)
              (DSeparation.yReachableBlock bn.graph X Y Z) xY)
          ∩
            eventOfConstraints (bn := bn)
              (constraintsOfRestrict (bn := bn) Z xZ)))
      =
    ∑ xR : (∀ r : {r // r ∈ DSeparation.relevantVertices bn.graph X Y Z}, bn.stateSpace r.1),
      if xR ∈ relevantAssignmentsMatchingBlocks (bn := bn) X Y Z xX xY xZ then
        cpt.jointMeasure
          (eventOfConstraints (bn := bn)
            (constraintsOfRestrict (bn := bn)
              (DSeparation.relevantVertices bn.graph X Y Z) xR))
      else 0 := by
  rw [blockConstraint_inter_eq_relevantPreimage (bn := bn) X Y Z xX xY xZ]
  simpa [relevantAssignmentsMatchingBlocks] using
    measure_vertices_preimage_eq_sum
      (bn := bn) (μ := cpt.jointMeasure)
      (S := DSeparation.relevantVertices bn.graph X Y Z)
      (T := relevantAssignmentsMatchingBlocks (bn := bn) X Y Z xX xY xZ)

/-- Substituting the full relevant-atom factorization turns the previous block
decomposition into a finite sum of block products. This is the first
residual-summation theorem on the route from full relevant atoms to partial
`X/Y/Z` block atoms. -/
theorem jointMeasure_blockConstraint_eq_sum_relevantBlockProducts
    [∀ v, MeasurableSingletonClass (bn.stateSpace v)]
    (cpt : bn.DiscreteCPT) (X Y Z : Set V)
    (hirr : ∀ v : V, ¬bn.graph.edges v v)
    (hXY : Disjoint X Y)
    (hSep : DSeparation.SeparatedInMoralAncestral bn.graph X Y Z)
    (xX : ∀ p : {v // v ∈ DSeparation.xReachableBlock bn.graph X Y Z}, bn.stateSpace p.1)
    (xY : ∀ p : {v // v ∈ DSeparation.yReachableBlock bn.graph X Y Z}, bn.stateSpace p.1)
    (xZ : ∀ p : Z, bn.stateSpace p.1) :
    cpt.jointMeasure
      (eventOfConstraints (bn := bn)
          (constraintsOfRestrict (bn := bn)
            (DSeparation.xReachableBlock bn.graph X Y Z) xX)
        ∩
          (eventOfConstraints (bn := bn)
            (constraintsOfRestrict (bn := bn)
              (DSeparation.yReachableBlock bn.graph X Y Z) xY)
          ∩
            eventOfConstraints (bn := bn)
              (constraintsOfRestrict (bn := bn) Z xZ)))
      =
    ∑ xR : (∀ r : {r // r ∈ DSeparation.relevantVertices bn.graph X Y Z}, bn.stateSpace r.1),
      if xR ∈ relevantAssignmentsMatchingBlocks (bn := bn) X Y Z xX xY xZ then
        (∏ v ∈ relevantHeadXFinset bn X Y Z,
            cpt.nodeProb (baseFromRelevant (bn := bn) X Y Z xR) v) *
          ((∏ v ∈ relevantHeadYFinset bn X Y Z,
              cpt.nodeProb (baseFromRelevant (bn := bn) X Y Z xR) v) *
            ((∏ v ∈ relevantHeadResidualFinset bn X Y Z,
                cpt.nodeProb (baseFromRelevant (bn := bn) X Y Z xR) v) *
              ∏ v ∈ relevantHeadConditioningFinset bn X Y Z,
                cpt.nodeProb (baseFromRelevant (bn := bn) X Y Z xR) v))
      else 0 := by
  calc
    cpt.jointMeasure
        (eventOfConstraints (bn := bn)
            (constraintsOfRestrict (bn := bn)
              (DSeparation.xReachableBlock bn.graph X Y Z) xX)
          ∩
            (eventOfConstraints (bn := bn)
              (constraintsOfRestrict (bn := bn)
                (DSeparation.yReachableBlock bn.graph X Y Z) xY)
            ∩
              eventOfConstraints (bn := bn)
                (constraintsOfRestrict (bn := bn) Z xZ)))
        =
      ∑ xR : (∀ r : {r // r ∈ DSeparation.relevantVertices bn.graph X Y Z},
          bn.stateSpace r.1),
        if xR ∈ relevantAssignmentsMatchingBlocks (bn := bn) X Y Z xX xY xZ then
          cpt.jointMeasure
            (eventOfConstraints (bn := bn)
              (constraintsOfRestrict (bn := bn)
                (DSeparation.relevantVertices bn.graph X Y Z) xR))
        else 0 := by
          exact jointMeasure_blockConstraint_eq_sum_relevantAtoms
            (bn := bn) (cpt := cpt) X Y Z xX xY xZ
    _ =
      ∑ xR : (∀ r : {r // r ∈ DSeparation.relevantVertices bn.graph X Y Z},
          bn.stateSpace r.1),
        if xR ∈ relevantAssignmentsMatchingBlocks (bn := bn) X Y Z xX xY xZ then
          (∏ v ∈ relevantHeadXFinset bn X Y Z,
              cpt.nodeProb (baseFromRelevant (bn := bn) X Y Z xR) v) *
            ((∏ v ∈ relevantHeadYFinset bn X Y Z,
                cpt.nodeProb (baseFromRelevant (bn := bn) X Y Z xR) v) *
              ((∏ v ∈ relevantHeadResidualFinset bn X Y Z,
                  cpt.nodeProb (baseFromRelevant (bn := bn) X Y Z xR) v) *
                ∏ v ∈ relevantHeadConditioningFinset bn X Y Z,
                  cpt.nodeProb (baseFromRelevant (bn := bn) X Y Z xR) v))
        else 0 := by
          refine Finset.sum_congr rfl ?_
          intro xR _
          by_cases hxR :
              xR ∈ relevantAssignmentsMatchingBlocks (bn := bn) X Y Z xX xY xZ
          · simp [hxR, jointMeasure_relevantAtom_eq_relevantBlockProducts
              (bn := bn) (cpt := cpt) X Y Z hirr hXY hSep xR]
          · simp [hxR]

/-- Explicit residual-summation form of the partial block-atom theorem. Once
the `X`-reachable block, `Y`-reachable block, and conditioning coordinates are
fixed, the remaining degrees of freedom are exactly the assignments on the
residual block. -/
theorem jointMeasure_blockConstraint_eq_residualSum_relevantBlockProducts
    [∀ v, MeasurableSingletonClass (bn.stateSpace v)]
    (cpt : bn.DiscreteCPT) (X Y Z : Set V)
    (hirr : ∀ v : V, ¬bn.graph.edges v v)
    (hXY : Disjoint X Y)
    (hSep : DSeparation.SeparatedInMoralAncestral bn.graph X Y Z)
    (xX : ∀ p : {v // v ∈ DSeparation.xReachableBlock bn.graph X Y Z}, bn.stateSpace p.1)
    (xY : ∀ p : {v // v ∈ DSeparation.yReachableBlock bn.graph X Y Z}, bn.stateSpace p.1)
    (xZ : ∀ p : Z, bn.stateSpace p.1) :
    cpt.jointMeasure
      (eventOfConstraints (bn := bn)
          (constraintsOfRestrict (bn := bn)
            (DSeparation.xReachableBlock bn.graph X Y Z) xX)
        ∩
          (eventOfConstraints (bn := bn)
            (constraintsOfRestrict (bn := bn)
              (DSeparation.yReachableBlock bn.graph X Y Z) xY)
          ∩
            eventOfConstraints (bn := bn)
              (constraintsOfRestrict (bn := bn) Z xZ)))
      =
    ∑ xU : (∀ p : {v // v ∈ DSeparation.residualBlock bn.graph X Y Z}, bn.stateSpace p.1),
      let xR := mergeRelevantFromBlockAssignments (bn := bn) X Y Z xX xY xU xZ
      (∏ v ∈ relevantHeadXFinset bn X Y Z,
          cpt.nodeProb (baseFromRelevant (bn := bn) X Y Z xR) v) *
        ((∏ v ∈ relevantHeadYFinset bn X Y Z,
            cpt.nodeProb (baseFromRelevant (bn := bn) X Y Z xR) v) *
          ((∏ v ∈ relevantHeadResidualFinset bn X Y Z,
              cpt.nodeProb (baseFromRelevant (bn := bn) X Y Z xR) v) *
            ∏ v ∈ relevantHeadConditioningFinset bn X Y Z,
              cpt.nodeProb (baseFromRelevant (bn := bn) X Y Z xR) v)) := by
  classical
  let T := relevantAssignmentsMatchingBlocks (bn := bn) X Y Z xX xY xZ
  let F :
      (∀ r : {r // r ∈ DSeparation.relevantVertices bn.graph X Y Z}, bn.stateSpace r.1) →
        ENNReal :=
    fun xR =>
      (∏ v ∈ relevantHeadXFinset bn X Y Z,
          cpt.nodeProb (baseFromRelevant (bn := bn) X Y Z xR) v) *
        ((∏ v ∈ relevantHeadYFinset bn X Y Z,
            cpt.nodeProb (baseFromRelevant (bn := bn) X Y Z xR) v) *
          ((∏ v ∈ relevantHeadResidualFinset bn X Y Z,
              cpt.nodeProb (baseFromRelevant (bn := bn) X Y Z xR) v) *
            ∏ v ∈ relevantHeadConditioningFinset bn X Y Z,
              cpt.nodeProb (baseFromRelevant (bn := bn) X Y Z xR) v))
  calc
    cpt.jointMeasure
        (eventOfConstraints (bn := bn)
            (constraintsOfRestrict (bn := bn)
              (DSeparation.xReachableBlock bn.graph X Y Z) xX)
          ∩
            (eventOfConstraints (bn := bn)
              (constraintsOfRestrict (bn := bn)
                (DSeparation.yReachableBlock bn.graph X Y Z) xY)
            ∩
              eventOfConstraints (bn := bn)
                (constraintsOfRestrict (bn := bn) Z xZ)))
        =
      ∑ xR : (∀ r : {r // r ∈ DSeparation.relevantVertices bn.graph X Y Z},
          bn.stateSpace r.1),
        if xR ∈ T then F xR else 0 := by
          simpa [T, F] using
            jointMeasure_blockConstraint_eq_sum_relevantBlockProducts
              (bn := bn) (cpt := cpt) X Y Z hirr hXY hSep xX xY xZ
    _ = ∑ xR : {xR //
          xR ∈ T},
        F xR.1 := by
          rw [← Finset.sum_filter]
          simpa using
            (Finset.sum_subtype_eq_sum_filter
              (s := Finset.univ)
              (f := F)
              (p := fun xR :
                (∀ r : {r // r ∈ DSeparation.relevantVertices bn.graph X Y Z},
                  bn.stateSpace r.1) => xR ∈ T)).symm
    _ =
      ∑ xU : (∀ p : {v // v ∈ DSeparation.residualBlock bn.graph X Y Z},
          bn.stateSpace p.1),
        F (mergeRelevantFromBlockAssignments (bn := bn) X Y Z xX xY xU xZ) := by
          refine (Fintype.sum_equiv
            (residualMatchingEquiv (bn := bn) X Y Z hXY hSep xX xY xZ)
            (fun xU => F (mergeRelevantFromBlockAssignments (bn := bn) X Y Z xX xY xU xZ))
            (fun xR => F xR.1) ?_).symm
          intro xU
          rfl
    _ = _ := by
          simp [F]

/-- Default block assignment used to name the separated block factors. -/
noncomputable def defaultBlockAssignment
    (S : Set V) : ∀ p : S, bn.stateSpace p.1 :=
  fun p => Classical.choice (inferInstance : Nonempty (bn.stateSpace p.1))

/-- The `X`-reachable head-factor product induced by a fixed `X`-block and
conditioning assignment. -/
noncomputable def xReachableBlockFactor
    (cpt : bn.DiscreteCPT) (X Y Z : Set V)
    (xX : ∀ p : {v // v ∈ DSeparation.xReachableBlock bn.graph X Y Z}, bn.stateSpace p.1)
    (xZ : ∀ p : Z, bn.stateSpace p.1) : ℝ≥0∞ :=
  let xR :=
    mergeRelevantFromBlockAssignments (bn := bn) X Y Z
      xX
      (defaultBlockAssignment (bn := bn) (DSeparation.yReachableBlock bn.graph X Y Z))
      (defaultBlockAssignment (bn := bn) (DSeparation.residualBlock bn.graph X Y Z))
      xZ
  ∏ v ∈ relevantHeadXFinset bn X Y Z,
    cpt.nodeProb (baseFromRelevant (bn := bn) X Y Z xR) v

/-- The `Y`-reachable head-factor product induced by a fixed `Y`-block and
conditioning assignment. -/
noncomputable def yReachableBlockFactor
    (cpt : bn.DiscreteCPT) (X Y Z : Set V)
    (xY : ∀ p : {v // v ∈ DSeparation.yReachableBlock bn.graph X Y Z}, bn.stateSpace p.1)
    (xZ : ∀ p : Z, bn.stateSpace p.1) : ℝ≥0∞ :=
  let xR :=
    mergeRelevantFromBlockAssignments (bn := bn) X Y Z
      (defaultBlockAssignment (bn := bn) (DSeparation.xReachableBlock bn.graph X Y Z))
      xY
      (defaultBlockAssignment (bn := bn) (DSeparation.residualBlock bn.graph X Y Z))
      xZ
  ∏ v ∈ relevantHeadYFinset bn X Y Z,
    cpt.nodeProb (baseFromRelevant (bn := bn) X Y Z xR) v

/-- The residual head-factor product induced by a fixed residual block and
conditioning assignment. -/
noncomputable def residualBlockFactor
    (cpt : bn.DiscreteCPT) (X Y Z : Set V)
    (xU : ∀ p : {v // v ∈ DSeparation.residualBlock bn.graph X Y Z}, bn.stateSpace p.1)
    (xZ : ∀ p : Z, bn.stateSpace p.1) : ℝ≥0∞ :=
  let xR :=
    mergeRelevantFromBlockAssignments (bn := bn) X Y Z
      (defaultBlockAssignment (bn := bn) (DSeparation.xReachableBlock bn.graph X Y Z))
      (defaultBlockAssignment (bn := bn) (DSeparation.yReachableBlock bn.graph X Y Z))
      xU
      xZ
  ∏ v ∈ relevantHeadResidualFinset bn X Y Z,
    cpt.nodeProb (baseFromRelevant (bn := bn) X Y Z xR) v

/-- The conditioning-only head-factor product induced by a fixed conditioning
assignment. -/
noncomputable def conditioningBlockFactor
    (cpt : bn.DiscreteCPT) (X Y Z : Set V)
    (xZ : ∀ p : Z, bn.stateSpace p.1) : ℝ≥0∞ :=
  let xR :=
    mergeRelevantFromBlockAssignments (bn := bn) X Y Z
      (defaultBlockAssignment (bn := bn) (DSeparation.xReachableBlock bn.graph X Y Z))
      (defaultBlockAssignment (bn := bn) (DSeparation.yReachableBlock bn.graph X Y Z))
      (defaultBlockAssignment (bn := bn) (DSeparation.residualBlock bn.graph X Y Z))
      xZ
  ∏ v ∈ relevantHeadConditioningFinset bn X Y Z,
    cpt.nodeProb (baseFromRelevant (bn := bn) X Y Z xR) v

/-- The `X`-head product does not depend on the `Y` or residual assignments once
the `X`-block and conditioning coordinates are fixed. -/
theorem relevantHeadXProd_mergeRelevant_eq_xReachableBlockFactor
    (cpt : bn.DiscreteCPT) (X Y Z : Set V)
    (hirr : ∀ v : V, ¬bn.graph.edges v v)
    (xX : ∀ p : {v // v ∈ DSeparation.xReachableBlock bn.graph X Y Z}, bn.stateSpace p.1)
    (xY : ∀ p : {v // v ∈ DSeparation.yReachableBlock bn.graph X Y Z}, bn.stateSpace p.1)
    (xU : ∀ p : {v // v ∈ DSeparation.residualBlock bn.graph X Y Z}, bn.stateSpace p.1)
    (xZ : ∀ p : Z, bn.stateSpace p.1) :
    let xR :=
      mergeRelevantFromBlockAssignments (bn := bn) X Y Z xX xY xU xZ
    ∏ v ∈ relevantHeadXFinset bn X Y Z,
      cpt.nodeProb (baseFromRelevant (bn := bn) X Y Z xR) v
      =
    xReachableBlockFactor (bn := bn) cpt X Y Z xX xZ := by
  classical
  let xR :=
    mergeRelevantFromBlockAssignments (bn := bn) X Y Z xX xY xU xZ
  let xR0 :=
    mergeRelevantFromBlockAssignments (bn := bn) X Y Z
      xX
      (defaultBlockAssignment (bn := bn) (DSeparation.yReachableBlock bn.graph X Y Z))
      (defaultBlockAssignment (bn := bn) (DSeparation.residualBlock bn.graph X Y Z))
      xZ
  have hAgree :
      ∀ s, s ∈ DSeparation.xReachableBlock bn.graph X Y Z ∪ Z →
        baseFromRelevant (bn := bn) X Y Z xR s =
          baseFromRelevant (bn := bn) X Y Z xR0 s := by
    intro s hs
    rcases hs with hsX | hsZ
    · simp [baseFromRelevant, xR, xR0, mergeRelevantFromBlockAssignments, hsX, hsX.1.1]
    · have hs_not_x : s ∉ DSeparation.xReachableBlock bn.graph X Y Z := by
        intro hsX
        exact hsX.1.2 hsZ
      have hs_not_y : s ∉ DSeparation.yReachableBlock bn.graph X Y Z := by
        intro hsY
        exact hsY.1.2 hsZ
      simp [baseFromRelevant, xR, xR0, mergeRelevantFromBlockAssignments, hs_not_x, hs_not_y,
        hsZ]
  have hProd :=
    prod_relevantHeadXFinset_eq_of_agree
      (bn := bn) (cpt := cpt) X Y Z hirr
      (baseFromRelevant (bn := bn) X Y Z xR)
      (baseFromRelevant (bn := bn) X Y Z xR0) hAgree
  simpa [xReachableBlockFactor, xR, xR0]
    using hProd

/-- The `Y`-head product does not depend on the `X` or residual assignments once
the `Y`-block and conditioning coordinates are fixed. -/
theorem relevantHeadYProd_mergeRelevant_eq_yReachableBlockFactor
    (cpt : bn.DiscreteCPT) (X Y Z : Set V)
    (hirr : ∀ v : V, ¬bn.graph.edges v v)
    (hXY : Disjoint X Y)
    (hSep : DSeparation.SeparatedInMoralAncestral bn.graph X Y Z)
    (xX : ∀ p : {v // v ∈ DSeparation.xReachableBlock bn.graph X Y Z}, bn.stateSpace p.1)
    (xY : ∀ p : {v // v ∈ DSeparation.yReachableBlock bn.graph X Y Z}, bn.stateSpace p.1)
    (xU : ∀ p : {v // v ∈ DSeparation.residualBlock bn.graph X Y Z}, bn.stateSpace p.1)
    (xZ : ∀ p : Z, bn.stateSpace p.1) :
    let xR :=
      mergeRelevantFromBlockAssignments (bn := bn) X Y Z xX xY xU xZ
    ∏ v ∈ relevantHeadYFinset bn X Y Z,
      cpt.nodeProb (baseFromRelevant (bn := bn) X Y Z xR) v
      =
    yReachableBlockFactor (bn := bn) cpt X Y Z xY xZ := by
  classical
  let xR :=
    mergeRelevantFromBlockAssignments (bn := bn) X Y Z xX xY xU xZ
  let xR0 :=
    mergeRelevantFromBlockAssignments (bn := bn) X Y Z
      (defaultBlockAssignment (bn := bn) (DSeparation.xReachableBlock bn.graph X Y Z))
      xY
      (defaultBlockAssignment (bn := bn) (DSeparation.residualBlock bn.graph X Y Z))
      xZ
  have hAgree :
      ∀ s, s ∈ DSeparation.yReachableBlock bn.graph X Y Z ∪ Z →
        baseFromRelevant (bn := bn) X Y Z xR s =
          baseFromRelevant (bn := bn) X Y Z xR0 s := by
    intro s hs
    rcases hs with hsY | hsZ
    · have hs_not_x : s ∉ DSeparation.xReachableBlock bn.graph X Y Z := by
        intro hsX
        exact (Set.disjoint_left.mp
          (DSeparation.xReachableBlock_disjoint_yReachableBlock
            bn.graph X Y Z hXY hSep)) hsX hsY
      simp [baseFromRelevant, xR, xR0, mergeRelevantFromBlockAssignments, hs_not_x, hsY]
    · have hs_not_x : s ∉ DSeparation.xReachableBlock bn.graph X Y Z := by
        intro hsX
        exact hsX.1.2 hsZ
      have hs_not_y : s ∉ DSeparation.yReachableBlock bn.graph X Y Z := by
        intro hsY
        exact hsY.1.2 hsZ
      simp [baseFromRelevant, xR, xR0, mergeRelevantFromBlockAssignments, hs_not_x, hs_not_y,
        hsZ]
  have hProd :=
    prod_relevantHeadYFinset_eq_of_agree
      (bn := bn) (cpt := cpt) X Y Z hirr
      (baseFromRelevant (bn := bn) X Y Z xR)
      (baseFromRelevant (bn := bn) X Y Z xR0) hAgree
  simpa [yReachableBlockFactor, xR, xR0]
    using hProd

/-- The residual-head product does not depend on the endpoint-block assignments
once the residual block and conditioning coordinates are fixed. -/
theorem relevantHeadResidualProd_mergeRelevant_eq_residualBlockFactor
    (cpt : bn.DiscreteCPT) (X Y Z : Set V)
    (hirr : ∀ v : V, ¬bn.graph.edges v v)
    (xX : ∀ p : {v // v ∈ DSeparation.xReachableBlock bn.graph X Y Z}, bn.stateSpace p.1)
    (xY : ∀ p : {v // v ∈ DSeparation.yReachableBlock bn.graph X Y Z}, bn.stateSpace p.1)
    (xU : ∀ p : {v // v ∈ DSeparation.residualBlock bn.graph X Y Z}, bn.stateSpace p.1)
    (xZ : ∀ p : Z, bn.stateSpace p.1) :
    let xR :=
      mergeRelevantFromBlockAssignments (bn := bn) X Y Z xX xY xU xZ
    ∏ v ∈ relevantHeadResidualFinset bn X Y Z,
      cpt.nodeProb (baseFromRelevant (bn := bn) X Y Z xR) v
      =
    residualBlockFactor (bn := bn) cpt X Y Z xU xZ := by
  classical
  let xR :=
    mergeRelevantFromBlockAssignments (bn := bn) X Y Z xX xY xU xZ
  let xR0 :=
    mergeRelevantFromBlockAssignments (bn := bn) X Y Z
      (defaultBlockAssignment (bn := bn) (DSeparation.xReachableBlock bn.graph X Y Z))
      (defaultBlockAssignment (bn := bn) (DSeparation.yReachableBlock bn.graph X Y Z))
      xU
      xZ
  have hAgree :
      ∀ s, s ∈ DSeparation.residualBlock bn.graph X Y Z ∪ Z →
        baseFromRelevant (bn := bn) X Y Z xR s =
          baseFromRelevant (bn := bn) X Y Z xR0 s := by
    intro s hs
    rcases hs with hsU | hsZ
    · have hs_not_x : s ∉ DSeparation.xReachableBlock bn.graph X Y Z := by
        exact fun hsX => hsU.2 (Or.inl hsX)
      have hs_not_y : s ∉ DSeparation.yReachableBlock bn.graph X Y Z := by
        exact fun hsY => hsU.2 (Or.inr hsY)
      have hs_not_z : s ∉ Z := hsU.1.2
      simp [baseFromRelevant, xR, xR0, mergeRelevantFromBlockAssignments, hs_not_x, hs_not_y,
        hs_not_z]
    · have hs_not_x : s ∉ DSeparation.xReachableBlock bn.graph X Y Z := by
        intro hsX
        exact hsX.1.2 hsZ
      have hs_not_y : s ∉ DSeparation.yReachableBlock bn.graph X Y Z := by
        intro hsY
        exact hsY.1.2 hsZ
      simp [baseFromRelevant, xR, xR0, mergeRelevantFromBlockAssignments, hs_not_x, hs_not_y,
        hsZ]
  have hProd :=
    prod_relevantHeadResidualFinset_eq_of_agree
      (bn := bn) (cpt := cpt) X Y Z hirr
      (baseFromRelevant (bn := bn) X Y Z xR)
      (baseFromRelevant (bn := bn) X Y Z xR0) hAgree
  simpa [residualBlockFactor, xR, xR0]
    using hProd

/-- The conditioning-only product depends only on the conditioning coordinates. -/
theorem relevantHeadConditioningProd_mergeRelevant_eq_conditioningBlockFactor
    (cpt : bn.DiscreteCPT) (X Y Z : Set V)
    (xX : ∀ p : {v // v ∈ DSeparation.xReachableBlock bn.graph X Y Z}, bn.stateSpace p.1)
    (xY : ∀ p : {v // v ∈ DSeparation.yReachableBlock bn.graph X Y Z}, bn.stateSpace p.1)
    (xU : ∀ p : {v // v ∈ DSeparation.residualBlock bn.graph X Y Z}, bn.stateSpace p.1)
    (xZ : ∀ p : Z, bn.stateSpace p.1) :
    let xR :=
      mergeRelevantFromBlockAssignments (bn := bn) X Y Z xX xY xU xZ
    ∏ v ∈ relevantHeadConditioningFinset bn X Y Z,
      cpt.nodeProb (baseFromRelevant (bn := bn) X Y Z xR) v
      =
    conditioningBlockFactor (bn := bn) cpt X Y Z xZ := by
  classical
  let xR :=
    mergeRelevantFromBlockAssignments (bn := bn) X Y Z xX xY xU xZ
  let xR0 :=
    mergeRelevantFromBlockAssignments (bn := bn) X Y Z
      (defaultBlockAssignment (bn := bn) (DSeparation.xReachableBlock bn.graph X Y Z))
      (defaultBlockAssignment (bn := bn) (DSeparation.yReachableBlock bn.graph X Y Z))
      (defaultBlockAssignment (bn := bn) (DSeparation.residualBlock bn.graph X Y Z))
      xZ
  have hAgree :
      ∀ s, s ∈ Z →
        baseFromRelevant (bn := bn) X Y Z xR s =
          baseFromRelevant (bn := bn) X Y Z xR0 s := by
    intro s hsZ
    have hs_not_x : s ∉ DSeparation.xReachableBlock bn.graph X Y Z := by
      intro hsX
      exact hsX.1.2 hsZ
    have hs_not_y : s ∉ DSeparation.yReachableBlock bn.graph X Y Z := by
      intro hsY
      exact hsY.1.2 hsZ
    simp [baseFromRelevant, xR, xR0, mergeRelevantFromBlockAssignments, hs_not_x, hs_not_y,
      hsZ]
  have hProd :=
    prod_relevantHeadConditioningFinset_eq_of_agree
      (bn := bn) (cpt := cpt) X Y Z
      (baseFromRelevant (bn := bn) X Y Z xR)
      (baseFromRelevant (bn := bn) X Y Z xR0) hAgree
  simpa [conditioningBlockFactor, xR, xR0]
    using hProd

/-- Factored residual-summation form of the separated `X/Y/Z` block atom. The
`X`- and `Y`-reachable head products depend only on their own block plus `Z`,
the residual product depends only on the residual block plus `Z`, and the
conditioning-only product depends only on `Z`. -/
theorem jointMeasure_blockConstraint_eq_factoredResidualSum
    [∀ v, MeasurableSingletonClass (bn.stateSpace v)]
    (cpt : bn.DiscreteCPT) (X Y Z : Set V)
    (hirr : ∀ v : V, ¬bn.graph.edges v v)
    (hXY : Disjoint X Y)
    (hSep : DSeparation.SeparatedInMoralAncestral bn.graph X Y Z)
    (xX : ∀ p : {v // v ∈ DSeparation.xReachableBlock bn.graph X Y Z}, bn.stateSpace p.1)
    (xY : ∀ p : {v // v ∈ DSeparation.yReachableBlock bn.graph X Y Z}, bn.stateSpace p.1)
    (xZ : ∀ p : Z, bn.stateSpace p.1) :
    cpt.jointMeasure
      (eventOfConstraints (bn := bn)
          (constraintsOfRestrict (bn := bn)
            (DSeparation.xReachableBlock bn.graph X Y Z) xX)
        ∩
          (eventOfConstraints (bn := bn)
            (constraintsOfRestrict (bn := bn)
              (DSeparation.yReachableBlock bn.graph X Y Z) xY)
          ∩
            eventOfConstraints (bn := bn)
              (constraintsOfRestrict (bn := bn) Z xZ)))
      =
    xReachableBlockFactor (bn := bn) cpt X Y Z xX xZ *
      (yReachableBlockFactor (bn := bn) cpt X Y Z xY xZ *
        ∑ xU : (∀ p : {v // v ∈ DSeparation.residualBlock bn.graph X Y Z}, bn.stateSpace p.1),
          residualBlockFactor (bn := bn) cpt X Y Z xU xZ *
            conditioningBlockFactor (bn := bn) cpt X Y Z xZ) := by
  classical
  calc
    cpt.jointMeasure
        (eventOfConstraints (bn := bn)
            (constraintsOfRestrict (bn := bn)
              (DSeparation.xReachableBlock bn.graph X Y Z) xX)
          ∩
            (eventOfConstraints (bn := bn)
              (constraintsOfRestrict (bn := bn)
                (DSeparation.yReachableBlock bn.graph X Y Z) xY)
            ∩
              eventOfConstraints (bn := bn)
                (constraintsOfRestrict (bn := bn) Z xZ)))
        =
      ∑ xU : (∀ p : {v // v ∈ DSeparation.residualBlock bn.graph X Y Z},
          bn.stateSpace p.1),
        let xR := mergeRelevantFromBlockAssignments (bn := bn) X Y Z xX xY xU xZ
        (∏ v ∈ relevantHeadXFinset bn X Y Z,
            cpt.nodeProb (baseFromRelevant (bn := bn) X Y Z xR) v) *
          ((∏ v ∈ relevantHeadYFinset bn X Y Z,
              cpt.nodeProb (baseFromRelevant (bn := bn) X Y Z xR) v) *
            ((∏ v ∈ relevantHeadResidualFinset bn X Y Z,
                cpt.nodeProb (baseFromRelevant (bn := bn) X Y Z xR) v) *
              ∏ v ∈ relevantHeadConditioningFinset bn X Y Z,
                cpt.nodeProb (baseFromRelevant (bn := bn) X Y Z xR) v)) := by
          exact jointMeasure_blockConstraint_eq_residualSum_relevantBlockProducts
            (bn := bn) (cpt := cpt) X Y Z hirr hXY hSep xX xY xZ
    _ =
      ∑ xU : (∀ p : {v // v ∈ DSeparation.residualBlock bn.graph X Y Z},
          bn.stateSpace p.1),
        xReachableBlockFactor (bn := bn) cpt X Y Z xX xZ *
          (yReachableBlockFactor (bn := bn) cpt X Y Z xY xZ *
            (residualBlockFactor (bn := bn) cpt X Y Z xU xZ *
              conditioningBlockFactor (bn := bn) cpt X Y Z xZ)) := by
          refine Finset.sum_congr rfl ?_
          intro xU _
          have hX :=
            relevantHeadXProd_mergeRelevant_eq_xReachableBlockFactor
              (bn := bn) (cpt := cpt) X Y Z hirr xX xY xU xZ
          have hY :=
            relevantHeadYProd_mergeRelevant_eq_yReachableBlockFactor
              (bn := bn) (cpt := cpt) X Y Z hirr hXY hSep xX xY xU xZ
          have hU :=
            relevantHeadResidualProd_mergeRelevant_eq_residualBlockFactor
              (bn := bn) (cpt := cpt) X Y Z hirr xX xY xU xZ
          have hZ :=
            relevantHeadConditioningProd_mergeRelevant_eq_conditioningBlockFactor
              (bn := bn) (cpt := cpt) X Y Z xX xY xU xZ
          simpa [mul_assoc] using congrArg (fun z => z)
            (show
              (let xR := mergeRelevantFromBlockAssignments (bn := bn) X Y Z xX xY xU xZ
               (∏ v ∈ relevantHeadXFinset bn X Y Z,
                  cpt.nodeProb (baseFromRelevant (bn := bn) X Y Z xR) v) *
                ((∏ v ∈ relevantHeadYFinset bn X Y Z,
                    cpt.nodeProb (baseFromRelevant (bn := bn) X Y Z xR) v) *
                  ((∏ v ∈ relevantHeadResidualFinset bn X Y Z,
                      cpt.nodeProb (baseFromRelevant (bn := bn) X Y Z xR) v) *
                    ∏ v ∈ relevantHeadConditioningFinset bn X Y Z,
                      cpt.nodeProb (baseFromRelevant (bn := bn) X Y Z xR) v)))
              =
              xReachableBlockFactor (bn := bn) cpt X Y Z xX xZ *
                (yReachableBlockFactor (bn := bn) cpt X Y Z xY xZ *
                  (residualBlockFactor (bn := bn) cpt X Y Z xU xZ *
                    conditioningBlockFactor (bn := bn) cpt X Y Z xZ)) from by
              simp only [hX, hY, hU, hZ])
    _ =
      xReachableBlockFactor (bn := bn) cpt X Y Z xX xZ *
        (yReachableBlockFactor (bn := bn) cpt X Y Z xY xZ *
          ∑ xU : (∀ p : {v // v ∈ DSeparation.residualBlock bn.graph X Y Z},
              bn.stateSpace p.1),
            residualBlockFactor (bn := bn) cpt X Y Z xU xZ *
              conditioningBlockFactor (bn := bn) cpt X Y Z xZ) := by
          calc
            ∑ xU : (∀ p : {v // v ∈ DSeparation.residualBlock bn.graph X Y Z},
                bn.stateSpace p.1),
              xReachableBlockFactor (bn := bn) cpt X Y Z xX xZ *
                (yReachableBlockFactor (bn := bn) cpt X Y Z xY xZ *
                  (residualBlockFactor (bn := bn) cpt X Y Z xU xZ *
                    conditioningBlockFactor (bn := bn) cpt X Y Z xZ))
                =
              ∑ xU : (∀ p : {v // v ∈ DSeparation.residualBlock bn.graph X Y Z},
                  bn.stateSpace p.1),
                (xReachableBlockFactor (bn := bn) cpt X Y Z xX xZ *
                  yReachableBlockFactor (bn := bn) cpt X Y Z xY xZ) *
                    (residualBlockFactor (bn := bn) cpt X Y Z xU xZ *
                      conditioningBlockFactor (bn := bn) cpt X Y Z xZ) := by
                  simp [mul_assoc]
            _ =
              (xReachableBlockFactor (bn := bn) cpt X Y Z xX xZ *
                yReachableBlockFactor (bn := bn) cpt X Y Z xY xZ) *
                  ∑ xU : (∀ p : {v // v ∈ DSeparation.residualBlock bn.graph X Y Z},
                      bn.stateSpace p.1),
                    residualBlockFactor (bn := bn) cpt X Y Z xU xZ *
                      conditioningBlockFactor (bn := bn) cpt X Y Z xZ := by
                        rw [← Finset.mul_sum]
            _ =
              xReachableBlockFactor (bn := bn) cpt X Y Z xX xZ *
                (yReachableBlockFactor (bn := bn) cpt X Y Z xY xZ *
                  ∑ xU : (∀ p : {v // v ∈ DSeparation.residualBlock bn.graph X Y Z},
                      bn.stateSpace p.1),
                    residualBlockFactor (bn := bn) cpt X Y Z xU xZ *
                      conditioningBlockFactor (bn := bn) cpt X Y Z xZ) := by
                        ac_rfl

/-- Summing the separated `X/Y/Z` block atom over all assignments to the
`Y`-reachable block yields the corresponding `X/Z` block atom. -/
theorem jointMeasure_xzBlock_eq_sum_blockConstraints
    [∀ v, MeasurableSingletonClass (bn.stateSpace v)]
    (cpt : bn.DiscreteCPT) (X Y Z : Set V)
    (xX : ∀ p : {v // v ∈ DSeparation.xReachableBlock bn.graph X Y Z}, bn.stateSpace p.1)
    (xZ : ∀ p : Z, bn.stateSpace p.1) :
    cpt.jointMeasure
      (eventOfConstraints (bn := bn)
          (constraintsOfRestrict (bn := bn)
            (DSeparation.xReachableBlock bn.graph X Y Z) xX)
        ∩
          eventOfConstraints (bn := bn)
            (constraintsOfRestrict (bn := bn) Z xZ))
      =
    ∑ xY : (∀ p : {v // v ∈ DSeparation.yReachableBlock bn.graph X Y Z}, bn.stateSpace p.1),
      cpt.jointMeasure
        (eventOfConstraints (bn := bn)
            (constraintsOfRestrict (bn := bn)
              (DSeparation.xReachableBlock bn.graph X Y Z) xX)
          ∩
            (eventOfConstraints (bn := bn)
              (constraintsOfRestrict (bn := bn)
                (DSeparation.yReachableBlock bn.graph X Y Z) xY)
            ∩
              eventOfConstraints (bn := bn)
                (constraintsOfRestrict (bn := bn) Z xZ))) := by
  classical
  let u : Set bn.JointSpace :=
    eventOfConstraints (bn := bn)
      (constraintsOfRestrict (bn := bn)
        (DSeparation.xReachableBlock bn.graph X Y Z) xX)
    ∩
      eventOfConstraints (bn := bn)
        (constraintsOfRestrict (bn := bn) Z xZ)
  have hu : MeasurableSet u := by
    exact (measurable_eventOfConstraints (bn := bn)
      (constraintsOfRestrict (bn := bn)
        (DSeparation.xReachableBlock bn.graph X Y Z) xX)).inter
      (measurable_eventOfConstraints (bn := bn)
        (constraintsOfRestrict (bn := bn) Z xZ))
  have hsum :=
    measure_vertices_preimage_eq_sum
      (bn := bn)
      (μ := cpt.jointMeasure.restrict u)
      (S := DSeparation.yReachableBlock bn.graph X Y Z)
      (T := (Set.univ :
        Set (∀ p : {v // v ∈ DSeparation.yReachableBlock bn.graph X Y Z},
          bn.stateSpace p.1)))
  have hpre_univ :
      (restrictToSet (bn := bn) (DSeparation.yReachableBlock bn.graph X Y Z)) ⁻¹'
          (Set.univ :
            Set (∀ p : {v // v ∈ DSeparation.yReachableBlock bn.graph X Y Z},
              bn.stateSpace p.1))
        =
      (Set.univ : Set bn.JointSpace) := by
    ext ω
    simp
  have hmeas_pre :
      MeasurableSet
        ((restrictToSet (bn := bn) (DSeparation.yReachableBlock bn.graph X Y Z)) ⁻¹'
          (Set.univ :
            Set (∀ p : {v // v ∈ DSeparation.yReachableBlock bn.graph X Y Z},
              bn.stateSpace p.1))) := by
    simp [hpre_univ]
  rw [Measure.restrict_apply hmeas_pre] at hsum
  simpa [u, hpre_univ, hu, Measure.restrict_apply,
    measurable_eventOfConstraints, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using hsum

/-- Summing the separated `X/Y/Z` block atom over all assignments to the
`X`-reachable block yields the corresponding `Y/Z` block atom. -/
theorem jointMeasure_yzBlock_eq_sum_blockConstraints
    [∀ v, MeasurableSingletonClass (bn.stateSpace v)]
    (cpt : bn.DiscreteCPT) (X Y Z : Set V)
    (xY : ∀ p : {v // v ∈ DSeparation.yReachableBlock bn.graph X Y Z}, bn.stateSpace p.1)
    (xZ : ∀ p : Z, bn.stateSpace p.1) :
    cpt.jointMeasure
      (eventOfConstraints (bn := bn)
          (constraintsOfRestrict (bn := bn)
            (DSeparation.yReachableBlock bn.graph X Y Z) xY)
        ∩
          eventOfConstraints (bn := bn)
            (constraintsOfRestrict (bn := bn) Z xZ))
      =
    ∑ xX : (∀ p : {v // v ∈ DSeparation.xReachableBlock bn.graph X Y Z}, bn.stateSpace p.1),
      cpt.jointMeasure
        (eventOfConstraints (bn := bn)
            (constraintsOfRestrict (bn := bn)
              (DSeparation.xReachableBlock bn.graph X Y Z) xX)
          ∩
            (eventOfConstraints (bn := bn)
              (constraintsOfRestrict (bn := bn)
                (DSeparation.yReachableBlock bn.graph X Y Z) xY)
            ∩
              eventOfConstraints (bn := bn)
                (constraintsOfRestrict (bn := bn) Z xZ))) := by
  classical
  let u : Set bn.JointSpace :=
    eventOfConstraints (bn := bn)
      (constraintsOfRestrict (bn := bn)
        (DSeparation.yReachableBlock bn.graph X Y Z) xY)
    ∩
      eventOfConstraints (bn := bn)
        (constraintsOfRestrict (bn := bn) Z xZ)
  have hu : MeasurableSet u := by
    exact (measurable_eventOfConstraints (bn := bn)
      (constraintsOfRestrict (bn := bn)
        (DSeparation.yReachableBlock bn.graph X Y Z) xY)).inter
      (measurable_eventOfConstraints (bn := bn)
        (constraintsOfRestrict (bn := bn) Z xZ))
  have hsum :=
    measure_vertices_preimage_eq_sum
      (bn := bn)
      (μ := cpt.jointMeasure.restrict u)
      (S := DSeparation.xReachableBlock bn.graph X Y Z)
      (T := (Set.univ :
        Set (∀ p : {v // v ∈ DSeparation.xReachableBlock bn.graph X Y Z},
          bn.stateSpace p.1)))
  have hpre_univ :
      (restrictToSet (bn := bn) (DSeparation.xReachableBlock bn.graph X Y Z)) ⁻¹'
          (Set.univ :
            Set (∀ p : {v // v ∈ DSeparation.xReachableBlock bn.graph X Y Z},
              bn.stateSpace p.1))
        =
      (Set.univ : Set bn.JointSpace) := by
    ext ω
    simp
  have hmeas_pre :
      MeasurableSet
        ((restrictToSet (bn := bn) (DSeparation.xReachableBlock bn.graph X Y Z)) ⁻¹'
          (Set.univ :
            Set (∀ p : {v // v ∈ DSeparation.xReachableBlock bn.graph X Y Z},
              bn.stateSpace p.1))) := by
    simp [hpre_univ]
  rw [Measure.restrict_apply hmeas_pre] at hsum
  simpa [u, hpre_univ, hu, Measure.restrict_apply,
    measurable_eventOfConstraints, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using hsum

/-- Summing the `X/Z` block atoms over all assignments to the `X`-reachable
block yields the pure conditioning atom. -/
theorem jointMeasure_zBlock_eq_sum_xzBlocks
    [∀ v, MeasurableSingletonClass (bn.stateSpace v)]
    (cpt : bn.DiscreteCPT) (X Y Z : Set V)
    (xZ : ∀ p : Z, bn.stateSpace p.1) :
    cpt.jointMeasure
      (eventOfConstraints (bn := bn)
        (constraintsOfRestrict (bn := bn) Z xZ))
      =
    ∑ xX : (∀ p : {v // v ∈ DSeparation.xReachableBlock bn.graph X Y Z}, bn.stateSpace p.1),
      cpt.jointMeasure
        (eventOfConstraints (bn := bn)
            (constraintsOfRestrict (bn := bn)
              (DSeparation.xReachableBlock bn.graph X Y Z) xX)
          ∩
            eventOfConstraints (bn := bn)
              (constraintsOfRestrict (bn := bn) Z xZ)) := by
  classical
  let u : Set bn.JointSpace :=
    eventOfConstraints (bn := bn)
      (constraintsOfRestrict (bn := bn) Z xZ)
  have hu : MeasurableSet u := by
    exact measurable_eventOfConstraints (bn := bn)
      (constraintsOfRestrict (bn := bn) Z xZ)
  have hsum :=
    measure_vertices_preimage_eq_sum
      (bn := bn)
      (μ := cpt.jointMeasure.restrict u)
      (S := DSeparation.xReachableBlock bn.graph X Y Z)
      (T := (Set.univ :
        Set (∀ p : {v // v ∈ DSeparation.xReachableBlock bn.graph X Y Z},
          bn.stateSpace p.1)))
  have hpre_univ :
      (restrictToSet (bn := bn) (DSeparation.xReachableBlock bn.graph X Y Z)) ⁻¹'
          (Set.univ :
            Set (∀ p : {v // v ∈ DSeparation.xReachableBlock bn.graph X Y Z},
              bn.stateSpace p.1))
        =
      (Set.univ : Set bn.JointSpace) := by
    ext ω
    simp
  have hmeas_pre :
      MeasurableSet
        ((restrictToSet (bn := bn) (DSeparation.xReachableBlock bn.graph X Y Z)) ⁻¹'
          (Set.univ :
            Set (∀ p : {v // v ∈ DSeparation.xReachableBlock bn.graph X Y Z},
              bn.stateSpace p.1))) := by
    simp [hpre_univ]
  rw [Measure.restrict_apply hmeas_pre] at hsum
  simpa [u, hpre_univ, hu, Measure.restrict_apply,
    measurable_eventOfConstraints, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using hsum

/-- Factored `X/Z` block-atom formula obtained by summing out the
`Y`-reachable block. -/
theorem jointMeasure_xzBlock_eq_factoredReachableSum
    [∀ v, MeasurableSingletonClass (bn.stateSpace v)]
    (cpt : bn.DiscreteCPT) (X Y Z : Set V)
    (hirr : ∀ v : V, ¬bn.graph.edges v v)
    (hXY : Disjoint X Y)
    (hSep : DSeparation.SeparatedInMoralAncestral bn.graph X Y Z)
    (xX : ∀ p : {v // v ∈ DSeparation.xReachableBlock bn.graph X Y Z}, bn.stateSpace p.1)
    (xZ : ∀ p : Z, bn.stateSpace p.1) :
    cpt.jointMeasure
      (eventOfConstraints (bn := bn)
          (constraintsOfRestrict (bn := bn)
            (DSeparation.xReachableBlock bn.graph X Y Z) xX)
        ∩
          eventOfConstraints (bn := bn)
            (constraintsOfRestrict (bn := bn) Z xZ))
      =
    xReachableBlockFactor (bn := bn) cpt X Y Z xX xZ *
      ∑ xY : (∀ p : {v // v ∈ DSeparation.yReachableBlock bn.graph X Y Z}, bn.stateSpace p.1),
        yReachableBlockFactor (bn := bn) cpt X Y Z xY xZ *
          ∑ xU : (∀ p : {v // v ∈ DSeparation.residualBlock bn.graph X Y Z}, bn.stateSpace p.1),
            residualBlockFactor (bn := bn) cpt X Y Z xU xZ *
              conditioningBlockFactor (bn := bn) cpt X Y Z xZ := by
  classical
  calc
    cpt.jointMeasure
        (eventOfConstraints (bn := bn)
            (constraintsOfRestrict (bn := bn)
              (DSeparation.xReachableBlock bn.graph X Y Z) xX)
          ∩
            eventOfConstraints (bn := bn)
              (constraintsOfRestrict (bn := bn) Z xZ))
        =
      ∑ xY : (∀ p : {v // v ∈ DSeparation.yReachableBlock bn.graph X Y Z}, bn.stateSpace p.1),
        cpt.jointMeasure
          (eventOfConstraints (bn := bn)
              (constraintsOfRestrict (bn := bn)
                (DSeparation.xReachableBlock bn.graph X Y Z) xX)
            ∩
              (eventOfConstraints (bn := bn)
                (constraintsOfRestrict (bn := bn)
                  (DSeparation.yReachableBlock bn.graph X Y Z) xY)
              ∩
                eventOfConstraints (bn := bn)
                  (constraintsOfRestrict (bn := bn) Z xZ))) := by
          exact jointMeasure_xzBlock_eq_sum_blockConstraints
            (bn := bn) (cpt := cpt) X Y Z xX xZ
    _ =
      ∑ xY : (∀ p : {v // v ∈ DSeparation.yReachableBlock bn.graph X Y Z}, bn.stateSpace p.1),
        xReachableBlockFactor (bn := bn) cpt X Y Z xX xZ *
          (yReachableBlockFactor (bn := bn) cpt X Y Z xY xZ *
            ∑ xU : (∀ p : {v // v ∈ DSeparation.residualBlock bn.graph X Y Z},
                bn.stateSpace p.1),
              residualBlockFactor (bn := bn) cpt X Y Z xU xZ *
                conditioningBlockFactor (bn := bn) cpt X Y Z xZ) := by
          refine Finset.sum_congr rfl ?_
          intro xY _
          exact jointMeasure_blockConstraint_eq_factoredResidualSum
            (bn := bn) (cpt := cpt) X Y Z hirr hXY hSep xX xY xZ
    _ =
      xReachableBlockFactor (bn := bn) cpt X Y Z xX xZ *
        ∑ xY : (∀ p : {v // v ∈ DSeparation.yReachableBlock bn.graph X Y Z}, bn.stateSpace p.1),
          yReachableBlockFactor (bn := bn) cpt X Y Z xY xZ *
            ∑ xU : (∀ p : {v // v ∈ DSeparation.residualBlock bn.graph X Y Z},
                bn.stateSpace p.1),
              residualBlockFactor (bn := bn) cpt X Y Z xU xZ *
                conditioningBlockFactor (bn := bn) cpt X Y Z xZ := by
          rw [← Finset.mul_sum]

/-- Factored `Y/Z` block-atom formula obtained by summing out the
`X`-reachable block. -/
theorem jointMeasure_yzBlock_eq_factoredReachableSum
    [∀ v, MeasurableSingletonClass (bn.stateSpace v)]
    (cpt : bn.DiscreteCPT) (X Y Z : Set V)
    (hirr : ∀ v : V, ¬bn.graph.edges v v)
    (hXY : Disjoint X Y)
    (hSep : DSeparation.SeparatedInMoralAncestral bn.graph X Y Z)
    (xY : ∀ p : {v // v ∈ DSeparation.yReachableBlock bn.graph X Y Z}, bn.stateSpace p.1)
    (xZ : ∀ p : Z, bn.stateSpace p.1) :
    cpt.jointMeasure
      (eventOfConstraints (bn := bn)
          (constraintsOfRestrict (bn := bn)
            (DSeparation.yReachableBlock bn.graph X Y Z) xY)
        ∩
          eventOfConstraints (bn := bn)
            (constraintsOfRestrict (bn := bn) Z xZ))
      =
    (∑ xX : (∀ p : {v // v ∈ DSeparation.xReachableBlock bn.graph X Y Z}, bn.stateSpace p.1),
        xReachableBlockFactor (bn := bn) cpt X Y Z xX xZ) *
      (yReachableBlockFactor (bn := bn) cpt X Y Z xY xZ *
        ∑ xU : (∀ p : {v // v ∈ DSeparation.residualBlock bn.graph X Y Z}, bn.stateSpace p.1),
          residualBlockFactor (bn := bn) cpt X Y Z xU xZ *
            conditioningBlockFactor (bn := bn) cpt X Y Z xZ) := by
  classical
  calc
    cpt.jointMeasure
        (eventOfConstraints (bn := bn)
            (constraintsOfRestrict (bn := bn)
              (DSeparation.yReachableBlock bn.graph X Y Z) xY)
          ∩
            eventOfConstraints (bn := bn)
              (constraintsOfRestrict (bn := bn) Z xZ))
        =
      ∑ xX : (∀ p : {v // v ∈ DSeparation.xReachableBlock bn.graph X Y Z}, bn.stateSpace p.1),
        cpt.jointMeasure
          (eventOfConstraints (bn := bn)
              (constraintsOfRestrict (bn := bn)
                (DSeparation.xReachableBlock bn.graph X Y Z) xX)
            ∩
              (eventOfConstraints (bn := bn)
                (constraintsOfRestrict (bn := bn)
                  (DSeparation.yReachableBlock bn.graph X Y Z) xY)
              ∩
                eventOfConstraints (bn := bn)
                  (constraintsOfRestrict (bn := bn) Z xZ))) := by
          exact jointMeasure_yzBlock_eq_sum_blockConstraints
            (bn := bn) (cpt := cpt) X Y Z xY xZ
    _ =
      ∑ xX : (∀ p : {v // v ∈ DSeparation.xReachableBlock bn.graph X Y Z}, bn.stateSpace p.1),
        xReachableBlockFactor (bn := bn) cpt X Y Z xX xZ *
          (yReachableBlockFactor (bn := bn) cpt X Y Z xY xZ *
            ∑ xU : (∀ p : {v // v ∈ DSeparation.residualBlock bn.graph X Y Z},
                bn.stateSpace p.1),
              residualBlockFactor (bn := bn) cpt X Y Z xU xZ *
                conditioningBlockFactor (bn := bn) cpt X Y Z xZ) := by
          refine Finset.sum_congr rfl ?_
          intro xX _
          exact jointMeasure_blockConstraint_eq_factoredResidualSum
            (bn := bn) (cpt := cpt) X Y Z hirr hXY hSep xX xY xZ
    _ =
      (∑ xX : (∀ p : {v // v ∈ DSeparation.xReachableBlock bn.graph X Y Z}, bn.stateSpace p.1),
          xReachableBlockFactor (bn := bn) cpt X Y Z xX xZ) *
        (yReachableBlockFactor (bn := bn) cpt X Y Z xY xZ *
          ∑ xU : (∀ p : {v // v ∈ DSeparation.residualBlock bn.graph X Y Z},
              bn.stateSpace p.1),
            residualBlockFactor (bn := bn) cpt X Y Z xU xZ *
              conditioningBlockFactor (bn := bn) cpt X Y Z xZ) := by
          rw [Finset.sum_mul]

/-- Factored pure conditioning-atom formula obtained by summing out the
`X`-reachable block from the `X/Z` factorization. -/
theorem jointMeasure_zBlock_eq_factoredReachableSum
    [∀ v, MeasurableSingletonClass (bn.stateSpace v)]
    (cpt : bn.DiscreteCPT) (X Y Z : Set V)
    (hirr : ∀ v : V, ¬bn.graph.edges v v)
    (hXY : Disjoint X Y)
    (hSep : DSeparation.SeparatedInMoralAncestral bn.graph X Y Z)
    (xZ : ∀ p : Z, bn.stateSpace p.1) :
    cpt.jointMeasure
      (eventOfConstraints (bn := bn)
        (constraintsOfRestrict (bn := bn) Z xZ))
      =
    (∑ xX : (∀ p : {v // v ∈ DSeparation.xReachableBlock bn.graph X Y Z}, bn.stateSpace p.1),
        xReachableBlockFactor (bn := bn) cpt X Y Z xX xZ) *
      ∑ xY : (∀ p : {v // v ∈ DSeparation.yReachableBlock bn.graph X Y Z}, bn.stateSpace p.1),
        yReachableBlockFactor (bn := bn) cpt X Y Z xY xZ *
          ∑ xU : (∀ p : {v // v ∈ DSeparation.residualBlock bn.graph X Y Z}, bn.stateSpace p.1),
            residualBlockFactor (bn := bn) cpt X Y Z xU xZ *
              conditioningBlockFactor (bn := bn) cpt X Y Z xZ := by
  classical
  calc
    cpt.jointMeasure
        (eventOfConstraints (bn := bn)
          (constraintsOfRestrict (bn := bn) Z xZ))
        =
      ∑ xX : (∀ p : {v // v ∈ DSeparation.xReachableBlock bn.graph X Y Z}, bn.stateSpace p.1),
        cpt.jointMeasure
          (eventOfConstraints (bn := bn)
              (constraintsOfRestrict (bn := bn)
                (DSeparation.xReachableBlock bn.graph X Y Z) xX)
            ∩
              eventOfConstraints (bn := bn)
                (constraintsOfRestrict (bn := bn) Z xZ)) := by
          exact jointMeasure_zBlock_eq_sum_xzBlocks
            (bn := bn) (cpt := cpt) X Y Z xZ
    _ =
      ∑ xX : (∀ p : {v // v ∈ DSeparation.xReachableBlock bn.graph X Y Z}, bn.stateSpace p.1),
        xReachableBlockFactor (bn := bn) cpt X Y Z xX xZ *
          ∑ xY : (∀ p : {v // v ∈ DSeparation.yReachableBlock bn.graph X Y Z}, bn.stateSpace p.1),
            yReachableBlockFactor (bn := bn) cpt X Y Z xY xZ *
              ∑ xU : (∀ p : {v // v ∈ DSeparation.residualBlock bn.graph X Y Z},
                  bn.stateSpace p.1),
                residualBlockFactor (bn := bn) cpt X Y Z xU xZ *
                  conditioningBlockFactor (bn := bn) cpt X Y Z xZ := by
          refine Finset.sum_congr rfl ?_
          intro xX _
          exact jointMeasure_xzBlock_eq_factoredReachableSum
            (bn := bn) (cpt := cpt) X Y Z hirr hXY hSep xX xZ
    _ =
      (∑ xX : (∀ p : {v // v ∈ DSeparation.xReachableBlock bn.graph X Y Z}, bn.stateSpace p.1),
          xReachableBlockFactor (bn := bn) cpt X Y Z xX xZ) *
        ∑ xY : (∀ p : {v // v ∈ DSeparation.yReachableBlock bn.graph X Y Z}, bn.stateSpace p.1),
          yReachableBlockFactor (bn := bn) cpt X Y Z xY xZ *
            ∑ xU : (∀ p : {v // v ∈ DSeparation.residualBlock bn.graph X Y Z},
                bn.stateSpace p.1),
              residualBlockFactor (bn := bn) cpt X Y Z xU xZ *
                conditioningBlockFactor (bn := bn) cpt X Y Z xZ := by
          rw [Finset.sum_mul]

/-- Atomic separated-block multiplication identity for a discrete CPT joint
measure. This is the event-level semantic heart of the disjoint-core d-separation
soundness bridge. -/
theorem jointMeasure_blockConstraint_mul_eq
    [∀ v, MeasurableSingletonClass (bn.stateSpace v)]
    (cpt : bn.DiscreteCPT) (X Y Z : Set V)
    (hirr : ∀ v : V, ¬bn.graph.edges v v)
    (hXY : Disjoint X Y)
    (hSep : DSeparation.SeparatedInMoralAncestral bn.graph X Y Z)
    (xX : ∀ p : {v // v ∈ DSeparation.xReachableBlock bn.graph X Y Z}, bn.stateSpace p.1)
    (xY : ∀ p : {v // v ∈ DSeparation.yReachableBlock bn.graph X Y Z}, bn.stateSpace p.1)
    (xZ : ∀ p : Z, bn.stateSpace p.1) :
    cpt.jointMeasure
      (eventOfConstraints (bn := bn)
          (constraintsOfRestrict (bn := bn)
            (DSeparation.xReachableBlock bn.graph X Y Z) xX)
        ∩
          (eventOfConstraints (bn := bn)
            (constraintsOfRestrict (bn := bn)
              (DSeparation.yReachableBlock bn.graph X Y Z) xY)
          ∩
            eventOfConstraints (bn := bn)
              (constraintsOfRestrict (bn := bn) Z xZ)))
      *
      cpt.jointMeasure
        (eventOfConstraints (bn := bn)
          (constraintsOfRestrict (bn := bn) Z xZ))
      =
    cpt.jointMeasure
      (eventOfConstraints (bn := bn)
          (constraintsOfRestrict (bn := bn)
            (DSeparation.xReachableBlock bn.graph X Y Z) xX)
        ∩
          eventOfConstraints (bn := bn)
            (constraintsOfRestrict (bn := bn) Z xZ))
      *
      cpt.jointMeasure
        (eventOfConstraints (bn := bn)
            (constraintsOfRestrict (bn := bn)
              (DSeparation.yReachableBlock bn.graph X Y Z) xY)
          ∩
            eventOfConstraints (bn := bn)
              (constraintsOfRestrict (bn := bn) Z xZ)) := by
  have hXYZ :=
    jointMeasure_blockConstraint_eq_factoredResidualSum
      (bn := bn) (cpt := cpt) X Y Z hirr hXY hSep xX xY xZ
  have hXZ :=
    jointMeasure_xzBlock_eq_factoredReachableSum
      (bn := bn) (cpt := cpt) X Y Z hirr hXY hSep xX xZ
  have hYZ :=
    jointMeasure_yzBlock_eq_factoredReachableSum
      (bn := bn) (cpt := cpt) X Y Z hirr hXY hSep xY xZ
  have hZ :=
    jointMeasure_zBlock_eq_factoredReachableSum
      (bn := bn) (cpt := cpt) X Y Z hirr hXY hSep xZ
  rw [hXYZ, hXZ, hYZ, hZ]
  ac_rfl

/-- A single pair of separated `X`- and `Y`-block atoms is conditionally
independent given the conditioning block `Z`. This packages the atomic
multiplication theorem into Mathlib's `CondIndepSet` API. -/
theorem jointMeasure_blockConstraint_condIndepSet
    [∀ v, MeasurableSingletonClass (bn.stateSpace v)]
    (cpt : bn.DiscreteCPT) (X Y Z : Set V)
    (hirr : ∀ v : V, ¬bn.graph.edges v v)
    (hXY : Disjoint X Y)
    (hSep : DSeparation.SeparatedInMoralAncestral bn.graph X Y Z)
    (xX : ∀ p : {v // v ∈ DSeparation.xReachableBlock bn.graph X Y Z}, bn.stateSpace p.1)
    (xY : ∀ p : {v // v ∈ DSeparation.yReachableBlock bn.graph X Y Z}, bn.stateSpace p.1) :
    ProbabilityTheory.CondIndepSet
      (m' := bn.measurableSpaceOfVertices Z)
      (hm' := measurableSpaceOfVertices_le (bn := bn) Z)
      (eventOfConstraints (bn := bn)
        (constraintsOfRestrict (bn := bn)
          (DSeparation.xReachableBlock bn.graph X Y Z) xX))
      (eventOfConstraints (bn := bn)
        (constraintsOfRestrict (bn := bn)
          (DSeparation.yReachableBlock bn.graph X Y Z) xY))
      cpt.jointMeasure := by
  classical
  let μ : Measure bn.JointSpace := cpt.jointMeasure
  let mZ : MeasurableSpace bn.JointSpace := bn.measurableSpaceOfVertices Z
  let hmZ : mZ ≤ MeasurableSpace.pi := measurableSpaceOfVertices_le (bn := bn) Z
  let sA : Set bn.JointSpace :=
    eventOfConstraints (bn := bn)
      (constraintsOfRestrict (bn := bn)
        (DSeparation.xReachableBlock bn.graph X Y Z) xX)
  let sC : Set bn.JointSpace :=
    eventOfConstraints (bn := bn)
      (constraintsOfRestrict (bn := bn)
        (DSeparation.yReachableBlock bn.graph X Y Z) xY)
  let atomZ : (∀ p : Z, bn.stateSpace p.1) → Set bn.JointSpace :=
    fun xZ =>
      eventOfConstraints (bn := bn)
        (constraintsOfRestrict (bn := bn) Z xZ)
  let fA : bn.JointSpace → ℝ := μ⟦sA | mZ⟧
  let fC : bn.JointSpace → ℝ := μ⟦sC | mZ⟧
  let fAC : bn.JointSpace → ℝ := μ⟦sA ∩ sC | mZ⟧
  have hsA : @MeasurableSet _ MeasurableSpace.pi sA := by
    exact measurable_eventOfConstraints (bn := bn)
      (constraintsOfRestrict (bn := bn)
        (DSeparation.xReachableBlock bn.graph X Y Z) xX)
  have hsC : @MeasurableSet _ MeasurableSpace.pi sC := by
    exact measurable_eventOfConstraints (bn := bn)
      (constraintsOfRestrict (bn := bn)
        (DSeparation.yReachableBlock bn.graph X Y Z) xY)
  rw [ProbabilityTheory.condIndepSet_iff
    (m' := mZ) (hm' := hmZ) (s := sA) (t := sC) hsA hsC (μ := μ)]
  let badAssignments : Set (∀ p : Z, bn.stateSpace p.1) :=
    {xZ | μ (atomZ xZ) = 0}
  let badSet : Set bn.JointSpace := (restrictToSet (bn := bn) Z) ⁻¹' badAssignments
  have hBad_zero : μ badSet = 0 := by
    rw [measure_vertices_preimage_eq_sum
      (bn := bn) (μ := μ) (S := Z) (T := badAssignments)]
    refine Finset.sum_eq_zero ?_
    intro xZ _
    by_cases hxZ : xZ ∈ badAssignments
    · simpa [badAssignments, atomZ, hxZ]
    · simp [badAssignments, atomZ, hxZ]
  refine (MeasureTheory.ae_iff).2 ?_
  refine MeasureTheory.measure_mono_null ?_ hBad_zero
  intro ω hω
  let xZ : ∀ p : Z, bn.stateSpace p.1 := restrictToSet (bn := bn) Z ω
  let sB : Set bn.JointSpace := atomZ xZ
  change xZ ∈ badAssignments
  by_contra hgood
  have hμB_ne : μ sB ≠ 0 := by
    simpa [badAssignments, atomZ, xZ, sB] using hgood
  have hsB_meas : @MeasurableSet _ MeasurableSpace.pi sB := by
    exact measurable_eventOfConstraints (bn := bn)
      (constraintsOfRestrict (bn := bn) Z xZ)
  have hsB_meas_mZ : MeasurableSet[mZ] sB := by
    simpa [mZ, atomZ, sB] using
      measurable_eventOfConstraints_constraintsOfRestrict_vertices
        (bn := bn) Z xZ
  have hAconst :
      (fun ω' => fA ω') =ᵐ[μ.restrict sB] fun _ => fA ω := by
    simpa [fA, mZ, μ, atomZ, sB, xZ] using
      condExp_ae_eq_const_on_constraintsOfRestrict
        (bn := bn) (μ := μ) (S := Z) (xS := xZ) (s := sA) (ω0 := ω) rfl
  have hCconst :
      (fun ω' => fC ω') =ᵐ[μ.restrict sB] fun _ => fC ω := by
    simpa [fC, mZ, μ, atomZ, sB, xZ] using
      condExp_ae_eq_const_on_constraintsOfRestrict
        (bn := bn) (μ := μ) (S := Z) (xS := xZ) (s := sC) (ω0 := ω) rfl
  have hACconst :
      (fun ω' => fAC ω') =ᵐ[μ.restrict sB] fun _ => fAC ω := by
    simpa [fAC, mZ, μ, atomZ, sB, xZ] using
      condExp_ae_eq_const_on_constraintsOfRestrict
        (bn := bn) (μ := μ) (S := Z) (xS := xZ) (s := sA ∩ sC) (ω0 := ω) rfl
  haveI : SigmaFinite (μ.trim hmZ) :=
    sigmaFinite_trim_of_le (bn := bn) (μ := μ) (m' := mZ) hmZ
  have hAint :
      μ.real (sA ∩ sB) = fA ω * μ.real sB := by
    exact real_inter_eq_condExp_const (bn := bn) (μ := μ) (m' := mZ)
      (hm' := hmZ) (sX := sA) (sB := sB) hsA hsB_meas_mZ hsB_meas
      (ω0 := ω) hAconst
  have hCint :
      μ.real (sC ∩ sB) = fC ω * μ.real sB := by
    exact real_inter_eq_condExp_const (bn := bn) (μ := μ) (m' := mZ)
      (hm' := hmZ) (sX := sC) (sB := sB) hsC hsB_meas_mZ hsB_meas
      (ω0 := ω) hCconst
  have hACint :
      μ.real ((sA ∩ sC) ∩ sB) = fAC ω * μ.real sB := by
    exact real_inter_eq_condExp_const (bn := bn) (μ := μ) (m' := mZ)
      (hm' := hmZ) (sX := sA ∩ sC) (sB := sB) (hsA.inter hsC) hsB_meas_mZ hsB_meas
      (ω0 := ω) hACconst
  have hmul :=
    jointMeasure_blockConstraint_mul_eq
      (bn := bn) (cpt := cpt) X Y Z hirr hXY hSep xX xY xZ
  have hmul_real :
      μ.real ((sA ∩ sC) ∩ sB) * μ.real sB =
        μ.real (sA ∩ sB) * μ.real (sC ∩ sB) := by
    have htoReal := congrArg ENNReal.toReal hmul
    simpa [μ, sA, sB, sC, atomZ, Measure.real, ENNReal.toReal_mul,
      MeasureTheory.measure_ne_top (μ := μ) (s := ((sA ∩ sC) ∩ sB)),
      MeasureTheory.measure_ne_top (μ := μ) (s := sB),
      MeasureTheory.measure_ne_top (μ := μ) (s := (sA ∩ sB)),
      MeasureTheory.measure_ne_top (μ := μ) (s := (sC ∩ sB)),
      Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using htoReal
  have hμB_real_ne : μ.real sB ≠ 0 := by
    simp only [Measure.real, ENNReal.toReal_ne_zero]
    exact ⟨hμB_ne, MeasureTheory.measure_ne_top (μ := μ) (s := sB)⟩
  have hconst_eq : fAC ω = fA ω * fC ω := by
    have hcalc :
        fAC ω * (μ.real sB * μ.real sB) =
          (fA ω * fC ω) * (μ.real sB * μ.real sB) := by
      calc
        fAC ω * (μ.real sB * μ.real sB)
            = (fAC ω * μ.real sB) * μ.real sB := by ring
        _ = μ.real ((sA ∩ sC) ∩ sB) * μ.real sB := by rw [hACint]
        _ = μ.real (sA ∩ sB) * μ.real (sC ∩ sB) := hmul_real
        _ = (fA ω * μ.real sB) * (fC ω * μ.real sB) := by rw [hAint, hCint]
        _ = (fA ω * fC ω) * (μ.real sB * μ.real sB) := by ring
    have hsq_ne : μ.real sB * μ.real sB ≠ 0 :=
      mul_ne_zero hμB_real_ne hμB_real_ne
    exact mul_right_cancel₀ hsq_ne hcalc
  exact hω hconst_eq


end Mettapedia.ProbabilityTheory.BayesianNetworks.DiscreteLocalMarkov
