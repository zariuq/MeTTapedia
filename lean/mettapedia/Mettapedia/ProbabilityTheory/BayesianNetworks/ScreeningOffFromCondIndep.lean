import Mettapedia.ProbabilityTheory.BayesianNetworks.DSeparationSoundness

open MeasureTheory ProbabilityTheory

namespace Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (bn : BayesianNetwork V)
variable [∀ v : V, StandardBorelSpace (bn.stateSpace v)]
variable [StandardBorelSpace bn.JointSpace]
variable (μ : Measure bn.JointSpace) [IsFiniteMeasure μ]

abbrev CondIndepOn (A B C : V) : Prop :=
  ProbabilityTheory.CondIndep
    (m' := bn.measurableSpaceOfVertices ({B} : Set V))
    (m₁ := bn.measurableSpaceOfVertices ({A} : Set V))
    (m₂ := bn.measurableSpaceOfVertices ({C} : Set V))
    (hm' := measurableSpaceOfVertices_le (bn := bn) ({B} : Set V))
    μ

omit [Fintype V] [DecidableEq V] [∀ v : V, StandardBorelSpace (bn.stateSpace v)] in
lemma screening_const_eq_of_ae_chain
    {sB : Set bn.JointSpace}
    {condA condC condAC : bn.JointSpace → ℝ}
    {ω0 : bn.JointSpace}
    (hACconst_ae : (fun ω => condAC ω) =ᵐ[μ.restrict sB] fun _ => condAC ω0)
    (hcondR : (fun ω => condAC ω) =ᵐ[μ.restrict sB] fun ω => condA ω * condC ω)
    (hAconst_ae : (fun ω => condA ω) =ᵐ[μ.restrict sB] fun _ => condA ω0)
    (hCconst_ae : (fun ω => condC ω) =ᵐ[μ.restrict sB] fun _ => condC ω0)
    (hB0 : μ sB ≠ 0) :
    condAC ω0 = condA ω0 * condC ω0 := by
  have hProdConst :
      (fun ω => condA ω * condC ω) =ᵐ[μ.restrict sB]
        fun _ => condA ω0 * condC ω0 := by
    filter_upwards [hAconst_ae, hCconst_ae] with ω hA hC
    simp [hA, hC]
  have hConstEqAE :
      (fun _ : bn.JointSpace => condAC ω0) =ᵐ[μ.restrict sB]
        (fun _ => condA ω0 * condC ω0) := by
    calc
      (fun _ : bn.JointSpace => condAC ω0) =ᵐ[μ.restrict sB] (fun ω => condAC ω) := by
        exact hACconst_ae.symm
      _ =ᵐ[μ.restrict sB] (fun ω => condA ω * condC ω) := hcondR
      _ =ᵐ[μ.restrict sB] (fun _ => condA ω0 * condC ω0) := hProdConst
  exact ae_const_eq_of_restrict_ne_zero (bn := bn) (μ := μ) (s := sB) hB0 hConstEqAE

omit [Fintype V] [DecidableEq V] [∀ v : V, StandardBorelSpace (bn.stateSpace v)] in
lemma real_inter_eq_const_mul_of_setIntegral
    (sX sB : Set bn.JointSpace)
    (hsX : @MeasurableSet bn.JointSpace (MeasurableSpace.pi) sX)
    (hsB : @MeasurableSet bn.JointSpace (MeasurableSpace.pi) sB)
    {condX : bn.JointSpace → ℝ}
    {ω0 : bn.JointSpace}
    (hset :
      ∫ x in sB, condX x ∂μ =
        ∫ x in sB, (sX.indicator fun _ : bn.JointSpace => (1 : ℝ)) x ∂μ)
    (hconst_ae : (fun ω => condX ω) =ᵐ[μ.restrict sB] fun _ => condX ω0) :
    μ.real (sX ∩ sB) = condX ω0 * μ.real sB := by
  have hconst_int :
      ∫ x in sB, condX x ∂μ =
        condX ω0 * μ.real sB :=
    setIntegral_const_on (bn := bn) (μ := μ) (s := sB) hsB (condX ω0) hconst_ae
  have hInt :
      ∫ x in sB, (sX.indicator fun _ : bn.JointSpace => (1 : ℝ)) x ∂μ =
        μ.real (sX ∩ sB) := by
    calc
      ∫ x in sB, (sX.indicator fun _ : bn.JointSpace => (1 : ℝ)) x ∂μ
          = ∫ x in sB ∩ sX, (fun _ : bn.JointSpace => (1 : ℝ)) x ∂μ := by
              simpa using
                (MeasureTheory.setIntegral_indicator (μ := μ)
                  (s := sB) (t := sX) (f := fun _ : bn.JointSpace => (1 : ℝ)) hsX)
      _ = μ.real (sB ∩ sX) := by
            simpa using (MeasureTheory.setIntegral_const (μ := μ) (s := sB ∩ sX) (c := (1 : ℝ)))
      _ = μ.real (sX ∩ sB) := by
            simp [Set.inter_comm]
  calc
    μ.real (sX ∩ sB) =
        ∫ x in sB, (sX.indicator fun _ : bn.JointSpace => (1 : ℝ)) x ∂μ := by
          symm
          exact hInt
    _ = ∫ x in sB, condX x ∂μ := by
          symm
          exact hset
    _ = condX ω0 * μ.real sB := hconst_int

omit [Fintype V] [DecidableEq V] [∀ v : V, StandardBorelSpace (bn.stateSpace v)] in
lemma real_inter_eq_condExp_const
    (m' : MeasurableSpace bn.JointSpace)
    (hm' : m' ≤ (MeasurableSpace.pi : MeasurableSpace bn.JointSpace))
    [SigmaFinite (μ.trim hm')]
    (sX sB : Set bn.JointSpace)
    (hsX : @MeasurableSet bn.JointSpace (MeasurableSpace.pi) sX)
    (hsB_meas_m' : MeasurableSet[m'] sB)
    (hsB_meas : @MeasurableSet bn.JointSpace (MeasurableSpace.pi) sB)
    {ω0 : bn.JointSpace}
    (hconst_ae :
      (fun ω => MeasureTheory.condExp m' μ (sX.indicator (fun _ : bn.JointSpace => (1 : ℝ))) ω)
        =ᵐ[μ.restrict sB]
      (fun _ => MeasureTheory.condExp m' μ (sX.indicator (fun _ : bn.JointSpace => (1 : ℝ))) ω0)) :
    μ.real (sX ∩ sB) =
      (MeasureTheory.condExp m' μ (sX.indicator (fun _ : bn.JointSpace => (1 : ℝ))) ω0) * μ.real sB := by
  let fX : bn.JointSpace → ℝ := sX.indicator (fun _ : bn.JointSpace => (1 : ℝ))
  have hfX : Integrable fX μ := by
    simpa [fX] using (integrable_const (1 : ℝ)).indicator hsX
  have hset :
      ∫ x in sB, MeasureTheory.condExp m' μ fX x ∂μ =
        ∫ x in sB, fX x ∂μ := by
    simpa [fX] using
      (setIntegral_condExp (hm := hm') (μ := μ) (f := fX) hfX hsB_meas_m')
  exact real_inter_eq_const_mul_of_setIntegral (bn := bn) (μ := μ)
    (sX := sX) (sB := sB) hsX hsB_meas hset (by simpa [fX] using hconst_ae)

lemma ennreal_mul_eq_of_real_mul_eq
    {a b c d : ENNReal}
    (hreal : a.toReal * b.toReal = c.toReal * d.toReal)
    (ha : a ≠ ⊤) (hb : b ≠ ⊤) (hc : c ≠ ⊤) (hd : d ≠ ⊤) :
    a * b = c * d := by
  have htoReal :
      (a * b).toReal = (c * d).toReal := by
    simpa [ENNReal.toReal_mul, ha, hb, hc, hd] using hreal
  exact (ENNReal.toReal_eq_toReal_iff' (ENNReal.mul_ne_top ha hb) (ENNReal.mul_ne_top hc hd)).1 htoReal

omit [Fintype V] [DecidableEq V] [∀ v : V, StandardBorelSpace (bn.stateSpace v)] in
lemma real_screening_mul_eq
    (sA sB sC : Set bn.JointSpace)
    {condA condC condAC : bn.JointSpace → ℝ}
    {ω0 : bn.JointSpace}
    (hAint : μ.real (sA ∩ sB) = condA ω0 * μ.real sB)
    (hCint : μ.real (sC ∩ sB) = condC ω0 * μ.real sB)
    (hACint : μ.real ((sA ∩ sC) ∩ sB) = condAC ω0 * μ.real sB)
    (hconst_eq : μ sB ≠ 0 → condAC ω0 = condA ω0 * condC ω0) :
    μ.real ((sA ∩ sC) ∩ sB) * μ.real sB =
      μ.real (sA ∩ sB) * μ.real (sC ∩ sB) := by
  by_cases hB0 : μ sB = 0
  · have hA0 : μ (sA ∩ sB) = 0 := by
      apply MeasureTheory.measure_mono_null (s := sA ∩ sB) (t := sB) ?_ hB0
      intro ω hω
      exact hω.2
    have hC0 : μ (sC ∩ sB) = 0 := by
      apply MeasureTheory.measure_mono_null (s := sC ∩ sB) (t := sB) ?_ hB0
      intro ω hω
      exact hω.2
    have hAC0 : μ ((sA ∩ sC) ∩ sB) = 0 := by
      apply MeasureTheory.measure_mono_null (s := (sA ∩ sC) ∩ sB) (t := sB) ?_ hB0
      intro ω hω
      exact hω.2
    simp [Measure.real, hB0, hA0, hC0, hAC0]
  · calc
      μ.real ((sA ∩ sC) ∩ sB) * μ.real sB
          = (condAC ω0 * μ.real sB) * μ.real sB := by
                simp [hACint]
      _ = (condA ω0 * μ.real sB) * (condC ω0 * μ.real sB) := by
            simp [hconst_eq hB0, mul_comm, mul_left_comm, mul_assoc]
      _ = μ.real (sA ∩ sB) * μ.real (sC ∩ sB) := by
            simp [hAint, hCint, mul_comm, mul_left_comm, mul_assoc]

omit [Fintype V] [DecidableEq V] [∀ v : V, StandardBorelSpace (bn.stateSpace v)] in
lemma condIndep_mul_cond_core
    [IsProbabilityMeasure μ]
    (m' : MeasurableSpace bn.JointSpace)
    (hm' : m' ≤ (MeasurableSpace.pi : MeasurableSpace bn.JointSpace))
    (sA sB sC : Set bn.JointSpace)
    (hsA : @MeasurableSet bn.JointSpace (MeasurableSpace.pi) sA)
    (hsC : @MeasurableSet bn.JointSpace (MeasurableSpace.pi) sC)
    (hsB_meas_m' : MeasurableSet[m'] sB)
    (hsB_meas : @MeasurableSet bn.JointSpace (MeasurableSpace.pi) sB)
    (hcond' :
      μ⟦sA ∩ sC | m'⟧ =ᵐ[μ] (μ⟦sA | m'⟧) * (μ⟦sC | m'⟧))
    (ω0 : bn.JointSpace)
    (hAconst_ae :
      (fun ω => μ⟦sA | m'⟧ ω) =ᵐ[μ.restrict sB] fun _ => μ⟦sA | m'⟧ ω0)
    (hCconst_ae :
      (fun ω => μ⟦sC | m'⟧ ω) =ᵐ[μ.restrict sB] fun _ => μ⟦sC | m'⟧ ω0)
    (hACconst_ae :
      (fun ω => μ⟦sA ∩ sC | m'⟧ ω) =ᵐ[μ.restrict sB] fun _ => μ⟦sA ∩ sC | m'⟧ ω0) :
    μ ((sA ∩ sC) ∩ sB) * μ sB = μ (sA ∩ sB) * μ (sC ∩ sB) := by
  have hcondR :
      (fun ω => μ⟦sA ∩ sC | m'⟧ ω) =ᵐ[μ.restrict sB]
        fun ω => μ⟦sA | m'⟧ ω * μ⟦sC | m'⟧ ω := by
    exact ae_restrict_of_ae hcond'
  have hconst_eq (hB0 : μ sB ≠ 0) :
      μ⟦sA ∩ sC | m'⟧ ω0 = μ⟦sA | m'⟧ ω0 * μ⟦sC | m'⟧ ω0 := by
    exact screening_const_eq_of_ae_chain (bn := bn) (μ := μ)
      (hACconst_ae := hACconst_ae) (hcondR := hcondR)
      (hAconst_ae := hAconst_ae) (hCconst_ae := hCconst_ae) hB0
  haveI : SigmaFinite (μ.trim hm') :=
    sigmaFinite_trim_of_le (bn := bn) (μ := μ) (m' := m') hm'
  have hAint :
      μ.real (sA ∩ sB) = μ⟦sA | m'⟧ ω0 * μ.real sB := by
    exact real_inter_eq_condExp_const (bn := bn) (μ := μ) (m' := m')
      (hm' := hm') (sX := sA) (sB := sB) hsA hsB_meas_m' hsB_meas
      (ω0 := ω0) hAconst_ae
  have hCint :
      μ.real (sC ∩ sB) = μ⟦sC | m'⟧ ω0 * μ.real sB := by
    exact real_inter_eq_condExp_const (bn := bn) (μ := μ) (m' := m')
      (hm' := hm') (sX := sC) (sB := sB) hsC hsB_meas_m' hsB_meas
      (ω0 := ω0) hCconst_ae
  have hACint :
      μ.real ((sA ∩ sC) ∩ sB) = μ⟦sA ∩ sC | m'⟧ ω0 * μ.real sB := by
    exact real_inter_eq_condExp_const (bn := bn) (μ := μ) (m' := m')
      (hm' := hm') (sX := sA ∩ sC) (sB := sB) (hsA.inter hsC) hsB_meas_m' hsB_meas
      (ω0 := ω0) hACconst_ae
  have hreal :
      μ.real ((sA ∩ sC) ∩ sB) * μ.real sB =
        μ.real (sA ∩ sB) * μ.real (sC ∩ sB) := by
    exact real_screening_mul_eq (bn := bn) (μ := μ)
      (sA := sA) (sB := sB) (sC := sC)
      (hAint := hAint) (hCint := hCint) (hACint := hACint)
      (hconst_eq := hconst_eq)
  have htoReal :
      (μ ((sA ∩ sC) ∩ sB)).toReal * (μ sB).toReal =
        (μ (sA ∩ sB)).toReal * (μ (sC ∩ sB)).toReal := by
    simpa [Measure.real, ENNReal.toReal_mul] using hreal
  exact ennreal_mul_eq_of_real_mul_eq htoReal
    (MeasureTheory.measure_ne_top (μ := μ) (s := (sA ∩ sC) ∩ sB))
    (MeasureTheory.measure_ne_top (μ := μ) (s := sB))
    (MeasureTheory.measure_ne_top (μ := μ) (s := sA ∩ sB))
    (MeasureTheory.measure_ne_top (μ := μ) (s := sC ∩ sB))

set_option maxHeartbeats 10000000 in
theorem condIndep_eventEq_mul_cond
    [IsProbabilityMeasure μ]
    [∀ v, Inhabited (bn.stateSpace v)]
    [∀ v, MeasurableSingletonClass (bn.stateSpace v)]
    (A B C : V)
    (valA : bn.stateSpace A) (valB : bn.stateSpace B) (valC : bn.stateSpace C)
    (hci : CondIndepOn (bn := bn) (μ := μ) A B C) :
    μ (eventEq (bn := bn) A valA ∩
        eventEq (bn := bn) C valC ∩
        eventEq (bn := bn) B valB) *
      μ (eventEq (bn := bn) B valB) =
      μ (eventEq (bn := bn) A valA ∩
        eventEq (bn := bn) B valB) *
      μ (eventEq (bn := bn) C valC ∩
        eventEq (bn := bn) B valB) := by
  classical
  let sA : Set bn.JointSpace := eventEq (bn := bn) A valA
  let sB : Set bn.JointSpace := eventEq (bn := bn) B valB
  let sC : Set bn.JointSpace := eventEq (bn := bn) C valC
  let m' := bn.measurableSpaceOfVertices ({B} : Set V)
  have hm' : m' ≤ (MeasurableSpace.pi : MeasurableSpace bn.JointSpace) :=
    measurableSpaceOfVertices_le (bn := bn) ({B} : Set V)
  have hsB_meas_m' : MeasurableSet[m'] sB := by
    simpa [m'] using measurable_eventEq_vertices (bn := bn) B valB
  have hsB_meas : @MeasurableSet bn.JointSpace (MeasurableSpace.pi) sB := by
    simpa [sB] using measurable_eventEq (bn := bn) B valB
  have hcond :=
    (condIndep_iff
      (m' := m')
      (m₁ := bn.measurableSpaceOfVertices ({A} : Set V))
      (m₂ := bn.measurableSpaceOfVertices ({C} : Set V))
      (mΩ := (by infer_instance : MeasurableSpace bn.JointSpace))
      (hm' := hm')
      (hm₁ := measurableSpaceOfVertices_le (bn := bn) ({A} : Set V))
      (hm₂ := measurableSpaceOfVertices_le (bn := bn) ({C} : Set V))
      (μ := μ)).1 hci
  have hAmeas :
      MeasurableSet[bn.measurableSpaceOfVertices ({A} : Set V)] sA := by
    simpa using measurable_eventEq_vertices (bn := bn) A valA
  have hCmeas :
      MeasurableSet[bn.measurableSpaceOfVertices ({C} : Set V)] sC := by
    simpa using measurable_eventEq_vertices (bn := bn) C valC
  have hcond' :
      μ⟦sA ∩ sC | m'⟧ =ᵐ[μ] (μ⟦sA | m'⟧) * (μ⟦sC | m'⟧) := by
    simpa [sA, sC, m'] using hcond sA sC hAmeas hCmeas
  let omega0 : bn.JointSpace :=
    fun v => if h : v = B then (by cases h; exact valB) else default
  have hAconst_ae :
      (fun ω => μ⟦sA | m'⟧ ω) =ᵐ[μ.restrict sB] fun _ => μ⟦sA | m'⟧ omega0 := by
    simpa [sA, sB, m', omega0] using
      (condExp_ae_eq_const_on_eventEq (bn := bn) (μ := μ)
        (B := B) (valB := valB) (s := sA) (ω0 := omega0))
  have hCconst_ae :
      (fun ω => μ⟦sC | m'⟧ ω) =ᵐ[μ.restrict sB] fun _ => μ⟦sC | m'⟧ omega0 := by
    simpa [sC, sB, m', omega0] using
      (condExp_ae_eq_const_on_eventEq (bn := bn) (μ := μ)
        (B := B) (valB := valB) (s := sC) (ω0 := omega0))
  have hACconst_ae :
      (fun ω => μ⟦sA ∩ sC | m'⟧ ω) =ᵐ[μ.restrict sB] fun _ => μ⟦sA ∩ sC | m'⟧ omega0 := by
    simpa [sA, sC, sB, m', omega0] using
      (condExp_ae_eq_const_on_eventEq (bn := bn) (μ := μ)
        (B := B) (valB := valB) (s := sA ∩ sC) (ω0 := omega0))
  have hmul :=
    condIndep_mul_cond_core (bn := bn) (μ := μ)
      (m' := m') (hm' := hm')
      (sA := sA) (sB := sB) (sC := sC)
      (hsA := measurable_eventEq (bn := bn) A valA)
      (hsC := measurable_eventEq (bn := bn) C valC)
      (hsB_meas_m' := hsB_meas_m') (hsB_meas := hsB_meas)
      (hcond' := hcond') (ω0 := omega0)
      (hAconst_ae := hAconst_ae) (hCconst_ae := hCconst_ae)
      (hACconst_ae := hACconst_ae)
  simpa [sA, sB, sC, Set.inter_assoc] using hmul

end Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork
