import Mettapedia.ProbabilityTheory.BayesianNetworks.DiscreteLocalMarkov.BlockFactorization

/-!
# Conditional masses from conditional independence

`CondIndepVertices` is a statement about σ-algebras. On a finite discrete
joint it yields an equality of atomic conditional masses: when the mass of
the covariate together with the conditioning set is positive,

`P(y | z, w) = P(y | w)`.

The atoms are the joint-measure masses of coordinate assignments, which are
the sums of the joint weight over those assignments.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (bn : BayesianNetwork V)
variable [∀ v : V, Fintype (bn.stateSpace v)]
variable [∀ v : V, Inhabited (bn.stateSpace v)]
variable [∀ v : V, MeasurableSingletonClass (bn.stateSpace v)]
variable [∀ v : V, StandardBorelSpace (bn.stateSpace v)]
variable [StandardBorelSpace bn.JointSpace]

open Mettapedia.ProbabilityTheory.BayesianNetworks.DiscreteLocalMarkov

/-- A configuration that carries `xS` on `S` and the default elsewhere. -/
def realizeAssign (S : Finset V)
    (xS : ∀ p : ((S : Finset V) : Set V), bn.stateSpace p.1) : bn.JointSpace :=
  fun v => if hv : v ∈ S then xS ⟨v, Finset.mem_coe.mpr hv⟩ else default

omit [Fintype V] [(v : V) → Fintype (bn.stateSpace v)]
  [∀ v : V, MeasurableSingletonClass (bn.stateSpace v)]
  [∀ v : V, StandardBorelSpace (bn.stateSpace v)]
  [StandardBorelSpace bn.JointSpace] in
lemma restrict_realizeAssign (S : Finset V)
    (xS : ∀ p : ((S : Finset V) : Set V), bn.stateSpace p.1) :
    restrictToSet (bn := bn) (S : Set V) (realizeAssign (bn := bn) S xS) = xS := by
  ext p
  have hp : p.1 ∈ S := Finset.mem_coe.mp p.property
  simp [restrictToSet, realizeAssign, hp]

/-- The atom on which the coordinates in `S` equal `xS`. -/
def assignEvent (S : Finset V)
    (xS : ∀ p : ((S : Finset V) : Set V), bn.stateSpace p.1) : Set bn.JointSpace :=
  eventOfConstraints (bn := bn)
    (constraintsOfRestrict (bn := bn) (S : Set V) xS)

omit [StandardBorelSpace bn.JointSpace] in
lemma assignEvent_measurable_vertices (S : Finset V)
    (xS : ∀ p : ((S : Finset V) : Set V), bn.stateSpace p.1) :
    MeasurableSet[bn.measurableSpaceOfVertices (S : Set V)]
      (assignEvent (bn := bn) S xS) :=
  measurable_eventOfConstraints_constraintsOfRestrict_vertices
    (bn := bn) (S : Set V) xS

omit [DecidableEq V] [(v : V) → Fintype (bn.stateSpace v)]
  [(v : V) → Inhabited (bn.stateSpace v)]
  [∀ v : V, StandardBorelSpace (bn.stateSpace v)]
  [StandardBorelSpace bn.JointSpace] in
lemma assignEvent_measurable (S : Finset V)
    (xS : ∀ p : ((S : Finset V) : Set V), bn.stateSpace p.1) :
    MeasurableSet (assignEvent (bn := bn) S xS) :=
  measurable_eventOfConstraints (bn := bn)
    (constraintsOfRestrict (bn := bn) (S : Set V) xS)

/-- Conditional independence gives the atomic product
`P(y, z, w) P(w) = P(y, w) P(z, w)`. -/
theorem condIndepVertices_atom_mul
    (μ : Measure bn.JointSpace) [IsProbabilityMeasure μ]
    (X Z W : Finset V)
    (xX : ∀ p : ((X : Finset V) : Set V), bn.stateSpace p.1)
    (xZ : ∀ p : ((Z : Finset V) : Set V), bn.stateSpace p.1)
    (xW : ∀ p : ((W : Finset V) : Set V), bn.stateSpace p.1)
    (h : CondIndepVertices bn μ (X : Set V) (Z : Set V) (W : Set V)) :
    μ (assignEvent (bn := bn) X xX ∩ assignEvent (bn := bn) Z xZ ∩
        assignEvent (bn := bn) W xW) *
      μ (assignEvent (bn := bn) W xW) =
    μ (assignEvent (bn := bn) X xX ∩ assignEvent (bn := bn) W xW) *
      μ (assignEvent (bn := bn) Z xZ ∩ assignEvent (bn := bn) W xW) := by
  let sX := assignEvent (bn := bn) X xX
  let sZ := assignEvent (bn := bn) Z xZ
  let sW := assignEvent (bn := bn) W xW
  let m' := bn.measurableSpaceOfVertices (W : Set V)
  let hm' := measurableSpaceOfVertices_le (bn := bn) (W : Set V)
  unfold CondIndepVertices at h
  have hci :=
    (condIndep_iff
      (m' := m') (m₁ := bn.measurableSpaceOfVertices (X : Set V))
      (m₂ := bn.measurableSpaceOfVertices (Z : Set V))
      (hm' := hm')
      (hm₁ := measurableSpaceOfVertices_le (bn := bn) (X : Set V))
      (hm₂ := measurableSpaceOfVertices_le (bn := bn) (Z : Set V))
      (μ := μ)).1 h
  have hcond :=
    hci sX sZ (assignEvent_measurable_vertices (bn := bn) X xX)
      (assignEvent_measurable_vertices (bn := bn) Z xZ)
  let ω0 : bn.JointSpace := realizeAssign (bn := bn) W xW
  have hω0 := restrict_realizeAssign (bn := bn) W xW
  have hXconst :=
    condExp_ae_eq_const_on_constraintsOfRestrict (bn := bn) (μ := μ)
      (W : Set V) xW sX (ω0 := ω0) hω0
  have hZconst :=
    condExp_ae_eq_const_on_constraintsOfRestrict (bn := bn) (μ := μ)
      (W : Set V) xW sZ (ω0 := ω0) hω0
  have hXZconst :=
    condExp_ae_eq_const_on_constraintsOfRestrict (bn := bn) (μ := μ)
      (W : Set V) xW (sX ∩ sZ) (ω0 := ω0) hω0
  exact condIndep_mul_cond_core (bn := bn) (μ := μ)
    (m' := m') (hm' := hm')
    (sA := sX) (sB := sW) (sC := sZ)
    (hsA := assignEvent_measurable (bn := bn) X xX)
    (hsC := assignEvent_measurable (bn := bn) Z xZ)
    (hsB_meas_m' := assignEvent_measurable_vertices (bn := bn) W xW)
    (hsB_meas := assignEvent_measurable (bn := bn) W xW)
    (hcond' := by simpa [m', sX, sZ] using hcond)
    (ω0 := ω0)
    (hAconst_ae := by simpa [m', sX, sW, assignEvent] using hXconst)
    (hCconst_ae := by simpa [m', sZ, sW, assignEvent] using hZconst)
    (hACconst_ae := by simpa [m', sX, sZ, sW, assignEvent] using hXZconst)

/-- Cancel a common positive finite factor in `ℝ≥0∞`. -/
lemma ennreal_div_eq_of_cross_mul {a b c d : ℝ≥0∞}
    (h : a * c = b * d) (hd0 : d ≠ 0) (hdt : d ≠ ⊤) (hc0 : c ≠ 0) (hct : c ≠ ⊤) :
    a / d = b / c := by
  have hdc0 : d * c ≠ 0 := by
    intro h0
    rcases mul_eq_zero.mp h0 with hd | hc
    · exact hd0 hd
    · exact hc0 hc
  have hdct : d * c ≠ ⊤ := ENNReal.mul_ne_top hdt hct
  have hleft : (a / d) * (d * c) = a * c := by
    calc
      (a / d) * (d * c) = ((a / d) * d) * c := by rw [mul_assoc]
      _ = a * c := by rw [ENNReal.div_mul_cancel hd0 hdt]
  have hright : (b / c) * (d * c) = b * d := by
    calc
      (b / c) * (d * c) = (b / c) * (c * d) := by rw [mul_comm d c]
      _ = ((b / c) * c) * d := by rw [mul_assoc]
      _ = b * d := by rw [ENNReal.div_mul_cancel hc0 hct]
  have hmul : (a / d) * (d * c) = (b / c) * (d * c) := by
    rw [hleft, hright, h]
  exact (ENNReal.mul_left_inj hdc0 hdct).mp hmul

/-- Where `P(z, w)` is positive, conditional independence is
`P(y | z, w) = P(y | w)`. -/
theorem condIndepVertices_condMass
    (μ : Measure bn.JointSpace) [IsProbabilityMeasure μ]
    (X Z W : Finset V)
    (xX : ∀ p : ((X : Finset V) : Set V), bn.stateSpace p.1)
    (xZ : ∀ p : ((Z : Finset V) : Set V), bn.stateSpace p.1)
    (xW : ∀ p : ((W : Finset V) : Set V), bn.stateSpace p.1)
    (h : CondIndepVertices bn μ (X : Set V) (Z : Set V) (W : Set V))
    (hpos : μ (assignEvent (bn := bn) Z xZ ∩ assignEvent (bn := bn) W xW) ≠ 0) :
    μ (assignEvent (bn := bn) X xX ∩ assignEvent (bn := bn) Z xZ ∩
        assignEvent (bn := bn) W xW) /
      μ (assignEvent (bn := bn) Z xZ ∩ assignEvent (bn := bn) W xW) =
    μ (assignEvent (bn := bn) X xX ∩ assignEvent (bn := bn) W xW) /
      μ (assignEvent (bn := bn) W xW) := by
  have hmul :=
    condIndepVertices_atom_mul (bn := bn) (μ := μ) X Z W xX xZ xW h
  have hW0 : μ (assignEvent (bn := bn) W xW) ≠ 0 := by
    intro h0
    exact hpos (measure_mono_null (Set.inter_subset_right) h0)
  exact ennreal_div_eq_of_cross_mul hmul hpos
    (measure_ne_top μ _) hW0 (measure_ne_top μ _)

end Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork
