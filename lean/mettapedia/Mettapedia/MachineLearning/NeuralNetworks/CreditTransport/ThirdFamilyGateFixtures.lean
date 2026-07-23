import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ThirdFamilyGate

/-!
# Exact fixtures for the third-family gate

These two-dimensional fixtures reproduce the frozen collapse and separation
oracle.  They rule out weak novelty criteria without asserting that any
registered candidate is a new training family.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace ThirdFamilyGate

namespace OracleFixture

open Matrix
open OperatorClassification
open OperatorSplitting
open AmortizedInitialization

noncomputable section

abbrev Vec2 := Fin 2 → ℝ
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ

/-! ## Escaping one BP--PC chord is insufficient -/

def bpUpdate : Vec2 := ![1, 0]
def pcUpdate : Vec2 := ![0, 1]
def chordEscapeUpdate : Vec2 := ![2, 2]

def bpPcAffineChord (coefficient : ℝ) : Vec2 :=
  (1 - coefficient) • bpUpdate + coefficient • pcUpdate

theorem chordEscapeUpdate_outside_bpPcAffineChord :
    ¬ ∃ coefficient : ℝ,
      chordEscapeUpdate = bpPcAffineChord coefficient := by
  intro hexists
  rcases hexists with ⟨coefficient, heq⟩
  have hzero := congrFun heq 0
  have hone := congrFun heq 1
  norm_num [chordEscapeUpdate, bpPcAffineChord, bpUpdate, pcUpdate] at hzero hone
  linarith

def chordEscapePreconditioner : Mat2 :=
  !![2, 2; 2, 3]

theorem chordEscapePreconditioner_posDef :
    chordEscapePreconditioner.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [chordEscapePreconditioner]
  · intro x hx
    simp [chordEscapePreconditioner, dotProduct, Matrix.mulVec,
      Fin.sum_univ_two]
    have hcoordinates : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra h
      push Not at h
      apply hx
      funext i
      fin_cases i <;> simp [h.1, h.2]
    have hsumOrSecond : x 0 + x 1 ≠ 0 ∨ x 1 ≠ 0 := by
      by_cases hsum : x 0 + x 1 = 0
      · right
        intro hsecond
        apply hcoordinates.elim
        · intro hfirst
          apply hfirst
          linarith
        · exact fun h ↦ h hsecond
      · exact Or.inl hsum
    rcases hsumOrSecond with hsum | hsecond
    · nlinarith [sq_pos_of_ne_zero hsum, sq_nonneg (x 1)]
    · nlinarith [sq_nonneg (x 0 + x 1), sq_pos_of_ne_zero hsecond]

theorem chordEscapePreconditioner_maps_bp :
    chordEscapePreconditioner *ᵥ bpUpdate = chordEscapeUpdate := by
  ext i
  fin_cases i <;>
    norm_num [chordEscapePreconditioner, bpUpdate, chordEscapeUpdate,
      Matrix.mulVec, Fin.sum_univ_two]

theorem outside_chord_but_still_spd_preconditioned_bp :
    (¬ ∃ coefficient : ℝ,
        chordEscapeUpdate = bpPcAffineChord coefficient) ∧
      chordEscapePreconditioner.PosDef ∧
      chordEscapePreconditioner *ᵥ bpUpdate = chordEscapeUpdate :=
  ⟨chordEscapeUpdate_outside_bpPcAffineChord,
    chordEscapePreconditioner_posDef,
    chordEscapePreconditioner_maps_bp⟩

/-! ## Additive hybrids can collapse exactly -/

def broadcastMap : Mat2 := !![1, 0; 0, 0]
def localCorrectionMap : Mat2 := !![0, 0; 0, 1]
def additiveHybridMap : Mat2 := broadcastMap + localCorrectionMap

theorem additiveHybridMap_eq_identity : additiveHybridMap = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [additiveHybridMap, broadcastMap, localCorrectionMap]

theorem additiveHybrid_collapses_to_bp (update : Vec2) :
    broadcastMap *ᵥ update + localCorrectionMap *ᵥ update = update := by
  calc
    broadcastMap *ᵥ update + localCorrectionMap *ᵥ update =
        additiveHybridMap *ᵥ update := by
          rw [additiveHybridMap, Matrix.add_mulVec]
    _ = 1 *ᵥ update := by rw [additiveHybridMap_eq_identity]
    _ = update := Matrix.one_mulVec update

theorem additiveHybrid_probe_exact :
    let probe : Vec2 := ![2, -3]
    broadcastMap *ᵥ probe = ![2, 0] ∧
      localCorrectionMap *ᵥ probe = ![0, -3] ∧
      broadcastMap *ᵥ probe + localCorrectionMap *ᵥ probe = probe := by
  norm_num [broadcastMap, localCorrectionMap, Matrix.mulVec,
    Fin.sum_univ_two]

/-! ## Warm starts alter truncation, not a contractive endpoint -/

def warmStartSolver (state : ℝ) : ℝ := state / 2 + 1

def warmStartCertificate : ContractionCertificate warmStartSolver where
  factor := 1 / 2
  factor_nonneg := by norm_num
  factor_lt_one := by norm_num
  contracts := by
    intro left right
    rw [show warmStartSolver left - warmStartSolver right =
        (left - right) / 2 by simp [warmStartSolver]; ring]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_div]
    norm_num
    ring_nf
    exact le_rfl

theorem warmStart_two_fixed : IsFixedPoint warmStartSolver 2 := by
  norm_num [IsFixedPoint, warmStartSolver]

theorem warmStart_fixedPoint_unique
    {state : ℝ} (hfixed : IsFixedPoint warmStartSolver state) : state = 2 :=
  fixedPoint_unique warmStartCertificate hfixed warmStart_two_fixed

theorem warmStart_finite_trajectories_differ :
    warmStartSolver 0 ≠ warmStartSolver 3 := by
  norm_num [warmStartSolver]

theorem warmStart_iterate_error_le (initial : ℝ) (steps : ℕ) :
    |(warmStartSolver^[steps]) initial - 2| ≤
      warmStartCertificate.factor ^ steps * |initial - 2| := by
  simpa [Real.norm_eq_abs] using
    iterate_initializer_to_fixedPoint_le warmStartCertificate
      2 initial warmStart_two_fixed steps

theorem warmStart_changes_truncation_not_endpoint :
    warmStartSolver 0 ≠ warmStartSolver 3 ∧
      IsFixedPoint warmStartSolver 2 ∧
      (∀ state, IsFixedPoint warmStartSolver state → state = 2) :=
  ⟨warmStart_finite_trajectories_differ, warmStart_two_fixed,
    fun _ hfixed ↦ warmStart_fixedPoint_unique hfixed⟩

/-! ## Fixed-map escape can remain variable-metric BP -/

def gateProbe : Fin 3 → Vec2
  | 0 => ![1, 0]
  | 1 => ![0, 1]
  | 2 => ![1, 1]

def gateUpdate : Fin 3 → Vec2
  | 0 => ![1, 0]
  | 1 => ![0, 1]
  | 2 => ![2, 1]

def gateMetric : Fin 3 → Mat2
  | 0 => !![1, 0; 0, 1]
  | 1 => !![2, 0; 0, 1]
  | 2 => !![2, 0; 0, 1]

theorem no_single_linear_map_fits_gate_probes :
    ¬ ∃ fixedMap : Mat2,
      ∀ index : Fin 3, fixedMap *ᵥ gateProbe index = gateUpdate index := by
  intro hexists
  rcases hexists with ⟨fixedMap, hfits⟩
  have h00 := congrFun (hfits 0) 0
  have h10 := congrFun (hfits 0) 1
  have h01 := congrFun (hfits 1) 0
  have h11 := congrFun (hfits 1) 1
  have hthird := congrFun (hfits 2) 0
  norm_num [gateProbe, gateUpdate, Matrix.mulVec, Fin.sum_univ_two] at h00 h10 h01 h11 hthird
  linarith

private theorem diagonalMetric_posDef (first second : ℝ)
    (hfirst : 0 < first) (hsecond : 0 < second) :
    (!![first, 0; 0, second] : Mat2).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
  · intro x hx
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
    have hcoordinates : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra h
      push Not at h
      apply hx
      funext i
      fin_cases i <;> simp [h.1, h.2]
    rcases hcoordinates with hzero | hone
    · nlinarith [sq_pos_of_ne_zero hzero, sq_nonneg (x 1)]
    · nlinarith [sq_nonneg (x 0), sq_pos_of_ne_zero hone]

theorem gateMetric_posDef (index : Fin 3) :
    (gateMetric index).PosDef := by
  fin_cases index
  · exact diagonalMetric_posDef 1 1 (by norm_num) (by norm_num)
  · exact diagonalMetric_posDef 2 1 (by norm_num) (by norm_num)
  · exact diagonalMetric_posDef 2 1 (by norm_num) (by norm_num)

theorem gateMetric_realizes_update (index : Fin 3) :
    gateMetric index *ᵥ gateProbe index = gateUpdate index := by
  fin_cases index <;> ext coordinate <;> fin_cases coordinate <;>
    norm_num [gateMetric, gateProbe, gateUpdate, Matrix.mulVec,
      Fin.sum_univ_two]

theorem fixed_map_escape_but_variable_metric_collapse :
    (¬ ∃ fixedMap : Mat2,
        ∀ index : Fin 3, fixedMap *ᵥ gateProbe index = gateUpdate index) ∧
      (∀ index : Fin 3,
        (gateMetric index).PosDef ∧
          gateMetric index *ᵥ gateProbe index = gateUpdate index) := by
  refine ⟨no_single_linear_map_fits_gate_probes, ?_⟩
  intro index
  exact ⟨gateMetric_posDef index, gateMetric_realizes_update index⟩

/-! ## Skew transport is known optimizer geometry, with a real step bound -/

def skewTransport : Mat2 := rotationForwardStep
def skewProbe : Vec2 := ![1, 2]
def quadraticLoss (state : Vec2) : ℝ := (state ⬝ᵥ state) / 2
def transportedStep (rate : ℝ) (state : Vec2) : Vec2 :=
  state - rate • (skewTransport *ᵥ state)

theorem skewTransport_symmetricPart_eq_identity :
    symmetricPart skewTransport = 1 := by
  change symmetricPart (!![1, -1; 1, 1] : Mat2) = 1
  ext i j
  fin_cases i
  · fin_cases j
    · change (1 / 2 : ℝ) * (1 + 1) = 1
      norm_num
    · change (1 / 2 : ℝ) * (-1 + 1) = 0
      norm_num
  · fin_cases j
    · change (1 / 2 : ℝ) * (1 + -1) = 0
      norm_num
    · change (1 / 2 : ℝ) * (1 + 1) = 1
      norm_num

theorem skewTransport_not_symmetric : ¬ skewTransport.IsSymm := by
  intro hsymm
  have h01 := hsymm.apply 0 1
  norm_num [skewTransport, rotationForwardStep] at h01

theorem skewTransport_is_known_forward_step :
    skewTransport = 1 - rotationOperator :=
  rotationForwardStep_eq_one_sub_operator

theorem skewProbe_direction : skewTransport *ᵥ skewProbe = ![-1, 3] := by
  ext i
  fin_cases i <;>
    norm_num [skewTransport, skewProbe, rotationForwardStep,
      Matrix.mulVec, Fin.sum_univ_two]

theorem skewProbe_task_descent_margin :
    skewProbe ⬝ᵥ (skewTransport *ᵥ skewProbe) = 5 := by
  norm_num [skewTransport, skewProbe, rotationForwardStep, dotProduct,
    Matrix.mulVec, Fin.sum_univ_two]

theorem no_symmetric_map_matches_skew_basis_images :
    ¬ ∃ symmetricMap : Mat2,
      symmetricMap.IsSymm ∧
        symmetricMap *ᵥ ![1, 0] = skewTransport *ᵥ ![1, 0] ∧
        symmetricMap *ᵥ ![0, 1] = skewTransport *ᵥ ![0, 1] := by
  intro hexists
  rcases hexists with ⟨symmetricMap, hsymm, hfirst, hsecond⟩
  have h10 := congrFun hfirst 1
  norm_num [skewTransport, rotationForwardStep, Matrix.mulVec,
    Fin.sum_univ_two] at h10
  change symmetricMap 1 0 = 1 at h10
  have h01 := congrFun hsecond 0
  norm_num [skewTransport, rotationForwardStep, Matrix.mulVec,
    Fin.sum_univ_two] at h01
  change symmetricMap 0 1 = -1 at h01
  have hsymmetry := hsymm.apply 0 1
  linarith

theorem safe_skew_step_descends :
    transportedStep (1 / 4) skewProbe = ![5 / 4, 5 / 4] ∧
      quadraticLoss (transportedStep (1 / 4) skewProbe) = 25 / 16 ∧
      quadraticLoss (transportedStep (1 / 4) skewProbe) <
        quadraticLoss skewProbe := by
  constructor
  · ext i
    fin_cases i <;>
      norm_num [transportedStep, skewTransport, skewProbe,
        rotationForwardStep, Matrix.mulVec, Fin.sum_univ_two]
  · constructor <;>
      norm_num [transportedStep, quadraticLoss, skewTransport, skewProbe,
        rotationForwardStep, dotProduct, Matrix.mulVec, Fin.sum_univ_two]

theorem large_skew_step_ascends :
    transportedStep (3 / 2) skewProbe = ![5 / 2, -5 / 2] ∧
      quadraticLoss (transportedStep (3 / 2) skewProbe) = 25 / 4 ∧
      quadraticLoss skewProbe <
        quadraticLoss (transportedStep (3 / 2) skewProbe) := by
  constructor
  · ext i
    fin_cases i <;>
      norm_num [transportedStep, skewTransport, skewProbe,
        rotationForwardStep, Matrix.mulVec, Fin.sum_univ_two]
  · constructor <;>
      norm_num [transportedStep, quadraticLoss, skewTransport, skewProbe,
        rotationForwardStep, dotProduct, Matrix.mulVec, Fin.sum_univ_two]

theorem skew_transport_gate_crown :
    symmetricPart skewTransport = 1 ∧
      ¬ skewTransport.IsSymm ∧
      skewProbe ⬝ᵥ (skewTransport *ᵥ skewProbe) = 5 ∧
      (¬ ∃ symmetricMap : Mat2,
        symmetricMap.IsSymm ∧
          symmetricMap *ᵥ ![1, 0] = skewTransport *ᵥ ![1, 0] ∧
          symmetricMap *ᵥ ![0, 1] = skewTransport *ᵥ ![0, 1]) ∧
      quadraticLoss (transportedStep (1 / 4) skewProbe) <
        quadraticLoss skewProbe ∧
      quadraticLoss skewProbe <
        quadraticLoss (transportedStep (3 / 2) skewProbe) :=
  ⟨skewTransport_symmetricPart_eq_identity,
    skewTransport_not_symmetric,
    skewProbe_task_descent_margin,
    no_symmetric_map_matches_skew_basis_images,
    safe_skew_step_descends.2.2,
    large_skew_step_ascends.2.2⟩

#print axioms outside_chord_but_still_spd_preconditioned_bp
#print axioms additiveHybrid_collapses_to_bp
#print axioms warmStart_changes_truncation_not_endpoint
#print axioms no_single_linear_map_fits_gate_probes
#print axioms fixed_map_escape_but_variable_metric_collapse
#print axioms skew_transport_gate_crown

end

end OracleFixture

end ThirdFamilyGate

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
