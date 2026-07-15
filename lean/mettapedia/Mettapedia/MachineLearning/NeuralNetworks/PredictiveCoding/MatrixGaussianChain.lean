import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.LinearGaussianOperator
import Mathlib.Tactic

/-!
# Matrix-valued linear-Gaussian predictive-coding chains

This file instantiates the operator-level Bayesian crown for arbitrary-width
chains.  Every node is a real vector, every link has a matrix gain, and the
flattened residual field has an arbitrary positive-definite (not necessarily
block-diagonal) precision matrix.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

open MeasureTheory ProbabilityTheory Set

/-- A vector-valued predictive-coding link with a square matrix gain. -/
structure MatrixPCLink (width : ℕ) where
  gain : Matrix (Fin width) (Fin width) ℝ

/-- A chain state whose nodes are vectors of a fixed finite width. -/
abbrev MatrixPCState (width depth : ℕ) :=
  Fin (depth + 1) → Fin width → ℝ

/-- Flattened interior-coordinate index. -/
abbrev MatrixPCInteriorIndex (width interior : ℕ) :=
  Fin interior × Fin width

/-- Flattened edge-residual index. -/
abbrev MatrixPCResidualIndex (width interior : ℕ) :=
  Fin (interior + 1) × Fin width

/-- Euclidean coordinates for all unclamped vector nodes. -/
abbrev MatrixPCInteriorSpace (width interior : ℕ) :=
  EuclideanSpace ℝ (MatrixPCInteriorIndex width interior)

/-- Component of the vector residual `zᵢ₊₁ - Gᵢ zᵢ`. -/
noncomputable def matrixPCResidual {width depth : ℕ}
    (links : Fin depth → MatrixPCLink width)
    (z : MatrixPCState width depth) (edge : Fin depth) (coordinate : Fin width) : ℝ :=
  z edge.succ coordinate - (links edge).gain.mulVec (z edge.castSucc) coordinate

/-- Flattened vector residual field. -/
noncomputable def matrixPCResidualVector {width depth : ℕ}
    (links : Fin depth → MatrixPCLink width)
    (z : MatrixPCState width depth) : Fin depth × Fin width → ℝ :=
  fun index => matrixPCResidual links z index.1 index.2

/-- Pointwise addition of vector chain states. -/
noncomputable def matrixPCAddState {width depth : ℕ}
    (z δ : MatrixPCState width depth) : MatrixPCState width depth :=
  fun node coordinate => z node coordinate + δ node coordinate

theorem matrixPCResidual_add {width depth : ℕ}
    (links : Fin depth → MatrixPCLink width)
    (z δ : MatrixPCState width depth) (edge : Fin depth) (coordinate : Fin width) :
    matrixPCResidual links (matrixPCAddState z δ) edge coordinate =
      matrixPCResidual links z edge coordinate +
        matrixPCResidual links δ edge coordinate := by
  unfold matrixPCResidual matrixPCAddState
  change z edge.succ coordinate + δ edge.succ coordinate -
      (links edge).gain.mulVec (z edge.castSucc + δ edge.castSucc) coordinate = _
  rw [Matrix.mulVec_add]
  simp only [Pi.add_apply]
  ring

theorem matrixPCResidual_smul {width depth : ℕ}
    (links : Fin depth → MatrixPCLink width) (r : ℝ)
    (z : MatrixPCState width depth) (edge : Fin depth) (coordinate : Fin width) :
    matrixPCResidual links (r • z) edge coordinate =
      r * matrixPCResidual links z edge coordinate := by
  unfold matrixPCResidual
  change r * z edge.succ coordinate -
      (links edge).gain.mulVec (r • z edge.castSucc) coordinate = _
  rw [Matrix.mulVec_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- A vector-chain perturbation with both endpoints fixed at zero. -/
def matrixPCZeroEndpointPerturbation {width depth : ℕ}
    (δ : MatrixPCState width depth) : Prop :=
  δ 0 = 0 ∧ δ (Fin.last depth) = 0

/-- Zero residuals and a zero initial endpoint force every node of a
matrix-gain chain to vanish.  No gain invertibility is required. -/
theorem matrixPC_eq_zero_of_zero_residuals {width depth : ℕ}
    (links : Fin depth → MatrixPCLink width)
    (δ : MatrixPCState width depth)
    (hzero : matrixPCZeroEndpointPerturbation δ)
    (hres : ∀ edge : Fin depth, ∀ coordinate : Fin width,
      matrixPCResidual links δ edge coordinate = 0) :
    δ = 0 := by
  funext node coordinate
  have hnode : ∀ n (hn : n < depth + 1), δ ⟨n, hn⟩ = 0 := by
    intro n
    induction n with
    | zero =>
        intro _hn
        exact hzero.1
    | succ n ih =>
        intro hn
        have hn_depth : n < depth := by omega
        let edge : Fin depth := ⟨n, hn_depth⟩
        have hedge_cast : edge.castSucc = (⟨n, by omega⟩ : Fin (depth + 1)) := by
          ext
          simp [edge]
        have hedge_succ : edge.succ = (⟨n + 1, hn⟩ : Fin (depth + 1)) := by
          ext
          simp [edge]
        have hprev : δ edge.castSucc = 0 := by
          rw [hedge_cast]
          exact ih (by omega)
        funext c
        have hr := hres edge c
        unfold matrixPCResidual at hr
        rw [hedge_succ, hprev] at hr
        simpa using hr
  have hz := congrFun (hnode node.val node.isLt) coordinate
  simpa using hz

/-- Insert flattened interior coordinates into a zero-endpoint vector chain. -/
noncomputable def matrixPCInteriorPerturbation (width interior : ℕ)
    (u : MatrixPCInteriorSpace width interior) :
    MatrixPCState width (interior + 1) :=
  fun node coordinate =>
    if hzero : node.val = 0 then 0
    else if hlast : node.val = interior + 1 then 0
    else u (⟨node.val - 1, by omega⟩, coordinate)

@[simp] theorem matrixPCInteriorPerturbation_zero (width interior : ℕ)
    (u : MatrixPCInteriorSpace width interior) :
    matrixPCInteriorPerturbation width interior u 0 = 0 := by
  funext coordinate
  simp [matrixPCInteriorPerturbation]

@[simp] theorem matrixPCInteriorPerturbation_last (width interior : ℕ)
    (u : MatrixPCInteriorSpace width interior) :
    matrixPCInteriorPerturbation width interior u (Fin.last (interior + 1)) = 0 := by
  funext coordinate
  simp [matrixPCInteriorPerturbation]

@[simp] theorem matrixPCInteriorPerturbation_interior (width interior : ℕ)
    (u : MatrixPCInteriorSpace width interior)
    (node : Fin interior) (coordinate : Fin width) :
    matrixPCInteriorPerturbation width interior u
        ⟨node.val + 1, by omega⟩ coordinate = u (node, coordinate) := by
  simp [matrixPCInteriorPerturbation]
  omega

/-- Linear residual operator on zero-endpoint vector-chain perturbations. -/
noncomputable def matrixPCInteriorResidualLinearMap {width interior : ℕ}
    (links : Fin (interior + 1) → MatrixPCLink width) :
    MatrixPCInteriorSpace width interior →ₗ[ℝ]
      (MatrixPCResidualIndex width interior → ℝ) where
  toFun u := matrixPCResidualVector links
    (matrixPCInteriorPerturbation width interior u)
  map_add' u v := by
    funext index
    simp only [matrixPCResidualVector]
    rw [show matrixPCInteriorPerturbation width interior (u + v) =
        matrixPCAddState (matrixPCInteriorPerturbation width interior u)
          (matrixPCInteriorPerturbation width interior v) by
      funext node coordinate
      simp [matrixPCInteriorPerturbation, matrixPCAddState]
      split_ifs <;> simp]
    exact matrixPCResidual_add links _ _ index.1 index.2
  map_smul' r u := by
    funext index
    have hperturbation : matrixPCInteriorPerturbation width interior (r • u) =
        r • matrixPCInteriorPerturbation width interior u := by
      funext node coordinate
      simp only [matrixPCInteriorPerturbation, Pi.smul_apply, smul_eq_mul]
      split_ifs <;> simp
    rw [hperturbation]
    exact matrixPCResidual_smul links r _ index.1 index.2

theorem matrixPCInteriorResidualLinearMap_injective {width interior : ℕ}
    (links : Fin (interior + 1) → MatrixPCLink width) :
    Function.Injective (matrixPCInteriorResidualLinearMap links) := by
  intro u v huv
  have hmapzero : matrixPCInteriorResidualLinearMap links (u - v) = 0 := by
    rw [map_sub, huv, sub_self]
  let δ := matrixPCInteriorPerturbation width interior (u - v)
  have hzero : matrixPCZeroEndpointPerturbation δ := by
    constructor <;> simp [δ]
  have hres : ∀ edge : Fin (interior + 1), ∀ coordinate : Fin width,
      matrixPCResidual links δ edge coordinate = 0 := by
    intro edge coordinate
    have h := congrFun hmapzero (edge, coordinate)
    simpa [matrixPCInteriorResidualLinearMap, matrixPCResidualVector, δ] using h
  have hδ : δ = 0 :=
    matrixPC_eq_zero_of_zero_residuals links δ hzero hres
  apply sub_eq_zero.mp
  apply PiLp.ext
  intro index
  have hnode := congrFun (congrFun hδ
    (⟨index.1.val + 1, by omega⟩ : Fin (interior + 2))) index.2
  simpa [δ] using hnode

/-- Matrix of the injective block-incidence residual operator. -/
noncomputable def matrixPCInteriorIncidenceMatrix {width interior : ℕ}
    (links : Fin (interior + 1) → MatrixPCLink width) :
    Matrix (MatrixPCResidualIndex width interior)
      (MatrixPCInteriorIndex width interior) ℝ :=
  LinearMap.toMatrix
    (EuclideanSpace.basisFun (MatrixPCInteriorIndex width interior) ℝ).toBasis
    (Pi.basisFun ℝ (MatrixPCResidualIndex width interior))
    (matrixPCInteriorResidualLinearMap links)

theorem matrixPCInteriorIncidenceMatrix_mulVec {width interior : ℕ}
    (links : Fin (interior + 1) → MatrixPCLink width)
    (u : MatrixPCInteriorSpace width interior) :
    (matrixPCInteriorIncidenceMatrix links).mulVec (fun i => u i) =
      matrixPCInteriorResidualLinearMap links u := by
  have h := LinearMap.toMatrix_mulVec_repr
    (EuclideanSpace.basisFun (MatrixPCInteriorIndex width interior) ℝ).toBasis
    (Pi.basisFun ℝ (MatrixPCResidualIndex width interior))
    (matrixPCInteriorResidualLinearMap links) u
  have hdomain :
      ⇑((EuclideanSpace.basisFun (MatrixPCInteriorIndex width interior) ℝ)
        |>.toBasis.repr u) = (fun i => u i) := by
    funext i
    exact EuclideanSpace.basisFun_repr _ ℝ u i
  have hcodomain :
      ⇑((Pi.basisFun ℝ (MatrixPCResidualIndex width interior)).repr
        (matrixPCInteriorResidualLinearMap links u)) =
          matrixPCInteriorResidualLinearMap links u := by
    funext index
    exact Pi.basisFun_repr ℝ _ _ index
  rw [hdomain, hcodomain] at h
  exact h

theorem matrixPCInteriorIncidenceMatrix_mulVec_injective {width interior : ℕ}
    (links : Fin (interior + 1) → MatrixPCLink width) :
    Function.Injective (matrixPCInteriorIncidenceMatrix links).mulVec := by
  intro u v huv
  let u' : MatrixPCInteriorSpace width interior := WithLp.toLp 2 u
  let v' : MatrixPCInteriorSpace width interior := WithLp.toLp 2 v
  apply_fun WithLp.toLp 2 at huv
  have hlinear : matrixPCInteriorResidualLinearMap links u' =
      matrixPCInteriorResidualLinearMap links v' := by
    rw [← matrixPCInteriorIncidenceMatrix_mulVec links u',
      ← matrixPCInteriorIncidenceMatrix_mulVec links v']
    exact congrArg WithLp.ofLp huv
  have huv' := matrixPCInteriorResidualLinearMap_injective links hlinear
  funext index
  exact congrArg (fun w : MatrixPCInteriorSpace width interior => w index) huv'

/-! ## Arbitrary matrix precision and the Bayesian crown -/

/-- State containing only the two clamped vector endpoints. -/
noncomputable def matrixPCEndpointState (width interior : ℕ)
    (x y : Fin width → ℝ) : MatrixPCState width (interior + 1) :=
  fun node coordinate =>
    if node.val = 0 then x coordinate
    else if node.val = interior + 1 then y coordinate
    else 0

/-- Assemble a full vector chain from endpoints and flattened interior
coordinates. -/
noncomputable def matrixPCStateOfInterior (width interior : ℕ)
    (x y : Fin width → ℝ) (u : MatrixPCInteriorSpace width interior) :
    MatrixPCState width (interior + 1) :=
  matrixPCAddState (matrixPCEndpointState width interior x y)
    (matrixPCInteriorPerturbation width interior u)

@[simp] theorem matrixPCStateOfInterior_zero (width interior : ℕ)
    (x y : Fin width → ℝ) (u : MatrixPCInteriorSpace width interior) :
    matrixPCStateOfInterior width interior x y u 0 = x := by
  funext coordinate
  simp [matrixPCStateOfInterior, matrixPCAddState, matrixPCEndpointState]

@[simp] theorem matrixPCStateOfInterior_last (width interior : ℕ)
    (x y : Fin width → ℝ) (u : MatrixPCInteriorSpace width interior) :
    matrixPCStateOfInterior width interior x y u (Fin.last (interior + 1)) = y := by
  funext coordinate
  simp [matrixPCStateOfInterior, matrixPCAddState, matrixPCEndpointState]

@[simp] theorem matrixPCStateOfInterior_interior (width interior : ℕ)
    (x y : Fin width → ℝ) (u : MatrixPCInteriorSpace width interior)
    (node : Fin interior) (coordinate : Fin width) :
    matrixPCStateOfInterior width interior x y u
        ⟨node.val + 1, by omega⟩ coordinate = u (node, coordinate) := by
  simp [matrixPCStateOfInterior, matrixPCAddState, matrixPCEndpointState]
  omega

/-- Vector-chain states with both endpoint vectors clamped. -/
def matrixPCClampedStateSet (width interior : ℕ)
    (x y : Fin width → ℝ) : Set (MatrixPCState width (interior + 1)) :=
  {z | z 0 = x ∧ z (Fin.last (interior + 1)) = y}

theorem matrixPCStateOfInterior_mem_clamped (width interior : ℕ)
    (x y : Fin width → ℝ) (u : MatrixPCInteriorSpace width interior) :
    matrixPCStateOfInterior width interior x y u ∈
      matrixPCClampedStateSet width interior x y :=
  ⟨matrixPCStateOfInterior_zero width interior x y u,
    matrixPCStateOfInterior_last width interior x y u⟩

/-- Extract flattened interior coordinates from a full vector chain. -/
noncomputable def matrixPCInteriorCoordinates (width interior : ℕ)
    (z : MatrixPCState width (interior + 1)) :
    MatrixPCInteriorSpace width interior :=
  WithLp.toLp 2 fun index =>
    z ⟨index.1.val + 1, by omega⟩ index.2

@[simp] theorem matrixPCInteriorCoordinates_stateOfInterior (width interior : ℕ)
    (x y : Fin width → ℝ) (u : MatrixPCInteriorSpace width interior) :
    matrixPCInteriorCoordinates width interior
      (matrixPCStateOfInterior width interior x y u) = u := by
  apply PiLp.ext
  intro index
  simp [matrixPCInteriorCoordinates]

theorem matrixPCStateOfInterior_coordinates_of_clamped (width interior : ℕ)
    (x y : Fin width → ℝ) (z : MatrixPCState width (interior + 1))
    (hz : z ∈ matrixPCClampedStateSet width interior x y) :
    matrixPCStateOfInterior width interior x y
      (matrixPCInteriorCoordinates width interior z) = z := by
  funext node coordinate
  by_cases hzero : node.val = 0
  · have hnode : node = 0 := Fin.ext hzero
    subst node
    simpa using congrFun hz.1.symm coordinate
  by_cases hlast : node.val = interior + 1
  · have hnode : node = Fin.last (interior + 1) := by
      apply Fin.ext
      simpa using hlast
    subst node
    simpa using congrFun hz.2.symm coordinate
  · have hpos : 0 < node.val := Nat.pos_of_ne_zero hzero
    let i : Fin interior := ⟨node.val - 1, by omega⟩
    have hnode : (⟨i.val + 1, by omega⟩ : Fin (interior + 2)) = node := by
      apply Fin.ext
      simp [i]
      omega
    rw [← hnode, matrixPCStateOfInterior_interior]
    simp [matrixPCInteriorCoordinates, i, hnode]

/-- Residual field contributed by the two clamped endpoint vectors. -/
noncomputable def matrixPCEndpointResidualVector {width interior : ℕ}
    (links : Fin (interior + 1) → MatrixPCLink width)
    (x y : Fin width → ℝ) : MatrixPCResidualIndex width interior → ℝ :=
  matrixPCResidualVector links (matrixPCEndpointState width interior x y)

/-- A matrix-gain vector chain equipped with an arbitrary fully correlated
positive-definite residual precision. -/
noncomputable def matrixPCOperatorModel {width interior : ℕ}
    (links : Fin (interior + 1) → MatrixPCLink width)
    (residualPrecision : Matrix (MatrixPCResidualIndex width interior)
      (MatrixPCResidualIndex width interior) ℝ)
    (hprecision : residualPrecision.PosDef)
    (x y : Fin width → ℝ) :
    LinearGaussianOperatorModel (MatrixPCInteriorIndex width interior)
      (MatrixPCResidualIndex width interior) where
  residualMatrix := matrixPCInteriorIncidenceMatrix links
  residualPrecision := residualPrecision
  residualOffset := matrixPCEndpointResidualVector links x y
  residualMatrix_injective := matrixPCInteriorIncidenceMatrix_mulVec_injective links
  residualPrecision_posDef := hprecision

theorem matrixPCOperatorModel_residual_eq_chain {width interior : ℕ}
    (links : Fin (interior + 1) → MatrixPCLink width)
    (residualPrecision : Matrix (MatrixPCResidualIndex width interior)
      (MatrixPCResidualIndex width interior) ℝ)
    (hprecision : residualPrecision.PosDef) (x y : Fin width → ℝ)
    (u : MatrixPCInteriorSpace width interior) :
    (matrixPCOperatorModel links residualPrecision hprecision x y).residual u =
      matrixPCResidualVector links
        (matrixPCStateOfInterior width interior x y u) := by
  funext index
  change (matrixPCInteriorIncidenceMatrix links).mulVec (fun i => u i) index +
      matrixPCEndpointResidualVector links x y index = _
  rw [matrixPCInteriorIncidenceMatrix_mulVec links u]
  change matrixPCResidual links
      (matrixPCInteriorPerturbation width interior u) index.1 index.2 +
    matrixPCResidual links (matrixPCEndpointState width interior x y)
      index.1 index.2 = _
  rw [add_comm, ← matrixPCResidual_add]
  rfl

/-- Precision-weighted energy of the flattened vector residual field. -/
noncomputable def matrixPCEnergy {width interior : ℕ}
    (links : Fin (interior + 1) → MatrixPCLink width)
    (residualPrecision : Matrix (MatrixPCResidualIndex width interior)
      (MatrixPCResidualIndex width interior) ℝ)
    (z : MatrixPCState width (interior + 1)) : ℝ :=
  matrixPCResidualVector links z ⬝ᵥ
    residualPrecision.mulVec (matrixPCResidualVector links z)

theorem matrixPCEnergy_stateOfInterior_eq_operator {width interior : ℕ}
    (links : Fin (interior + 1) → MatrixPCLink width)
    (residualPrecision : Matrix (MatrixPCResidualIndex width interior)
      (MatrixPCResidualIndex width interior) ℝ)
    (hprecision : residualPrecision.PosDef) (x y : Fin width → ℝ)
    (u : MatrixPCInteriorSpace width interior) :
    matrixPCEnergy links residualPrecision
        (matrixPCStateOfInterior width interior x y u) =
      (matrixPCOperatorModel links residualPrecision hprecision x y).energy u := by
  unfold matrixPCEnergy LinearGaussianOperatorModel.energy
  rw [matrixPCOperatorModel_residual_eq_chain]
  rfl

/-- A clamped vector-chain equilibrium minimizes its genuine residual energy
over the endpoint affine slice. -/
def matrixPCEquilibrium {width interior : ℕ}
    (links : Fin (interior + 1) → MatrixPCLink width)
    (residualPrecision : Matrix (MatrixPCResidualIndex width interior)
      (MatrixPCResidualIndex width interior) ℝ)
    (x y : Fin width → ℝ) (z : MatrixPCState width (interior + 1)) : Prop :=
  z ∈ matrixPCClampedStateSet width interior x y ∧
    IsMinOn (matrixPCEnergy links residualPrecision)
      (matrixPCClampedStateSet width interior x y) z

theorem matrixPCEquilibrium_iff_operatorEquilibrium {width interior : ℕ}
    (links : Fin (interior + 1) → MatrixPCLink width)
    (residualPrecision : Matrix (MatrixPCResidualIndex width interior)
      (MatrixPCResidualIndex width interior) ℝ)
    (hprecision : residualPrecision.PosDef) (x y : Fin width → ℝ)
    (z : MatrixPCState width (interior + 1)) :
    matrixPCEquilibrium links residualPrecision x y z ↔
      z ∈ matrixPCClampedStateSet width interior x y ∧
        (matrixPCOperatorModel links residualPrecision hprecision x y).Equilibrium
          (matrixPCInteriorCoordinates width interior z) := by
  constructor
  · intro hz
    refine ⟨hz.1, ?_⟩
    change IsMinOn (matrixPCOperatorModel links residualPrecision hprecision x y).energy
      Set.univ (matrixPCInteriorCoordinates width interior z)
    rw [isMinOn_univ_iff]
    intro u
    rw [← matrixPCEnergy_stateOfInterior_eq_operator,
      ← matrixPCEnergy_stateOfInterior_eq_operator,
      matrixPCStateOfInterior_coordinates_of_clamped width interior x y z hz.1]
    exact (isMinOn_iff.mp hz.2) _
      (matrixPCStateOfInterior_mem_clamped width interior x y u)
  · rintro ⟨hzclamp, hzoperator⟩
    refine ⟨hzclamp, ?_⟩
    rw [isMinOn_iff]
    intro w hw
    change IsMinOn (matrixPCOperatorModel links residualPrecision hprecision x y).energy
      Set.univ (matrixPCInteriorCoordinates width interior z) at hzoperator
    have hle := (isMinOn_univ_iff.mp hzoperator)
      (matrixPCInteriorCoordinates width interior w)
    rw [← matrixPCEnergy_stateOfInterior_eq_operator,
      ← matrixPCEnergy_stateOfInterior_eq_operator,
      matrixPCStateOfInterior_coordinates_of_clamped width interior x y z hzclamp,
      matrixPCStateOfInterior_coordinates_of_clamped width interior x y w hw] at hle
    exact hle

/-- Arbitrary-width, arbitrary-depth, arbitrary-matrix-precision Bayesian
crown for vector-valued predictive coding. -/
theorem matrixPCEquilibrium_iff_eq_conditionalPosteriorMean {width interior : ℕ}
    (links : Fin (interior + 1) → MatrixPCLink width)
    (residualPrecision : Matrix (MatrixPCResidualIndex width interior)
      (MatrixPCResidualIndex width interior) ℝ)
    (hprecision : residualPrecision.PosDef) (x y : Fin width → ℝ)
    (z : MatrixPCState width (interior + 1)) :
    matrixPCEquilibrium links residualPrecision x y z ↔
      z = matrixPCStateOfInterior width interior x y
        (∫ u, u ∂(matrixPCOperatorModel links residualPrecision hprecision x y).posterior) := by
  constructor
  · intro hz
    have hadapter := (matrixPCEquilibrium_iff_operatorEquilibrium
      links residualPrecision hprecision x y z).mp hz
    have hcoordinates : matrixPCInteriorCoordinates width interior z =
        ∫ u, u ∂(matrixPCOperatorModel links residualPrecision hprecision x y).posterior :=
      ((matrixPCOperatorModel links residualPrecision hprecision x y)
        |>.equilibrium_iff_eq_conditionalPosteriorMean _).mp hadapter.2
    calc
      z = matrixPCStateOfInterior width interior x y
          (matrixPCInteriorCoordinates width interior z) :=
        (matrixPCStateOfInterior_coordinates_of_clamped
          width interior x y z hadapter.1).symm
      _ = matrixPCStateOfInterior width interior x y
          (∫ u, u ∂(matrixPCOperatorModel links residualPrecision hprecision x y).posterior) := by
        rw [hcoordinates]
  · intro hz
    subst z
    apply (matrixPCEquilibrium_iff_operatorEquilibrium
      links residualPrecision hprecision x y _).mpr
    refine ⟨matrixPCStateOfInterior_mem_clamped width interior x y _, ?_⟩
    rw [matrixPCInteriorCoordinates_stateOfInterior]
    exact ((matrixPCOperatorModel links residualPrecision hprecision x y)
      |>.equilibrium_iff_eq_conditionalPosteriorMean _).mpr rfl

/-- Positive fixture: the posterior-mean state is always an equilibrium. -/
theorem matrixPC_posteriorMean_equilibrium {width interior : ℕ}
    (links : Fin (interior + 1) → MatrixPCLink width)
    (residualPrecision : Matrix (MatrixPCResidualIndex width interior)
      (MatrixPCResidualIndex width interior) ℝ)
    (hprecision : residualPrecision.PosDef) (x y : Fin width → ℝ) :
    matrixPCEquilibrium links residualPrecision x y
      (matrixPCStateOfInterior width interior x y
        (∫ u, u ∂(matrixPCOperatorModel links residualPrecision hprecision x y).posterior)) :=
  (matrixPCEquilibrium_iff_eq_conditionalPosteriorMean
    links residualPrecision hprecision x y _).mpr rfl

/-- Negative fixture: any clamped state different from the posterior-mean
state is not an equilibrium. -/
theorem matrixPC_not_equilibrium_of_ne_posteriorMean {width interior : ℕ}
    (links : Fin (interior + 1) → MatrixPCLink width)
    (residualPrecision : Matrix (MatrixPCResidualIndex width interior)
      (MatrixPCResidualIndex width interior) ℝ)
    (hprecision : residualPrecision.PosDef) (x y : Fin width → ℝ)
    (z : MatrixPCState width (interior + 1))
    (hne : z ≠ matrixPCStateOfInterior width interior x y
      (∫ u, u ∂(matrixPCOperatorModel links residualPrecision hprecision x y).posterior)) :
    ¬ matrixPCEquilibrium links residualPrecision x y z := by
  rw [matrixPCEquilibrium_iff_eq_conditionalPosteriorMean]
  exact hne

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
