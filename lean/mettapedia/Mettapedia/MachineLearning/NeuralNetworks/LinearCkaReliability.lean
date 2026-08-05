import Mathlib.Tactic

/-!
# Linear CKA invariance and reliability boundaries

Kornblith et al., *Similarity of Neural Network Representations Revisited*
(arXiv:1905.00414), motivate centered kernel alignment (CKA) as invariant to
orthogonal feature transformations and isotropic scaling, but not to arbitrary
invertible feature transformations.  Davari et al., *On the Reliability of CKA
as a Measure of Similarity in Deep Learning* (arXiv:2210.16156), show that
function-preserving representation transformations can nevertheless change
linear CKA substantially.

This file formalizes squared linear CKA.  Squaring removes the square roots
from the normalized Gram alignment while preserving its nonnegative ordering
and the source invariances.  Representations are finite sample-indexed feature
vectors.  Centering is explicit rather than hidden inside the statistic.

The positive results prove exact invariance under nonzero isotropic scaling
and arbitrary dot-product-preserving feature maps.  The negative fixture
starts from a centered three-sample, two-feature representation, translates
one sample in a feature direction ignored by a declared readout, and recenters
the result.  The readout is unchanged on every sample, while squared linear CKA
with the original representation drops from one to five eighths.

No claim is made that CKA determines functional equivalence, behavioral
equivalence, transfer performance, or causal mechanism.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks

namespace LinearCkaReliability

noncomputable section

open scoped BigOperators

/-- A finite collection of sample-indexed feature vectors. -/
abbrev Representation (samples features : ℕ) :=
  Fin samples → Fin features → ℝ

/-- Squared cosine alignment of two finite real signatures.  The value at a
zero signature is Lean's totalized field value zero. -/
def squaredAlignment {index : Type*} [Fintype index]
    (left right : index → ℝ) : ℝ :=
  (left ⬝ᵥ right) ^ 2 /
    ((left ⬝ᵥ left) * (right ⬝ᵥ right))

/-- Squared alignment is invariant under independent nonzero scalar
rescalings. -/
theorem squaredAlignment_smul {index : Type*} [Fintype index]
    (left right : index → ℝ) (leftScale rightScale : ℝ)
    (leftScale_ne : leftScale ≠ 0)
    (rightScale_ne : rightScale ≠ 0) :
    squaredAlignment (leftScale • left) (rightScale • right) =
      squaredAlignment left right := by
  by_cases leftZero : left ⬝ᵥ left = 0
  · simp [squaredAlignment, leftZero, smul_dotProduct, dotProduct_smul]
  by_cases rightZero : right ⬝ᵥ right = 0
  · simp [squaredAlignment, rightZero, smul_dotProduct, dotProduct_smul]
  simp only [squaredAlignment, smul_dotProduct, dotProduct_smul,
    smul_eq_mul]
  field_simp [leftScale_ne, rightScale_ne, leftZero, rightZero]

/-- Dot product between two samples in one representation. -/
def gramEntry {samples features : ℕ}
    (representation : Representation samples features)
    (first second : Fin samples) : ℝ :=
  representation first ⬝ᵥ representation second

/-- Flattened Gram matrix used as the linear-kernel similarity signature. -/
def gramSignature {samples features : ℕ}
    (representation : Representation samples features) :
    Fin samples × Fin samples → ℝ :=
  fun pair => gramEntry representation pair.1 pair.2

/-- Squared linear CKA of two representations over the same samples.  Callers
who need centered CKA must pass centered representations. -/
def linearCkaSquared {samples leftFeatures rightFeatures : ℕ}
    (left : Representation samples leftFeatures)
    (right : Representation samples rightFeatures) : ℝ :=
  squaredAlignment (gramSignature left) (gramSignature right)

/-- Pointwise isotropic scaling of a representation. -/
def scaleRepresentation {samples features : ℕ}
    (scale : ℝ) (representation : Representation samples features) :
    Representation samples features :=
  fun sample => scale • representation sample

/-- Isotropic feature scaling multiplies every Gram entry by scale squared. -/
theorem gramSignature_scale {samples features : ℕ}
    (scale : ℝ) (representation : Representation samples features) :
    gramSignature (scaleRepresentation scale representation) =
      (scale ^ 2) • gramSignature representation := by
  funext pair
  simp [gramSignature, gramEntry, scaleRepresentation, smul_dotProduct,
    dotProduct_smul, pow_two]
  ring

/-- Squared linear CKA is exactly invariant under independent nonzero
isotropic feature scalings. -/
theorem linearCkaSquared_scale {samples leftFeatures rightFeatures : ℕ}
    (leftScale rightScale : ℝ)
    (left : Representation samples leftFeatures)
    (right : Representation samples rightFeatures)
    (leftScale_ne : leftScale ≠ 0)
    (rightScale_ne : rightScale ≠ 0) :
    linearCkaSquared
        (scaleRepresentation leftScale left)
        (scaleRepresentation rightScale right) =
      linearCkaSquared left right := by
  rw [linearCkaSquared, linearCkaSquared,
    gramSignature_scale, gramSignature_scale]
  exact squaredAlignment_smul
    (gramSignature left) (gramSignature right)
    (leftScale ^ 2) (rightScale ^ 2)
    (pow_ne_zero 2 leftScale_ne) (pow_ne_zero 2 rightScale_ne)

/-- A feature transformation preserves the Euclidean dot product.  Orthogonal
linear maps, coordinate permutations, rotations, and reflections instantiate
this interface. -/
def DotPreserving {sourceFeatures targetFeatures : ℕ}
    (transform :
      (Fin sourceFeatures → ℝ) → (Fin targetFeatures → ℝ)) : Prop :=
  ∀ first second,
    transform first ⬝ᵥ transform second = first ⬝ᵥ second

/-- Apply one feature transformation to every sample. -/
def mapRepresentation {samples sourceFeatures targetFeatures : ℕ}
    (transform :
      (Fin sourceFeatures → ℝ) → (Fin targetFeatures → ℝ))
    (representation : Representation samples sourceFeatures) :
    Representation samples targetFeatures :=
  fun sample => transform (representation sample)

/-- A dot-product-preserving map leaves the complete Gram signature
unchanged. -/
theorem gramSignature_map_of_dotPreserving
    {samples sourceFeatures targetFeatures : ℕ}
    (transform :
      (Fin sourceFeatures → ℝ) → (Fin targetFeatures → ℝ))
    (representation : Representation samples sourceFeatures)
    (preservesDot : DotPreserving transform) :
    gramSignature (mapRepresentation transform representation) =
      gramSignature representation := by
  funext pair
  exact preservesDot (representation pair.1) (representation pair.2)

/-- Squared linear CKA is invariant when either representation is transformed
by a dot-product-preserving feature map. -/
theorem linearCkaSquared_map_of_dotPreserving
    {samples leftFeatures rightFeatures
      mappedLeftFeatures mappedRightFeatures : ℕ}
    (leftTransform :
      (Fin leftFeatures → ℝ) → (Fin mappedLeftFeatures → ℝ))
    (rightTransform :
      (Fin rightFeatures → ℝ) → (Fin mappedRightFeatures → ℝ))
    (left : Representation samples leftFeatures)
    (right : Representation samples rightFeatures)
    (leftPreserves : DotPreserving leftTransform)
    (rightPreserves : DotPreserving rightTransform) :
    linearCkaSquared
        (mapRepresentation leftTransform left)
        (mapRepresentation rightTransform right) =
      linearCkaSquared left right := by
  simp only [linearCkaSquared,
    gramSignature_map_of_dotPreserving _ _ leftPreserves,
    gramSignature_map_of_dotPreserving _ _ rightPreserves]

/-- A nonzero Gram signature has self-CKA squared equal to one. -/
theorem linearCkaSquared_self {samples features : ℕ}
    (representation : Representation samples features)
    (nonzeroGram :
      gramSignature representation ⬝ᵥ gramSignature representation ≠ 0) :
    linearCkaSquared representation representation = 1 := by
  simp [linearCkaSquared, squaredAlignment, pow_two, nonzeroGram]

/-- Degenerate boundary: the totalized statistic assigns zero when the first
representation is identically zero. -/
theorem linearCkaSquared_zero_left
    {samples leftFeatures rightFeatures : ℕ}
    (right : Representation samples rightFeatures) :
    linearCkaSquared
        (0 : Representation samples leftFeatures) right = 0 := by
  simp [linearCkaSquared, squaredAlignment, gramSignature, gramEntry,
    dotProduct]

/-! ## Explicit centering and a function-preserving failure fixture -/

/-- Column mean of a finite representation. -/
def columnMean {samples features : ℕ}
    (representation : Representation samples features)
    (feature : Fin features) : ℝ :=
  (∑ sample, representation sample feature) / samples

/-- Column-wise centering. -/
def centerRepresentation {samples features : ℕ}
    (representation : Representation samples features) :
    Representation samples features :=
  fun sample feature =>
    representation sample feature - columnMean representation feature

/-- Centering makes every feature column sum to zero when the sample set is
nonempty. -/
theorem sum_centerRepresentation_eq_zero
    {samples features : ℕ}
    (representation : Representation samples features)
    (feature : Fin features)
    (samples_ne : samples ≠ 0) :
    ∑ sample, centerRepresentation representation sample feature = 0 := by
  have samplesCast_ne : (samples : ℝ) ≠ 0 := by
    exact_mod_cast samples_ne
  simp [centerRepresentation, columnMean, Finset.sum_sub_distrib]
  field_simp [samplesCast_ne]
  ring

def baseRepresentation : Representation 3 2 :=
  fun sample =>
    if sample = 0 then ![1, 0]
    else if sample = 1 then ![0, 1]
    else ![-1, -1]

/-- Translate only the first sample by three units in the second feature. -/
def subsetTranslatedRepresentation : Representation 3 2 :=
  fun sample =>
    if sample = 0 then ![1, 3]
    else if sample = 1 then ![0, 1]
    else ![-1, -1]

@[simp] theorem baseRepresentation_zero :
    baseRepresentation 0 = ![1, 0] := by
  simp [baseRepresentation]

@[simp] theorem baseRepresentation_one :
    baseRepresentation 1 = ![0, 1] := by
  simp [baseRepresentation]

@[simp] theorem baseRepresentation_two :
    baseRepresentation 2 = ![-1, -1] := by
  have two_ne_zero : (2 : Fin 3) ≠ 0 := by decide
  have two_ne_one : (2 : Fin 3) ≠ 1 := by decide
  simp [baseRepresentation, two_ne_zero, two_ne_one]

@[simp] theorem subsetTranslatedRepresentation_zero :
    subsetTranslatedRepresentation 0 = ![1, 3] := by
  simp [subsetTranslatedRepresentation]

@[simp] theorem subsetTranslatedRepresentation_one :
    subsetTranslatedRepresentation 1 = ![0, 1] := by
  simp [subsetTranslatedRepresentation]

@[simp] theorem subsetTranslatedRepresentation_two :
    subsetTranslatedRepresentation 2 = ![-1, -1] := by
  have two_ne_zero : (2 : Fin 3) ≠ 0 := by decide
  have two_ne_one : (2 : Fin 3) ≠ 1 := by decide
  simp [subsetTranslatedRepresentation, two_ne_zero, two_ne_one]

/-- A readout that ignores the translated feature direction. -/
def firstCoordinateReadout
    (representation : Representation 3 2) : Fin 3 → ℝ :=
  fun sample => representation sample 0

@[simp] theorem subsetTranslatedRepresentation_firstCoordinate
    (sample : Fin 3) :
    subsetTranslatedRepresentation sample 0 =
      baseRepresentation sample 0 := by
  unfold subsetTranslatedRepresentation baseRepresentation
  split_ifs <;> rfl

/-- The base fixture is already column-centered. -/
theorem baseRepresentation_centered :
    centerRepresentation baseRepresentation = baseRepresentation := by
  funext sample feature
  fin_cases sample <;> fin_cases feature <;>
    norm_num [centerRepresentation, columnMean, Fin.sum_univ_three]

/-- Translation in an ignored feature direction, followed by recentering,
leaves the declared task readout unchanged on every sample. -/
theorem subsetTranslation_preserves_readout :
    firstCoordinateReadout
        (centerRepresentation subsetTranslatedRepresentation) =
      firstCoordinateReadout baseRepresentation := by
  have baseFirstCoordinateSum :
      ∑ sample, baseRepresentation sample 0 = 0 := by
    have centeredSum :=
      sum_centerRepresentation_eq_zero baseRepresentation (0 : Fin 2)
        (by decide)
    rw [baseRepresentation_centered] at centeredSum
    exact centeredSum
  funext sample
  simp [firstCoordinateReadout, centerRepresentation, columnMean,
    baseFirstCoordinateSum]

/-- The original representation has unit squared self-CKA. -/
theorem baseRepresentation_selfCkaSquared :
    linearCkaSquared baseRepresentation baseRepresentation = 1 := by
  norm_num [linearCkaSquared, squaredAlignment, gramSignature, gramEntry,
    dotProduct, Fintype.sum_prod_type,
    Fin.sum_univ_two, Fin.sum_univ_three]

/-- Rescale the second feature by two while leaving the first unchanged. -/
def anisotropicScaleTwo (features : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![features 0, 2 * features 1]

/-- Inverse of `anisotropicScaleTwo`. -/
def anisotropicUnscaleTwo (features : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![features 0, features 1 / 2]

/-- The anisotropic feature rescaling used below is genuinely invertible. -/
theorem anisotropicUnscaleTwo_scaleTwo (features : Fin 2 → ℝ) :
    anisotropicUnscaleTwo (anisotropicScaleTwo features) = features := by
  funext feature
  fin_cases feature <;>
    simp [anisotropicScaleTwo, anisotropicUnscaleTwo]

/-- Boundary to orthogonal/isotropic invariance: an invertible anisotropic
feature rescaling changes squared linear CKA in a finite centered fixture. -/
theorem invertibleAnisotropicRescaling_changesCka :
    linearCkaSquared baseRepresentation
        (mapRepresentation anisotropicScaleTwo baseRepresentation) =
      125 / 152 ∧
    linearCkaSquared baseRepresentation
        (mapRepresentation anisotropicScaleTwo baseRepresentation) ≠
      linearCkaSquared baseRepresentation baseRepresentation := by
  norm_num [linearCkaSquared, squaredAlignment, gramSignature, gramEntry,
    mapRepresentation, anisotropicScaleTwo, dotProduct,
    Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three]

/-- Function-preserving subset translation changes the diagnostic: after
recentering, squared linear CKA with the original drops to five eighths. -/
theorem functionPreserving_subsetTranslation_changesCka :
    linearCkaSquared baseRepresentation
        (centerRepresentation subsetTranslatedRepresentation) =
      5 / 8 ∧
    linearCkaSquared baseRepresentation
        (centerRepresentation subsetTranslatedRepresentation) ≠
      linearCkaSquared baseRepresentation baseRepresentation := by
  norm_num [linearCkaSquared, squaredAlignment, gramSignature, gramEntry,
    centerRepresentation, columnMean, dotProduct, Fintype.sum_prod_type,
    Fin.sum_univ_two, Fin.sum_univ_three]

#print axioms squaredAlignment_smul
#print axioms gramSignature_scale
#print axioms linearCkaSquared_scale
#print axioms gramSignature_map_of_dotPreserving
#print axioms linearCkaSquared_map_of_dotPreserving
#print axioms linearCkaSquared_self
#print axioms linearCkaSquared_zero_left
#print axioms sum_centerRepresentation_eq_zero
#print axioms baseRepresentation_centered
#print axioms subsetTranslation_preserves_readout
#print axioms baseRepresentation_selfCkaSquared
#print axioms anisotropicUnscaleTwo_scaleTwo
#print axioms invertibleAnisotropicRescaling_changesCka
#print axioms functionPreserving_subsetTranslation_changesCka

end

end LinearCkaReliability

end Mettapedia.MachineLearning.NeuralNetworks
