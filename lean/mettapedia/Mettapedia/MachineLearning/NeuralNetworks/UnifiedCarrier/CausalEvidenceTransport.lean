import Mathlib
import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.CausalInnovationLedger

/-!
# Causal evidence transport

The causal-memory protocol separates evidence accounting from the coordinate
frame in which an innovation was observed.  This file supplies the missing
connection between those planes.

For source operators `Hₛ` and target operators `Hₜ`, a transport `T`
intertwines them when `Hₜ ∘ T = T ∘ Hₛ`.  Exact intertwining extends to every
finite operator word.  Approximate intertwining extends as well, with an
explicit recursive error budget that accounts for both target-side
amplification of earlier error and source-side growth of later error.

Metric preservation is kept separate from intertwining.  In particular, the
zero transport intertwines every pair of operators but preserves no nonzero
metric information.  This negative boundary prevents a vacuous intertwiner
from serving as a mechanism-match certificate.

Finally, additive changes of evidence frame commute with the existing
exactly-once innovation ledger.  Causal identity remains unchanged while the
accepted payload is transported exactly once.

The operator-intertwining and metric-preservation objectives correspond to the
transport contract in Goertzel's Causal Memory and Credit Protocol (2026).
Operator estimation, causal identity assignment, and empirical confidence
calibration remain external obligations.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier

namespace CausalEvidenceTransport

noncomputable section

open scoped InnerProductSpace

variable {Source Target : Type*}
variable [NormedAddCommGroup Source] [NormedSpace ℝ Source]
variable [NormedAddCommGroup Target] [NormedSpace ℝ Target]

/-- Residual of the operator-intertwining equation
`targetOperator ∘ transport = transport ∘ sourceOperator`. -/
def intertwiningResidual
    (transport : Source →L[ℝ] Target)
    (sourceOperator : Source →L[ℝ] Source)
    (targetOperator : Target →L[ℝ] Target) :
    Source →L[ℝ] Target :=
  targetOperator ∘L transport - transport ∘L sourceOperator

/-- Exact compatibility of one source/target operator pair with a transport. -/
def Intertwines
    (transport : Source →L[ℝ] Target)
    (sourceOperator : Source →L[ℝ] Source)
    (targetOperator : Target →L[ℝ] Target) : Prop :=
  targetOperator ∘L transport = transport ∘L sourceOperator

/-- A pointwise-homogeneous error certificate for approximate intertwining. -/
structure ApproxIntertwines
    (transport : Source →L[ℝ] Target)
    (sourceOperator : Source →L[ℝ] Source)
    (targetOperator : Target →L[ℝ] Target)
    (error : ℝ) : Prop where
  error_nonneg : 0 ≤ error
  bound : ∀ source,
    ‖targetOperator (transport source) -
        transport (sourceOperator source)‖ ≤
      error * ‖source‖

theorem intertwines_iff_residual_eq_zero
    (transport : Source →L[ℝ] Target)
    (sourceOperator : Source →L[ℝ] Source)
    (targetOperator : Target →L[ℝ] Target) :
    Intertwines transport sourceOperator targetOperator ↔
      intertwiningResidual transport sourceOperator targetOperator = 0 := by
  simp only [Intertwines, intertwiningResidual, sub_eq_zero]

/-- An operator-norm bound on the alignment objective supplies the pointwise
approximate-intertwining certificate consumed below. -/
theorem approxIntertwines_of_residual_opNorm_le
    (transport : Source →L[ℝ] Target)
    (sourceOperator : Source →L[ℝ] Source)
    (targetOperator : Target →L[ℝ] Target)
    (error : ℝ)
    (herror :
      ‖intertwiningResidual transport sourceOperator targetOperator‖ ≤ error) :
    ApproxIntertwines transport sourceOperator targetOperator error := by
  refine ⟨(norm_nonneg _).trans herror, ?_⟩
  intro source
  have happly :=
    (intertwiningResidual transport sourceOperator targetOperator).le_opNorm source
  calc
    ‖targetOperator (transport source) -
        transport (sourceOperator source)‖ =
        ‖intertwiningResidual transport sourceOperator targetOperator source‖ := by
          rfl
    _ ≤ ‖intertwiningResidual transport sourceOperator targetOperator‖ *
        ‖source‖ := happly
    _ ≤ error * ‖source‖ :=
      mul_le_mul_of_nonneg_right herror (norm_nonneg source)

/-- Exact intertwining is the zero-error endpoint. -/
theorem Intertwines.toApprox
    {transport : Source →L[ℝ] Target}
    {sourceOperator : Source →L[ℝ] Source}
    {targetOperator : Target →L[ℝ] Target}
    (h : Intertwines transport sourceOperator targetOperator) :
    ApproxIntertwines transport sourceOperator targetOperator 0 := by
  refine ⟨le_rfl, ?_⟩
  intro source
  have happly := DFunLike.congr_fun h source
  simp only [ContinuousLinearMap.comp_apply] at happly
  simp [happly]

/-- Exact intertwining is closed under sequential operator composition. -/
theorem Intertwines.comp
    {transport : Source →L[ℝ] Target}
    {sourceFirst sourceSecond : Source →L[ℝ] Source}
    {targetFirst targetSecond : Target →L[ℝ] Target}
    (hfirst : Intertwines transport sourceFirst targetFirst)
    (hsecond : Intertwines transport sourceSecond targetSecond) :
    Intertwines transport
      (sourceSecond ∘L sourceFirst)
      (targetSecond ∘L targetFirst) := by
  ext source
  have hfirstApply :
      targetFirst (transport source) =
        transport (sourceFirst source) := by
    simpa only [ContinuousLinearMap.comp_apply] using
      DFunLike.congr_fun hfirst source
  have hsecondApply :
      targetSecond (transport (sourceFirst source)) =
        transport (sourceSecond (sourceFirst source)) := by
    simpa only [ContinuousLinearMap.comp_apply] using
      DFunLike.congr_fun hsecond (sourceFirst source)
  change targetSecond (targetFirst (transport source)) =
    transport (sourceSecond (sourceFirst source))
  rw [hfirstApply, hsecondApply]

/-- Two approximate intertwiners compose.  Earlier error is amplified by the
later target operator; later error is evaluated on the grown source state. -/
theorem ApproxIntertwines.comp
    {transport : Source →L[ℝ] Target}
    {sourceFirst sourceSecond : Source →L[ℝ] Source}
    {targetFirst targetSecond : Target →L[ℝ] Target}
    {firstError secondError : ℝ}
    (hfirst :
      ApproxIntertwines transport sourceFirst targetFirst firstError)
    (hsecond :
      ApproxIntertwines transport sourceSecond targetSecond secondError) :
    ApproxIntertwines transport
      (sourceSecond ∘L sourceFirst)
      (targetSecond ∘L targetFirst)
      (‖targetSecond‖ * firstError + secondError * ‖sourceFirst‖) := by
  refine ⟨add_nonneg
    (mul_nonneg (norm_nonneg _) hfirst.error_nonneg)
    (mul_nonneg hsecond.error_nonneg (norm_nonneg _)), ?_⟩
  intro source
  let firstResidual :=
    targetFirst (transport source) - transport (sourceFirst source)
  let secondResidual :=
    targetSecond (transport (sourceFirst source)) -
      transport (sourceSecond (sourceFirst source))
  have hdecompose :
      targetSecond (targetFirst (transport source)) -
          transport (sourceSecond (sourceFirst source)) =
        targetSecond firstResidual + secondResidual := by
    simp only [firstResidual, secondResidual, map_sub]
    abel
  simp only [ContinuousLinearMap.comp_apply]
  rw [hdecompose]
  calc
    ‖targetSecond firstResidual + secondResidual‖ ≤
        ‖targetSecond firstResidual‖ + ‖secondResidual‖ :=
      norm_add_le _ _
    _ ≤
        ‖targetSecond‖ * (firstError * ‖source‖) +
          secondError * ‖sourceFirst source‖ := by
      apply add_le_add
      · exact (targetSecond.le_opNorm firstResidual).trans
          (mul_le_mul_of_nonneg_left (hfirst.bound source) (norm_nonneg _))
      · exact hsecond.bound (sourceFirst source)
    _ ≤
        ‖targetSecond‖ * (firstError * ‖source‖) +
          secondError * (‖sourceFirst‖ * ‖source‖) := by
      exact add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left
          (sourceFirst.le_opNorm source) hsecond.error_nonneg)
    _ =
        (‖targetSecond‖ * firstError +
          secondError * ‖sourceFirst‖) * ‖source‖ := by
      ring

/-! ## Finite operator tuples and words -/

/-- Composite operator for a word ordered from first application to last. -/
def operatorWord {Index : Type*} {State : Type*}
    [NormedAddCommGroup State] [NormedSpace ℝ State]
    (operator : Index → State →L[ℝ] State) :
    List Index → State →L[ℝ] State
  | [] => ContinuousLinearMap.id ℝ State
  | index :: rest => operatorWord operator rest ∘L operator index

/-- Recursive error budget for transporting one finite operator word. -/
def operatorWordErrorBudget {Index : Type*}
    (sourceOperator : Index → Source →L[ℝ] Source)
    (targetOperator : Index → Target →L[ℝ] Target)
    (localError : Index → ℝ) :
    List Index → ℝ
  | [] => 0
  | index :: rest =>
      ‖operatorWord targetOperator rest‖ * localError index +
        operatorWordErrorBudget sourceOperator targetOperator localError rest *
          ‖sourceOperator index‖

/-- Exact tuple alignment transports every finite operator word. -/
theorem intertwines_operatorWord
    {Index : Type*}
    (transport : Source →L[ℝ] Target)
    (sourceOperator : Index → Source →L[ℝ] Source)
    (targetOperator : Index → Target →L[ℝ] Target)
    (halign : ∀ index,
      Intertwines transport (sourceOperator index) (targetOperator index))
    (word : List Index) :
    Intertwines transport
      (operatorWord sourceOperator word)
      (operatorWord targetOperator word) := by
  induction word with
  | nil =>
      ext source
      simp [operatorWord]
  | cons index rest ih =>
      exact (halign index).comp ih

/-- Approximate tuple alignment transports every finite word with the explicit
recursive amplification budget above. -/
theorem approxIntertwines_operatorWord
    {Index : Type*}
    (transport : Source →L[ℝ] Target)
    (sourceOperator : Index → Source →L[ℝ] Source)
    (targetOperator : Index → Target →L[ℝ] Target)
    (localError : Index → ℝ)
    (halign : ∀ index,
      ApproxIntertwines transport
        (sourceOperator index) (targetOperator index) (localError index))
    (word : List Index) :
    ApproxIntertwines transport
      (operatorWord sourceOperator word)
      (operatorWord targetOperator word)
      (operatorWordErrorBudget
        sourceOperator targetOperator localError word) := by
  induction word with
  | nil =>
      refine ⟨le_rfl, ?_⟩
      intro source
      simp [operatorWord, operatorWordErrorBudget]
  | cons index rest ih =>
      simpa only [operatorWord, operatorWordErrorBudget] using
        (halign index).comp ih

/-! ## Metric compatibility and the nontriviality boundary -/

section InnerProduct

/-- Exact preservation of the local information metric represented by the
ambient real inner products. -/
def PreservesInnerProduct
    {InnerSource InnerTarget : Type*}
    [NormedAddCommGroup InnerSource] [InnerProductSpace ℝ InnerSource]
    [NormedAddCommGroup InnerTarget] [InnerProductSpace ℝ InnerTarget]
    (transport : InnerSource →L[ℝ] InnerTarget) : Prop :=
  ∀ left right,
    ⟪transport left, transport right⟫_ℝ = ⟪left, right⟫_ℝ

/-- An intertwining, metric-preserving transport makes every finite
operator-word response invariant under change of frame. -/
theorem operatorWord_inner_preserved
    {Index InnerSource InnerTarget : Type*}
    [NormedAddCommGroup InnerSource] [InnerProductSpace ℝ InnerSource]
    [NormedAddCommGroup InnerTarget] [InnerProductSpace ℝ InnerTarget]
    (transport : InnerSource →L[ℝ] InnerTarget)
    (sourceOperator : Index → InnerSource →L[ℝ] InnerSource)
    (targetOperator : Index → InnerTarget →L[ℝ] InnerTarget)
    (halign : ∀ index,
      Intertwines transport (sourceOperator index) (targetOperator index))
    (hmetric : PreservesInnerProduct transport)
    (word : List Index) (left right : InnerSource) :
    ⟪operatorWord targetOperator word (transport left),
        operatorWord targetOperator word (transport right)⟫_ℝ =
      ⟪operatorWord sourceOperator word left,
        operatorWord sourceOperator word right⟫_ℝ := by
  have hword := intertwines_operatorWord
    transport sourceOperator targetOperator halign word
  have hleft := DFunLike.congr_fun hword left
  have hright := DFunLike.congr_fun hword right
  simp only [ContinuousLinearMap.comp_apply] at hleft hright
  rw [hleft, hright]
  exact hmetric _ _

end InnerProduct

/-- The zero map satisfies every bare intertwining equation. -/
theorem zero_intertwines
    (sourceOperator : Source →L[ℝ] Source)
    (targetOperator : Target →L[ℝ] Target) :
    Intertwines (0 : Source →L[ℝ] Target)
      sourceOperator targetOperator := by
  ext source
  simp

/-- Scalar fixture for the nontriviality and positive endpoint examples. -/
def scalarOperator (coefficient : ℝ) : ℝ →L[ℝ] ℝ :=
  coefficient • ContinuousLinearMap.id ℝ ℝ

/-- Bare intertwining cannot identify mechanisms: the zero transport
intertwines two unequal scalar operators. -/
theorem zeroTransport_intertwines_unequal_scalarOperators :
    scalarOperator 1 ≠ scalarOperator 2 ∧
      Intertwines (0 : ℝ →L[ℝ] ℝ)
        (scalarOperator 1) (scalarOperator 2) := by
  constructor
  · intro heq
    have happly := DFunLike.congr_fun heq 1
    norm_num [scalarOperator] at happly
  · exact zero_intertwines _ _

/-- The zero transport fails the metric objective on a nonzero source. -/
theorem zeroTransport_not_preservesInnerProduct :
    ¬ PreservesInnerProduct (0 : ℝ →L[ℝ] ℝ) := by
  intro hmetric
  have hone := hmetric 1 1
  norm_num at hone

/-- The identity transport is a nontrivial exact positive endpoint for every
operator on one frame. -/
theorem identity_intertwines (operator : Source →L[ℝ] Source) :
    Intertwines (ContinuousLinearMap.id ℝ Source) operator operator := by
  ext source
  simp

/-- Zero claimed error is substantive for a nonzero transport: identity does
not exactly intertwine the unequal scalar fixture. -/
theorem identity_not_zeroApproxIntertwines_unequal_scalarOperators :
    ¬ ApproxIntertwines
      (ContinuousLinearMap.id ℝ ℝ)
      (scalarOperator 1) (scalarOperator 2) 0 := by
  intro h
  have hone := h.bound 1
  norm_num [scalarOperator] at hone

/-! ## Exactly-once transport of additive evidence -/

end

end CausalEvidenceTransport

universe uId uEvidence uTransported

namespace InnovationPacket

/-- Change the evidence frame while preserving causal identity. -/
def mapEvidence {Id : Type uId}
    {Evidence : Type uEvidence} {Transported : Type uTransported}
    [AddZeroClass Evidence] [AddZeroClass Transported]
    (transport : Evidence →+ Transported)
    (packet : InnovationPacket Id Evidence) :
    InnovationPacket Id Transported where
  id := packet.id
  evidence := transport packet.evidence

end InnovationPacket

namespace CausalInnovationLedger

/-- Change the payload frame of every accepted causal innovation. -/
def mapEvidence {Id : Type uId}
    {Evidence : Type uEvidence} {Transported : Type uTransported}
    [AddZeroClass Evidence] [AddZeroClass Transported]
    (transport : Evidence →+ Transported)
    (ledger : CausalInnovationLedger Id Evidence) :
    CausalInnovationLedger Id Transported where
  seen := ledger.seen
  payload := fun identity => transport (ledger.payload identity)

/-- Transport commutes with the finite accepted-evidence total. -/
theorem total_mapEvidence {Id : Type uId}
    {Evidence : Type uEvidence} {Transported : Type uTransported}
    [AddCommMonoid Evidence] [AddCommMonoid Transported]
    (transport : Evidence →+ Transported)
    (ledger : CausalInnovationLedger Id Evidence) :
    CausalInnovationLedger.total (mapEvidence transport ledger) =
      transport (CausalInnovationLedger.total ledger) := by
  simp [CausalInnovationLedger.total, mapEvidence]

/-- Lawful evidence transport commutes with exactly-once assimilation. -/
theorem mapEvidence_assimilate {Id : Type uId}
    {Evidence : Type uEvidence} {Transported : Type uTransported}
    [AddZeroClass Evidence] [AddZeroClass Transported]
    [DecidableEq Id]
    (transport : Evidence →+ Transported)
    (ledger : CausalInnovationLedger Id Evidence)
    (packet : InnovationPacket Id Evidence) :
    mapEvidence transport
        (CausalInnovationLedger.assimilate ledger packet) =
      CausalInnovationLedger.assimilate (mapEvidence transport ledger)
        (packet.mapEvidence transport) := by
  by_cases hseen : packet.id ∈ ledger.seen
  · simp [CausalInnovationLedger.assimilate, hseen, mapEvidence,
      InnovationPacket.mapEvidence]
  · simp only [CausalInnovationLedger.assimilate, hseen, ↓reduceIte,
      mapEvidence, InnovationPacket.mapEvidence]
    congr 1
    funext identity
    by_cases hid : identity = packet.id
    · subst identity
      simp [Function.update]
    · simp [Function.update, hid]

/-- Consequently a fresh causal identity contributes one transported payload,
not one payload per manifestation. -/
theorem total_mapEvidence_assimilate_of_fresh {Id : Type uId}
    {Evidence : Type uEvidence} {Transported : Type uTransported}
    [AddCommMonoid Evidence] [AddCommMonoid Transported]
    [DecidableEq Id]
    (transport : Evidence →+ Transported)
    (ledger : CausalInnovationLedger Id Evidence)
    (packet : InnovationPacket Id Evidence)
    (hfresh : packet.id ∉ ledger.seen) :
    CausalInnovationLedger.total
        (mapEvidence transport
          (CausalInnovationLedger.assimilate ledger packet)) =
      transport (CausalInnovationLedger.total ledger) +
        transport packet.evidence := by
  rw [total_mapEvidence,
    CausalInnovationLedger.total_assimilate_of_fresh ledger packet hfresh,
    map_add]

end CausalInnovationLedger

#print axioms CausalEvidenceTransport.approxIntertwines_of_residual_opNorm_le
#print axioms CausalEvidenceTransport.ApproxIntertwines.comp
#print axioms CausalEvidenceTransport.intertwines_operatorWord
#print axioms CausalEvidenceTransport.approxIntertwines_operatorWord
#print axioms CausalEvidenceTransport.operatorWord_inner_preserved
#print axioms CausalEvidenceTransport.zeroTransport_intertwines_unequal_scalarOperators
#print axioms CausalInnovationLedger.mapEvidence_assimilate
#print axioms CausalInnovationLedger.total_mapEvidence_assimilate_of_fresh

end Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier
