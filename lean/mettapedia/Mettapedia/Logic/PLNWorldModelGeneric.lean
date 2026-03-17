import Mettapedia.Logic.PLNWorldModelAdditive
import Mettapedia.Logic.ConjugateEvidenceSurface

/-!
# Generic PLN World Models

This module generalizes the binary `PLNWorldModel.BinaryWorldModel` interface to arbitrary
additive extract carriers.

The existing `BinaryWorldModel` remains the PLN-facing specialization with extract codomain
`BinaryEvidence = (n⁺, n⁻)`.  This module adds a parallel generic interface:

- `AdditiveWorldModel State Query Ev`
- additive query extraction into any `AddCommMonoid Ev`
- count/confidence views when `Ev` carries `ConjugateEvidence`

This is the right layer for Dirichlet- and Normal-Gamma-valued query extraction.
It does not replace the binary PLN layer; it sits strictly below it.
-/

namespace Mettapedia.Logic.PLNWorldModelGeneric

open scoped ENNReal
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNWorldModelAdditive
open Mettapedia.Logic.ConjugateEvidenceSurface
open Mettapedia.Logic.EvidenceDirichlet

/-- A revisable posterior state supporting additive extraction into an arbitrary
conjugate or extract-like carrier `Ev`.

`State` keeps the same revision discipline as the binary `BinaryWorldModel`: it is an
`EvidenceType`, so state revision is additive.  The codomain of extraction is
now any `AddCommMonoid Ev` rather than the fixed binary carrier `BinaryEvidence`.
-/
class AdditiveWorldModel (State Query Ev : Type*) [EvidenceType State] [AddCommMonoid Ev] where
  /-- Extract a value for a query from a state. -/
  extract : State → Query → Ev
  /-- Extraction commutes with additive revision in the state. -/
  extract_add : ∀ W₁ W₂ q, extract (W₁ + W₂) q = extract W₁ q + extract W₂ q

namespace AdditiveWorldModel

variable {State Query Ev : Type*}
variable [EvidenceType State] [AddCommMonoid Ev] [AdditiveWorldModel State Query Ev]

/-- Convenience form of the additive extraction law. -/
theorem extract_add' (W₁ W₂ : State) (q : Query) :
    AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := Ev) (W₁ + W₂) q =
      AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := Ev) W₁ q +
        AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := Ev) W₂ q :=
  AdditiveWorldModel.extract_add (State := State) (Query := Query) (Ev := Ev) W₁ W₂ q

/-- Generic query equivalence: two queries extract identical `Ev`-extract from every state. -/
def GMQueryEq (q₁ q₂ : Query) : Prop :=
  ∀ W : State,
    AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := Ev) W q₁ =
      AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := Ev) W q₂

theorem GMQueryEq.refl (q : Query) :
    GMQueryEq (State := State) (Query := Query) (Ev := Ev) q q := by
  intro W
  rfl

theorem GMQueryEq.symm {q₁ q₂ : Query} :
    GMQueryEq (State := State) (Query := Query) (Ev := Ev) q₁ q₂ →
      GMQueryEq (State := State) (Query := Query) (Ev := Ev) q₂ q₁ := by
  intro h W
  simpa using (h W).symm

theorem GMQueryEq.trans {q₁ q₂ q₃ : Query} :
    GMQueryEq (State := State) (Query := Query) (Ev := Ev) q₁ q₂ →
    GMQueryEq (State := State) (Query := Query) (Ev := Ev) q₂ q₃ →
      GMQueryEq (State := State) (Query := Query) (Ev := Ev) q₁ q₃ := by
  intro h12 h23 W
  simpa [h12 W] using h23 W

section Conjugate

variable [ConjugateEvidence Ev]

/-- Observation-count view of a generic query. -/
noncomputable def queryObservationCount (W : State) (q : Query) : ℝ≥0∞ :=
  ConjugateEvidence.observationCount
    (AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := Ev) W q)

/-- Count-induced confidence view of a generic query. -/
noncomputable def queryObservationConfidence (κ : ℝ≥0∞) (W : State) (q : Query) : ℝ≥0∞ :=
  observationConfidence κ
    (AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := Ev) W q)

/-- Equality transport for the count view. -/
theorem GMQueryEq.to_queryObservationCount {q₁ q₂ : Query} :
    GMQueryEq (State := State) (Query := Query) (Ev := Ev) q₁ q₂ →
    ∀ W : State,
      queryObservationCount (State := State) (Query := Query) (Ev := Ev) W q₁ =
        queryObservationCount (State := State) (Query := Query) (Ev := Ev) W q₂ := by
  intro h W
  unfold queryObservationCount
  simpa using congrArg ConjugateEvidence.observationCount (h W)

/-- Equality transport for the count-induced confidence view. -/
theorem GMQueryEq.to_queryObservationConfidence {q₁ q₂ : Query}
    (h : GMQueryEq (State := State) (Query := Query) (Ev := Ev) q₁ q₂)
    (κ : ℝ≥0∞) (W : State) :
    queryObservationConfidence (State := State) (Query := Query) (Ev := Ev) κ W q₁ =
      queryObservationConfidence (State := State) (Query := Query) (Ev := Ev) κ W q₂ := by
  unfold queryObservationConfidence
  simpa using congrArg (observationConfidence κ) (h W)

end Conjugate

end AdditiveWorldModel

/-- The existing binary PLN world-model interface is the specialization of the
generic interface at `Ev = BinaryEvidence`. -/
noncomputable instance instGenericWorldModelOfWorldModel
    {State Query : Type*} [EvidenceType State] [BinaryWorldModel State Query] :
    AdditiveWorldModel State Query BinaryEvidence where
  extract := BinaryWorldModel.evidence (State := State) (Query := Query)
  extract_add := BinaryWorldModel.evidence_add (State := State) (Query := Query)

namespace AdditiveWorldModel

section BinaryBridge

variable {State Query : Type*}
variable [EvidenceType State] [BinaryWorldModel State Query]

@[simp] theorem evidence_eq_binary_evidence (W : State) (q : Query) :
    AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := BinaryEvidence) W q =
      BinaryWorldModel.evidence (State := State) (Query := Query) W q :=
  rfl

@[simp] theorem queryObservationCount_eq_binary_total (W : State) (q : Query) :
    queryObservationCount (State := State) (Query := Query) (Ev := BinaryEvidence) W q =
      (BinaryWorldModel.evidence (State := State) (Query := Query) W q).total := by
  rfl

theorem queryObservationConfidence_eq_queryConfidence
    (κ : ℝ≥0∞) (W : State) (q : Query) :
    queryObservationConfidence (State := State) (Query := Query) (Ev := BinaryEvidence) κ W q =
      BinaryWorldModel.queryConfidence (State := State) (Query := Query) κ W q := by
  unfold queryObservationConfidence BinaryWorldModel.queryConfidence
  simpa [evidence_eq_binary_evidence (State := State) (Query := Query) W q] using
    beta_observationConfidence_eq_toConfidence κ
      (AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := BinaryEvidence) W q)

end BinaryBridge

/-! ## Generic multiset world models

The multiset construction from `PLNWorldModelAdditive` works for any additive
carrier `Ev`, not just binary `BinaryEvidence`.
-/

/-- Any atomic `Ev`-valued contribution induces a multiset-based generic world model. -/
noncomputable def genericWorldModelOfAtomicEvidence
    {Obs Query Ev : Type*} [AddCommMonoid Ev]
    (a : GenAtomicEvidenceContribution Obs Query Ev) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    AdditiveWorldModel (Multiset Obs) Query Ev := by
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  exact
    { extract := genAdditiveExtension a
      extract_add := genAdditiveExtension_add a }

/-- For a unit-observation atomic contribution, the generic query observation count
    equals the multiset cardinality. -/
theorem queryObservationCount_of_unit
    {Obs Query Ev : Type*} [ConjugateEvidence Ev]
    (a : GenAtomicEvidenceContribution Obs Query Ev)
    (hunit : ∀ o q, ConjugateEvidence.observationCount (a o q) = 1)
    (σ : Multiset Obs) (q : Query) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    @queryObservationCount (Multiset Obs) Query Ev _ _
      (genericWorldModelOfAtomicEvidence a) _ σ q = (σ.card : ℝ≥0∞) := by
  simpa [queryObservationCount, genericWorldModelOfAtomicEvidence] using
    observationCount_genAdditiveExtension_of_unit a hunit σ q

/-- For a unit-observation atomic contribution, the generic query observation confidence
    equals `σ.card / (σ.card + κ)`. -/
theorem queryObservationConfidence_of_unit
    {Obs Query Ev : Type*} [ConjugateEvidence Ev]
    (κ : ℝ≥0∞)
    (a : GenAtomicEvidenceContribution Obs Query Ev)
    (hunit : ∀ o q, ConjugateEvidence.observationCount (a o q) = 1)
    (σ : Multiset Obs) (q : Query) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    @queryObservationConfidence (Multiset Obs) Query Ev _ _
      (genericWorldModelOfAtomicEvidence a) _ κ σ q =
        (σ.card : ℝ≥0∞) / ((σ.card : ℝ≥0∞) + κ) := by
  simpa [queryObservationConfidence, genericWorldModelOfAtomicEvidence] using
    observationConfidence_genAdditiveExtension_of_unit κ a hunit σ q

/-- If a state is idempotent under revision, then every finite query observation
count extracted from it must be zero. -/
theorem queryObservationCount_eq_zero_of_revision_idempotent
    {State Query Ev : Type*}
    [EvidenceType State] [ConjugateEvidence Ev] [AdditiveWorldModel State Query Ev]
    (W : State) (q : Query)
    (hfin :
      queryObservationCount (State := State) (Query := Query) (Ev := Ev) W q ≠ ⊤)
    (hidem : W + W = W) :
    queryObservationCount (State := State) (Query := Query) (Ev := Ev) W q = 0 := by
  unfold queryObservationCount
  apply observationCount_eq_zero_of_add_idempotent hfin
  have heq := AdditiveWorldModel.extract_add' (State := State) (Query := Query) (Ev := Ev) W W q
  simpa [hidem] using heq.symm

/-- A state with finite, nonzero query observation count cannot be idempotent
under revision. -/
theorem not_revision_idempotent_of_finite_nonzero_queryObservationCount
    {State Query Ev : Type*}
    [EvidenceType State] [ConjugateEvidence Ev] [AdditiveWorldModel State Query Ev]
    (W : State) (q : Query)
    (hfin :
      queryObservationCount (State := State) (Query := Query) (Ev := Ev) W q ≠ ⊤)
    (hne :
      queryObservationCount (State := State) (Query := Query) (Ev := Ev) W q ≠ 0) :
    W + W ≠ W := by
  intro hidem
  exact hne (queryObservationCount_eq_zero_of_revision_idempotent
    (State := State) (Query := Query) (Ev := Ev) W q hfin hidem)

/-- Dirichlet specialization: when each atomic contribution has `total = 1`,
    the generic query observation count equals the multiset cardinality.

    This is the first concrete non-binary instantiation of the generic WM layer. -/
theorem dirichlet_queryObservationCount_of_single {k : ℕ}
    {Obs Query : Type*}
    (a : GenAtomicEvidenceContribution Obs Query (MultiEvidence k))
    (hunit : ∀ o q, (a o q).total = 1)
    (σ : Multiset Obs) (q : Query) :
    letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
    @queryObservationCount (Multiset Obs) Query (MultiEvidence k) _ _
      (genericWorldModelOfAtomicEvidence a) _ σ q = (σ.card : ℝ≥0∞) := by
  have hobs : ∀ o q, ConjugateEvidence.observationCount (a o q) = 1 := by
    intro o q
    show (↑(a o q).total : ℝ≥0∞) = 1
    simp [hunit o q]
  exact queryObservationCount_of_unit a hobs σ q

end AdditiveWorldModel

-- Forward alias note: AdditiveWorldModel lacks extract_zero.
-- The zero-preserving version is ZeroPreservingGWM in WorldModelCore.lean
-- or GSLTEvidenceAssignment in GSLTEvidence.lean.
-- The canonical `BinaryWorldModel` name will eventually go to the
-- zero-preserving version parameterized by V.

end Mettapedia.Logic.PLNWorldModelGeneric
