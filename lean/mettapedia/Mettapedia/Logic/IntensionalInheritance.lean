import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mettapedia.Logic.AbstractInheritance
import Mettapedia.Logic.ConceptOntology.Basic
import Mettapedia.InformationTheory.MutualInformation

/-!
# Intensional Inheritance: Semantic Base and Information-Theoretic Surface

This module now treats PLN-style inheritance as a specialization of the existing
abstract inheritance stack:

- `AbstractInheritance.DualConcept` for crisp extent/intent semantics
- `AbstractInheritance.Interpretation` for semantic meaning of a carrier
- `ConceptOntology.EvidenceMembershipContext` for graded/additive membership evidence

The Chapter-12 information-theoretic scalar stays available here, but it is now
understood as a score layered on top of semantic inheritance rather than as the
primary semantic object itself.
-/

namespace Mettapedia.Logic.IntensionalInheritance

open Real

/-! ## §1: Primary semantic objects -/

/-- Crisp semantic concepts for the inheritance layer. -/
abbrev DualConcept (Obj : Type*) (Attr : Type*) :=
  Mettapedia.Logic.AbstractInheritance.DualConcept Obj Attr

/-- A carrier acquires inheritance semantics by interpretation into dual concepts. -/
abbrev Interpretation (Carrier : Type*) (Obj : Type*) (Attr : Type*) :=
  Mettapedia.Logic.AbstractInheritance.Interpretation Carrier Obj Attr

/-- Evidence-valued membership is the graded semantic substrate for PLN inheritance. -/
abbrev EvidenceMembershipContext
    (State : Type*) (Obj : Type*) (Con : Type*) (Ev : Type*)
    [Mettapedia.Logic.EvidenceClass.EvidenceType State] [AddCommMonoid Ev] :=
  Mettapedia.Logic.ConceptOntology.EvidenceMembershipContext State Obj Con Ev

/-- Evidence-valued concepts are fixed points of the extent/intent adjunction. -/
abbrev EvidenceConcept {Obj : Type*} {Con : Type*} {Q : Type*}
    [CommSemigroup Q] [CompleteLattice Q] [IsQuantale Q]
    (M : Obj → Con → Q) :=
  Mettapedia.Logic.ConceptOntology.EvidenceConcept M

namespace EvidenceMembershipContext

variable {State : Type*} {Obj : Type*} {Con : Type*} {Q : Type*}
variable [Mettapedia.Logic.EvidenceClass.EvidenceType State] [AddCommMonoid Q] [Preorder Q]

/-- The crisp abstract-inheritance interpretation induced by the membership
evidence carried by a particular world/model state and evidence gate. -/
noncomputable def crispInterpretationAt
    (M : Mettapedia.Logic.ConceptOntology.EvidenceMembershipContext State Obj Con Q)
    (G : Mettapedia.Logic.ConceptOntology.EvidenceGate Q)
    (W : State) :
    Mettapedia.Logic.AbstractInheritance.Interpretation Con Obj Con :=
  Mettapedia.Logic.AbstractInheritance.crispInterpretation G (M.memberEvidence W)

/-- Extensional inheritance at a fixed world/model state. -/
def ExtensionalInheritsAt
    (M : Mettapedia.Logic.ConceptOntology.EvidenceMembershipContext State Obj Con Q)
    (G : Mettapedia.Logic.ConceptOntology.EvidenceGate Q)
    (W : State) (c d : Con) : Prop :=
  (crispInterpretationAt M G W).ExtensionalInherits c d

/-- Intensional inheritance at a fixed world/model state. -/
def IntensionalInheritsAt
    (M : Mettapedia.Logic.ConceptOntology.EvidenceMembershipContext State Obj Con Q)
    (G : Mettapedia.Logic.ConceptOntology.EvidenceGate Q)
    (W : State) (c d : Con) : Prop :=
  (crispInterpretationAt M G W).IntensionalInherits c d

/-- Full dual inheritance at a fixed world/model state. -/
def InheritsAt
    (M : Mettapedia.Logic.ConceptOntology.EvidenceMembershipContext State Obj Con Q)
    (G : Mettapedia.Logic.ConceptOntology.EvidenceGate Q)
    (W : State) (c d : Con) : Prop :=
  (crispInterpretationAt M G W).Inherits c d

/-- Pairwise monotonicity relation induced from the abstract inheritance base. -/
def PairSubsetRelAt
    (M : Mettapedia.Logic.ConceptOntology.EvidenceMembershipContext State Obj Con Q)
    (G : Mettapedia.Logic.ConceptOntology.EvidenceGate Q)
    (W : State) (a b c d : Con) : Prop :=
  (crispInterpretationAt M G W).PairSubsetRel a b c d

theorem extensionalInheritsAt_iff
    (M : Mettapedia.Logic.ConceptOntology.EvidenceMembershipContext State Obj Con Q)
    (G : Mettapedia.Logic.ConceptOntology.EvidenceGate Q)
    (W : State) (c d : Con) :
    ExtensionalInheritsAt M G W c d ↔
      Mettapedia.Logic.ConceptOntology.crispExtensionalInherits G (M.memberEvidence W) c d := by
  simpa [ExtensionalInheritsAt, crispInterpretationAt] using
    (Mettapedia.Logic.AbstractInheritance.crispInterpretation_extensionalInherits_iff
      G (M.memberEvidence W) c d)

theorem inheritsAt_iff
    (M : Mettapedia.Logic.ConceptOntology.EvidenceMembershipContext State Obj Con Q)
    (G : Mettapedia.Logic.ConceptOntology.EvidenceGate Q)
    (W : State) (c d : Con) :
    InheritsAt M G W c d ↔
      Mettapedia.Logic.ConceptOntology.crispExtensionalInherits G (M.memberEvidence W) c d := by
  simpa [InheritsAt, crispInterpretationAt] using
    (Mettapedia.Logic.AbstractInheritance.crispInterpretation_inherits_iff
      G (M.memberEvidence W) c d)

theorem extensionalInheritsAt_iff_inheritsAt
    (M : Mettapedia.Logic.ConceptOntology.EvidenceMembershipContext State Obj Con Q)
    (G : Mettapedia.Logic.ConceptOntology.EvidenceGate Q)
    (W : State) (c d : Con) :
    ExtensionalInheritsAt M G W c d ↔ InheritsAt M G W c d := by
  rw [extensionalInheritsAt_iff, inheritsAt_iff]

theorem pairSubsetRelAt_iff
    (M : Mettapedia.Logic.ConceptOntology.EvidenceMembershipContext State Obj Con Q)
    (G : Mettapedia.Logic.ConceptOntology.EvidenceGate Q)
    (W : State) (a b c d : Con) :
    PairSubsetRelAt M G W a b c d ↔
      InheritsAt M G W c a ∧ InheritsAt M G W b d := by
  rfl

end EvidenceMembershipContext

/-! ## §2: Finite interpreted counting semantics

For Chapter-12-style numeric inheritance, the abstract `Interpretation` needs a
finite object carrier so we can read probabilities from extent cardinalities.
-/

namespace Interpretation

section FiniteCounting

variable {Carrier : Type*} {Obj : Type*} {Attr : Type*}
variable [Fintype Obj]

/-- Cardinality of the interpreted extent of a carrier element. -/
noncomputable def extentCount
    (I : Mettapedia.Logic.AbstractInheritance.Interpretation Carrier Obj Attr)
    (c : Carrier) : ℕ := by
  classical
  exact Fintype.card {x : Obj // x ∈ (I.meaning c).extent}

/-- Cardinality of the overlap of two interpreted extents. -/
noncomputable def jointExtentCount
    (I : Mettapedia.Logic.AbstractInheritance.Interpretation Carrier Obj Attr)
    (a b : Carrier) : ℕ := by
  classical
  exact Fintype.card {x : Obj // x ∈ (I.meaning a).extent ∧ x ∈ (I.meaning b).extent}

/-- Finite prior probability `P(W)` read from an interpreted extent. -/
noncomputable def finitePriorProb
    (I : Mettapedia.Logic.AbstractInheritance.Interpretation Carrier Obj Attr)
    (w : Carrier) : ℝ :=
  (extentCount I w : ℝ) / Fintype.card Obj

/-- Plain-language alias for the prior of a candidate superconcept in the
finite interpreted semantics. -/
noncomputable def finiteInheritancePrior
    (I : Mettapedia.Logic.AbstractInheritance.Interpretation Carrier Obj Attr)
    (superConcept : Carrier) : ℝ :=
  finitePriorProb I superConcept

/-- Finite extensional inheritance `P(W | F)` read from interpreted extents. -/
noncomputable def finiteExtensionalProb
    (I : Mettapedia.Logic.AbstractInheritance.Interpretation Carrier Obj Attr)
    (f w : Carrier) : ℝ :=
  if _h : extentCount I f = 0 then
    0
  else
    (jointExtentCount I f w : ℝ) / extentCount I f

/-- Plain-language alias for finite extensional inheritance strength from a
subconcept to a superconcept. -/
noncomputable def finiteInheritanceStrength
    (I : Mettapedia.Logic.AbstractInheritance.Interpretation Carrier Obj Attr)
    (subConcept superConcept : Carrier) : ℝ :=
  finiteExtensionalProb I subConcept superConcept

/-- Pointwise Chapter-12 score derived from finite interpreted counting
semantics. -/
noncomputable def finitePointwiseLogRatioBits
    (I : Mettapedia.Logic.AbstractInheritance.Interpretation Carrier Obj Attr)
    (f w : Carrier) : ℝ :=
  Mettapedia.InformationTheory.logRatioInformationGainBits
    (finiteExtensionalProb I f w) (finitePriorProb I w)

/-- Plain-language alias for the Chapter-12 log-ratio score of an inheritance
query. -/
noncomputable def finiteInheritanceLogRatioBits
    (I : Mettapedia.Logic.AbstractInheritance.Interpretation Carrier Obj Attr)
    (subConcept superConcept : Carrier) : ℝ :=
  finitePointwiseLogRatioBits I subConcept superConcept

@[simp] theorem finiteInheritancePrior_eq
    (I : Mettapedia.Logic.AbstractInheritance.Interpretation Carrier Obj Attr)
    (superConcept : Carrier) :
    finiteInheritancePrior I superConcept = finitePriorProb I superConcept := rfl

@[simp] theorem finiteInheritanceStrength_eq
    (I : Mettapedia.Logic.AbstractInheritance.Interpretation Carrier Obj Attr)
    (subConcept superConcept : Carrier) :
    finiteInheritanceStrength I subConcept superConcept =
      finiteExtensionalProb I subConcept superConcept := rfl

@[simp] theorem finiteInheritanceLogRatioBits_eq
    (I : Mettapedia.Logic.AbstractInheritance.Interpretation Carrier Obj Attr)
    (subConcept superConcept : Carrier) :
    finiteInheritanceLogRatioBits I subConcept superConcept =
      finitePointwiseLogRatioBits I subConcept superConcept := rfl

/-- Finite interpreted Chapter-12 formula. -/
theorem finite_goertzel_formula
    (I : Mettapedia.Logic.AbstractInheritance.Interpretation Carrier Obj Attr)
    {f w : Carrier}
    (hExt : 0 < finiteExtensionalProb I f w)
    (hPrior : 0 < finitePriorProb I w) :
    finiteExtensionalProb I f w =
      finitePriorProb I w * (2 : ℝ).rpow (finitePointwiseLogRatioBits I f w) := by
  unfold finitePointwiseLogRatioBits
  exact
    Mettapedia.InformationTheory.posterior_eq_prior_mul_two_rpow_logRatioInformationGainBits
      hExt hPrior

/-- Rearranged finite interpreted Chapter-12 formula. -/
theorem finite_pointwise_logRatio_reduction
    (I : Mettapedia.Logic.AbstractInheritance.Interpretation Carrier Obj Attr)
    {f w : Carrier}
    (hExt : 0 < finiteExtensionalProb I f w)
    (hPrior : 0 < finitePriorProb I w) :
    (2 : ℝ).rpow (finitePointwiseLogRatioBits I f w) =
      finiteExtensionalProb I f w / finitePriorProb I w := by
  have h := finite_goertzel_formula I hExt hPrior
  have hPriorNe : finitePriorProb I w ≠ 0 := ne_of_gt hPrior
  field_simp [hPriorNe] at h ⊢
  linarith [h]

end FiniteCounting

end Interpretation

/-! ## §3: Information-theoretic score surface

The Chapter-12 scalar lives above the semantic base. It is the evidence-level
log-ratio score relating an observed conditional term to a prior term.
-/

/-- Evidence-level log-ratio information gain in bits.

Given:
- `strength = P(W | F)`
- `prior = P(W)`

this returns `log₂(strength / prior)` when both terms are positive. -/
noncomputable abbrev logRatioInformationGainFromEvidence (strength prior : ℝ) : ℝ :=
  Mettapedia.InformationTheory.logRatioInformationGainBits strength prior

theorem logRatioInformationGainFromEvidence_eq_log2_ratio
    {strength prior : ℝ}
    (hStrength : 0 < strength) (hPrior : 0 < prior) :
    logRatioInformationGainFromEvidence strength prior =
      Real.log (strength / prior) / Real.log 2 :=
  Mettapedia.InformationTheory.logRatioInformationGainBits_eq_log2_ratio hStrength hPrior

theorem strength_eq_prior_mul_two_rpow_logRatioInformationGainFromEvidence
    {strength prior : ℝ}
    (hStrength : 0 < strength) (hPrior : 0 < prior) :
    strength = prior * (2 : ℝ).rpow (logRatioInformationGainFromEvidence strength prior) :=
  Mettapedia.InformationTheory.posterior_eq_prior_mul_two_rpow_logRatioInformationGainBits
    hStrength hPrior

/-! ## §4: Honest Chapter-12 theorems at the evidence level -/

/-- **Goertzel-style unifying formula** at the evidence level.

Given positive prior and conditional terms, the observed conditional equals the
prior scaled by `2` to the pointwise Chapter-12 log-ratio score. -/
theorem goertzel_formula
    {strength prior : ℝ}
    (hStrength : 0 < strength) (hPrior : 0 < prior) :
    strength = prior * (2 : ℝ).rpow (logRatioInformationGainFromEvidence strength prior) := by
  exact strength_eq_prior_mul_two_rpow_logRatioInformationGainFromEvidence hStrength hPrior

/-- Rearranged evidence-level reduction theorem. -/
theorem pointwise_logRatio_reduction
    {strength prior : ℝ}
    (hStrength : 0 < strength) (hPrior : 0 < prior) :
    (2 : ℝ).rpow (logRatioInformationGainFromEvidence strength prior) = strength / prior := by
  have h := goertzel_formula hStrength hPrior
  have hPriorNe : prior ≠ 0 := ne_of_gt hPrior
  field_simp [hPriorNe] at h ⊢
  linarith [h]

-- Hook to Optimality: Bayes mixture provides the "universal" information score.
-- Hook to MarkovExchangeability: sufficient statistics reduce empirical score computation.

/-! ## §5: Small semantic examples -/

section Examples

variable {α : Type*}

/-- One-attribute semantic concept, presented directly as extent/intent. -/
def unaryAttributeConcept (name : String) (holds : α → Prop) :
    Mettapedia.Logic.AbstractInheritance.DualConcept α String where
  extent := {x | holds x}
  intent := {label | label = name}

/-- Example: "creatures with hearts" as a semantic extent/intent object. -/
def heartConcept (hasHeart : α → Prop) :
    Mettapedia.Logic.AbstractInheritance.DualConcept α String :=
  unaryAttributeConcept "heart" hasHeart

/-- Example: "creatures with kidneys" as a semantic extent/intent object. -/
def kidneyConcept (hasKidney : α → Prop) :
    Mettapedia.Logic.AbstractInheritance.DualConcept α String :=
  unaryAttributeConcept "kidney" hasKidney

end Examples

end Mettapedia.Logic.IntensionalInheritance
