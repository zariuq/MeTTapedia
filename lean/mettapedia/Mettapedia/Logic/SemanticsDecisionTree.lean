import Mettapedia.Logic.PLN_KS_Bridge
import Mettapedia.Logic.NARSEvidenceBridge
import Mettapedia.Logic.NARSSecondOrderProbability
import Mettapedia.ProbabilityTheory.Hypercube.Basic

/-!
# BinaryEvidence/Probability Decision Tree (PLN + NARS)

This note is a compact "which semantics should I use?" guide.

## Core idea

Use the strongest layer justified by assumptions:

1. **Probability layer** (scalar `[0,1]` formulas)
   - Use when comparability/precision gates are justified.
2. **BinaryEvidence/Heyting layer** (default)
   - Use when evidence values can be incomparable or assumptions are uncertain.
3. **Interval/imprecise layer** (weaker-than-KS setting)
   - Use when precision is explicitly imprecise (bounds, credal style semantics).
4. **NARS mirror layer**
   - Use for parity with `lib_nars.metta`; keep in mind operational clamps.

## Concrete theorem pointers

- No faithful scalarization in general evidence order:
  `PLN_KS_Bridge.evidence_no_point_representation`.
- K&S/classical commutative quantale slice:
  `Hypercube.knuthSkilling_has_standard_pln`.
- Weaker-than-KS interval slice:
  `Hypercube.dempsterShafer_quantale`,
  `Hypercube.dempsterShafer_has_interval_pln`.
- NARS core revision as evidence aggregation:
  `NARSSecondOrderProbability.truthRevisionCore_toEvidence`,
  `NARSEvidenceBridge.nars_revision_is_evidence_aggregation`.
- NARS mirror includes implementation guards:
  `NARSMettaTruthFunctions.truthRevision`.
-/

namespace Mettapedia.Logic.SemanticsDecisionTree

/-- High-level assumption profile for choosing the semantic layer. -/
inductive KnowledgeProfile where
  /-- Total/precise regime where scalar probability is justified. -/
  | preciseComparable
  /-- BinaryEvidence may be incomparable; use evidence-level semantics directly. -/
  | evidentialIncomparable
  /-- Explicitly imprecise regime (interval/credal semantics). -/
  | impreciseInterval
  /-- Exact mirror/parity with NARS MeTTa formulas. -/
  | narsMirror
  deriving DecidableEq, Repr

/-- Recommended semantic layer for each profile. -/
inductive SemanticLayer where
  | probabilityScalar
  | evidenceHeyting
  | intervalImprecise
  | narsOperationalMirror
  deriving DecidableEq, Repr

/-- Decision tree: pick the strongest justified layer, not stronger. -/
def chooseLayer : KnowledgeProfile → SemanticLayer
  | .preciseComparable => .probabilityScalar
  | .evidentialIncomparable => .evidenceHeyting
  | .impreciseInterval => .intervalImprecise
  | .narsMirror => .narsOperationalMirror

example : chooseLayer .preciseComparable = .probabilityScalar := rfl
example : chooseLayer .evidentialIncomparable = .evidenceHeyting := rfl
example : chooseLayer .impreciseInterval = .intervalImprecise := rfl
example : chooseLayer .narsMirror = .narsOperationalMirror := rfl

/-- Classify a concrete hypercube vertex into a knowledge profile.
This is a practical gate: quantale type drives the recommended layer. -/
def profileOfVertex
    (v : Mettapedia.ProbabilityTheory.Hypercube.ProbabilityVertex) :
    KnowledgeProfile :=
  match Mettapedia.ProbabilityTheory.Hypercube.quantaleTypeOf v with
  | Mettapedia.ProbabilityTheory.Hypercube.QuantaleType.commutative => .preciseComparable
  | Mettapedia.ProbabilityTheory.Hypercube.QuantaleType.interval => .impreciseInterval
  | Mettapedia.ProbabilityTheory.Hypercube.QuantaleType.noncommutative => .evidentialIncomparable
  | Mettapedia.ProbabilityTheory.Hypercube.QuantaleType.free => .evidentialIncomparable
  | Mettapedia.ProbabilityTheory.Hypercube.QuantaleType.boolean => .evidentialIncomparable
  | Mettapedia.ProbabilityTheory.Hypercube.QuantaleType.monotone => .evidentialIncomparable
  | Mettapedia.ProbabilityTheory.Hypercube.QuantaleType.booleanAlgebra => .evidentialIncomparable

/-- Concrete gate example: K&S vertex recommends scalar probability layer. -/
theorem gate_example_knuthSkilling :
    chooseLayer
      (profileOfVertex Mettapedia.ProbabilityTheory.Hypercube.knuthSkilling) =
      .probabilityScalar := rfl

/-- Concrete gate example: Dempster-Shafer vertex recommends interval/imprecise layer. -/
theorem gate_example_dempsterShafer :
    chooseLayer
      (profileOfVertex Mettapedia.ProbabilityTheory.Hypercube.dempsterShafer) =
      .intervalImprecise := rfl

/-! ## Hard gates (formal facts) -/

/-- If evidence values are incomparable, no faithful scalar order map exists. -/
theorem evidence_blocks_faithful_scalarization :
    ¬ ∃ Θ : Mettapedia.Logic.EvidenceQuantale.BinaryEvidence → ℝ,
      ∀ a b : Mettapedia.Logic.EvidenceQuantale.BinaryEvidence, a ≤ b ↔ Θ a ≤ Θ b :=
  Mettapedia.Logic.PLN_KS_Bridge.evidence_no_point_representation

/-- K&S sits in the standard commutative quantale inference slice. -/
theorem ks_has_standard_inference :
    Mettapedia.ProbabilityTheory.Hypercube.hasStandardPLNInference
      Mettapedia.ProbabilityTheory.Hypercube.knuthSkilling :=
  Mettapedia.ProbabilityTheory.Hypercube.knuthSkilling_has_standard_pln

/-- A canonical weaker-than-KS case: Dempster-Shafer uses interval quantales. -/
theorem weaker_than_ks_interval_quantale :
    Mettapedia.ProbabilityTheory.Hypercube.quantaleTypeOf
      Mettapedia.ProbabilityTheory.Hypercube.dempsterShafer =
      Mettapedia.ProbabilityTheory.Hypercube.QuantaleType.interval :=
  Mettapedia.ProbabilityTheory.Hypercube.dempsterShafer_quantale

/-- Dempster-Shafer is in interval-PLN inference, not standard scalar PLN slice. -/
theorem weaker_than_ks_interval_inference :
    Mettapedia.ProbabilityTheory.Hypercube.hasIntervalPLNInference
      Mettapedia.ProbabilityTheory.Hypercube.dempsterShafer :=
  Mettapedia.ProbabilityTheory.Hypercube.dempsterShafer_has_interval_pln

/-! ## Reference pointers (for quick navigation) -/

/-- Canonical symbol list for the semantics choice flow.
Includes weaker-than-KS interval/imprecise references. -/
def keyReferenceSymbols : List String :=
  [ "Mettapedia.Logic.PLN_KS_Bridge.evidence_no_point_representation"
  , "Mettapedia.ProbabilityTheory.Hypercube.knuthSkilling_has_standard_pln"
  , "Mettapedia.ProbabilityTheory.Hypercube.dempsterShafer_quantale"
  , "Mettapedia.ProbabilityTheory.Hypercube.dempsterShafer_has_interval_pln"
  , "Mettapedia.Logic.PLN.pln_deduction_from_total_probability"
  , "Mettapedia.Logic.PLNBayesNetFastRules.chainBN_plnDeductionStrength_exact"
  , "Mettapedia.Logic.PLNXiDerivedBNRules.xi_deduction_queryStrength_eq_plnDeduction_of_chainBN"
  , "Mettapedia.Logic.NARSSecondOrderProbability.truthRevisionCore_toEvidence"
  , "Mettapedia.Logic.NARSEvidenceBridge.nars_revision_is_evidence_aggregation"
  , "Mettapedia.Logic.NARSMettaTruthFunctions.truthRevision"
  ]

/-- Operational note: NARS mirror revision adds explicit clamp guards. -/
theorem nars_revision_has_clamps
    (t1 t2 : Mettapedia.Logic.NARSMettaTruthFunctions.TV) :
    (Mettapedia.Logic.NARSMettaTruthFunctions.truthRevision t1 t2).f ≤ 1 ∧
    (Mettapedia.Logic.NARSMettaTruthFunctions.truthRevision t1 t2).c ≤ 0.99 := by
  unfold Mettapedia.Logic.NARSMettaTruthFunctions.truthRevision
  constructor <;> simp

/-! ## Quick usage checklist

- If you need exact parity with the runtime NARS formulas: use `.narsMirror`.
- If you need theorem-safe semantics across uncertain assumptions: use `.evidenceHeyting`.
- If precision is explicitly imprecise (interval/credal): use `.intervalImprecise`.
- Only project to scalar probability when the precise/comparable gate is justified.
-/

end Mettapedia.Logic.SemanticsDecisionTree
