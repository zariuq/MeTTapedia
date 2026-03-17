import Mettapedia.Logic.OSLFDistinctionGraphWeighted
import Mettapedia.Logic.PLNWorldModel
import Mettapedia.Logic.OSLFKSUnificationSketch

/-!
# Dynamic Distinction Graph (World-Model Layer)

Connects the weighted distinction graph to world-model dynamics:

- **`wmEvidenceAtomSem`**: Constructs an `EvidenceAtomSem` from a BinaryWorldModel state,
  using full BinaryEvidence values (not threshold projections).
- **`dynamicEdgeWeight`**: Distinction graph weight parameterized by WM state.
- **Revision law**: WM revision (`W₁ + W₂`) affects atom evidence additively
  via `evidence_add`.
- **Bridge to threshold semantics**: Connects to `thresholdAtomSemOfWM` from
  the existing 3-layer unification.

All theorems proven (0 sorry).

## References

- Goertzel, "MetaGoal Stability" (2026)
- Meredith & Stay, "Operational Semantics in Logical Form"
-/

namespace Mettapedia.Logic.OSLFDistinctionGraphWM

open Mettapedia.Logic.OSLFDistinctionGraph
open Mettapedia.Logic.OSLFDistinctionGraphWeighted
open Mettapedia.Logic.OSLFEvidenceSemantics
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.OSLFKSUnificationSketch
open Mettapedia.OSLF.Formula
open Mettapedia.ProbabilityTheory.KnuthSkilling.TotalityImprecision

open scoped ENNReal

abbrev Pat := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern

/-! ## WM-Induced BinaryEvidence Atom Semantics -/

/-- BinaryEvidence-valued atom semantics from a BinaryWorldModel state.
Maps atom names and patterns to BinaryEvidence via a query constructor.
Unlike `thresholdAtomSemOfWM` (which thresholds to Prop), this preserves
the full BinaryEvidence structure. -/
noncomputable def wmEvidenceAtomSem
    {State : Type*} [EvidenceType State] [BinaryWorldModel State Pat]
    (W : State) (queryOfAtom : String → Pat → Pat) : EvidenceAtomSem :=
  fun a p => BinaryWorldModel.evidence (State := State) (Query := Pat) W (queryOfAtom a p)

/-! ## Dynamic Distinction Graph -/

/-- Dynamic distinction graph edge weight at a given WM state.
The weight measures how indistinguishable two patterns are according to
formulas whose atoms are grounded in the world model. -/
noncomputable def dynamicEdgeWeight
    {State : Type*} [EvidenceType State] [BinaryWorldModel State Pat]
    (W : State) (R : Pat → Pat → Prop) (queryOfAtom : String → Pat → Pat)
    (p q : Pat) : BinaryEvidence :=
  indistWeightE R (wmEvidenceAtomSem W queryOfAtom) p q

/-- Dynamic scalar edge weight. -/
noncomputable def dynamicEdgeWeightS
    {State : Type*} [EvidenceType State] [BinaryWorldModel State Pat]
    (W : State) (R : Pat → Pat → Prop) (queryOfAtom : String → Pat → Pat)
    (p q : Pat) : ℝ≥0∞ :=
  BinaryEvidence.toStrength (dynamicEdgeWeight W R queryOfAtom p q)

/-! ## Self-Edge Properties -/

/-- Self-edge weight is ⊤ at any WM state. -/
theorem dynamicEdge_self_top
    {State : Type*} [EvidenceType State] [BinaryWorldModel State Pat]
    (W : State) (R : Pat → Pat → Prop) (queryOfAtom : String → Pat → Pat)
    (p : Pat) : dynamicEdgeWeight W R queryOfAtom p p = ⊤ :=
  indistWeightE_self_top R (wmEvidenceAtomSem W queryOfAtom) p

/-! ## WM Revision Laws -/

/-- WM revision decomposes atom evidence additively.
At a revised state `W₁ + W₂`, the atom evidence is the sum of individual evidences. -/
theorem wmAtomSem_revision
    {State : Type*} [EvidenceType State] [BinaryWorldModel State Pat]
    (W₁ W₂ : State) (queryOfAtom : String → Pat → Pat) (a : String) (p : Pat) :
    wmEvidenceAtomSem (W₁ + W₂) queryOfAtom a p =
      wmEvidenceAtomSem W₁ queryOfAtom a p + wmEvidenceAtomSem W₂ queryOfAtom a p := by
  simp only [wmEvidenceAtomSem]
  exact BinaryWorldModel.evidence_add (State := State) (Query := Pat) W₁ W₂ (queryOfAtom a p)

/-! ## Bridge to Threshold Semantics -/

/-- The threshold projection of WM BinaryEvidence atom semantics gives the
existing `thresholdAtomSemOfWM`. This connects the imprecise (BinaryEvidence-valued)
graph to the classical (Prop-valued) semantics. -/
theorem wmAtomSem_threshold_bridge
    {State : Type*} [EvidenceType State] [BinaryWorldModel State Pat]
    (W : State) (tau : ℝ≥0∞) (queryOfAtom : String → Pat → Pat)
    (a : String) (p : Pat) :
    thresholdAtomSemOfWM W tau queryOfAtom a p ↔
      tau ≤ BinaryEvidence.toStrength (wmEvidenceAtomSem W queryOfAtom a p) :=
  Iff.rfl

/-! ## Extended Unification -/

/-- The 3-layer unification schema extended with the distinction graph layer:
1. Meredith: bisimulation → observational equivalence
2. Stay/Baez: measurement factors through equivalence classes
3. Knuth/Skilling: imprecision gate (no faithful scalar collapse)
4. Distinction graph: weighted edges via BinaryEvidence-valued Heyting implication -/
theorem oslf_ks_wm_graph_unification
    {State : Type*} [EvidenceType State] [BinaryWorldModel State Pat] :
    -- Layer 1 (Meredith): bisim → obs eq (from existing schema)
    (∀ (R : Pat → Pat → Prop) (I : AtomSem) (equiv : Pat → Pat → Prop),
      StepBisimulation R equiv →
      StepBisimulation (fun a b => R b a) equiv →
      (∀ a p q, equiv p q → (I a p ↔ I a q)) →
      ∀ p q, equiv p q → OSLFObsEq R I p q) ∧
    -- Layer 2 (Stay/Baez): measurement factors through obs eq
    (∀ (mu : Pat → ℝ) (equiv : Pat → Pat → Prop),
      (∀ p q, equiv p q → mu p = mu q) →
      ∃ muQ : Quot (fun p q => equiv p q) → ℝ, ∀ p, muQ (Quot.mk _ p) = mu p) ∧
    -- Layer 3 (Knuth/Skilling): imprecision gate
    (¬ FaithfulPointRepresentation BinaryEvidence) ∧
    -- Layer 4 (Graph): self-edge is ⊤ + revision decomposes additively
    (∀ (W : State) (R : Pat → Pat → Prop) (qoa : String → Pat → Pat) (p : Pat),
      dynamicEdgeWeight W R qoa p p = ⊤) ∧
    (∀ (W₁ W₂ : State) (qoa : String → Pat → Pat) (a : String) (p : Pat),
      wmEvidenceAtomSem (W₁ + W₂) qoa a p =
        wmEvidenceAtomSem W₁ qoa a p + wmEvidenceAtomSem W₂ qoa a p) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact fun R I equiv hB hBR hA p q hpq φ =>
      bisimulation_invariant_sem hB hBR hA hpq φ
  · exact fun mu equiv hC => valuation_factors_through_obsEq mu equiv hC
  · exact evidence_imprecision_gate
  · exact fun W R qoa p => dynamicEdge_self_top W R qoa p
  · exact fun W₁ W₂ qoa a p => wmAtomSem_revision W₁ W₂ qoa a p

end Mettapedia.Logic.OSLFDistinctionGraphWM
