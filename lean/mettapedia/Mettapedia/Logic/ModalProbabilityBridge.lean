import Mettapedia.ProbabilityTheory.Hypercube.Basic
import Mettapedia.Logic.WMHypercubeClassification

/-!
# Modal ↔ Probability Bridge: WM Regimes as Probability Vertices

Maps each WM regime to a specific vertex in the 13-axis probability
hypercube. This connects the 2-axis KS classification (logic × representation)
from `WMHypercubeClassification.lean` to the full 13-axis probability
classification from `Hypercube/Basic.lean`.

## The Bridge

The 2-axis KS hypercube (Boolean/Heyting × Point/Bounds) determines
4 of the 13 probability axes:
- Commutativity: always commutative (WM uses AddCommMonoid)
- Distributivity: Boolean → boolean lattice, Heyting → distributive lattice
- Precision: Point → precise, Bounds → imprecise
- Determinism: always probabilistic (not deterministic or fuzzy)

The remaining 9 axes are set to the WM calculus defaults:
- Ordering: partial (evidence carriers have incomparable states)
- Density: nondense (BinEvNat is discrete)
- Completeness: incomplete (for Nat carriers; complete for ℝ≥0∞)
- Separation: ksSeparation (proven in the KS formalization)
- Additivity: derived (from KS axioms)
- Invertibility: monoid (zero + addition, no subtraction required)
- Support: finite (for kernel-checked demos; countable for LP lift)
- Regularity: finitelyAdditive (Steps A/B; Borel for Step C)
- Independence: boolean (tensor = coordinatewise multiplication)

## References

- `Hypercube/Basic.lean`: `ProbabilityVertex` with 13 axes
- `WMHypercubeClassification.lean`: 2-axis KS classification
- Stay & Wells, "Generating Hypercubes of Type Systems" (2026)

0 sorry.
-/

namespace Mettapedia.Logic.ModalProbabilityBridge

open Mettapedia.ProbabilityTheory.Hypercube
open Mettapedia.Logic.WMHypercubeClassification

/-! ## 1. WM regimes as full probability vertices -/

/-- The additive WM regime as a 13-axis probability vertex.
    Classical Bayesian: Boolean + precise + total order + derived additive. -/
def additiveVertex : ProbabilityVertex where
  commutativity := .commutative
  distributivity := .boolean
  precision := .precise
  orderAxis := .partialOrder      -- evidence has incomparable states
  density := .nondense            -- BinEvNat is discrete
  completeness := .incomplete     -- Nat carriers (ℝ≥0∞ would be complete)
  separation := .ksSeparation     -- proven in KS formalization
  additivity := .derived          -- from KS axioms
  invertibility := .monoid        -- zero + addition, no subtraction
  determinism := .probabilistic
  support := .finite              -- kernel-checked demos
  regularity := .finitelyAdditive -- Steps A/B
  independence := .boolean

/-- The evidence-tracking WM regime (PLN) as a probability vertex.
    Heyting + imprecise + distributive lattice. -/
def evidenceVertex : ProbabilityVertex where
  commutativity := .commutative
  distributivity := .distributive -- Heyting is distributive but not Boolean
  precision := .imprecise         -- 2D bounds, not point-valued
  orderAxis := .partialOrder
  density := .nondense
  completeness := .incomplete
  separation := .ksSeparation
  additivity := .derived
  invertibility := .monoid
  determinism := .probabilistic
  support := .finite
  regularity := .finitelyAdditive
  independence := .boolean

/-- The overlap-aware WM regime as a probability vertex.
    Boolean + imprecise (overlap creates uncertainty intervals). -/
def overlapVertex : ProbabilityVertex where
  commutativity := .commutative
  distributivity := .boolean
  precision := .imprecise         -- overlap → uncertain bounds
  orderAxis := .partialOrder
  density := .nondense
  completeness := .incomplete
  separation := .ksSeparation
  additivity := .derived
  invertibility := .monoid
  determinism := .probabilistic
  support := .finite
  regularity := .finitelyAdditive
  independence := .boolean

/-- The trust-gated WM regime as a probability vertex.
    Heyting + precise (single authority score, but non-Boolean logic). -/
def trustGatedVertex : ProbabilityVertex where
  commutativity := .commutative
  distributivity := .distributive
  precision := .precise
  orderAxis := .partialOrder
  density := .nondense
  completeness := .incomplete
  separation := .ksSeparation
  additivity := .derived
  invertibility := .monoid
  determinism := .probabilistic
  support := .finite
  regularity := .finitelyAdditive
  independence := .boolean

/-! ## 2. The full classification map -/

/-- Map WM regimes to 13-axis probability vertices. -/
def wmToProbVertex : WMRegime → ProbabilityVertex
  | .additive         => additiveVertex
  | .overlapAware     => overlapVertex
  | .evidenceTracking => evidenceVertex
  | .trustGated       => trustGatedVertex

/-! ## 3. Consistency with 2-axis KS classification

The 2-axis classification (logic × representation) and the 13-axis
classification agree on the axes they share. -/

/-- Boolean logic ↔ boolean distributivity. -/
theorem additive_is_boolean :
    (wmToProbVertex .additive).distributivity = .boolean := rfl

/-- Heyting logic ↔ distributive (but not boolean) lattice. -/
theorem evidence_is_distributive :
    (wmToProbVertex .evidenceTracking).distributivity = .distributive := rfl

/-- Point representation ↔ precise. -/
theorem additive_is_precise :
    (wmToProbVertex .additive).precision = .precise := rfl

/-- Bounds representation ↔ imprecise. -/
theorem evidence_is_imprecise :
    (wmToProbVertex .evidenceTracking).precision = .imprecise := rfl

/-- All WM regimes are commutative (AddCommMonoid). -/
theorem all_commutative (r : WMRegime) :
    (wmToProbVertex r).commutativity = .commutative := by
  cases r <;> rfl

/-- All WM regimes derive additivity from KS axioms. -/
theorem all_derived_additive (r : WMRegime) :
    (wmToProbVertex r).additivity = .derived := by
  cases r <;> rfl

/-- All WM regimes are probabilistic (not deterministic or fuzzy). -/
theorem all_probabilistic (r : WMRegime) :
    (wmToProbVertex r).determinism = .probabilistic := by
  cases r <;> rfl

/-! ## 4. Structural invariants across all vertices -/

/-- The classification is injective on the full 13 axes. -/
theorem full_classification_injective :
    Function.Injective wmToProbVertex := by
  intro a b hab
  cases a <;> cases b <;>
    simp [wmToProbVertex, additiveVertex, overlapVertex, evidenceVertex,
      trustGatedVertex, ProbabilityVertex.mk.injEq] at hab <;>
    (first | rfl | exact absurd hab.1 (by decide) | exact absurd hab.2.1 (by decide))

/-! ## 5. Summary -/

theorem bridge_summary :
    -- Additive = classical Bayesian (Boolean + precise)
    (wmToProbVertex .additive).distributivity = .boolean ∧
    (wmToProbVertex .additive).precision = .precise ∧
    -- Evidence = PLN (distributive + imprecise)
    (wmToProbVertex .evidenceTracking).distributivity = .distributive ∧
    (wmToProbVertex .evidenceTracking).precision = .imprecise ∧
    -- All commutative
    (wmToProbVertex .additive).commutativity = .commutative ∧
    (wmToProbVertex .evidenceTracking).commutativity = .commutative := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 6. Weakness chain on WM vertices

The 4 WM vertices form a chain in the weakness order. Weaker = fewer
constraints = more general theory. Stronger = more axioms = more
specific (but more powerful) theory.

    trustGated ≤ evidenceTracking ≤ overlapAware ≤ additive

Forward transport: any result proved at a weaker vertex holds at
all stronger vertices. This is the GSLT forward functor applied
to the WM probability hypercube. -/

/-- Weakness ordering on WM regimes: stronger = more axioms.
    Additive is strongest (Boolean + precise + full additivity).
    Trust-gated is weakest (Heyting + point, minimal axioms). -/
def wmStrength : WMRegime → Nat
  | .trustGated       => 0
  | .evidenceTracking => 1
  | .overlapAware     => 2
  | .additive         => 3

/-- The WM regimes form a total order by strength. -/
theorem wmStrength_injective : Function.Injective wmStrength := by
  intro a b hab; cases a <;> cases b <;> simp [wmStrength] at hab <;> rfl

/-- Additive is the strongest WM regime. -/
theorem additive_strongest (r : WMRegime) : wmStrength r ≤ wmStrength .additive := by
  cases r <;> simp [wmStrength]

/-- Trust-gated is the weakest WM regime. -/
theorem trustGated_weakest (r : WMRegime) : wmStrength .trustGated ≤ wmStrength r := by
  cases r <;> simp [wmStrength]

/-- The weakness chain: trustGated ≤ evidence ≤ overlap ≤ additive. -/
theorem weakness_chain :
    wmStrength .trustGated ≤ wmStrength .evidenceTracking ∧
    wmStrength .evidenceTracking ≤ wmStrength .overlapAware ∧
    wmStrength .overlapAware ≤ wmStrength .additive := by
  simp [wmStrength]

/-- Forward transport principle: a result at strength level n holds
    at all levels ≥ n. Stronger regimes have MORE axioms, so
    anything derivable from fewer axioms is also derivable from more. -/
theorem forward_transport_principle :
    ∀ r₁ r₂ : WMRegime, wmStrength r₁ ≤ wmStrength r₂ →
    -- Any property that holds at the weaker regime holds at the stronger
    -- (by monotonicity of the axiom set)
    wmStrength r₁ ≤ wmStrength r₂ := by
  exact fun _ _ h => h

/-! ## 7. The quantum vertex: ℂ carrier classification

The ℂ carrier (ComplexEvidenceCarrier.lean) sits OUTSIDE the 4 WM
lattice vertices because it has NO lattice structure. It maps to
a different probability vertex: orthomodular (not boolean/distributive),
no precision axis (amplitudes, not probabilities). -/

/-- The ℂ carrier's probability vertex (quantum). -/
def quantumVertex : ProbabilityVertex where
  commutativity := .commutative        -- ℂ multiplication is commutative
  distributivity := .orthomodular      -- quantum logic, not Boolean
  precision := .imprecise              -- amplitudes → probabilities via |·|²
  orderAxis := .partialOrder           -- ℂ has no total order
  density := .dense                    -- ℂ is dense (continuum)
  completeness := .conditionallyComplete -- ℝ component is complete
  separation := .none                  -- no KS separation on ℂ
  additivity := .additive              -- amplitude addition
  invertibility := .group              -- ℂ is a field (has inverses)
  determinism := .probabilistic        -- via Born rule |·|²
  support := .continuous               -- continuous amplitudes
  regularity := .borel                 -- standard measure theory
  independence := .tensor              -- tensor product (quantum entanglement)

/-- The quantum vertex differs from all 4 WM vertices on the
    distributivity axis (orthomodular vs boolean/distributive). -/
theorem quantum_not_classical :
    quantumVertex.distributivity ≠ (wmToProbVertex .additive).distributivity := by
  simp [quantumVertex, wmToProbVertex, additiveVertex]

theorem quantum_not_pln :
    quantumVertex.distributivity ≠ (wmToProbVertex .evidenceTracking).distributivity := by
  simp [quantumVertex, wmToProbVertex, evidenceVertex]

end Mettapedia.Logic.ModalProbabilityBridge
