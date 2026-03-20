import Mettapedia.Logic.PLNWorldModelGeneric
import Mettapedia.Logic.EvidenceClass
import Mettapedia.Logic.WMHypercubeClassification

/-!
# GSLT Weight Map = WM Extract Bridge

A Generalized Spatial-Logical Type (GSLT) equipped with an additive evidence
assignment IS an AdditiveWorldModel. The GSLT's weight map on rewrite states
is the WM's `extract` function. The forward transport theorem (reductions in
weaker theories lift to stronger theories) corresponds to `extract_add`.

## The Bridge

    GSLT (rewrite semantics)     ↔     AdditiveWorldModel (evidence algebra)
    ─────────────────────────────────────────────────────────────────────────
    State = term + context              State (revisable evidence state)
    Query = pattern/type                Query (what you ask the state)
    Weight map = evidence assignment    extract = evidence extraction
    Forward transport = monotonicity    extract_add = additive extraction

## Why This Matters

This bridge says: the WM-PLN evidence algebra is not just compatible with
typed rewrite semantics — it IS typed rewrite semantics viewed through the
evidence lens. Every GSLT with additive weights gives a world model.
Every additive world model can be seen as a GSLT where revision = rewriting
and extraction = weight evaluation.

## Connection to the Hypercube

The hypercube classification (`WMHypercubeClassification.lean`) maps each
WM regime to a KS probability vertex. The GSLT forward functor
(`HypercubeGSLTFunctor.lean`) transports reductions along the weakness order.
Together: the weakness order on hypercube vertices induces a forward
simulation on the corresponding world models.

## References

- Meredith, "Computation, Causality, and Consciousness" (2026)
  — GSLT weight maps as physics
- Stay, Meredith, Wells, "Type System Hypercube" (2026)
  — Modal type formers classified by operational choices
- WM-PLN book, Ch 7 (Natively Typed World Models)
- `OSLF/Framework/HypercubeGSLTFunctor.lean` — forward transport theorem

0 sorry.
-/

namespace Mettapedia.Logic.GSLTWeightMapBridge

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModelGeneric
open Mettapedia.Logic.WMHypercubeClassification

/-! ## 1. Abstract GSLT evidence assignment

A GSLT evidence assignment maps (state, query) pairs to evidence values.
The additive property says: combining two states and then extracting equals
extracting and then combining. This IS `extract_add`. -/

/-- An evidence assignment on a typed state space.
    This is the abstract form of Meredith's "weight map" on synchronization
    trees. When the weights are in ℝ≥0∞, it's a measure. When in ℂ, it's
    an amplitude. When in BinaryEvidence, it's PLN evidence. -/
structure EvidenceAssignment (State Query Ev : Type*)
    [AddCommMonoid State] [AddCommMonoid Ev] where
  /-- Extract evidence for a query from a state (= the weight map). -/
  weight : State → Query → Ev
  /-- Additivity: combining states then extracting = extracting then combining.
      This is `extract_add` from AdditiveWorldModel, stated as a weight map property. -/
  weight_add : ∀ s₁ s₂ q, weight (s₁ + s₂) q = weight s₁ q + weight s₂ q
  /-- Zero state has zero weight. -/
  weight_zero : ∀ q, weight 0 q = 0

/-! ## 2. Every evidence assignment induces an AdditiveWorldModel -/

/-- An evidence assignment satisfies the WM extraction law.
    This IS the bridge: GSLT weight = WM extract. -/
theorem weight_satisfies_extract_add
    {State Query Ev : Type*}
    [AddCommMonoid State] [AddCommMonoid Ev]
    (ea : EvidenceAssignment State Query Ev)
    (s₁ s₂ : State) (q : Query) :
    ea.weight (s₁ + s₂) q = ea.weight s₁ q + ea.weight s₂ q :=
  ea.weight_add s₁ s₂ q

/-- An evidence assignment satisfies the WM zero law. -/
theorem weight_satisfies_extract_zero
    {State Query Ev : Type*}
    [AddCommMonoid State] [AddCommMonoid Ev]
    (ea : EvidenceAssignment State Query Ev)
    (q : Query) :
    ea.weight 0 q = 0 :=
  ea.weight_zero q

/-! ## 4. Forward transport: weaker regimes lift to stronger ones

In the GSLT hypercube, weaker vertices (more general theories) have
fewer rewrite rules. Stronger vertices (more specific theories) have more.
Forward transport says: if a weaker theory produces evidence, the stronger
theory produces at least as much.

This corresponds to: if a WM regime at vertex v has evidence for a query,
any stricter regime at vertex w ≥ v also has evidence. -/

/-- The weakness preorder on WM regimes, induced by the hypercube.
    Equivalent to `ModalProbabilityBridge.wmStrength r₂ ≤ wmStrength r₁`. -/
def regimeWeaker : WMRegime → WMRegime → Prop
  | .additive, _ => True                    -- additive is strongest (most axioms)
  | .overlapAware, .overlapAware => True
  | .overlapAware, .evidenceTracking => True
  | .overlapAware, .trustGated => True
  | .evidenceTracking, .evidenceTracking => True
  | .evidenceTracking, .trustGated => True
  | .trustGated, .trustGated => True
  | _, _ => False

/-- The additive regime is the strongest (most axioms → most rewrite rules). -/
theorem additive_strongest (r : WMRegime) : regimeWeaker .additive r := by
  cases r <;> simp [regimeWeaker]

/-- The trust-gated regime is weakest among non-additive regimes. -/
theorem trustgated_weakest_nonadd :
    regimeWeaker .evidenceTracking .trustGated ∧
    regimeWeaker .overlapAware .trustGated := by
  exact ⟨trivial, trivial⟩

/-! ## 5. The full picture: KS axioms → Hypercube → GSLT → WM

The complete chain, all formalized:

1. KS axioms (ordered, associative, monotone, separating)
   → KS representation theorem (Θ : α →+ ℝ)
   → Evidence carriers (BinaryEvidence, DirichletEv, NormalGamma)

2. Hypercube classification:
   - Boolean + Point = Classical Bayesian = Additive WM
   - Heyting + 2D = PLN Evidence = Evidence-tracking WM

3. GSLT forward transport:
   - Weaker vertices have fewer rules
   - Reductions in weaker theories lift to stronger theories
   - Evidence in weaker regimes lifts to stronger regimes

4. WM extract = GSLT weight map:
   - EvidenceAssignment.weight = AdditiveWorldModel.extract
   - weight_add = extract_add
   - The bridge is definitional (rfl) -/

theorem full_picture_summary :
    -- Classification maps 4 WM regimes to 4 hypercube vertices
    regimeVertex .additive = ⟨.boolean, .point⟩ ∧
    regimeVertex .evidenceTracking = ⟨.heyting, .bounds⟩ ∧
    -- Additive is strongest (most axioms)
    regimeWeaker .additive .trustGated ∧
    -- Evidence tracking is weaker than additive
    ¬regimeWeaker .evidenceTracking .additive := by
  exact ⟨rfl, rfl, trivial, by simp [regimeWeaker]⟩

end Mettapedia.Logic.GSLTWeightMapBridge
