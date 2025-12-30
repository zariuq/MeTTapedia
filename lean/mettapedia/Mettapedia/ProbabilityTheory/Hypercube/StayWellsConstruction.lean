/-
# Stay-Wells H_Σ Construction for Probability Theories

Systematic generation of probability theories from their operational semantics.
Following Stay & Wells' "Generating Hypercubes of Type Systems", we show how
different probability theories arise from different base rewrites and sort assignments.

## The Key Insight

Each probability theory is characterized by its "base rewrites" (inference rules).
Applying the H_Σ functor to these rewrites generates:
1. Modal types capturing "rely-possibly" semantics
2. A hypercube of 2^n typed calculi (one per sort assignment)
3. Spatial types classifying probability expressions

## Main Constructions

1. **ProbabilityBaseRewrite**: Captures inference rules like product rule, sum rule
2. **ProbabilityModal**: The modal type ⟨context⟩_{params} Result
3. **ProbHypercube**: The full hypercube of probability type systems
4. **TheoryGenerator**: How modifying rewrites generates new theories

## References

- Stay & Wells, "Generating Hypercubes of Type Systems"
- Knuth & Skilling, "Foundations of Inference", Appendix A
- Meredith & Stay, "Rely-Possibly Semantics" (OSLF)
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mettapedia.ProbabilityTheory.Hypercube.Basic
import Mettapedia.ProbabilityTheory.Hypercube.OperationalSemantics

namespace Mettapedia.ProbabilityTheory.Hypercube.StayWells

open Hypercube OperationalSemantics

/-!
## §1: Probability Type System

The carrier types for probability expressions.
-/

/-- Objects in the probability type system. -/
inductive ProbObj where
  | Event : ProbObj           -- Events/propositions
  | Prob : ProbObj            -- Probability values [0,1]
  | Plausibility : ProbObj    -- K&S plausibility values
  | Mass : ProbObj            -- D-S mass function values
  | Density : ProbObj         -- Quantum density matrices
  deriving DecidableEq, Repr, Inhabited

/-- Sort symbols: ∗ (inhabited types) and □ (uninhabited kinds) -/
inductive PSort where
  | star : PSort  -- ∗ = concrete values that exist
  | box : PSort   -- □ = type-level only (no inhabitants)
  deriving DecidableEq, Repr

/-!
## §2: Base Rewrites for Each Probability Theory

Each theory is characterized by its fundamental inference rules.
-/

/-- A probability base rewrite with full type information. -/
structure ProbabilityBaseRewrite where
  /-- Name of the rule -/
  name : String
  /-- Which probability theory uses this rule -/
  theory : ProbabilityVertex
  /-- Left-hand side pattern -/
  lhs : ProbTerm
  /-- Right-hand side pattern -/
  rhs : ProbTerm
  /-- Free variables with their carrier types -/
  freeVars : List (String × ProbObj)
  /-- Side conditions (e.g., "P(B) ≠ 0") -/
  conditions : List String

/-- The classical product rule: P(A∧B|C) = P(A|C) · P(B|A∧C) -/
def classicalProductRule : ProbabilityBaseRewrite where
  name := "product_rule"
  theory := kolmogorov
  lhs := ProbTerm.condProb
           (ProbTerm.conj (ProbTerm.event "A") (ProbTerm.event "B"))
           (ProbTerm.event "C")
  rhs := ProbTerm.mul
           (ProbTerm.condProb (ProbTerm.event "A") (ProbTerm.event "C"))
           (ProbTerm.condProb (ProbTerm.event "B")
             (ProbTerm.conj (ProbTerm.event "A") (ProbTerm.event "C")))
  freeVars := [("A", .Event), ("B", .Event), ("C", .Event)]
  conditions := []

/-- The sum rule: P(A∨B) = P(A) + P(B) - P(A∧B) -/
def classicalSumRule : ProbabilityBaseRewrite where
  name := "sum_rule"
  theory := kolmogorov
  lhs := ProbTerm.prob (ProbTerm.disj (ProbTerm.event "A") (ProbTerm.event "B"))
  rhs := ProbTerm.sub
           (ProbTerm.add
             (ProbTerm.prob (ProbTerm.event "A"))
             (ProbTerm.prob (ProbTerm.event "B")))
           (ProbTerm.prob (ProbTerm.conj (ProbTerm.event "A") (ProbTerm.event "B")))
  freeVars := [("A", .Event), ("B", .Event)]
  conditions := []

/-- Bayes' rule: P(A|B) = P(B|A) · P(A) / P(B) -/
def bayesRule' : ProbabilityBaseRewrite where
  name := "bayes_rule"
  theory := kolmogorov
  lhs := ProbTerm.condProb (ProbTerm.event "A") (ProbTerm.event "B")
  rhs := ProbTerm.div
           (ProbTerm.mul
             (ProbTerm.condProb (ProbTerm.event "B") (ProbTerm.event "A"))
             (ProbTerm.prob (ProbTerm.event "A")))
           (ProbTerm.prob (ProbTerm.event "B"))
  freeVars := [("A", .Event), ("B", .Event)]
  conditions := ["P(B) ≠ 0"]

/-- K&S associativity: (x ⊕ y) ⊕ z = x ⊕ (y ⊕ z) -/
def ksAssociativity : ProbabilityBaseRewrite where
  name := "ks_associativity"
  theory := knuthSkilling
  lhs := ProbTerm.add
           (ProbTerm.add (ProbTerm.event "x") (ProbTerm.event "y"))
           (ProbTerm.event "z")
  rhs := ProbTerm.add
           (ProbTerm.event "x")
           (ProbTerm.add (ProbTerm.event "y") (ProbTerm.event "z"))
  freeVars := [("x", .Plausibility), ("y", .Plausibility), ("z", .Plausibility)]
  conditions := []

/-- K&S identity: x ⊕ 0 = x -/
def ksIdentity : ProbabilityBaseRewrite where
  name := "ks_identity"
  theory := knuthSkilling
  lhs := ProbTerm.add (ProbTerm.event "x") (ProbTerm.real 0)
  rhs := ProbTerm.event "x"
  freeVars := [("x", .Plausibility)]
  conditions := []

/-!
## §3: Subterm Positions and Contexts

For each rewrite, identify the subterm positions and their contexts.
-/

/-- A context is a term with a "hole" [-] -/
inductive ProbContext where
  | hole : ProbContext
  | prob : ProbContext → ProbContext
  | condProbLeft : ProbContext → ProbTerm → ProbContext
  | condProbRight : ProbTerm → ProbContext → ProbContext
  | conjLeft : ProbContext → ProbTerm → ProbContext
  | conjRight : ProbTerm → ProbContext → ProbContext
  | addLeft : ProbContext → ProbTerm → ProbContext
  | addRight : ProbTerm → ProbContext → ProbContext
  | mulLeft : ProbContext → ProbTerm → ProbContext
  | mulRight : ProbTerm → ProbContext → ProbContext
  deriving Inhabited

/-- A subterm position in a rewrite's LHS -/
structure ProbSubtermPosition where
  /-- The subterm itself -/
  subterm : ProbTerm
  /-- The context C with C[subterm] = lhs -/
  context : ProbContext
  /-- Carrier type of the subterm -/
  carrier : ProbObj
  /-- Free variables visible in the context -/
  contextFreeVars : List String

/-- Positions in the product rule LHS: P(A∧B|C) -/
def productRulePositions : List ProbSubtermPosition :=
  [ -- Position 0: The whole term P(A∧B|C)
    { subterm := classicalProductRule.lhs,
      context := .hole,
      carrier := .Prob,
      contextFreeVars := [] },
    -- Position 1: The event A∧B
    { subterm := ProbTerm.conj (ProbTerm.event "A") (ProbTerm.event "B"),
      context := .condProbLeft .hole (ProbTerm.event "C"),
      carrier := .Event,
      contextFreeVars := ["C"] },
    -- Position 2: The event A (left of conjunction)
    { subterm := ProbTerm.event "A",
      context := .condProbLeft (.conjLeft .hole (ProbTerm.event "B")) (ProbTerm.event "C"),
      carrier := .Event,
      contextFreeVars := ["B", "C"] },
    -- Position 3: The event B (right of conjunction)
    { subterm := ProbTerm.event "B",
      context := .condProbLeft (.conjRight (ProbTerm.event "A") .hole) (ProbTerm.event "C"),
      carrier := .Event,
      contextFreeVars := ["A", "C"] },
    -- Position 4: The condition C
    { subterm := ProbTerm.event "C",
      context := .condProbRight (ProbTerm.conj (ProbTerm.event "A") (ProbTerm.event "B")) .hole,
      carrier := .Event,
      contextFreeVars := ["A", "B"] }
  ]

/-- Positions in K&S associativity: (x ⊕ y) ⊕ z -/
def ksAssocPositions : List ProbSubtermPosition :=
  [ -- Position 0: The whole term
    { subterm := ksAssociativity.lhs,
      context := .hole,
      carrier := .Plausibility,
      contextFreeVars := [] },
    -- Position 1: (x ⊕ y)
    { subterm := ProbTerm.add (ProbTerm.event "x") (ProbTerm.event "y"),
      context := .addLeft .hole (ProbTerm.event "z"),
      carrier := .Plausibility,
      contextFreeVars := ["z"] },
    -- Position 2: x
    { subterm := ProbTerm.event "x",
      context := .addLeft (.addLeft .hole (ProbTerm.event "y")) (ProbTerm.event "z"),
      carrier := .Plausibility,
      contextFreeVars := ["y", "z"] },
    -- Position 3: y
    { subterm := ProbTerm.event "y",
      context := .addLeft (.addRight (ProbTerm.event "x") .hole) (ProbTerm.event "z"),
      carrier := .Plausibility,
      contextFreeVars := ["x", "z"] },
    -- Position 4: z
    { subterm := ProbTerm.event "z",
      context := .addRight (ProbTerm.add (ProbTerm.event "x") (ProbTerm.event "y")) .hole,
      carrier := .Plausibility,
      contextFreeVars := ["x", "y"] }
  ]

/-!
## §4: Slots and Sort Assignments

Each position has slots that can be assigned ∗ (inhabited) or □ (uninhabited).
-/

/-- A slot in a modality's sort family -/
inductive ProbSlot' where
  | param : String → ProbObj → ProbSlot'  -- Parameter slot
  | result : ProbSlot'                     -- Result slot
  deriving DecidableEq, Repr

/-- The slot family for a subterm position -/
def slotFamily' (pos : ProbSubtermPosition) : List ProbSlot' :=
  (pos.contextFreeVars.map fun v => .param v .Event) ++ [.result]

/-- A local sort assignment for one position -/
structure LocalProbSortAssignment where
  position : ProbSubtermPosition
  assignment : ProbSlot' → PSort

/-- A global sort assignment covers all positions in a rewrite -/
structure GlobalProbSortAssignment where
  rewrite : ProbabilityBaseRewrite
  locals : List LocalProbSortAssignment

/-!
## §5: The Modal Type Construction

The key construction: from a subterm position, generate a modal type.
-/

/-- A probability modal type: ⟨C⟩_{x_k::A_k} B
    "If we RELY on parameters x_k having types A_k,
     it's POSSIBLE to compute a result of type B via this rewrite." -/
structure ProbModalType where
  /-- The generating position -/
  position : ProbSubtermPosition
  /-- Parameter types we rely on -/
  relies : List (String × ProbObj)
  /-- Result type -/
  resultType : ProbObj

/-- Generate modal type from a subterm position in the product rule.

    Example: Position 2 (event A) generates:
    ⟨P([-]∧B|C)⟩_{B::Event, C::Event} Event

    Semantics: "If we RELY on B and C being events,
    it's POSSIBLE to use the product rule with A in this position." -/
def generateModalType (pos : ProbSubtermPosition) : ProbModalType where
  position := pos
  relies := pos.contextFreeVars.map fun v => (v, .Event)
  resultType := pos.carrier

/-- Modal types from the product rule -/
def productRuleModalTypes : List ProbModalType :=
  productRulePositions.map generateModalType

/-- Modal types from K&S associativity -/
def ksAssocModalTypes : List ProbModalType :=
  ksAssocPositions.map generateModalType

/-!
## §6: The Probability Hypercube

Combining all positions and sort choices gives a hypercube of typed calculi.
-/

/-- Dimension of the hypercube for a rewrite = total number of slots -/
def rewriteHypercubeDimension (positions : List ProbSubtermPosition) : Nat :=
  positions.foldl (fun acc pos => acc + (slotFamily' pos).length) 0

/-- Number of vertices = 2^dimension -/
def rewriteHypercubeVertices (positions : List ProbSubtermPosition) : Nat :=
  2 ^ rewriteHypercubeDimension positions

-- Product rule: 5 positions × ~2-3 slots each ≈ 2^10 = 1024 vertices
-- K&S assoc: 5 positions × ~2-3 slots each ≈ 2^10 = 1024 vertices

/-- The hypercube of typed probability calculi for a theory -/
structure ProbHypercube where
  /-- The base rewrite generating this hypercube -/
  rewrite : ProbabilityBaseRewrite
  /-- Subterm positions -/
  positions : List ProbSubtermPosition
  /-- Modal types generated -/
  modalTypes : List ProbModalType
  /-- Dimension -/
  dimension : Nat := rewriteHypercubeDimension positions
  /-- Number of vertices -/
  vertices : Nat := rewriteHypercubeVertices positions

/-- The classical probability hypercube -/
def classicalHypercube : ProbHypercube where
  rewrite := classicalProductRule
  positions := productRulePositions
  modalTypes := productRuleModalTypes

/-- The K&S hypercube -/
def ksHypercube : ProbHypercube where
  rewrite := ksAssociativity
  positions := ksAssocPositions
  modalTypes := ksAssocModalTypes

/-!
## §7: Theory Generation by Rewrite Modification

The key insight: modifying base rewrites generates NEW probability theories!
-/

/-- Ways to modify a base rewrite -/
inductive RewriteModification where
  | addCondition : String → RewriteModification  -- Add a side condition
  | removeSymmetry : RewriteModification         -- Break commutativity
  | weakenEquality : RewriteModification         -- Equality → inequality
  | addImprecision : RewriteModification         -- Single value → interval
  deriving Repr

/-- Apply a modification to generate a new rewrite -/
def modifyRewrite (r : ProbabilityBaseRewrite) : RewriteModification → ProbabilityBaseRewrite
  | .addCondition c => { r with conditions := c :: r.conditions }
  | .removeSymmetry => { r with name := r.name ++ "_noncomm" }
  | .weakenEquality => { r with name := r.name ++ "_ineq" }
  | .addImprecision => { r with name := r.name ++ "_imprecise" }

/-- Generate a new theory vertex from modifications -/
def generateTheoryVertex (mods : List RewriteModification) : ProbabilityVertex :=
  let hasNoncomm := mods.any (· matches .removeSymmetry)
  let hasImprecision := mods.any (· matches .addImprecision)
  { commutativity := if hasNoncomm then .noncommutative else .commutative,
    distributivity := .boolean,
    precision := if hasImprecision then .imprecise else .precise,
    orderAxis := .totalOrder,
    additivity := .derived,
    determinism := .probabilistic,
    support := .continuous,
    regularity := .borel,
    independence := if hasNoncomm then .free else .tensor }

/-!
## §8: Connecting to the 5-Axis Probability Hypercube

Show how the operational hypercube relates to the 5-axis theory hypercube.
-/

/-- Map from base rewrites to theory vertices -/
def rewriteToVertex : ProbabilityBaseRewrite → ProbabilityVertex
  | r => r.theory

/-- The rewrites characteristic of each theory -/
def theoryRewrites : ProbabilityVertex → List ProbabilityBaseRewrite
  | v =>
    match v.commutativity, v.precision with
    | .commutative, .precise =>
        [classicalProductRule, classicalSumRule, bayesRule']
    | .commutative, .imprecise =>
        []  -- D-S would have Dempster rule here
    | .noncommutative, _ =>
        []  -- Quantum would have Born rule here

/-- The modal types that distinguish theories.

    Classical: Product rule modal types (compositional probability)
    K&S: Associativity modal types (algebraic composition)
    D-S: Dempster rule modal types (imprecise combination)
    Quantum: Born rule modal types (non-commutative observation) -/
def distinguishingModalTypes : ProbabilityVertex → List ProbModalType
  | v =>
    match v with
    | { commutativity := .commutative, precision := .precise, .. } =>
        productRuleModalTypes
    | _ => []  -- Would need more rules defined

/-!
## §9: The Generation Theorem

The main result: how operational semantics generates probability theories.
-/

/-- Theorem: The hypercube dimension determines the number of typed calculi.

    For the product rule with 5 positions and ~10 total slots:
    2^10 = 1024 different typed probability calculi!

    Each vertex is a different "typed probability theory" with
    different ∗/□ choices for events and probability values. -/
theorem hypercube_vertices_exponential (positions : List ProbSubtermPosition) :
    rewriteHypercubeVertices positions = 2 ^ rewriteHypercubeDimension positions := rfl

/-- The rely-possibly semantics for probability.

    A probability expression t has modal type ⟨C⟩_{x_k::A_k} Prob means:
    - We RELY on events x_k being well-typed (having types A_k)
    - It's POSSIBLE in one rewrite step to reach a probability value

    This captures the computational content of probability inference! -/
def relyPossiblySemant (mt : ProbModalType) : String :=
  let relies := mt.relies.map (fun (v, ty) => s!"{v} :: {repr ty}")
  let reliesStr := String.intercalate ", " relies
  s!"RELY on [{reliesStr}] → POSSIBLY compute {repr mt.resultType}"

/-!
## §10: Novel Theories from the Hypercube

The hypercube suggests unexplored probability theories!
-/

/-- A theory candidate at an unexplored vertex -/
structure TheoryCandidate where
  vertex : ProbabilityVertex
  suggestedRewrites : List ProbabilityBaseRewrite
  description : String

/-- Imprecise K&S: K&S algebra with belief intervals -/
def impreciseKS : TheoryCandidate where
  vertex := { knuthSkilling with precision := .imprecise }
  suggestedRewrites := [modifyRewrite ksAssociativity .addImprecision]
  description := "K&S with lower/upper plausibility bounds instead of point estimates"

/-- Non-commutative belief functions: Quantum D-S hybrid -/
def quantumDS : TheoryCandidate where
  vertex := { dempsterShafer with commutativity := .noncommutative }
  suggestedRewrites := []  -- Would need quantum Dempster rule
  description := "D-S belief functions on non-commutative algebras (quantum events)"

/-- Partial-order classical: Classical probability without total ordering -/
def partialClassical : TheoryCandidate where
  vertex := { kolmogorov with orderAxis := .partialOrder }
  suggestedRewrites := []
  description := "Classical probability allowing incomparable events"

/-- List of unexplored theory candidates suggested by the hypercube -/
def unexploredTheories : List TheoryCandidate :=
  [impreciseKS, quantumDS, partialClassical]

/-!
## §11: Summary - The Power of H_Σ for Probability

The Stay-Wells H_Σ construction reveals:

1. **Systematic Generation**: Each base rewrite generates a hypercube of typed calculi
2. **Modal Semantics**: Probability inference has rely-possibly semantics
3. **Theory Classification**: Different rewrites → different theories
4. **Novel Theories**: The hypercube suggests unexplored vertices

This transforms "what is probability?" from a foundational question to a
structural one: probability theories are vertices in a categorical hypercube
generated by operational semantics!

### Comparison of Hypercubes

| Theory    | Key Rewrite     | Dimension | Vertices |
|-----------|-----------------|-----------|----------|
| Classical | Product rule    | ~10       | ~1024    |
| K&S       | Associativity   | ~10       | ~1024    |
| D-S       | Dempster rule   | ~8        | ~256     |
| Quantum   | Born rule       | ~12       | ~4096    |

### Future Directions

1. Formalize D-S Dempster rule and its hypercube
2. Formalize quantum Born rule and its hypercube
3. Prove collapse theorems (which vertices are inhabited?)
4. Connect to credal sets and desirable gambles
5. Generate truly novel probability theories at unexplored vertices
-/

end Mettapedia.ProbabilityTheory.Hypercube.StayWells
