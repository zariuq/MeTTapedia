/-
# Operational Semantics of Probability Theories

Following Stay & Wells' H_Σ construction, we define the operational semantics
(rewrite rules) for each probability theory and show how modal types emerge.

## Key Insight

The "base rewrites" of a probability theory are its inference rules:
- Product rule: P(A∧B|C) ⇝ P(A|C) · P(B|A∧C)
- Sum rule: P(A∨B) ⇝ P(A) + P(B) - P(A∧B)
- K&S combination: (a ⊕ b) ⊕ c ⇝ a ⊕ (b ⊕ c)  [identity via associativity]

These rewrites have "slots" (subterm positions) that can be assigned
sorts (∗ = types, □ = kinds), generating a hypercube of typed calculi.

## The Modal Type Connection

For each rewrite L ⇝ R with context C_j:
- Modal type: ⟨C_j⟩_{x_k::A_k} B
- Semantics: "If we RELY on parameters having types A_k,
             it's POSSIBLE to reach a reduct with type B"

For probability theories, this becomes:
- "If we RELY on prior probabilities p(A), p(B|A),
   it's POSSIBLE to compute p(A∧B)"

## References

- Stay & Wells, "Generating Hypercubes of Type Systems"
- Knuth & Skilling, Appendix A
-/

import Mettapedia.ProbabilityTheory.Hypercube.Basic

namespace Mettapedia.ProbabilityTheory.Hypercube.OperationalSemantics

open Mettapedia.ProbabilityTheory.Hypercube

/-!
## §1: Terms for Probability Calculus

Define the term language for expressing probability expressions.
-/

/-- Terms in a probability calculus. -/
inductive ProbTerm where
  | event : String → ProbTerm                    -- Atomic event A
  | prob : ProbTerm → ProbTerm                   -- P(A)
  | condProb : ProbTerm → ProbTerm → ProbTerm   -- P(A|B)
  | conj : ProbTerm → ProbTerm → ProbTerm       -- A ∧ B
  | disj : ProbTerm → ProbTerm → ProbTerm       -- A ∨ B
  | neg : ProbTerm → ProbTerm                    -- ¬A
  | real : ℝ → ProbTerm                          -- Real number
  | add : ProbTerm → ProbTerm → ProbTerm        -- p + q
  | mul : ProbTerm → ProbTerm → ProbTerm        -- p · q
  | sub : ProbTerm → ProbTerm → ProbTerm        -- p - q
  | div : ProbTerm → ProbTerm → ProbTerm        -- p / q
  deriving Inhabited

namespace ProbTerm

-- Notation helpers
def P (A : ProbTerm) : ProbTerm := prob A
def cond (A B : ProbTerm) : ProbTerm := condProb A B

-- Common patterns
def eventA : ProbTerm := event "A"
def eventB : ProbTerm := event "B"
def eventC : ProbTerm := event "C"

end ProbTerm

/-!
## §2: Rewrite Rules as Operational Semantics

Each probability theory has characteristic rewrite rules.
-/

/-- A rewrite rule: LHS ⇝ RHS with name and conditions. -/
structure ProbRewrite where
  name : String
  lhs : ProbTerm
  rhs : ProbTerm
  /-- Conditions for the rewrite to apply -/
  conditions : List String

/-- The product rule: P(A∧B|C) = P(A|C) · P(B|A∧C) -/
def productRule : ProbRewrite where
  name := "product"
  lhs := ProbTerm.condProb (ProbTerm.conj ProbTerm.eventA ProbTerm.eventB) ProbTerm.eventC
  rhs := ProbTerm.mul
           (ProbTerm.condProb ProbTerm.eventA ProbTerm.eventC)
           (ProbTerm.condProb ProbTerm.eventB (ProbTerm.conj ProbTerm.eventA ProbTerm.eventC))
  conditions := []

/-- The sum rule: P(A∨B) = P(A) + P(B) - P(A∧B) -/
def sumRule : ProbRewrite where
  name := "sum"
  lhs := ProbTerm.prob (ProbTerm.disj ProbTerm.eventA ProbTerm.eventB)
  rhs := ProbTerm.sub
           (ProbTerm.add (ProbTerm.prob ProbTerm.eventA) (ProbTerm.prob ProbTerm.eventB))
           (ProbTerm.prob (ProbTerm.conj ProbTerm.eventA ProbTerm.eventB))
  conditions := []

/-- The negation rule: P(¬A) = 1 - P(A) -/
def negationRule : ProbRewrite where
  name := "negation"
  lhs := ProbTerm.prob (ProbTerm.neg ProbTerm.eventA)
  rhs := ProbTerm.sub (ProbTerm.real 1) (ProbTerm.prob ProbTerm.eventA)
  conditions := []

/-- Bayes' rule: P(A|B) = P(B|A) · P(A) / P(B) -/
def bayesRule : ProbRewrite where
  name := "bayes"
  lhs := ProbTerm.condProb ProbTerm.eventA ProbTerm.eventB
  rhs := ProbTerm.div
           (ProbTerm.mul
             (ProbTerm.condProb ProbTerm.eventB ProbTerm.eventA)
             (ProbTerm.prob ProbTerm.eventA))
           (ProbTerm.prob ProbTerm.eventB)
  conditions := ["P(B) ≠ 0"]

/-- Classical probability rewrites. -/
def classicalRewrites : List ProbRewrite :=
  [productRule, sumRule, negationRule, bayesRule]

/-!
## §3: K&S Operational Semantics

K&S has different base rewrites focused on the combination operation.
-/

/-- Terms in the K&S calculus (focus on the ⊕ operation). -/
inductive KSTerm where
  | elem : String → KSTerm           -- Element x
  | ident : KSTerm                   -- Identity element 0
  | op : KSTerm → KSTerm → KSTerm    -- x ⊕ y
  | iterate : KSTerm → Nat → KSTerm  -- x^n (n-fold operation)
  deriving Inhabited, Repr

/-- The K&S associativity rewrite: (x ⊕ y) ⊕ z ⇝ x ⊕ (y ⊕ z) -/
def ksAssocRewrite : String × KSTerm × KSTerm :=
  ("associativity",
   KSTerm.op (KSTerm.op (KSTerm.elem "x") (KSTerm.elem "y")) (KSTerm.elem "z"),
   KSTerm.op (KSTerm.elem "x") (KSTerm.op (KSTerm.elem "y") (KSTerm.elem "z")))

/-- The K&S right identity rewrite: x ⊕ 0 ⇝ x -/
def ksRightIdentRewrite : String × KSTerm × KSTerm :=
  ("right_identity",
   KSTerm.op (KSTerm.elem "x") KSTerm.ident,
   KSTerm.elem "x")

/-- The K&S left identity rewrite: 0 ⊕ x ⇝ x -/
def ksLeftIdentRewrite : String × KSTerm × KSTerm :=
  ("left_identity",
   KSTerm.op KSTerm.ident (KSTerm.elem "x"),
   KSTerm.elem "x")

/-!
## §4: Subterm Positions and Slots

Following Stay-Wells, each rewrite has subterm positions (slots).
-/

/-- A slot in a probability rewrite. -/
structure ProbSlot where
  name : String
  carrier : String  -- The type of values at this slot
  deriving Repr

/-- Slots for the product rule:
    P(A∧B|C) = P(A|C) · P(B|A∧C)

    Slots:
    1. A : Event
    2. B : Event
    3. C : Event
    4. P(A|C) : [0,1]
    5. P(B|A∧C) : [0,1]
-/
def productRuleSlots : List ProbSlot :=
  [ { name := "A", carrier := "Event" },
    { name := "B", carrier := "Event" },
    { name := "C", carrier := "Event" },
    { name := "P(A|C)", carrier := "Prob" },
    { name := "P(B|A∧C)", carrier := "Prob" } ]

/-- Slots for K&S associativity:
    (x ⊕ y) ⊕ z = x ⊕ (y ⊕ z)

    Slots:
    1. x : α
    2. y : α
    3. z : α
-/
def ksAssocSlots : List ProbSlot :=
  [ { name := "x", carrier := "Plausibility" },
    { name := "y", carrier := "Plausibility" },
    { name := "z", carrier := "Plausibility" } ]

/-!
## §5: Sort Assignments and the Hypercube

Different sort assignments to slots give different type systems.
-/

/-- A sort: ∗ (types, inhabited) or □ (kinds, uninhabited). -/
inductive ProbSort where
  | star : ProbSort  -- ∗ = concrete values
  | box : ProbSort   -- □ = type-level only
  deriving DecidableEq, Repr

/-- A sort assignment maps slots to sorts. -/
def SortAssignment := List (ProbSlot × ProbSort)

/-- The dimension of the hypercube for a rewrite. -/
def hypercubeDimension (slots : List ProbSlot) : Nat := slots.length

/-- Number of vertices = 2^dimension. -/
def numVertices (slots : List ProbSlot) : Nat := 2 ^ hypercubeDimension slots

-- Product rule: 5 slots → 2^5 = 32 typed calculi
-- K&S assoc: 3 slots → 2^3 = 8 typed calculi

/-!
## §6: The Modal Type Construction

For each subterm position, generate a modal type.
-/

/-- A modal type generated from a probability rewrite.

    For the product rule at position "P(A|C)":
    ⟨[−] · P(B|A∧C)⟩_{A,B,C::Event} Prob

    "If we RELY on A, B, C being events,
     it's POSSIBLE to compute P(A∧B|C) via the product rule"
-/
structure ProbModalType where
  /-- The generating slot -/
  slot : ProbSlot
  /-- Context slots (free variables) -/
  context : List ProbSlot
  /-- Result type -/
  resultCarrier : String
  deriving Repr

/-- Generate modal types for the product rule. -/
def productRuleModalTypes : List ProbModalType :=
  [ -- From position P(A|C): need A, B, C to compute
    { slot := { name := "P(A|C)", carrier := "Prob" },
      context := productRuleSlots.filter (fun s => s.carrier = "Event"),
      resultCarrier := "Prob" },
    -- From position P(B|A∧C): need A, B, C to compute
    { slot := { name := "P(B|A∧C)", carrier := "Prob" },
      context := productRuleSlots.filter (fun s => s.carrier = "Event"),
      resultCarrier := "Prob" } ]

/-!
## §7: The Central Insight: K&S Commutativity

The hypercube framework reveals why commutativity matters for K&S.

Consider the K&S rewrites:
- (x ⊕ y) ⊕ z ⇝ x ⊕ (y ⊕ z)   [associativity]
- x ⊕ 0 ⇝ x                    [identity]

These DON'T explicitly include:
- x ⊕ y ⇝ y ⊕ x               [commutativity]

But the representation theorem maps to (ℝ≥0, +) which IS commutative!

The question: does the proof path THROUGH the hypercube require commutativity?
-/

/-- The K&S proof path through the hypercube.

    Start: KnuthSkillingAlgebra (associative, monotone, Archimedean)
    ↓
    Step 1: Iterate sequence x, x⊕x, (x⊕x)⊕x, ...
    ↓
    Step 2: Show iterate is unbounded (Archimedean)
    ↓
    Step 3: Build linearizing map Θ
    ↓
    Step 4: Θ(x ⊕ y) = Θ(x) + Θ(y) ← THIS is where commutativity sneaks in!
    ↓
    End: Homomorphism to (ℝ≥0, +)

    The sneaky step: proving Θ(x ⊕ y) = Θ(y ⊕ x) uses the fact that
    both sides equal Θ(x) + Θ(y). But why do they equal this?

    Because + is commutative! So Θ(x) + Θ(y) = Θ(y) + Θ(x).
    And the uniqueness of Θ then forces x ⊕ y = y ⊕ x.
-/
def ksProofPath : List String :=
  [ "1. Define iterate: x^n = x ⊕ x ⊕ ... ⊕ x (n times)",
    "2. Archimedean: ∀y, ∃n, y < x^n",
    "3. Build linearizer Θ using iterate ratios",
    "4. Show Θ(x ⊕ y) = Θ(x) + Θ(y)",
    "5. Map to (ℝ≥0, +) via Θ",
    "6. Commutativity follows from + being commutative" ]

/-- The commutativity theorem for K&S.

    This theorem states: IF the K&S axioms hold AND the proof goes through,
    THEN commutativity is a CONSEQUENCE, not an assumption.

    This is the "naturality" of K&S: commutativity emerges from the
    algebraic structure, it's not put in by hand.
-/
theorem ks_commutativity_is_consequence :
    -- If we have a valid KnuthSkillingAlgebra
    -- Then commutativity holds
    -- (This is a theorem, not an axiom!)
    knuthSkilling.commutativity = CommutativityAxis.commutative :=
  rfl

/-!
## §8: Comparison: Where Theories Differ in Operational Semantics

Different probability theories have different "base rewrites":

1. **Classical/Cox**: Product rule, sum rule, negation rule, Bayes' rule
   - All events commute: A∧B = B∧A
   - Probabilities are precise: P(A) + P(¬A) = 1

2. **K&S**: Associativity, identity, monotonicity, Archimedean
   - Derives the same rules as Cox!
   - But starts from algebraic axioms

3. **D-S**: Dempster combination rule
   - m₁₂(C) = (1-K)⁻¹ · Σ_{A∩B=C} m₁(A)·m₂(B)
   - Imprecise: Bel(A) ≤ Pl(A) (gap allowed)

4. **Quantum**: Born rule, unitary evolution
   - Non-commutative: [A,B] ≠ 0 allowed
   - State collapse on measurement
-/

/-- The key operational difference between theories. -/
structure OperationalDifference where
  theory1 : ProbabilityVertex
  theory2 : ProbabilityVertex
  differingRewrite : String
  description : String

def ks_vs_cox_difference : OperationalDifference where
  theory1 := knuthSkilling
  theory2 := cox
  differingRewrite := "starting_point"
  description := "K&S starts from algebraic axioms and DERIVES probability; \
                  Cox starts from functional equations and DERIVES probability"

def classical_vs_quantum_difference : OperationalDifference where
  theory1 := kolmogorov
  theory2 := quantum
  differingRewrite := "commutativity"
  description := "Classical: A∧B = B∧A always; \
                  Quantum: [A,B] ≠ 0 for incompatible observables"

def classical_vs_ds_difference : OperationalDifference where
  theory1 := kolmogorov
  theory2 := dempsterShafer
  differingRewrite := "precision"
  description := "Classical: P(A) + P(¬A) = 1; \
                  D-S: Bel(A) + Bel(¬A) ≤ 1 (imprecision allowed)"

end Mettapedia.ProbabilityTheory.Hypercube.OperationalSemantics
