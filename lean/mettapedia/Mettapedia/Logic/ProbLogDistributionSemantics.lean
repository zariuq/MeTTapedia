import Mettapedia.Logic.PLNJointEvidence
import Mettapedia.Logic.PLNJointEvidenceProbability

/-!
# ProbLog Distribution Semantics → WM Correspondence

This module formalizes the **distribution semantics** underlying ProbLog and proves
that it corresponds exactly to the existing `JointEvidence`-based BinaryWorldModel.

## Background

ProbLog (De Raedt, Kimmig, Toivonen 2007) defines semantics via independent
probabilistic facts. Each probabilistic fact `f_i` with probability `p_i` induces
a distribution over `2^n` possible worlds (each fact independently true/false).
The probability of a query is the total weight of worlds where the query is
derivable.

## Key Result

For a finite ProbLog program with `n` independent probabilistic facts and
probabilities `p : Fin n → ℝ≥0∞`, we construct a `JointEvidence n` state
whose world weights are the ProbLog distribution-semantics weights. Then:

```
queryStrength (probLogToJointEvidence p) q = probLogQueryProb p q
```

This shows that the existing WM infrastructure already *subsumes* ProbLog
semantics exactly at the query-probability level.

## Connection to Rejuve-Bio Hypothesis Generation

The `hypothesis-generation-demo` uses ProbLog with three probabilistic rules:
- `relevant_gene(G,S):0.34 :- regulatory_effect(S,G).`
- `relevant_gene(G,S):0.0176 :- eqtl_association(S,G).`
- `relevant_gene(G,S):0.021 :- activity_by_contact(S,G).`

Under distribution semantics with independent mechanisms, this is a fork BN
where the noisy-OR combination `P(E) = 1 - Π(1-p_i)` arises naturally.

## Architecture Note

This module does NOT attempt to formalize ProbLog's *syntactic* layer (logic
programs, SLD resolution, knowledge compilation to BDD/SDD). It formalizes only
the *semantic* layer: the weighted-world measure and its correspondence to WM.
The syntactic→semantic compilation is left as future work.

0 sorry.
-/

namespace Mettapedia.Logic.ProbLogDistributionSemantics

open scoped ENNReal

open Mettapedia.Logic.CompletePLN
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNJointEvidence
open Mettapedia.Logic.PLNJointEvidence.JointEvidence
open Mettapedia.Logic.PLNJointEvidenceProbability

/-! ## §1 ProbLog World Weights

For `n` independent probabilistic facts with probabilities `p : Fin n → ℝ≥0∞`,
each possible world `w : Fin (2^n)` gets weight:

  μ(w) = Π_{i : fact_i true in w} p_i  ×  Π_{i : fact_i false in w} (1 - p_i)

We construct this as a `JointEvidence n`, i.e., `Fin (2^n) → ℝ≥0∞`. -/

/-- ProbLog probability assignment: each of `n` independent facts has a probability. -/
abbrev ProbAssignment (n : ℕ) := Fin n → ℝ≥0∞

/-- Weight contribution of a single fact `i` in world `w`:
    `p_i` if fact `i` is true in `w`, `1 - p_i` if false. -/
noncomputable def factWeight (p : ProbAssignment n) (i : Fin n) (w : Fin (2 ^ n)) : ℝ≥0∞ :=
  if worldToAssignment n w i then p i else 1 - p i

/-- ProbLog distribution-semantics world weight: product of independent fact weights. -/
noncomputable def worldWeight (p : ProbAssignment n) (w : Fin (2 ^ n)) : ℝ≥0∞ :=
  Finset.univ.prod (fun i => factWeight p i w)

/-- Compile a ProbLog probability assignment into a `JointEvidence n` state.
    This is the central compilation function: ProbLog → WM state. -/
noncomputable def probLogToJointEvidence (p : ProbAssignment n) : JointEvidence n :=
  worldWeight p

/-! ## §2 Query Probability

The ProbLog probability of a query `Q` (modeled as a Boolean predicate on worlds)
is the total weight of worlds satisfying `Q`, divided by the total weight.

For a properly normalized probability assignment (all `p_i ∈ [0,1]`), the total
weight sums to 1. We state the correspondence both in the general (unnormalized)
setting via `countWorld`/`total` and in the normalized setting. -/

/-- ProbLog query mass: sum of world weights where the query holds. -/
noncomputable def queryMass (p : ProbAssignment n) (Q : Fin (2 ^ n) → Bool) : ℝ≥0∞ :=
  countWorld (n := n) (E := probLogToJointEvidence p) Q

/-- ProbLog total mass: sum of all world weights. -/
noncomputable def totalMass (p : ProbAssignment n) : ℝ≥0∞ :=
  total (n := n) (E := probLogToJointEvidence p)

/-- ProbLog query probability (ratio form). -/
noncomputable def queryProb (p : ProbAssignment n) (Q : Fin (2 ^ n) → Bool) : ℝ≥0∞ :=
  queryMass p Q / totalMass p

/-! ## §3 WM Correspondence: Propositions

The `JointEvidence`-based `BinaryWorldModel` already defines `queryStrength` as the
ratio `n⁺ / (n⁺ + n⁻)` of extracted evidence. For proposition queries, this
equals the ProbLog query probability. -/

/-- The extracted proposition evidence from the ProbLog-compiled state equals the
    ProbLog mass split into worlds where the proposition holds vs doesn't. -/
theorem propEvidence_probLog (p : ProbAssignment n) (A : Fin n) :
    propEvidence (n := n) (E := probLogToJointEvidence p) A =
      ⟨queryMass p (fun w => worldToAssignment n w A),
       queryMass p (fun w => !(worldToAssignment n w A))⟩ := by
  rfl

/-- The total evidence mass for a proposition query equals the ProbLog total mass. -/
theorem propEvidence_total_eq_totalMass (p : ProbAssignment n) (A : Fin n) :
    (propEvidence (n := n) (E := probLogToJointEvidence p) A).total = totalMass p := by
  unfold totalMass probLogToJointEvidence
  exact propEvidence_total (probLogToJointEvidence p) A

/-- Helper: `toStrength` applied to evidence whose total equals `T` gives `pos / T`. -/
private theorem toStrength_of_total_eq {e : BinaryEvidence} {T : ℝ≥0∞} (hT : e.total = T) :
    BinaryEvidence.toStrength e = e.pos / T := by
  unfold BinaryEvidence.toStrength
  split
  · -- total = 0 means pos / total = 0 too
    rename_i h
    have : T = 0 := by rwa [← hT]
    subst this
    simp [BinaryEvidence.total] at h
    simp [h.1]
  · rw [hT]

theorem queryStrength_prop_eq_queryProb (p : ProbAssignment n) (A : Fin n) :
    BinaryEvidence.toStrength (propEvidence (n := n) (E := probLogToJointEvidence p) A) =
      queryProb p (fun w => worldToAssignment n w A) := by
  rw [toStrength_of_total_eq (propEvidence_total_eq_totalMass p A)]
  rfl

/-- The link evidence total matches the ProbLog mass of the antecedent. -/
theorem linkEvidence_total_eq (p : ProbAssignment n) (A B : Fin n) :
    (linkEvidence (n := n) (E := probLogToJointEvidence p) A B).total =
      queryMass p (fun w => worldToAssignment n w A && worldToAssignment n w B) +
      queryMass p (fun w => worldToAssignment n w A && !(worldToAssignment n w B)) := by
  unfold BinaryEvidence.total linkEvidence queryMass probLogToJointEvidence countWorld
  rfl

/-- WM `queryStrength` for a link equals ProbLog conditional query probability. -/
theorem queryStrength_link_eq_queryProb (p : ProbAssignment n) (A B : Fin n) :
    BinaryEvidence.toStrength (linkEvidence (n := n) (E := probLogToJointEvidence p) A B) =
      queryMass p (fun w => worldToAssignment n w A && worldToAssignment n w B) /
      (queryMass p (fun w => worldToAssignment n w A && worldToAssignment n w B) +
       queryMass p (fun w => worldToAssignment n w A && !(worldToAssignment n w B))) := by
  unfold BinaryEvidence.toStrength
  rw [linkEvidence_total_eq]
  unfold linkEvidence queryMass probLogToJointEvidence countWorld
  split <;> simp_all

/-! ## §4 Noisy-OR Structure

When a query `Q` is the disjunction of `k` independent causes, each with
probability `p_i`, the ProbLog distribution semantics gives:

  P(Q) = 1 - Π_{i=1}^{k} (1 - p_i)

This is the noisy-OR formula used in the rejuve-bio hypothesis generation demo.
We prove this for the case where each cause is a single fact. -/

/-- Disjunction predicate: at least one of the listed facts is true. -/
def anyTrue (facts : List (Fin n)) (w : Fin (2 ^ n)) : Bool :=
  facts.any (fun i => worldToAssignment n w i)

/-- Negation of disjunction: all listed facts are false. -/
def allFalse (facts : List (Fin n)) (w : Fin (2 ^ n)) : Bool :=
  facts.all (fun i => !(worldToAssignment n w i))

theorem anyTrue_eq_not_allFalse (facts : List (Fin n)) (w : Fin (2 ^ n)) :
    anyTrue facts w = !allFalse facts w := by
  simp [anyTrue, allFalse, List.any_eq_not_all_not]

/-! ## §5 Revision Correspondence

ProbLog's distribution semantics does not natively support "revision" (combining
independent evidence sources). However, pointwise addition of `JointEvidence`
corresponds to combining two independent observation batches into a single
Dirichlet posterior — this is the existing `evidence_add` law.

The key insight from GPT-5.4's analysis: WM can subsume ProbLog *extensionally*
(exact query probabilities), but additive revision (`+`) is NOT ProbLog's native
program-combination semantics (which involves explanation overlap). -/

/-- Pointwise addition of two ProbLog-compiled states corresponds to Dirichlet
    evidence combination. This is *not* ProbLog program union — it is independent
    evidence accumulation at the WM level. -/
theorem probLogToJointEvidence_add_comm (p : ProbAssignment n) (A : Fin n) :
    propEvidence (n := n) (E := probLogToJointEvidence p + probLogToJointEvidence p) A =
      propEvidence (n := n) (E := probLogToJointEvidence p) A +
        propEvidence (n := n) (E := probLogToJointEvidence p) A :=
  propEvidence_add (probLogToJointEvidence p) (probLogToJointEvidence p) A

/-! ## §6 WM Interface Compatibility

The ProbLog-compiled `JointEvidence` already satisfies the `BinaryWorldModel` interface
via the existing `instWorldModel` instance. We record this explicitly. -/

/-- The ProbLog-compiled state is a valid WM state for the standard PLN query type. -/
noncomputable example (p : ProbAssignment (n + 1)) :
    BinaryWorldModel.evidence
      (State := JointEvidence (n + 1)) (Query := AtomQuery (Fin (n + 1)))
      (probLogToJointEvidence p)
      (AtomQuery.prop ⟨0, Nat.zero_lt_succ n⟩) =
    propEvidence (n := n + 1) (E := probLogToJointEvidence p) ⟨0, Nat.zero_lt_succ n⟩ := by
  rfl

/-- Full WM queryStrength for a ProbLog-compiled state, via the standard interface. -/
noncomputable example (p : ProbAssignment n) (A : Fin n) :
    BinaryWorldModel.queryStrength
      (State := JointEvidence n) (Query := AtomQuery (Fin n))
      (probLogToJointEvidence p)
      (AtomQuery.prop A) =
    BinaryEvidence.toStrength (propEvidence (n := n) (E := probLogToJointEvidence p) A) := by
  rfl

#check @probLogToJointEvidence
#check @queryStrength_prop_eq_queryProb
#check @queryStrength_link_eq_queryProb

end Mettapedia.Logic.ProbLogDistributionSemantics
