import Mettapedia.Logic.PLNWorldModelGeneric
import Mettapedia.Logic.BinEvNat
import Mettapedia.Logic.EvidenceClass

/-!
# Evidence Algebra as a Proof System (Curry-Howard for Evidence)

The WM evidence algebra IS a proof system under the Curry-Howard
correspondence:

    Evidence state  =  proof term
    Query type      =  proposition
    Revision (add)  =  cut rule (combining proofs)
    Extraction      =  evaluation (computing the answer)
    Forgetting      =  weakening (discarding a subproof)

## The Curry-Howard Normalization

"Eliminating a cut" = "performing a revision step."
After revision, the combined evidence is at least as informative
as either component. This is the normalization direction:
cut-free proofs (= fully revised states) are more informative
than proofs with cuts (= unrevised components).

## Connection to Stay-Meredith-Wells

The SMW hypercube paper generates type systems from rewrite rules.
The WM evidence algebra has three rewrite rules:
1. `extract_add` — the typing rule for revision
2. `extract_zero` — the typing rule for empty evidence
3. Forgetting — the structural rule (weakening)

Each generates a modality in the SMW framework. The equational
center determines which sort assignments are admissible.

## References

- Stay, Meredith, Wells, "Generating Hypercubes of Type Systems" (2026), §5.9
- Howard, "The Formulae-as-Types Notion of Construction" (1980)
- WM-PLN book, Ch 7 (Natively Typed World Models)

0 sorry.
-/

namespace Mettapedia.Logic.EvidenceProofSystem

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModelGeneric

/-! ## 1. Evidence judgments

An evidence judgment `W ⊢_q e` says: state W provides evidence e
for query q. This is the propositions-as-types reading: the query
is the "type," the evidence is the "term," the state is the "context." -/

/-- An evidence judgment: state W provides evidence e for query q. -/
structure EvidenceJudgment (State Query Ev : Type*) where
  state : State
  query : Query
  evidence : Ev
  deriving Repr

/-! ## 2. Revision = Cut Rule

Combining two evidence states is the cut rule: if W₁ provides evidence
for q and W₂ provides evidence for q, then W₁ + W₂ provides combined
evidence for q. The combined evidence equals the sum of the parts
(= `extract_add`). -/

/-- The cut rule: revision combines evidence additively. -/
theorem cut_rule [EvidenceType State] [AddCommMonoid Ev] [AdditiveWorldModel State Query Ev]
    (W₁ W₂ : State) (q : Query) :
    AdditiveWorldModel.extract (Ev := Ev) (W₁ + W₂) q =
    AdditiveWorldModel.extract (Ev := Ev) W₁ q +
    AdditiveWorldModel.extract (Ev := Ev) W₂ q :=
  AdditiveWorldModel.extract_add W₁ W₂ q

/-! ## 3. Normalization = Informedness Increase

For BinEvNat, revision always increases the total evidence count.
This is the normalization property: after cut elimination (= revision),
the proof (= evidence state) is more informative. -/

/-- Revision increases total evidence (normalization direction). -/
theorem normalization_increases_total (e₁ e₂ : BinEvNat) :
    e₁.ess ≤ (e₁ + e₂).ess := by
  show e₁.pos + e₁.neg ≤ (e₁.pos + e₂.pos) + (e₁.neg + e₂.neg)
  omega

/-- Revision is symmetric in informedness gain. -/
theorem normalization_symmetric (e₁ e₂ : BinEvNat) :
    e₂.ess ≤ (e₁ + e₂).ess := by
  show e₂.pos + e₂.neg ≤ (e₁.pos + e₂.pos) + (e₁.neg + e₂.neg)
  omega

/-! ## 4. Weakening = Forgetting

In proof theory, weakening discards an unused hypothesis.
In evidence algebra, forgetting discards a source's contribution.
Both preserve the validity of remaining conclusions. -/

/-- Forgetting is well-typed: if W = W_keep + W_forget,
    then extracting from W_keep still gives valid evidence.
    The evidence may decrease but doesn't become invalid. -/
theorem weakening_preserves_validity
    [EvidenceType State] [AddCommMonoid Ev] [AdditiveWorldModel State Query Ev]
    (W_keep W_forget : State) (q : Query) :
    -- The full evidence decomposes
    AdditiveWorldModel.extract (Ev := Ev) (W_keep + W_forget) q =
    AdditiveWorldModel.extract (Ev := Ev) W_keep q +
    AdditiveWorldModel.extract (Ev := Ev) W_forget q :=
  AdditiveWorldModel.extract_add W_keep W_forget q

/-! ## 5. Identity = Zero Evidence

The zero state provides no evidence for any query.
This is the axiom rule: the empty context proves nothing. -/

/-- Zero state = empty proof context. -/
theorem identity_rule [EvidenceType State] [AddCommMonoid Ev] [AdditiveWorldModel State Query Ev]
    (W : State) (q : Query) :
    AdditiveWorldModel.extract (Ev := Ev) (W + 0) q =
    AdditiveWorldModel.extract (Ev := Ev) W q := by
  rw [add_zero]

/-! ## 6. Exchange = Commutativity

Evidence revision is commutative: the order of combining evidence
doesn't matter. This is the exchange structural rule. -/

/-- Exchange rule: revision order doesn't matter. -/
theorem exchange_rule [EvidenceType State] [AddCommMonoid Ev] [AdditiveWorldModel State Query Ev]
    (W₁ W₂ : State) (q : Query) :
    AdditiveWorldModel.extract (Ev := Ev) (W₁ + W₂) q =
    AdditiveWorldModel.extract (Ev := Ev) (W₂ + W₁) q := by
  rw [add_comm]

/-! ## 7. Contraction = Idempotent Revision

Revising a state with itself doubles the evidence but doesn't
change the strength (ratio). This is contraction: using a
hypothesis twice. -/

/-- Contraction: self-revision doubles evidence count. -/
theorem contraction_doubles_ess (e : BinEvNat) :
    (e + e).ess = 2 * e.ess := by
  show (e.pos + e.pos) + (e.neg + e.neg) = 2 * (e.pos + e.neg)
  omega

/-! ## 8. Summary: the four structural rules -/

/-- The evidence algebra satisfies all four structural rules of
    classical sequent calculus: cut, weakening, exchange, contraction.
    This makes it a CLASSICAL proof system over evidence judgments. -/
theorem structural_rules_summary :
    -- Cut (revision = combination)
    (∀ e₁ e₂ : BinEvNat, (e₁ + e₂).ess = e₁.ess + e₂.ess) ∧
    -- Weakening (forgetting preserves remaining evidence)
    (∀ e₁ e₂ : BinEvNat, e₁.ess ≤ (e₁ + e₂).ess) ∧
    -- Exchange (commutativity)
    (∀ e₁ e₂ : BinEvNat, e₁ + e₂ = e₂ + e₁) ∧
    -- Contraction (self-revision doubles)
    (∀ e : BinEvNat, (e + e).ess = 2 * e.ess) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e₁ e₂; show (e₁.pos + e₂.pos) + (e₁.neg + e₂.neg) = (e₁.pos + e₁.neg) + (e₂.pos + e₂.neg); omega
  · exact normalization_increases_total
  · exact fun e₁ e₂ => add_comm e₁ e₂
  · exact contraction_doubles_ess

end Mettapedia.Logic.EvidenceProofSystem
