import Mettapedia.Logic.Datalog.Evaluation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Multiset.Basic

/-!
# Datalog ↔ PathMap Bridge

This module shows how the Datalog semantics connects to the PathMap/RelationalSpace
infrastructure in Mettapedia.

## Core idea

A finite Datalog model (`FinInterpretation τ = Finset (GroundAtom τ)`) can serve as
a relational store for conjunctive queries.  Concretely:

- **Store** = `FinInterpretation τ` (a `Finset (GroundAtom τ)`)
- **Query** = `DatalogQuery τ` (a `Bool`-valued predicate for Finset filtering)
- **Soundness** = facts in `leastModel` are exactly the derivable ground atoms
- **Evidence** = number of atoms satisfying a pattern (via multiset projection)

This connects to the PathMap world because:
1. `leastModel_finite` guarantees the least model is finite (= fits in a `Finset`)
2. The finite model can be converted to a `Multiset` for evidence counting
   (cf. `WorldModelBridge` in `OSLF/PathMap/WorldModelBridge.lean`)

## Key definitions

- `DatalogQuery τ` — a `Bool`-valued predicate on `GroundAtom τ` (decidable by construction)
- `queryResult` — answers a conjunctive query against a finite interpretation
- `positiveEvidence` / `negativeEvidence` — counting evidence
- `evidence_total` — positive + negative = total atoms
- `leastModel_monotone_in_rules` — more rules/facts ⇒ larger least model

-/

namespace Mettapedia.Logic.Datalog

/-! ## Section 1: Conjunctive queries -/

/-- A conjunctive query: a `Bool`-valued predicate on ground atoms.

    Using `Bool` (rather than `Prop`) ensures `DecidablePred` is automatically
    available for `Finset.filter` without extra typeclass assumptions. -/
abbrev DatalogQuery (τ : Signature) := GroundAtom τ → Bool

/-- Answer a conjunctive query against a finite interpretation. -/
def queryResult {τ : Signature}
    (q : DatalogQuery τ) (I : FinInterpretation τ) : Finset (GroundAtom τ) :=
  I.filter (fun a => q a)

/-- The multiset of all matching atoms (for evidence counting). -/
noncomputable def queryMultiset {τ : Signature}
    (q : DatalogQuery τ) (I : FinInterpretation τ) : Multiset (GroundAtom τ) :=
  (queryResult q I).val

/-! ## Section 2: Finite model from leastModel -/

/-- When constants and relation symbols are `Fintype`, extract a finite model from
    `leastModel kb` (using the finiteness proof from `leastModel_finite`). -/
noncomputable def leastModelFin {τ : Signature}
    [Fintype τ.constants] [DecidableEq τ.constants]
    [Fintype τ.relationSymbols] [DecidableEq τ.relationSymbols]
    (kb : KnowledgeBase τ) : FinInterpretation τ :=
  (leastModel_finite kb).toFinset

/-- The finite model agrees with the set model: `a ∈ leastModelFin kb ↔ a ∈ leastModel kb`. -/
theorem mem_leastModelFin_iff {τ : Signature}
    [Fintype τ.constants] [DecidableEq τ.constants]
    [Fintype τ.relationSymbols] [DecidableEq τ.relationSymbols]
    (kb : KnowledgeBase τ) (a : GroundAtom τ) :
    a ∈ leastModelFin kb ↔ a ∈ leastModel kb :=
  Set.Finite.mem_toFinset _

/-! ## Section 3: Evidence counting -/

/-- Count positive evidence: the number of atoms in `I` satisfying query `q`. -/
def positiveEvidence {τ : Signature}
    (q : DatalogQuery τ) (I : FinInterpretation τ) : ℕ :=
  (queryResult q I).card

/-- Count negative evidence: atoms in `I` NOT satisfying query `q`. -/
def negativeEvidence {τ : Signature}
    (q : DatalogQuery τ) (I : FinInterpretation τ) : ℕ :=
  (I.filter (fun a => !q a)).card

/-- Total evidence = positive + negative = total atoms in I. -/
theorem evidence_total {τ : Signature}
    (q : DatalogQuery τ) (I : FinInterpretation τ) :
    positiveEvidence q I + negativeEvidence q I = I.card := by
  simp only [positiveEvidence, negativeEvidence, queryResult]
  -- Rewrite the Bool negation filter as a Prop negation filter, then apply
  -- the non-deprecated Finset.card_filter_add_card_filter_not.
  have hneq : I.filter (fun a => !q a) = I.filter (fun a => ¬(q a : Prop)) := by
    congr 1; ext a; simp [Bool.not_eq_true]
  rw [hneq]
  exact Finset.card_filter_add_card_filter_not (fun a => (q a : Prop))

/-! ## Section 4: Monotonicity -/

/-- Adding more rules (or facts) to a knowledge base can only increase the leastModel. -/
theorem leastModel_monotone_in_rules {τ : Signature}
    (kb₁ kb₂ : KnowledgeBase τ)
    (h_db : kb₁.db ⊆ kb₂.db)
    (h_prog : ∀ r ∈ kb₁.prog, r ∈ kb₂.prog) :
    leastModel kb₁ ⊆ leastModel kb₂ := by
  apply leastModel_least
  rw [T_P_le_iff]
  exact ⟨fun a ha => leastModel_db kb₂ a (h_db (Finset.mem_coe.mp ha)),
         fun r g hr hbody => leastModel_rule kb₂ r (h_prog r hr) g hbody⟩

end Mettapedia.Logic.Datalog
