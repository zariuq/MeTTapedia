import Mettapedia.Logic.LP.FunctionFreeEvaluation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Multiset.Basic

/-!
# LP ↔ PathMap Bridge

Port of `Mettapedia.Logic.Datalog.PathMapBridge` onto LP types.

A finite LP model (`FinInterpretation σ = Finset (GroundAtom σ)`) can serve as
a relational store for conjunctive queries.

- `LPQuery` — a `Bool`-valued predicate on ground atoms
- `queryResult` — filter a finite interpretation by a query
- `leastHerbrandModelFin` — extract a `Finset` from the least Herbrand model
- `evidence_total` — positive + negative = total
- `leastHerbrandModel_monotone_in_rules` — more rules/facts ⇒ larger least model

## References

- Green, Karvounarakis, Tannen, "Provenance Semirings", PODS 2007.
-/

namespace Mettapedia.Logic.LP

/-! ## Section 1: Conjunctive queries -/

/-- A conjunctive query: a `Bool`-valued predicate on ground atoms. -/
abbrev LPQuery (σ : LPSignature) := GroundAtom σ → Bool

/-- Answer a conjunctive query against a finite interpretation. -/
def queryResult {σ : LPSignature}
    (q : LPQuery σ) (I : FinInterpretation σ) : Finset (GroundAtom σ) :=
  I.filter (fun a => q a)

/-- The multiset of all matching atoms (for evidence counting). -/
noncomputable def queryMultiset {σ : LPSignature}
    (q : LPQuery σ) (I : FinInterpretation σ) : Multiset (GroundAtom σ) :=
  (queryResult q I).val

/-! ## Section 2: Finite model from leastHerbrandModel -/

/-- When the signature is function-free and constants/relations are `Fintype`, extract
    a finite model from `leastHerbrandModel kb`. -/
noncomputable def leastHerbrandModelFin {σ : LPSignature}
    [IsEmpty σ.functionSymbols]
    [Fintype σ.constants] [DecidableEq σ.constants]
    [Fintype σ.relationSymbols] [DecidableEq σ.relationSymbols]
    (kb : KnowledgeBase σ) : FinInterpretation σ :=
  (leastHerbrandModel_finite kb).toFinset

/-- The finite model agrees with the set model. -/
theorem mem_leastHerbrandModelFin_iff {σ : LPSignature}
    [IsEmpty σ.functionSymbols]
    [Fintype σ.constants] [DecidableEq σ.constants]
    [Fintype σ.relationSymbols] [DecidableEq σ.relationSymbols]
    (kb : KnowledgeBase σ) (a : GroundAtom σ) :
    a ∈ leastHerbrandModelFin kb ↔ a ∈ leastHerbrandModel kb :=
  Set.Finite.mem_toFinset _

/-! ## Section 3: BinaryEvidence counting -/

/-- Count positive evidence: atoms in `I` satisfying query `q`. -/
def positiveEvidence {σ : LPSignature}
    (q : LPQuery σ) (I : FinInterpretation σ) : ℕ :=
  (queryResult q I).card

/-- Count negative evidence: atoms in `I` NOT satisfying query `q`. -/
def negativeEvidence {σ : LPSignature}
    (q : LPQuery σ) (I : FinInterpretation σ) : ℕ :=
  (I.filter (fun a => !q a)).card

/-- Total evidence = positive + negative = total atoms in I. -/
theorem evidence_total {σ : LPSignature}
    (q : LPQuery σ) (I : FinInterpretation σ) :
    positiveEvidence q I + negativeEvidence q I = I.card := by
  simp only [positiveEvidence, negativeEvidence, queryResult]
  have hneq : I.filter (fun a => !q a) = I.filter (fun a => ¬(q a : Prop)) := by
    congr 1; ext a; simp [Bool.not_eq_true]
  rw [hneq]
  exact Finset.card_filter_add_card_filter_not (fun a => (q a : Prop))

/-! ## Section 4: Monotonicity -/

/-- Adding more rules (or facts) to a knowledge base can only increase the leastHerbrandModel. -/
theorem leastHerbrandModel_monotone_in_rules {σ : LPSignature}
    (kb₁ kb₂ : KnowledgeBase σ)
    (h_db : kb₁.db ⊆ kb₂.db)
    (h_prog : ∀ r ∈ kb₁.prog, r ∈ kb₂.prog) :
    leastHerbrandModel kb₁ ⊆ leastHerbrandModel kb₂ := by
  apply leastHerbrandModel_least
  rw [T_P_LP_le_iff]
  exact ⟨fun a ha => leastHerbrandModel_db kb₂ a (h_db ha),
         fun c g hc hbody => leastHerbrandModel_clause kb₂ c (h_prog c hc) g hbody⟩

end Mettapedia.Logic.LP
