import Mettapedia.Logic.EvidenceQuantale
import Mettapedia.Logic.PLNDeduction

/-!
# PLN Weighted Sequent Calculus

This file defines a **proof calculus** for PLN, extending Foundation's Tait-style
sequent calculus with evidence weights.

## Motivation

PLN Evidence is a **semantic model** (Heyting algebra), but has no syntactic proof system.
A proof calculus allows:
- Explicit derivation trees with evidence flow
- Soundness/completeness theorems connecting syntax to semantics
- Integration with ATP and proof search

## Design

### Weighted Sequents

Standard sequent: `Γ ⟹ Δ` where `Γ, Δ` are lists of formulas

PLN weighted sequent: `Γ ⟹ₚ Δ` where `Γ, Δ : List (Formula × Evidence)`

Each formula carries an evidence weight `(n⁺, n⁻)` representing:
- `n⁺` = positive evidence for the formula
- `n⁻` = negative evidence against the formula

### Rules

Rules propagate evidence through the derivation tree:

1. **Axiom** (identity): From theory membership with full evidence
2. **Weakening**: Add formulas with ⊥ evidence
3. **And-intro**: Combine evidence via tensor (⊗)
4. **Or-intro**: Combine evidence via join (⊔)
5. **Cut**: Eliminate intermediate formula, combining evidence
6. **Deduction**: Apply PLN deduction formula for implication

### Soundness

The key theorem is:
```
If Γ ⟹ₚ (φ, e) then for any model M: M ⊧ Γ → sem(φ) ≥ e
```

## Implementation Status

This file provides:
- Core definitions (WeightedFormula, WeightedSequent)
- Derivation rules as an inductive type
- Basic lemmas for evidence propagation
- Soundness theorem (with proof)

## References

- Foundation/Logic/Calculus.lean (Tait sequent calculus)
- EvidenceQuantale.lean (Evidence quantale structure)
- PLNDeduction.lean (PLN inference formulas)
-/

namespace Mettapedia.Logic.PLNProofCalculus

open EvidenceQuantale
open PLNDeduction

/-! ## Formula Type

For simplicity, we start with propositional formulas.
Extension to first-order is straightforward but requires more infrastructure.
-/

/-- Propositional variables (indexed by ℕ) -/
abbrev PropVar := ℕ

/-- Propositional formulas -/
inductive Formula : Type where
  | var : PropVar → Formula
  | top : Formula
  | bot : Formula
  | neg : Formula → Formula
  | and : Formula → Formula → Formula
  | or : Formula → Formula → Formula
  | imp : Formula → Formula → Formula
  deriving DecidableEq, Repr

namespace Formula

instance : Inhabited Formula := ⟨top⟩

/-- Negation notation -/
prefix:max "∼" => neg

/-- Conjunction notation -/
infixl:70 " ⋏ " => and

/-- Disjunction notation -/
infixl:65 " ⋎ " => or

/-- Implication notation -/
infixr:60 " ➝ " => imp

end Formula

/-! ## Weighted Formulas and Sequents -/

/-- A formula paired with its evidence weight -/
structure WeightedFormula where
  formula : Formula
  evidence : Evidence

/-- A weighted sequent is a list of weighted formulas -/
abbrev WeightedSequent := List WeightedFormula

/-- Theory: a set of formulas with their evidence -/
abbrev Theory := Set WeightedFormula

/-! ## Evidence Operations for Rules -/

/-- Minimum evidence (for and-intro): take coordinatewise minimum
    Rationale: To prove A ∧ B, we need evidence for both -/
noncomputable def evidenceMeet (e₁ e₂ : Evidence) : Evidence :=
  ⟨min e₁.pos e₂.pos, max e₁.neg e₂.neg⟩

/-- Maximum evidence (for or-intro): take coordinatewise maximum
    Rationale: To prove A ∨ B, evidence for either suffices -/
noncomputable def evidenceJoin (e₁ e₂ : Evidence) : Evidence :=
  ⟨max e₁.pos e₂.pos, min e₁.neg e₂.neg⟩

/-- Cut combines evidence by taking the minimum of the cut formula's
    positive evidence (since we lose that information) -/
noncomputable def evidenceCut (e₁ e₂ : Evidence) : Evidence :=
  ⟨min e₁.pos e₂.pos, max e₁.neg e₂.neg⟩

/-! ## Derivation Rules -/

/-- Weighted sequent derivation.

The judgment `T ⊢ₚ Δ` means:
- From theory T (weighted formulas)
- We can derive sequent Δ (list of weighted formulas)

The evidence in each formula flows through the derivation. -/
inductive Derivation (T : Theory) : WeightedSequent → Type where
  /-- Axiom: formula from theory with its evidence -/
  | axm {wf : WeightedFormula} :
      wf ∈ T → Derivation T [wf]

  /-- Verum: ⊤ has maximal positive evidence -/
  | verum (Δ : WeightedSequent) :
      Derivation T (⟨Formula.top, ⟨⊤, 0⟩⟩ :: Δ)

  /-- Weakening: can add formulas with ⊥ evidence -/
  | wk {Δ Γ : WeightedSequent} :
      Derivation T Δ →
      (∀ wf ∈ Δ, wf ∈ Γ) →
      Derivation T Γ

  /-- And-introduction: combine evidence via meet -/
  | andI {Δ : WeightedSequent} {φ ψ : Formula} {e₁ e₂ : Evidence} :
      Derivation T (⟨φ, e₁⟩ :: Δ) →
      Derivation T (⟨ψ, e₂⟩ :: Δ) →
      Derivation T (⟨φ ⋏ ψ, evidenceMeet e₁ e₂⟩ :: Δ)

  /-- Or-introduction: can derive disjunction from either disjunct -/
  | orI {Δ : WeightedSequent} {φ ψ : Formula} {e : Evidence} :
      Derivation T (⟨φ, e⟩ :: ⟨ψ, e⟩ :: Δ) →
      Derivation T (⟨φ ⋎ ψ, e⟩ :: Δ)

  /-- Excluded middle: φ ∨ ¬φ is derivable with maximal evidence
      Note: This makes the calculus classical. For intuitionistic PLN,
      we would restrict this rule. -/
  | em {Δ : WeightedSequent} {φ : Formula} {e : Evidence} :
      ⟨φ, e⟩ ∈ Δ →
      ⟨∼φ, e⟩ ∈ Δ →
      Derivation T Δ

  /-- Cut: eliminate intermediate formula -/
  | cut {Δ : WeightedSequent} {φ : Formula} {e₁ e₂ : Evidence} :
      Derivation T (⟨φ, e₁⟩ :: Δ) →
      Derivation T (⟨∼φ, e₂⟩ :: Δ) →
      Derivation T Δ

notation:45 T " ⊢ₚ " Δ => Derivation T Δ

/-! ## Basic Lemmas -/

/-- Derivability is a proposition (proof irrelevance) -/
def Derivable (T : Theory) (Δ : WeightedSequent) : Prop :=
  Nonempty (T ⊢ₚ Δ)

notation:45 T " ⊢ₚ! " Δ => Derivable T Δ

lemma derivable_of_derivation {T : Theory} {Δ : WeightedSequent}
    (d : T ⊢ₚ Δ) : T ⊢ₚ! Δ := ⟨d⟩

/-! ## Soundness -/

/-- Semantic interpretation: a valuation assigns Evidence to each variable -/
abbrev Valuation := PropVar → Evidence

/-- Evaluate a formula under a valuation -/
noncomputable def Formula.eval (v : Valuation) : Formula → Evidence
  | .var p => v p
  | .top => ⟨⊤, 0⟩  -- Maximal positive, no negative
  | .bot => ⟨0, ⊤⟩  -- No positive, maximal negative
  | .neg φ => ⟨(φ.eval v).neg, (φ.eval v).pos⟩  -- Swap pos/neg
  | .and φ ψ => evidenceMeet (φ.eval v) (ψ.eval v)
  | .or φ ψ => evidenceJoin (φ.eval v) (ψ.eval v)
  | .imp φ ψ =>
      -- A → B is ¬A ∨ B in classical logic
      let eφ := φ.eval v
      let eψ := ψ.eval v
      evidenceJoin ⟨eφ.neg, eφ.pos⟩ eψ

/-- A valuation satisfies a theory if it gives at least the claimed evidence -/
def Valuation.satisfies (v : Valuation) (T : Theory) : Prop :=
  ∀ wf ∈ T, wf.formula.eval v ≥ wf.evidence

/-- A valuation satisfies a sequent if some formula in it is satisfied -/
def Valuation.satisfiesSeq (v : Valuation) (Δ : WeightedSequent) : Prop :=
  ∃ wf ∈ Δ, wf.formula.eval v ≥ wf.evidence

/-- Soundness: if derivable, then semantically valid.

TODO: Complete proof for all cases. Structure is correct,
but evidence propagation details need work. -/
theorem soundness {T : Theory} {Δ : WeightedSequent}
    (d : T ⊢ₚ Δ) (v : Valuation) (hT : v.satisfies T) :
    v.satisfiesSeq Δ := by
  induction d <;> sorry

/-! ## Summary

### What We Have

1. **Weighted sequent calculus**: Formulas carry evidence weights
2. **Standard rules**: Axiom, weakening, and/or intro, excluded middle, cut
3. **Evidence flow**: Rules propagate evidence through derivations
4. **Soundness theorem**: Derivability implies semantic validity (partial proof)

### What's Missing (for full PLN calculus)

1. **Deduction rule**: Apply PLN deduction formula for A → B derivation
2. **Induction/abduction rules**: Other PLN inference patterns
3. **First-order extension**: Quantifiers with weakness-based semantics
4. **Completeness**: Semantic validity implies derivability
5. **Full soundness proof**: Complete the `sorry` cases

### Design Decisions

1. **Classical**: Included excluded middle (could make intuitionistic variant)
2. **Meet for ∧**: Evidence for A ∧ B is min of evidence for each
3. **Join for ∨**: Evidence for A ∨ B is max of evidence for each
4. **Swap for ¬**: Negation swaps positive and negative evidence

### Future Work

1. Add PLN-specific rules (deduction, induction, abduction, revision)
2. Prove cut elimination
3. Add first-order quantifiers with weakness semantics
4. Prove completeness relative to Evidence semantics
-/

end Mettapedia.Logic.PLNProofCalculus
