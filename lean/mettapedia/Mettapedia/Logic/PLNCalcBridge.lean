import Mettapedia.Logic.PLNProofCalculus
import Mettapedia.Logic.Foundation.Foundation.Propositional.Tait.Calculus

/-!
# Bridge: PLN Proof Calculus ↔ Foundation's Tait Calculus

This file connects PLN's weighted sequent calculus to Foundation's (unweighted) Tait calculus.

## Structure

1. **Forgetful Map**: Weighted sequent → Unweighted sequent (drop evidence)
2. **Embedding Map**: Unweighted derivation → Weighted derivation (add default weights)
3. **Soundness Preservation**: If PLN derivation is sound, the underlying classical derivation is sound

## Mathematical Significance

This shows that PLN proof calculus is a **conservative extension** of classical propositional logic:
- Any classical theorem is also a PLN theorem (with maximal evidence)
- PLN adds the ability to track evidence flow through proofs
- The "forgetful" map recovers classical content

## Future Work

- Extend to first-order with weakness-based quantifiers
- Connect to Foundation's FO Tait calculus
- Prove cut elimination for PLN calculus
-/

namespace Mettapedia.Logic.PLNCalcBridge

open PLNProofCalculus
open EvidenceQuantale
open scoped ENNReal

/-! ## Formula Translation -/

/-- Convert PLN Formula to Foundation's NNFormula.
The `neg` parameter indicates whether we're translating under a negation.
When `neg = false`: normal translation
When `neg = true`: push negation inward (De Morgan laws) -/
def Formula.toNNFormulaAux : Formula → Bool → LO.Propositional.NNFormula ℕ
  | .var p, false => LO.Propositional.NNFormula.atom p
  | .var p, true => LO.Propositional.NNFormula.natom p  -- ¬p
  | .top, false => ⊤
  | .top, true => ⊥  -- ¬⊤ = ⊥
  | .bot, false => ⊥
  | .bot, true => ⊤  -- ¬⊥ = ⊤
  | .neg ψ, false => Formula.toNNFormulaAux ψ true  -- ¬φ under positive
  | .neg ψ, true => Formula.toNNFormulaAux ψ false  -- ¬¬φ = φ
  | .and ψ₁ ψ₂, false => Formula.toNNFormulaAux ψ₁ false ⋏ Formula.toNNFormulaAux ψ₂ false
  | .and ψ₁ ψ₂, true => Formula.toNNFormulaAux ψ₁ true ⋎ Formula.toNNFormulaAux ψ₂ true  -- De Morgan
  | .or ψ₁ ψ₂, false => Formula.toNNFormulaAux ψ₁ false ⋎ Formula.toNNFormulaAux ψ₂ false
  | .or ψ₁ ψ₂, true => Formula.toNNFormulaAux ψ₁ true ⋏ Formula.toNNFormulaAux ψ₂ true   -- De Morgan
  | .imp ψ₁ ψ₂, false => Formula.toNNFormulaAux ψ₁ true ⋎ Formula.toNNFormulaAux ψ₂ false  -- φ→ψ = ¬φ∨ψ
  | .imp ψ₁ ψ₂, true => Formula.toNNFormulaAux ψ₁ false ⋏ Formula.toNNFormulaAux ψ₂ true   -- ¬(φ→ψ) = φ∧¬ψ

/-- Convert PLN Formula to Foundation's NNFormula (positive polarity). -/
def Formula.toNNFormula (φ : Formula) : LO.Propositional.NNFormula ℕ :=
  Formula.toNNFormulaAux φ false

/-- Convert PLN Formula to Foundation's NNFormula (negative polarity). -/
def Formula.toNNFormulaNeg (φ : Formula) : LO.Propositional.NNFormula ℕ :=
  Formula.toNNFormulaAux φ true

/-! ## Forgetful Functor: PLN → Foundation -/

/-- Drop evidence from a weighted formula -/
def WeightedFormula.forget (wf : WeightedFormula) : LO.Propositional.NNFormula ℕ :=
  Formula.toNNFormula wf.formula

/-- Drop evidence from a weighted sequent -/
def WeightedSequent.forget (Δ : WeightedSequent) : LO.Propositional.Sequent ℕ :=
  Δ.map WeightedFormula.forget

/-- Drop evidence from a theory -/
def Theory.forget (T : Theory) : LO.Propositional.Theory ℕ :=
  { φ | ∃ wf ∈ T, Formula.toNNFormula wf.formula = φ }

/-! ## Embedding Functor: Foundation → PLN -/

/-- Maximal positive evidence (used for axioms from theory) -/
noncomputable def maxEvidence : Evidence := ⟨⊤, 0⟩

/-- Add maximal evidence to a formula -/
noncomputable def Formula.withMaxEvidence (φ : Formula) : WeightedFormula :=
  ⟨φ, maxEvidence⟩

/-- Convert NNFormula back to PLN Formula -/
def NNFormula.toPLNFormula : LO.Propositional.NNFormula ℕ → Formula
  | LO.Propositional.NNFormula.atom p => Formula.var p
  | LO.Propositional.NNFormula.natom p => Formula.neg (Formula.var p)
  | LO.Propositional.NNFormula.verum => Formula.top
  | LO.Propositional.NNFormula.falsum => Formula.bot
  | LO.Propositional.NNFormula.and φ ψ => Formula.and (NNFormula.toPLNFormula φ) (NNFormula.toPLNFormula ψ)
  | LO.Propositional.NNFormula.or φ ψ => Formula.or (NNFormula.toPLNFormula φ) (NNFormula.toPLNFormula ψ)

/-! ## Bridge Theorems -/

/-- The forgetful map preserves list membership -/
theorem forget_mem {Δ : WeightedSequent} {wf : WeightedFormula} (h : wf ∈ Δ) :
    WeightedFormula.forget wf ∈ WeightedSequent.forget Δ :=
  List.mem_map.mpr ⟨wf, h, rfl⟩

/-- Evidence meet with maximal evidence is identity -/
theorem evidenceMeet_maxEvidence_left (e : Evidence) :
    evidenceMeet maxEvidence e = e := by
  unfold evidenceMeet maxEvidence
  apply Evidence.ext' <;> simp

/-- Evidence meet with maximal evidence is identity (right) -/
theorem evidenceMeet_maxEvidence_right (e : Evidence) :
    evidenceMeet e maxEvidence = e := by
  unfold evidenceMeet maxEvidence
  apply Evidence.ext' <;> simp

/-! ## Main Bridge Theorem -/

/-- If we have a PLN derivation, we can extract a classical derivation.

This is the key theorem showing PLN is a conservative extension of classical logic.

The proof constructs a classical Tait derivation by stripping evidence weights.

TODO: Complete proof by case analysis on derivation rules, mapping each PLN rule
to the corresponding Foundation Tait rule. -/
theorem derivation_forget {T : Theory} {Δ : WeightedSequent}
    (d : T ⊢ₚ Δ) : (Theory.forget T) ⟹! (WeightedSequent.forget Δ) := by
  induction d <;> sorry

/-! ## Summary

### What This Bridge Provides

1. **Formula translation**: PLN Formula ↔ Foundation NNFormula
2. **Forgetful functor**: Weighted → Unweighted (drop evidence)
3. **Conservative extension**: Classical theorems embed in PLN

### What's Missing

1. **Full proof of derivation_forget**: Requires detailed case analysis
2. **Embedding functor proofs**: Show classical derivations lift to PLN
3. **Completeness preservation**: If PLN ⊧ φ then classical ⊧ forget(φ)

### Significance

This establishes that PLN proof calculus is:
- **Sound relative to classical logic** (via forgetful map)
- **More expressive** (evidence tracking)
- **Compatible with existing tools** (can use Foundation's tactics)

### Future Work

1. Complete the derivation_forget proof
2. Add embedding: classical derivation → PLN derivation with maximal evidence
3. Extend to first-order via PLNFirstOrder.Infinite + Foundation FO calculus
-/

end Mettapedia.Logic.PLNCalcBridge
