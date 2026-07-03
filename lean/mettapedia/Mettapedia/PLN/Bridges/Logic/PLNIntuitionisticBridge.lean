/-
# PLN BinaryEvidence as a Model of Intuitionistic Propositional Logic

This file establishes that PLN BinaryEvidence forms a proper Heyting-valued
model of intuitionistic propositional logic (IPL), with soundness inherited
from the Foundation library and a separate completeness theorem for the class
of all Heyting models.

## Main Results

1. `Nontrivial BinaryEvidence` - BinaryEvidence has distinct bottom and top
2. `PLNSemantics` - HeytingSemantics instance using BinaryEvidence
3. `pln_soundness` - IPL derivability is valid in BinaryEvidence
4. `pln_completeness_from_all_models` - Foundation completeness for all
   Heyting models, not a BinaryEvidence-only completeness theorem

## Mathematical Content

BinaryEvidence has an `Order.Frame` instance (complete Heyting algebra), which
makes it a sound model for IPL. Completeness is used in its standard
all-Heyting-model form; a formula valid in BinaryEvidence alone need not be
claimed IPL-provable here.

## References

- Foundation library: Propositional/Heyting/Semantics.lean
- Troelstra & van Dalen, "Constructivism in Mathematics" Vol. 1
-/

import Mettapedia.PLN.Evidence.EvidenceQuantale
import Foundation.Propositional.Heyting.Semantics
import Foundation.Propositional.Kripke.Logic.Int
import Foundation.Propositional.Kripke.AxiomDummett
import Foundation.Propositional.Hilbert.Standard.Glivenko

namespace Mettapedia.PLN.Bridges.Logic.PLNIntuitionisticBridge

open scoped ENNReal
open Mettapedia.PLN.Evidence.EvidenceQuantale
open LO.Propositional
open Kripke

/-! ## Nontriviality

BinaryEvidence has distinct bottom and top elements.
-/

/-- BinaryEvidence is nontrivial: ⊥ ≠ ⊤ -/
instance : Nontrivial BinaryEvidence where
  exists_pair_ne := by
    use ⟨0, 0⟩, ⟨⊤, ⊤⟩
    intro h
    have hp : (0 : ℝ≥0∞) = ⊤ := congrArg BinaryEvidence.pos h
    exact ENNReal.zero_ne_top hp

/-- Explicit witness that ⊥ ≠ ⊤ in BinaryEvidence -/
theorem evidence_bot_ne_top : (⊥ : BinaryEvidence) ≠ ⊤ := by
  intro h
  have hp : (0 : ℝ≥0∞) = ⊤ := congrArg BinaryEvidence.pos h
  exact ENNReal.zero_ne_top hp

/-! ## HeytingSemantics Instance

We instantiate Foundation's HeytingSemantics structure with BinaryEvidence as
the algebra.  This gives a direct soundness route for formulas provable in the
relevant Hilbert systems.
-/

/-- Propositional variables (using natural numbers) -/
abbrev PropVar := ℕ

/-- PLN BinaryEvidence provides a HeytingSemantics for propositional logic.

Given a valuation `v : PropVar → BinaryEvidence` assigning evidence to atomic propositions,
this defines a complete interpretation of all propositional formulas in BinaryEvidence.

The interpretation is:
- Atomic `p` ↦ `v p`
- `⊥` ↦ `⊥` (zero evidence)
- `φ ⋏ ψ` ↦ `⟦φ⟧ ⊓ ⟦ψ⟧` (evidence inf)
- `φ ⋎ ψ` ↦ `⟦φ⟧ ⊔ ⟦ψ⟧` (evidence sup)
- `φ ➝ ψ` ↦ `⟦φ⟧ ⇨ ⟦ψ⟧` (Heyting implication)
-/
noncomputable def PLNSemantics (v : PropVar → BinaryEvidence) : HeytingSemantics PropVar where
  Algebra := BinaryEvidence
  valAtom := v
  heyting := inferInstance  -- From Order.Frame
  nontrivial := inferInstance  -- Just proved above

/-! ## Direct Formula Interpretation

For convenience, we also provide direct access to formula interpretation.
-/

/-- Interpret a propositional formula in BinaryEvidence -/
noncomputable def interpret (v : PropVar → BinaryEvidence) (φ : Formula PropVar) : BinaryEvidence :=
  φ.hVal v

/-- A formula is valid under valuation v if it interprets to ⊤ -/
def valid (v : PropVar → BinaryEvidence) (φ : Formula PropVar) : Prop :=
  interpret v φ = ⊤

/-- A formula is universally valid if valid under all valuations -/
def universallyValid (φ : Formula PropVar) : Prop :=
  ∀ v : PropVar → BinaryEvidence, valid v φ

/-! ## Soundness via Foundation

Foundation's HeytingSemantics provides a soundness theorem for Hilbert-style
intuitionistic propositional calculus. Since PLNSemantics is a HeytingSemantics
instance, we inherit soundness.
-/

/-- Soundness: If φ is provable in intuitionistic propositional logic,
    then φ is valid in all PLN BinaryEvidence models. -/
theorem pln_sound {Ax : LO.Propositional.Axiom PropVar} {φ : Formula PropVar}
    (d : Hilbert.Standard Ax ⊢ φ) :
    HeytingSemantics.mod (Hilbert.Standard Ax) ⊧ φ :=
  HeytingSemantics.sound d

/-! ## Key Theorems about BinaryEvidence Interpretation

The following theorems follow from BinaryEvidence being a Heyting algebra.
-/

/-- K axiom is valid: φ → (ψ → φ) -/
theorem evidence_valid_K (v : PropVar → BinaryEvidence) (p q : PropVar) :
    valid v ((#p) ➝ ((#q) ➝ (#p))) := by
  simp only [valid, interpret, Formula.hVal]
  rw [eq_top_iff, le_himp_iff, le_himp_iff, top_inf_eq]
  -- Goal: v p ⊓ v q ≤ v p
  exact inf_le_left

/-- Ex falso quodlibet: ⊥ → φ -/
theorem evidence_valid_efq (v : PropVar → BinaryEvidence) (φ : Formula PropVar) :
    valid v (⊥ ➝ φ) := by
  simp only [valid, interpret, Formula.hVal]
  rw [eq_top_iff, le_himp_iff]
  exact bot_le

/-- Modus ponens preserves validity -/
theorem evidence_modus_ponens (v : PropVar → BinaryEvidence) (φ ψ : Formula PropVar)
    (hφ : valid v φ) (hφψ : valid v (φ ➝ ψ)) : valid v ψ := by
  simp only [valid, interpret] at *
  simp only [Formula.hVal_imp] at hφψ
  rw [eq_top_iff] at hφψ ⊢
  have h : φ.hVal v ≤ ψ.hVal v := by
    rw [← inf_top_eq (φ.hVal v), inf_comm]
    exact le_himp_iff.mp hφψ
  rw [← hφ]; exact h

/-- Conjunction is sound -/
theorem evidence_valid_and_intro (v : PropVar → BinaryEvidence) (φ ψ : Formula PropVar)
    (hφ : valid v φ) (hψ : valid v ψ) : valid v (φ ⋏ ψ) := by
  simp only [valid, interpret] at *
  simp only [Formula.hVal_and, hφ, hψ, inf_top_eq]

/-- Conjunction elimination -/
theorem evidence_valid_and_elim_left (v : PropVar → BinaryEvidence) (φ ψ : Formula PropVar)
    (h : valid v (φ ⋏ ψ)) : valid v φ := by
  simp only [valid, interpret] at *
  simp only [Formula.hVal_and] at h
  rw [eq_top_iff] at h ⊢
  exact le_trans h inf_le_left

/-- Disjunction introduction left -/
theorem evidence_valid_or_intro_left (v : PropVar → BinaryEvidence) (φ ψ : Formula PropVar) :
    valid v (φ ➝ (φ ⋎ ψ)) := by
  simp only [valid, interpret]
  simp only [Formula.hVal_imp, Formula.hVal_or]
  rw [eq_top_iff, le_himp_iff, top_inf_eq]
  exact @le_sup_left BinaryEvidence _ (φ.hVal v) (ψ.hVal v)

/-! ## Classical Logic Does NOT Hold in PLN BinaryEvidence

BinaryEvidence is genuinely intuitionistic - the law of excluded middle fails.
This is because BinaryEvidence has elements that are neither ⊥ nor ⊤.
-/

/-- BinaryEvidence is NOT a Boolean algebra - LEM fails.

Specifically, there exist evidence values `e` where `e ⊔ eᶜ ≠ ⊤`.
For example, `⟨1, 0⟩ ⊔ ⟨1, 0⟩ᶜ = ⟨1, 0⟩ ⊔ ⟨0, ⊤⟩ = ⟨1, ⊤⟩ ≠ ⟨⊤, ⊤⟩`.
-/
theorem evidence_not_boolean : ¬∀ e : BinaryEvidence, e ⊔ eᶜ = ⊤ := by
  intro h
  -- Consider e = ⟨1, 0⟩ (weak positive evidence)
  let e : BinaryEvidence := ⟨1, 0⟩
  have hlem := h e
  -- From hlem : e ⊔ eᶜ = ⊤, we get (e ⊔ eᶜ).pos = ⊤
  have hpos_top : (e ⊔ eᶜ).pos = ⊤ := by rw [hlem]; rfl
  -- Compute eᶜ.pos using the himp definition
  -- himp ⟨1, 0⟩ ⟨0, 0⟩ has pos = if 1 ≤ 0 then ⊤ else 0 = 0 (since 1 > 0)
  have hecompl_pos : eᶜ.pos = 0 := by
    -- eᶜ = himp e ⊥
    -- By definition: himp ⟨1, 0⟩ ⟨0, 0⟩ = ⟨if 1 ≤ 0 then ⊤ else 0, if 0 ≤ 0 then ⊤ else 0⟩
    -- Since 1 > 0, the first component is 0
    show (himp e ⊥).pos = 0
    -- Directly compute
    have hone_not_le_zero : ¬((1 : ℝ≥0∞) ≤ 0) := by
      intro h
      have : (1 : ℝ≥0∞) = 0 := le_antisymm h bot_le
      exact one_ne_zero this
    -- (⊥ : BinaryEvidence).pos = 0
    have hbot_pos : (⊥ : BinaryEvidence).pos = 0 := rfl
    have he_pos : e.pos = 1 := rfl
    -- himp e ⊥ = ⟨if e.pos ≤ 0 then ⊤ else 0, if e.neg ≤ 0 then ⊤ else 0⟩
    have heq : (himp e ⊥).pos = if e.pos ≤ (⊥ : BinaryEvidence).pos then ⊤ else (⊥ : BinaryEvidence).pos := rfl
    rw [heq, hbot_pos, he_pos]
    -- Now goal is: (if 1 ≤ 0 then ⊤ else 0) = 0
    rw [if_neg hone_not_le_zero]
  -- e ⊔ eᶜ has pos component = max(e.pos, eᶜ.pos) = max(1, 0) = 1
  have hsup_pos : (e ⊔ eᶜ).pos = max e.pos eᶜ.pos := rfl
  have he_pos : e.pos = (1 : ℝ≥0∞) := rfl
  rw [hsup_pos, he_pos, hecompl_pos] at hpos_top
  -- max(1, 0) = 1 since 0 ≤ 1
  have hmax : max (1 : ℝ≥0∞) 0 = 1 := by simp
  rw [hmax] at hpos_top
  exact ENNReal.one_ne_top hpos_top

/-! ## Completeness via Foundation Models

Foundation's completeness theorem states: if φ is valid in all Heyting algebra models
satisfying the axiom set, then φ is provable. We show that PLNSemantics models are
included in the relevant model class.

This is not a BinaryEvidence-only completeness theorem.  The Foundation library
uses the Lindenbaum algebra for completeness; the theorem below exposes that
all-model consequence route while the BinaryEvidence-specific direction remains
only soundness.

Note: `Int.axioms` is defined as `{Axioms.EFQ (.atom 0)}` - the minimal intuitionistic axiom.
-/

/-- PLNSemantics validates EFQ formula instances: ⊥ → φ.
    This is the key axiom for intuitionistic logic. -/
theorem pln_validates_efq (v : PropVar → BinaryEvidence) (φ : Formula PropVar) :
    (PLNSemantics v) ⊧ (⊥ ➝ φ) := by
  simp only [HeytingSemantics.val_def']
  simp only [HeytingSemantics.hVal, Formula.hVal_imp, Formula.hVal_falsum]
  rw [eq_top_iff, le_himp_iff]
  exact bot_le

/-- PLNSemantics validates all tautologies of intuitionistic propositional logic.
    This follows from BinaryEvidence being a Heyting algebra. -/
theorem pln_validates_int_tautologies (v : PropVar → BinaryEvidence) (φ : Formula PropVar)
    (h : ∀ (H : HeytingSemantics.{0, 0} PropVar), H ⊧ φ) : (PLNSemantics v) ⊧ φ :=
  h (PLNSemantics v)

/-- For any valuation v, PLNSemantics v satisfies all Int.axioms instances.
    This is needed to apply Foundation's completeness theorem.

    Int.axioms = {Axioms.EFQ (.atom 0)} and its instances are all formulas
    of the form ⊥ → ψ (obtained by substituting into EFQ). -/
theorem pln_in_int_models (v : PropVar → BinaryEvidence) :
    (PLNSemantics v) ⊧* Int.axioms.instances := by
  -- Int.axioms instances come from substitution into EFQ formula
  constructor
  intro φ hφ
  simp only [Axiom.instances, Set.mem_setOf_eq] at hφ
  obtain ⟨ψ, hψ_mem, s, hs⟩ := hφ
  -- ψ ∈ Int.axioms means ψ = Axioms.EFQ (.atom 0)
  simp only [Int.axioms, Set.mem_singleton_iff] at hψ_mem
  rw [hψ_mem] at hs
  -- After substitution, φ = ⊥ → (s 0)
  simp only [Formula.subst] at hs
  rw [hs]
  -- Now prove ⊥ → (s 0) is valid
  simp only [HeytingSemantics.val_def']
  simp only [HeytingSemantics.hVal, Formula.hVal_imp, Formula.hVal_falsum]
  rw [eq_top_iff, le_himp_iff]
  exact bot_le

/-- PLNSemantics v is in the model class mod(Int.axioms).
    This means it validates all theorems of intuitionistic propositional logic. -/
theorem pln_in_mod_int (v : PropVar → BinaryEvidence) :
    (PLNSemantics v) ∈ HeytingSemantics.mod Int.axioms :=
  pln_in_int_models v

/-! ## Soundness and Completeness

Foundation provides both soundness and completeness for intuitionistic propositional
logic via the Lindenbaum algebra construction.
-/

/-- Soundness: provable in IPL implies valid in all BinaryEvidence valuations.

This follows directly: every Hilbert-style IPL derivation is valid in any
Heyting algebra model that validates the EFQ axiom. PLNSemantics v is such a model.

The proof uses induction on the Hilbert derivation, showing each axiom and rule
preserves validity in BinaryEvidence (which is a Heyting algebra). -/
theorem pln_soundness {φ : Formula PropVar}
    (h : Hilbert.Standard Int.axioms ⊢ φ) :
    ∀ v : PropVar → BinaryEvidence, (PLNSemantics v) ⊧ φ := by
  intro v
  -- Use induction on the Hilbert-style derivation
  induction h with
  | @axm ψ s hψ =>
    -- Axiom instances: ψ ∈ Int.axioms means ψ = Axioms.EFQ (.atom 0)
    -- After substitution, we get ⊥ → (s 0)
    simp only [HeytingSemantics.val_def']
    simp only [Int.axioms, Set.mem_singleton_iff] at hψ
    rw [hψ]
    simp only [Formula.subst, HeytingSemantics.hVal, Formula.hVal_imp, Formula.hVal_falsum]
    rw [eq_top_iff, le_himp_iff]
    exact bot_le
  | @mdp _ ψ _ _ ihpq ihp =>
    -- Modus ponens: if φ → ψ and φ are valid, then ψ is valid
    simp only [HeytingSemantics.val_def'] at *
    simp only [HeytingSemantics.hVal, Formula.hVal_imp] at ihpq
    rw [eq_top_iff, le_himp_iff] at ihpq
    rw [eq_top_iff]
    simp only [HeytingSemantics.hVal] at ihp
    rw [ihp, top_inf_eq] at ihpq
    exact ihpq
  | verum =>
    simp only [HeytingSemantics.val_def', HeytingSemantics.hVal_verum]
  | implyS =>
    -- S axiom: φ → ψ → φ
    simp only [HeytingSemantics.val_def', HeytingSemantics.hVal, Formula.hVal_imp]
    rw [eq_top_iff, le_himp_iff, le_himp_iff, top_inf_eq]
    exact inf_le_left
  | implyK =>
    -- K axiom: (φ → ψ → χ) → (φ → ψ) → φ → χ
    simp only [HeytingSemantics.val_def', HeytingSemantics.hVal, Formula.hVal_imp]
    rw [eq_top_iff, le_himp_iff, le_himp_iff, le_himp_iff, top_inf_eq]
    -- Goal: (a ⇨ b ⇨ c) ⊓ (a ⇨ b) ⊓ a ≤ c
    exact himp_himp_inf_himp_inf_le _ _ _
  | andElimL =>
    simp only [HeytingSemantics.val_def', HeytingSemantics.hVal, Formula.hVal_imp, Formula.hVal_and]
    rw [eq_top_iff, le_himp_iff, top_inf_eq]
    exact inf_le_left
  | andElimR =>
    simp only [HeytingSemantics.val_def', HeytingSemantics.hVal, Formula.hVal_imp, Formula.hVal_and]
    rw [eq_top_iff, le_himp_iff, top_inf_eq]
    exact inf_le_right
  | andIntro =>
    simp only [HeytingSemantics.val_def', HeytingSemantics.hVal, Formula.hVal_imp, Formula.hVal_and]
    rw [eq_top_iff, le_himp_iff, le_himp_iff, top_inf_eq, inf_comm]
  | orIntroL =>
    simp only [HeytingSemantics.val_def', HeytingSemantics.hVal, Formula.hVal_imp, Formula.hVal_or]
    rw [eq_top_iff, le_himp_iff, top_inf_eq]
    exact le_sup_left
  | orIntroR =>
    simp only [HeytingSemantics.val_def', HeytingSemantics.hVal, Formula.hVal_imp, Formula.hVal_or]
    rw [eq_top_iff, le_himp_iff, top_inf_eq]
    exact le_sup_right
  | orElim =>
    -- (φ → χ) → (ψ → χ) → (φ ∨ ψ → χ)
    simp only [HeytingSemantics.val_def', HeytingSemantics.hVal, Formula.hVal_imp, Formula.hVal_or]
    rw [eq_top_iff, le_himp_iff, le_himp_iff, le_himp_iff, top_inf_eq]
    -- Goal: (a ⇨ c) ⊓ (b ⇨ c) ⊓ (a ⊔ b) ≤ c
    exact himp_inf_himp_inf_sup_le _ _ _

/-- Completeness relative to the class of all HeytingSemantics models.

If φ is valid in ALL HeytingSemantics models satisfying Int.axioms
(including PLNSemantics for all v), then φ is provable in IPL.

This follows from Foundation's completeness theorem via the Lindenbaum algebra.
-/
theorem pln_completeness_from_all_models {φ : Formula PropVar}
    (h : ∀ (H : HeytingSemantics.{0, 0} PropVar), H ⊧* Int.axioms.instances → H ⊧ φ) :
    Hilbert.Standard Int.axioms ⊢ φ := by
  apply HeytingSemantics.complete
  exact HeytingSemantics.mod_models_iff.mpr h

/-! ### BinaryEvidence Validates Dummett's Axiom (Linearity)

BinaryEvidence is NOT just a model of IPL - it validates MORE than IPL.
Specifically, it validates Dummett's axiom: (p → q) ∨ (q → p).

This is because ℝ≥0∞ is a **linear order** (chain), so for any two elements,
one is ≤ the other. This makes the Heyting implication in each component
satisfy linearity.

**Consequence**: PLN BinaryEvidence is a sound semantic model for
**Gödel-Dummett logic (LC)**, not merely IPL.

The hierarchy is: IPL ⊂ LC ⊂ Classical Logic
- IPL: intuitionistic propositional logic
- LC: IPL + Dummett's axiom (p → q) ∨ (q → p)
- Classical: LC + LEM (p ∨ ¬p)

Every LC theorem is valid in BinaryEvidence, but classical logic is not valid
there: excluded middle fails.
-/

/-- In ℝ≥0∞ (a linear order), the Heyting implication satisfies:
    (a ⇨ b) ⊔ (b ⇨ a) = ⊤ for all a, b.
    This is because either a ≤ b or b ≤ a (or both). -/
theorem ennreal_himp_linear (a b : ℝ≥0∞) :
    (if a ≤ b then ⊤ else b) ⊔ (if b ≤ a then ⊤ else a) = ⊤ := by
  -- ℝ≥0∞ is a linear order, so either a ≤ b or b ≤ a
  rcases le_total a b with hab | hba
  · -- Case a ≤ b: first term is ⊤
    simp [hab]
  · -- Case b ≤ a: second term is ⊤
    simp [hba]

/-- BinaryEvidence satisfies Dummett's axiom (linearity): (e₁ ⇨ e₂) ⊔ (e₂ ⇨ e₁) = ⊤
    for all evidence values e₁, e₂.

    This follows from ℝ≥0∞ being a linear order in each component. -/
theorem evidence_dummett (e₁ e₂ : BinaryEvidence) : (e₁ ⇨ e₂) ⊔ (e₂ ⇨ e₁) = ⊤ := by
  -- Work with the explicit structure using BinaryEvidence.ext'
  apply BinaryEvidence.ext'
  · -- pos component: show (sup (himp e₁ e₂) (himp e₂ e₁)).pos = ⊤
    show max (himp e₁ e₂).pos (himp e₂ e₁).pos = ⊤
    simp only [himp]
    exact ennreal_himp_linear e₁.pos e₂.pos
  · -- neg component: show (sup (himp e₁ e₂) (himp e₂ e₁)).neg = ⊤
    show max (himp e₁ e₂).neg (himp e₂ e₁).neg = ⊤
    simp only [himp]
    exact ennreal_himp_linear e₁.neg e₂.neg

/-- Dummett's axiom is valid in all PLN BinaryEvidence valuations.

    This shows PLN models Gödel-Dummett logic (LC), not just IPL!
    The formula (p → q) ∨ (q → p) is NOT provable in IPL, but IS valid in BinaryEvidence. -/
theorem evidence_valid_dummett (v : PropVar → BinaryEvidence) (p q : PropVar) :
    valid v (((#p) ➝ (#q)) ⋎ ((#q) ➝ (#p))) := by
  simp only [valid, interpret, Formula.hVal]
  -- Goal: (v p ⇨ v q) ⊔ (v q ⇨ v p) = ⊤
  exact evidence_dummett (v p) (v q)

/-- Dummett's axiom is valid for arbitrary formula instances in BinaryEvidence. -/
theorem evidence_valid_dummett_formula (v : PropVar → BinaryEvidence)
    (φ ψ : Formula PropVar) :
    valid v ((φ ➝ ψ) ⋎ (ψ ➝ φ)) := by
  simp only [valid, interpret, Formula.hVal]
  exact evidence_dummett (φ.hVal v) (ψ.hVal v)

/-- Dummett's axiom is NOT provable in IPL.

    **Standard Result (Kripke Semantics)**:
    IPL is sound and complete for all Kripke frames (FrameClass.Int = FrameClass.all).
    The 4-world frame with root 0, worlds 1, 2, 3 where (1,2) and (2,1) are NOT related
    refutes Dummett: when we force the frame to validate Dummett, we get piecewise
    strong connectedness, which this frame violates.

    **Countermodel Structure** (from Foundation/Propositional/Kripke/Logic/LC.lean):
    - World = Fin 4
    - Rel x y := ¬(x = 1 ∧ y = 2) ∧ ¬(x = 2 ∧ y = 1) ∧ (x ≤ y)
    - This is a partial order but NOT piecewise strongly connected
    - Therefore Dummett fails at the root

    **Mathematical Insight**:
    `isPiecewiseStronglyConnected_of_validate_axiomDummett` shows that any frame
    validating Dummett must be piecewise strongly connected. By contrapositive,
    any frame that's NOT piecewise strongly connected provides a countermodel. -/
theorem dummett_not_provable_in_ipl :
    ¬(Hilbert.Standard Int.axioms ⊢ (((#0) ➝ (#1)) ⋎ ((#1) ➝ (#0)) : Formula PropVar)) := by
  -- Use the Kripke soundness theorem: if provable, then valid in all frames
  -- We construct a frame where Dummett fails
  apply LO.Sound.not_provable_of_countermodel (𝓜 := Kripke.FrameClass.Int)
  apply Kripke.not_validOnFrameClass_of_exists_frame
  -- Construct the 4-world countermodel frame (from LC.lean)
  use {
    World := Fin 4
    Rel := λ x y => ¬(x = 1 ∧ y = 2) ∧ ¬(x = 2 ∧ y = 1) ∧ (x ≤ y)
    rel_partial_order := {
      refl := by omega
      trans := by omega
      antisymm := by omega
    }
  }
  constructor
  · -- FrameClass.Int = FrameClass.all, so any frame is in this class
    trivial
  · -- Show Dummett is NOT valid on this frame
    -- By contrapositive of isPiecewiseStronglyConnected_of_validate_axiomDummett:
    -- if the frame is NOT piecewise strongly connected, then Dummett fails
    apply not_imp_not.mpr isPiecewiseStronglyConnected_of_validate_axiomDummett
    -- Show the frame is NOT piecewise strongly connected
    by_contra hC
    -- hC : IsPiecewiseStronglyConnected (the frame's relation)
    -- At nodes 0, 1, 2: 0 ≺ 1 and 0 ≺ 2, but neither 1 ≺ 2 nor 2 ≺ 1
    simpa using @hC.ps_connected 0 1 2

/-! ### BinaryEvidence is Strictly Stronger than IPL

We have proven:
1. `evidence_valid_dummett`: (p → q) ∨ (q → p) is valid in ALL BinaryEvidence valuations
2. `dummett_not_provable_in_ipl`: (p → q) ∨ (q → p) is NOT provable in IPL

Therefore: ∃φ. (∀v. PLNSemantics v ⊧ φ) ∧ ¬(IPL ⊢ φ)

This means BinaryEvidence validates strictly MORE than IPL proves.
-/

/-! ### Diagonal Gödel-chain embedding

The diagonal embedding `d(x) = ⟨x, x⟩` shows that BinaryEvidence contains the
`ℝ≥0∞` Gödel chain as a Heyting subalgebra.  Thus a countervaluation in that
single chain reflects to a BinaryEvidence countervaluation by composing atom
values with `diagonal`, and `diagonal x = ⊤` exactly when `x = ⊤`.

What this does **not** by itself prove is the converse completeness statement
`BinaryEvidence ⊧ φ → LC ⊢ φ`.  The available HOL Gödel-Dummett completeness
surface is `provableLC_of_prelinearHeytingConsequence`, which quantifies over
all prelinear Heyting-valued models.  The missing, not-declared bridge is
`ennrealGodelUniversallyValid_implies_prelinearHeytingConsequence`: validity in
the `ℝ≥0∞` Gödel chain would have to imply consequence over all prelinear
Heyting models.  Until that theorem is available, the honest established result
is LC soundness plus the exact reduction
`universallyValid_iff_ennrealGodelUniversallyValid`: BinaryEvidence validity is
equivalent to validity in the single `ℝ≥0∞` Gödel chain.
-/

/-- The diagonal embedding: ℝ≥0∞ → BinaryEvidence -/
def diagonal (x : ℝ≥0∞) : BinaryEvidence := ⟨x, x⟩

/-- Diagonal preserves ⊥ -/
theorem diagonal_bot : diagonal 0 = (⊥ : BinaryEvidence) := rfl

/-- Diagonal preserves ⊤ -/
theorem diagonal_top : diagonal ⊤ = (⊤ : BinaryEvidence) := rfl

/-- Diagonal top-reflection: a diagonal BinaryEvidence value is top exactly
when its source chain value is top. -/
theorem diagonal_eq_top_iff {x : ℝ≥0∞} :
    diagonal x = (⊤ : BinaryEvidence) ↔ x = ⊤ := by
  constructor
  · intro h
    exact congrArg BinaryEvidence.pos h
  · intro hx
    rw [hx, diagonal_top]

/-- Non-top chain values remain non-top after diagonal embedding. -/
theorem diagonal_reflects_non_top {x : ℝ≥0∞} (hx : x ≠ ⊤) :
    diagonal x ≠ (⊤ : BinaryEvidence) := by
  intro h
  exact hx (diagonal_eq_top_iff.mp h)

/-- Diagonal preserves ≤ -/
theorem diagonal_le {x y : ℝ≥0∞} : x ≤ y ↔ diagonal x ≤ diagonal y := by
  simp [diagonal, BinaryEvidence.le_def]

/-- Diagonal preserves ⊓ (meet/and) -/
theorem diagonal_inf (x y : ℝ≥0∞) : diagonal (x ⊓ y) = diagonal x ⊓ diagonal y := by
  simp [diagonal]; apply BinaryEvidence.ext' <;> rfl

/-- Diagonal preserves ⊔ (join/or) -/
theorem diagonal_sup (x y : ℝ≥0∞) : diagonal (x ⊔ y) = diagonal x ⊔ diagonal y := by
  simp [diagonal]; apply BinaryEvidence.ext' <;> rfl

/-- Diagonal preserves Heyting implication (Gödel arrow) -/
theorem diagonal_himp (x y : ℝ≥0∞) :
    diagonal (if x ≤ y then ⊤ else y) = diagonal x ⇨ diagonal y := rfl

/-- The diagonal embedding is a Heyting-algebra homomorphism for meet, join,
and the Gödel arrow on `ℝ≥0∞`.  Together with `diagonal_eq_top_iff`, this is
the reflection part of the single-chain countermodel route; it is not the
all-prelinear LC completeness theorem by itself. -/
theorem diagonal_heyting_hom :
    ∀ x y : ℝ≥0∞,
      diagonal (x ⊓ y) = diagonal x ⊓ diagonal y ∧
      diagonal (x ⊔ y) = diagonal x ⊔ diagonal y ∧
      diagonal (if x ≤ y then ⊤ else y) = diagonal x ⇨ diagonal y :=
  fun x y => ⟨diagonal_inf x y, diagonal_sup x y, diagonal_himp x y⟩

/-! ### Explicit ENNReal Gödel-chain semantics -/

/-- Gödel implication on the single `ℝ≥0∞` chain. -/
noncomputable def ennrealGodelImp (x y : ℝ≥0∞) : ℝ≥0∞ :=
  if x ≤ y then ⊤ else y

/-- Formula evaluation in the single `ℝ≥0∞` Gödel chain. -/
noncomputable def ennrealGodelVal (v : PropVar → ℝ≥0∞) :
    Formula PropVar → ℝ≥0∞
  | .atom p => v p
  | .falsum => 0
  | .and φ ψ => ennrealGodelVal v φ ⊓ ennrealGodelVal v ψ
  | .or φ ψ => ennrealGodelVal v φ ⊔ ennrealGodelVal v ψ
  | .imp φ ψ => ennrealGodelImp (ennrealGodelVal v φ) (ennrealGodelVal v ψ)

/-- A formula is valid under an `ℝ≥0∞` Gödel-chain valuation. -/
def ennrealGodelValid (v : PropVar → ℝ≥0∞) (φ : Formula PropVar) : Prop :=
  ennrealGodelVal v φ = ⊤

/-- A formula is valid in the single `ℝ≥0∞` Gödel chain. -/
def ennrealGodelUniversallyValid (φ : Formula PropVar) : Prop :=
  ∀ v : PropVar → ℝ≥0∞, ennrealGodelValid v φ

/-- Diagonal valuations commute with formula evaluation. -/
theorem diagonal_ennrealGodelVal (v : PropVar → ℝ≥0∞) (φ : Formula PropVar) :
    diagonal (ennrealGodelVal v φ) = interpret (fun p => diagonal (v p)) φ := by
  induction φ with
  | hatom p => rfl
  | hfalsum => rfl
  | hand φ ψ ihφ ihψ =>
      simp only [ennrealGodelVal, interpret, Formula.hVal]
      have ihφ' : diagonal (ennrealGodelVal v φ) =
          Formula.hVal (fun p => diagonal (v p)) φ := by
        simpa [interpret] using ihφ
      have ihψ' : diagonal (ennrealGodelVal v ψ) =
          Formula.hVal (fun p => diagonal (v p)) ψ := by
        simpa [interpret] using ihψ
      rw [← ihφ', ← ihψ']
      exact diagonal_inf _ _
  | hor φ ψ ihφ ihψ =>
      simp only [ennrealGodelVal, interpret, Formula.hVal]
      have ihφ' : diagonal (ennrealGodelVal v φ) =
          Formula.hVal (fun p => diagonal (v p)) φ := by
        simpa [interpret] using ihφ
      have ihψ' : diagonal (ennrealGodelVal v ψ) =
          Formula.hVal (fun p => diagonal (v p)) ψ := by
        simpa [interpret] using ihψ
      rw [← ihφ', ← ihψ']
      exact diagonal_sup _ _
  | himp φ ψ ihφ ihψ =>
      simp only [ennrealGodelVal, ennrealGodelImp, interpret, Formula.hVal]
      have ihφ' : diagonal (ennrealGodelVal v φ) =
          Formula.hVal (fun p => diagonal (v p)) φ := by
        simpa [interpret] using ihφ
      have ihψ' : diagonal (ennrealGodelVal v ψ) =
          Formula.hVal (fun p => diagonal (v p)) ψ := by
        simpa [interpret] using ihψ
      rw [← ihφ', ← ihψ']
      exact diagonal_himp _ _

/-- Positive projection of BinaryEvidence formula evaluation is the single-chain
Gödel evaluation of the positive-coordinate valuation. -/
theorem interpret_pos_eq_ennrealGodelVal
    (v : PropVar → BinaryEvidence) (φ : Formula PropVar) :
    (interpret v φ).pos = ennrealGodelVal (fun p => (v p).pos) φ := by
  induction φ with
  | hatom p => rfl
  | hfalsum => rfl
  | hand φ ψ ihφ ihψ =>
      simp only [interpret, Formula.hVal, ennrealGodelVal]
      have ihφ' : (Formula.hVal v φ).pos =
          ennrealGodelVal (fun p => (v p).pos) φ := by
        simpa [interpret] using ihφ
      have ihψ' : (Formula.hVal v ψ).pos =
          ennrealGodelVal (fun p => (v p).pos) ψ := by
        simpa [interpret] using ihψ
      change min (Formula.hVal v φ).pos (Formula.hVal v ψ).pos =
        min (ennrealGodelVal (fun p => (v p).pos) φ)
          (ennrealGodelVal (fun p => (v p).pos) ψ)
      rw [ihφ', ihψ']
  | hor φ ψ ihφ ihψ =>
      simp only [interpret, Formula.hVal, ennrealGodelVal]
      have ihφ' : (Formula.hVal v φ).pos =
          ennrealGodelVal (fun p => (v p).pos) φ := by
        simpa [interpret] using ihφ
      have ihψ' : (Formula.hVal v ψ).pos =
          ennrealGodelVal (fun p => (v p).pos) ψ := by
        simpa [interpret] using ihψ
      change max (Formula.hVal v φ).pos (Formula.hVal v ψ).pos =
        max (ennrealGodelVal (fun p => (v p).pos) φ)
          (ennrealGodelVal (fun p => (v p).pos) ψ)
      rw [ihφ', ihψ']
  | himp φ ψ ihφ ihψ =>
      simp only [interpret, Formula.hVal, ennrealGodelVal, ennrealGodelImp]
      have ihφ' : (Formula.hVal v φ).pos =
          ennrealGodelVal (fun p => (v p).pos) φ := by
        simpa [interpret] using ihφ
      have ihψ' : (Formula.hVal v ψ).pos =
          ennrealGodelVal (fun p => (v p).pos) ψ := by
        simpa [interpret] using ihψ
      change (if (Formula.hVal v φ).pos ≤ (Formula.hVal v ψ).pos
          then ⊤ else (Formula.hVal v ψ).pos) =
        if ennrealGodelVal (fun p => (v p).pos) φ ≤
            ennrealGodelVal (fun p => (v p).pos) ψ
          then ⊤ else ennrealGodelVal (fun p => (v p).pos) ψ
      rw [ihφ', ihψ']

/-- Negative projection of BinaryEvidence formula evaluation is the single-chain
Gödel evaluation of the negative-coordinate valuation. -/
theorem interpret_neg_eq_ennrealGodelVal
    (v : PropVar → BinaryEvidence) (φ : Formula PropVar) :
    (interpret v φ).neg = ennrealGodelVal (fun p => (v p).neg) φ := by
  induction φ with
  | hatom p => rfl
  | hfalsum => rfl
  | hand φ ψ ihφ ihψ =>
      simp only [interpret, Formula.hVal, ennrealGodelVal]
      have ihφ' : (Formula.hVal v φ).neg =
          ennrealGodelVal (fun p => (v p).neg) φ := by
        simpa [interpret] using ihφ
      have ihψ' : (Formula.hVal v ψ).neg =
          ennrealGodelVal (fun p => (v p).neg) ψ := by
        simpa [interpret] using ihψ
      change min (Formula.hVal v φ).neg (Formula.hVal v ψ).neg =
        min (ennrealGodelVal (fun p => (v p).neg) φ)
          (ennrealGodelVal (fun p => (v p).neg) ψ)
      rw [ihφ', ihψ']
  | hor φ ψ ihφ ihψ =>
      simp only [interpret, Formula.hVal, ennrealGodelVal]
      have ihφ' : (Formula.hVal v φ).neg =
          ennrealGodelVal (fun p => (v p).neg) φ := by
        simpa [interpret] using ihφ
      have ihψ' : (Formula.hVal v ψ).neg =
          ennrealGodelVal (fun p => (v p).neg) ψ := by
        simpa [interpret] using ihψ
      change max (Formula.hVal v φ).neg (Formula.hVal v ψ).neg =
        max (ennrealGodelVal (fun p => (v p).neg) φ)
          (ennrealGodelVal (fun p => (v p).neg) ψ)
      rw [ihφ', ihψ']
  | himp φ ψ ihφ ihψ =>
      simp only [interpret, Formula.hVal, ennrealGodelVal, ennrealGodelImp]
      have ihφ' : (Formula.hVal v φ).neg =
          ennrealGodelVal (fun p => (v p).neg) φ := by
        simpa [interpret] using ihφ
      have ihψ' : (Formula.hVal v ψ).neg =
          ennrealGodelVal (fun p => (v p).neg) ψ := by
        simpa [interpret] using ihψ
      change (if (Formula.hVal v φ).neg ≤ (Formula.hVal v ψ).neg
          then ⊤ else (Formula.hVal v ψ).neg) =
        if ennrealGodelVal (fun p => (v p).neg) φ ≤
            ennrealGodelVal (fun p => (v p).neg) ψ
          then ⊤ else ennrealGodelVal (fun p => (v p).neg) ψ
      rw [ihφ', ihψ']

/-- BinaryEvidence validity is coordinatewise single-chain validity. -/
theorem valid_iff_ennrealGodel_coordinates
    (v : PropVar → BinaryEvidence) (φ : Formula PropVar) :
    valid v φ ↔
      ennrealGodelValid (fun p => (v p).pos) φ ∧
        ennrealGodelValid (fun p => (v p).neg) φ := by
  constructor
  · intro h
    constructor
    · exact (interpret_pos_eq_ennrealGodelVal v φ).symm.trans
        (congrArg BinaryEvidence.pos h)
    · exact (interpret_neg_eq_ennrealGodelVal v φ).symm.trans
        (congrArg BinaryEvidence.neg h)
  · intro h
    apply BinaryEvidence.ext'
    · exact (interpret_pos_eq_ennrealGodelVal v φ).trans h.1
    · exact (interpret_neg_eq_ennrealGodelVal v φ).trans h.2

/-- Universal BinaryEvidence validity is exactly validity in the single
`ℝ≥0∞` Gödel chain. -/
theorem universallyValid_iff_ennrealGodelUniversallyValid
    (φ : Formula PropVar) :
    universallyValid φ ↔ ennrealGodelUniversallyValid φ := by
  constructor
  · intro h v
    have hv : valid (fun p => diagonal (v p)) φ := h _
    exact (diagonal_eq_top_iff).mp ((diagonal_ennrealGodelVal v φ).trans hv)
  · intro h v
    exact (valid_iff_ennrealGodel_coordinates v φ).mpr
      ⟨h (fun p => (v p).pos), h (fun p => (v p).neg)⟩

/-- Excluded middle is not universally valid in BinaryEvidence. -/
theorem lem_not_universallyValid :
    ¬ universallyValid (((#0) ⋎ (∼(#0))) : Formula PropVar) := by
  intro h
  apply evidence_not_boolean
  intro e
  have hv := h (fun _ => e)
  simpa [valid, interpret, Formula.neg_def] using hv

/-! ### BinaryEvidence Strictly Stronger than IPL (Witness)

**Mathematical insight**: BinaryEvidence = ℝ≥0∞ × ℝ≥0∞ is a product of chains.
Products of chains always validate Dummett's axiom because in each coordinate,
elements are linearly ordered, so one implication must be ⊤.
-/

theorem evidence_stronger_than_ipl :
    ∃ φ : Formula PropVar,
      (∀ v : PropVar → BinaryEvidence, (PLNSemantics v) ⊧ φ) ∧
      ¬(Hilbert.Standard Int.axioms ⊢ φ) := by
  use ((#0) ➝ (#1)) ⋎ ((#1) ➝ (#0))
  constructor
  · intro v
    simp only [HeytingSemantics.val_def', HeytingSemantics.hVal,
               Formula.hVal_or, Formula.hVal_imp]
    exact evidence_dummett (v 0) (v 1)
  · exact dummett_not_provable_in_ipl

/-! ### LC soundness for BinaryEvidence -/

/-- For any valuation `v`, `PLNSemantics v` validates all LC axiom instances.
The extra LC axiom is Dummett prelinearity, already valid for arbitrary
formula instances by `evidence_valid_dummett_formula`. -/
theorem pln_in_lc_models (v : PropVar → BinaryEvidence) :
    (PLNSemantics v) ⊧* LC.axioms.instances := by
  constructor
  intro φ hφ
  simp only [Axiom.instances, Set.mem_setOf_eq] at hφ
  obtain ⟨ψ, hψ_mem, s, hs⟩ := hφ
  simp only [LC.axioms, Set.mem_insert_iff, Set.mem_singleton_iff] at hψ_mem
  rcases hψ_mem with hψ_mem | hψ_mem
  · rw [hψ_mem] at hs
    simp only [Formula.subst] at hs
    rw [hs]
    simp only [HeytingSemantics.val_def']
    simp only [HeytingSemantics.hVal, Formula.hVal_imp, Formula.hVal_falsum]
    rw [eq_top_iff, le_himp_iff]
    exact bot_le
  · rw [hψ_mem] at hs
    simp only [Formula.subst] at hs
    rw [hs]
    simp only [HeytingSemantics.val_def']
    change (((s 0).hVal v ⇨ (s 1).hVal v) ⊔
      ((s 1).hVal v ⇨ (s 0).hVal v)) = (⊤ : BinaryEvidence)
    exact evidence_dummett ((s 0).hVal v) ((s 1).hVal v)

/-- LC soundness for BinaryEvidence valuations. -/
theorem pln_lc_soundness {φ : Formula PropVar}
    (h : LO.Propositional.LC ⊢ φ) :
    universallyValid φ := by
  have hsem : ∀ v : PropVar → BinaryEvidence, (PLNSemantics v) ⊧ φ := by
    intro v
    induction h with
    | @axm ψ s hψ =>
      simp only [HeytingSemantics.val_def']
      simp only [LC.axioms, Set.mem_insert_iff, Set.mem_singleton_iff] at hψ
      rcases hψ with hEFQ | hDummett
      · rw [hEFQ]
        simp only [Formula.subst, HeytingSemantics.hVal, Formula.hVal_imp,
          Formula.hVal_falsum]
        rw [eq_top_iff, le_himp_iff]
        exact bot_le
      · rw [hDummett]
        simp only [Formula.subst, HeytingSemantics.hVal, Formula.hVal_or,
          Formula.hVal_imp]
        exact evidence_dummett ((s 0).hVal v) ((s 1).hVal v)
    | @mdp _ ψ _ _ ihpq ihp =>
      simp only [HeytingSemantics.val_def'] at *
      simp only [HeytingSemantics.hVal, Formula.hVal_imp] at ihpq
      rw [eq_top_iff, le_himp_iff] at ihpq
      rw [eq_top_iff]
      simp only [HeytingSemantics.hVal] at ihp
      rw [ihp, top_inf_eq] at ihpq
      exact ihpq
    | verum =>
      simp only [HeytingSemantics.val_def', HeytingSemantics.hVal_verum]
    | implyS =>
      simp only [HeytingSemantics.val_def', HeytingSemantics.hVal, Formula.hVal_imp]
      rw [eq_top_iff, le_himp_iff, le_himp_iff, top_inf_eq]
      exact inf_le_left
    | implyK =>
      simp only [HeytingSemantics.val_def', HeytingSemantics.hVal, Formula.hVal_imp]
      rw [eq_top_iff, le_himp_iff, le_himp_iff, le_himp_iff, top_inf_eq]
      exact himp_himp_inf_himp_inf_le _ _ _
    | andElimL =>
      simp only [HeytingSemantics.val_def', HeytingSemantics.hVal, Formula.hVal_imp,
        Formula.hVal_and]
      rw [eq_top_iff, le_himp_iff, top_inf_eq]
      exact inf_le_left
    | andElimR =>
      simp only [HeytingSemantics.val_def', HeytingSemantics.hVal, Formula.hVal_imp,
        Formula.hVal_and]
      rw [eq_top_iff, le_himp_iff, top_inf_eq]
      exact inf_le_right
    | andIntro =>
      simp only [HeytingSemantics.val_def', HeytingSemantics.hVal, Formula.hVal_imp,
        Formula.hVal_and]
      rw [eq_top_iff, le_himp_iff, le_himp_iff, top_inf_eq, inf_comm]
    | orIntroL =>
      simp only [HeytingSemantics.val_def', HeytingSemantics.hVal, Formula.hVal_imp,
        Formula.hVal_or]
      rw [eq_top_iff, le_himp_iff, top_inf_eq]
      exact le_sup_left
    | orIntroR =>
      simp only [HeytingSemantics.val_def', HeytingSemantics.hVal, Formula.hVal_imp,
        Formula.hVal_or]
      rw [eq_top_iff, le_himp_iff, top_inf_eq]
      exact le_sup_right
    | orElim =>
      simp only [HeytingSemantics.val_def', HeytingSemantics.hVal, Formula.hVal_imp,
        Formula.hVal_or]
      rw [eq_top_iff, le_himp_iff, le_himp_iff, le_himp_iff, top_inf_eq]
      exact himp_inf_himp_inf_sup_le _ _ _
  intro v
  exact hsem v

/-! ### Classical Logic Simulation via Glivenko's Theorem

Foundation proves Glivenko's theorem (1929):
  `glivenko : Propositional.Int ⊢ ∼∼φ ↔ Propositional.Cl ⊢ φ`

This means: Classical ⊢ φ ↔ IPL ⊢ ¬¬φ

Combined with our soundness theorem, we get classical simulation:
  Classical ⊢ φ → IPL ⊢ ¬¬φ → BinaryEvidence ⊧ ¬¬φ
-/

/-- Classical logic can be simulated in BinaryEvidence via double-negation.

If φ is classically provable, then ¬¬φ is valid in all BinaryEvidence valuations.
This is Glivenko's theorem (1929) combined with PLN soundness. -/
theorem classical_simulation {φ : Formula PropVar}
    (hcl : LO.Propositional.Cl ⊢ φ) :
    ∀ v : PropVar → BinaryEvidence, (PLNSemantics v) ⊧ (∼∼φ) := by
  intro v
  -- By Glivenko: Classical ⊢ φ → IPL ⊢ ¬¬φ
  have hipl : LO.Propositional.Int ⊢ ∼∼φ := LO.Propositional.glivenko.mpr hcl
  -- By soundness: IPL ⊢ ¬¬φ → BinaryEvidence ⊧ ¬¬φ
  exact pln_soundness hipl v

/-- Corollary: LEM (p ∨ ¬p) becomes ¬¬(p ∨ ¬p) which IS valid in BinaryEvidence. -/
theorem lem_double_negation_valid (v : PropVar → BinaryEvidence) (p : PropVar) :
    (PLNSemantics v) ⊧ (∼∼((#p) ⋎ (∼(#p)))) := by
  -- LEM is classically provable (Propositional.Cl has HasAxiomLEM instance)
  have hcl : LO.Propositional.Cl ⊢ ((#p) ⋎ (∼(#p))) := LO.Entailment.lem!
  exact classical_simulation hcl v

/-! ## Summary

We have established:

### Core Results
1. `Nontrivial BinaryEvidence` - ⊥ ≠ ⊤
2. `PLNSemantics` - HeytingSemantics instance for Foundation
3. `pln_soundness` - IPL ⊢ φ → BinaryEvidence ⊧ φ
4. `evidence_not_boolean` - LEM fails (BinaryEvidence ⊭ p ∨ ¬p)
5. `evidence_dummett` - Dummett valid: (p→q)∨(q→p) is valid in BinaryEvidence
6. `evidence_stronger_than_ipl` - BinaryEvidence validates formulas IPL cannot prove
7. `classical_simulation` - Classical ⊢ φ → BinaryEvidence ⊧ ¬¬φ (via Glivenko)
8. `diagonal_heyting_hom` - Diagonal embedding is a Heyting homomorphism
9. `pln_lc_soundness` - LC ⊢ φ → BinaryEvidence ⊧ φ
10. `universallyValid_iff_ennrealGodelUniversallyValid` - BinaryEvidence validity
    is exactly single-chain `ℝ≥0∞` Gödel validity

### BinaryEvidence is a Semantic Model for LC (Gödel-Dummett Logic)

**PLN BinaryEvidence is a semantic model, NOT a proof system.**

PLN has no sequent calculus or proof calculus of its own - it provides truth values.
The relationship to standard logics is:
- **LC/IPL**: Have both SYNTAX (proof systems) and SEMANTICS (Heyting algebras)
- **PLN BinaryEvidence**: Is a particular SEMANTIC model (the Heyting algebra ℝ≥0∞ × ℝ≥0∞)

**Proven (LC soundness)**: LC ⊢ φ → BinaryEvidence ⊧ φ
- LC = IPL + Dummett's axiom
- `pln_in_lc_models` shows every BinaryEvidence valuation validates LC axiom instances
- `pln_lc_soundness` applies Foundation's Heyting soundness theorem

**Exact semantic reduction**:
- `universallyValid_iff_ennrealGodelUniversallyValid` shows
  BinaryEvidence ⊧ φ iff the single `ℝ≥0∞` Gödel chain validates φ

**Remaining LC exactness bridge**: the current HOL/LO surface proves completeness
for all-prelinear Heyting consequence via
`provableLC_of_prelinearHeytingConsequence`; it does not currently provide
single-chain completeness.  The missing bridge is
`ennrealGodelUniversallyValid_implies_prelinearHeytingConsequence`, which would
turn validity in the single `ℝ≥0∞` Gödel chain into all-prelinear consequence,
and then LC provability.

### Logic Hierarchy (Propositional)
```
IPL ⊂ LC (Gödel-Dummett) ⊂ Classical
          ↑
    BinaryEvidence is a semantic model for LC (soundness proven)
```

- **IPL**: Intuitionistic propositional logic (all Heyting algebras)
- **LC**: IPL + Dummett's axiom (linear Heyting algebras / products of chains)
- **Classical**: LC + LEM (Boolean algebras)

### Why BinaryEvidence Validates LC Despite 2D Structure?

BinaryEvidence = ℝ≥0∞ × ℝ≥0∞ has **incomparable elements** (2D partial order).
LC's standard semantics use **linearly ordered** sets like [0,1] (1D total order).

These are structurally different! But for **propositional logic**, BinaryEvidence validates
all LC-provable formulas (soundness) because:
1. Each component of BinaryEvidence is linearly ordered (ℝ≥0∞)
2. Dummett holds componentwise: either e₁.pos ≤ e₂.pos or e₂.pos ≤ e₁.pos

### Where 2D Structure Matters

The 2D structure of BinaryEvidence provides distinctions that 1D cannot capture:
- `⟨low, low⟩` = uncertain (little evidence either way)
- `⟨high, high⟩` = contradictory (much evidence both ways)

These map to the SAME interval in 1D representations! The 2D structure matters for:
- Semantic richness (distinguishing uncertainty from contradiction)
- First-order/modal extensions (quantifying over BinaryEvidence values)
- Paraconsistent reasoning (handling contradictory evidence)
-/

end Mettapedia.PLN.Bridges.Logic.PLNIntuitionisticBridge
