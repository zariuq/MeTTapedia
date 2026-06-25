import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDerivation
import Mettapedia.PLN.TruthValues.PLNWeightTV
import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction

/-!
# PLN Link Calculus (Weight-First)

This module defines a small, *link-centric* proof calculus for PLN:

- Primary judgments are **links** `A ⟹ B` (conditional probabilities).
- Every judgment carries a **weight-based truth value** (`WTV`), i.e. `(strength, weight)`,
  where confidence is derived as `w/(w+1)`.

This is intentionally parametric in the formula type `F`, so the same calculus can be
instantiated for:
- propositional PLN
- first-order PLN (via satisfying-sets)
- higher-order PLN (via reduction to first-order)

Important design choice:
- Side conditions (e.g. independence / non-double-counting) are **explicit parameters**.
  We do *not* encode them as `True` placeholders.
- This file focuses on the *calculus objects*; semantic soundness lemmas live elsewhere.
-/

namespace Mettapedia.PLN.RuleFamilies.FirstOrder.PLNLinkCalculus

open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction
open Mettapedia.PLN.TruthValues.PLNWeightTV
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDerivation

universe u

/-! ## Judgments -/

inductive Judgment (F : Type u) where
  | term : F → WTV → Judgment F
  | link : F → F → WTV → Judgment F

abbrev Context (F : Type u) := Set (Judgment F)

/-! ## Weight-first truth functions (rule outputs) -/

namespace Truth

open WTV

private noncomputable def minW₂ (x y : WTV) : ℝ :=
  min x.weight y.weight

private noncomputable def minW₅ (a b c d e : WTV) : ℝ :=
  min a.weight (min b.weight (min c.weight (min d.weight e.weight)))

private lemma minW₂_nonneg (x y : WTV) : 0 ≤ minW₂ x y := by
  unfold minW₂
  exact le_min x.weight_nonneg y.weight_nonneg

private lemma minW₅_nonneg (a b c d e : WTV) : 0 ≤ minW₅ a b c d e := by
  unfold minW₅
  refine le_min a.weight_nonneg ?_
  refine le_min b.weight_nonneg ?_
  refine le_min c.weight_nonneg ?_
  exact le_min d.weight_nonneg e.weight_nonneg

/-- Revision (independent evidence): add weights, weighted-average strengths. -/
noncomputable def revision (t₁ t₂ : WTV) : WTV :=
  revisionWTV t₁ t₂

/-- Deduction (A→B, B→C ⊢ A→C), weight propagated as a conservative minimum.

Strength uses the standard PLN deduction strength formula; we clamp to `[0,1]` at the
boundary to keep the judgment well-formed operationally.
-/
noncomputable def deduction (tA tB tC tAB tBC : WTV) : WTV where
  strength :=
    clamp01 (plnDeductionStrength tAB.strength tBC.strength tB.strength tC.strength)
  weight := minW₅ tA tB tC tAB tBC
  strength_nonneg := clamp01_nonneg _
  strength_le_one := clamp01_le_one _
  weight_nonneg := minW₅_nonneg tA tB tC tAB tBC

/-- SourceRule (Induction): B→A and B→C yield A→C.

Weight follows the PeTTa/MeTTa convention: min of the *link* weights only.
-/
noncomputable def sourceRule (tA tB tC tBA tBC : WTV) : WTV where
  strength :=
    clamp01 (plnSourceRuleStrength tBA.strength tBC.strength tA.strength tB.strength tC.strength)
  weight := minW₂ tBA tBC
  strength_nonneg := clamp01_nonneg _
  strength_le_one := clamp01_le_one _
  weight_nonneg := minW₂_nonneg tBA tBC

/-- SinkRule (Abduction): A→B and C→B yield A→C.

Weight follows the PeTTa/MeTTa convention: min of the *link* weights only.
-/
noncomputable def sinkRule (tA tB tC tAB tCB : WTV) : WTV where
  strength := clamp01 (plnAbductionStrength tAB.strength tCB.strength tA.strength tB.strength tC.strength)
  weight := minW₂ tAB tCB
  strength_nonneg := clamp01_nonneg _
  strength_le_one := clamp01_le_one _
  weight_nonneg := minW₂_nonneg tAB tCB

end Truth

/-! ## Derivations -/

/-- A minimal derivation system for PLN link judgments.

`Indep j₁ j₂` is the *explicit* side condition used by revision:
"the evidence supporting these judgments is independent / not double-counted".
-/
inductive Derivation {F : Type u}
    (Indep : Judgment F → Judgment F → Prop)
    (DedSide : F → F → F → WTV → WTV → WTV → WTV → WTV → Prop)
    (SourceSide : F → F → F → WTV → WTV → WTV → WTV → WTV → Prop)
    (SinkSide : F → F → F → WTV → WTV → WTV → WTV → WTV → Prop)
    (Γ : Context F) : Judgment F → Type (u+1) where
  | axm {j : Judgment F} :
      j ∈ Γ →
      Derivation Indep DedSide SourceSide SinkSide Γ j

  | revision {A B : F} {t₁ t₂ : WTV} :
      Derivation Indep DedSide SourceSide SinkSide Γ (.link A B t₁) →
      Derivation Indep DedSide SourceSide SinkSide Γ (.link A B t₂) →
      Indep (.link A B t₁) (.link A B t₂) →
      Derivation Indep DedSide SourceSide SinkSide Γ (.link A B (Truth.revision t₁ t₂))

  | deduction {A B C : F} {tA tB tC tAB tBC : WTV} :
      Derivation Indep DedSide SourceSide SinkSide Γ (.term A tA) →
      Derivation Indep DedSide SourceSide SinkSide Γ (.term B tB) →
      Derivation Indep DedSide SourceSide SinkSide Γ (.term C tC) →
      Derivation Indep DedSide SourceSide SinkSide Γ (.link A B tAB) →
      Derivation Indep DedSide SourceSide SinkSide Γ (.link B C tBC) →
      DedSide A B C tA tB tC tAB tBC →
      Derivation Indep DedSide SourceSide SinkSide Γ (.link A C (Truth.deduction tA tB tC tAB tBC))

  | sourceRule {A B C : F} {tA tB tC tBA tBC : WTV} :
      Derivation Indep DedSide SourceSide SinkSide Γ (.term A tA) →
      Derivation Indep DedSide SourceSide SinkSide Γ (.term B tB) →
      Derivation Indep DedSide SourceSide SinkSide Γ (.term C tC) →
      Derivation Indep DedSide SourceSide SinkSide Γ (.link B A tBA) →
      Derivation Indep DedSide SourceSide SinkSide Γ (.link B C tBC) →
      SourceSide A B C tA tB tC tBA tBC →
      Derivation Indep DedSide SourceSide SinkSide Γ (.link A C (Truth.sourceRule tA tB tC tBA tBC))

  | sinkRule {A B C : F} {tA tB tC tAB tCB : WTV} :
      Derivation Indep DedSide SourceSide SinkSide Γ (.term A tA) →
      Derivation Indep DedSide SourceSide SinkSide Γ (.term B tB) →
      Derivation Indep DedSide SourceSide SinkSide Γ (.term C tC) →
      Derivation Indep DedSide SourceSide SinkSide Γ (.link A B tAB) →
      Derivation Indep DedSide SourceSide SinkSide Γ (.link C B tCB) →
      SinkSide A B C tA tB tC tAB tCB →
      Derivation Indep DedSide SourceSide SinkSide Γ (.link A C (Truth.sinkRule tA tB tC tAB tCB))

end Mettapedia.PLN.RuleFamilies.FirstOrder.PLNLinkCalculus
