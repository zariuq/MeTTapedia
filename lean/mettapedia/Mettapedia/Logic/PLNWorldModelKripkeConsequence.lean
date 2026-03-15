import Mathlib.Data.Multiset.Count
import Mettapedia.Logic.PLNWorldModelCalculus
import Mettapedia.Logic.GovernanceReasoning.Core

/-!
# Kripke WM Consequence Rules (Deontic Modal Layer)

This module instantiates `WMConsequenceRule` over multisets of pointed
deontic-transition models and lifts two core modal bridge theorems:

- `rexist_reflexive_bridge`  -> strength inequality `rexistFormula φ ⪯ φ`
- `dts_ob_pe_modal`          -> strength inequality `obFormula φ ⪯ peFormula φ`
-/

namespace Mettapedia.Logic.PLNWorldModelKripkeConsequence

open scoped ENNReal
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.ModalMuCalculus
open Mettapedia.Logic.GovernanceReasoning.Core
open Mettapedia.Logic.PLNWorldModel

abbrev DeonticQuery := Formula DeonticAct 0

/-- A pointed deontic transition model (`lts, env, world`) for query evaluation. -/
structure PointedDeonticKripke (S : Type*) where
  lts : LTS S DeonticAct
  env : Env S 0
  world : S

namespace PointedDeonticKripke

variable {S : Type*}

/-- Satisfaction predicate at the pointed state. -/
def satisfies (pk : PointedDeonticKripke S) (φ : DeonticQuery) : Prop :=
  Mettapedia.Logic.ModalMuCalculus.satisfies pk.lts pk.env φ pk.world

end PointedDeonticKripke

variable {S : Type*}

instance : EvidenceType (Multiset (PointedDeonticKripke S)) where

/-- Evidence from a multiset of pointed deontic models:
positive count = satisfying points; negative count = refuting points. -/
noncomputable def deonticKripkeEvidence
    (W : Multiset (PointedDeonticKripke S)) (φ : DeonticQuery) : Evidence := by
  classical
  exact
    ⟨(Multiset.countP (fun pk : PointedDeonticKripke S =>
        PointedDeonticKripke.satisfies pk φ) W : ℝ≥0∞),
     (Multiset.countP (fun pk : PointedDeonticKripke S =>
        ¬ PointedDeonticKripke.satisfies pk φ) W : ℝ≥0∞)⟩

theorem deonticKripkeEvidence_add
    (W₁ W₂ : Multiset (PointedDeonticKripke S)) (φ : DeonticQuery) :
    deonticKripkeEvidence (W₁ + W₂) φ =
      deonticKripkeEvidence W₁ φ + deonticKripkeEvidence W₂ φ := by
  classical
  apply Evidence.ext'
  · simp [deonticKripkeEvidence, Multiset.countP_add, Evidence.hplus_def]
  · simp [deonticKripkeEvidence, Multiset.countP_add, Evidence.hplus_def]

/-- `WorldModel` instance induced by multiset counting of deontic satisfaction. -/
noncomputable instance : WorldModel (Multiset (PointedDeonticKripke S)) DeonticQuery where
  evidence := deonticKripkeEvidence
  evidence_add := deonticKripkeEvidence_add
  evidence_zero q := by
    classical
    simp only [deonticKripkeEvidence, Multiset.countP_zero, Nat.cast_zero]; rfl

private theorem countP_le_countP_of_imp
    (W : Multiset (PointedDeonticKripke S))
    {p q : PointedDeonticKripke S → Prop}
    [DecidablePred p] [DecidablePred q]
    (himp : ∀ pk, p pk → q pk) :
    Multiset.countP p W ≤ Multiset.countP q W := by
  induction W using Multiset.induction_on with
  | empty =>
      simp
  | @cons a W ih =>
      by_cases hp : p a
      · have hq : q a := himp a hp
        simpa [Multiset.countP_cons_of_pos, hp, hq] using Nat.succ_le_succ ih
      · by_cases hq : q a
        · have hstep : Multiset.countP p W ≤ Multiset.countP q W + 1 :=
            le_trans ih (Nat.le_succ _)
          simpa [Multiset.countP_cons_of_neg, hp, Multiset.countP_cons_of_pos, hq]
            using hstep
        · simpa [Multiset.countP_cons_of_neg, hp, hq] using ih

private theorem deonticKripkeEvidence_total
    (W : Multiset (PointedDeonticKripke S)) (φ : DeonticQuery) :
    (deonticKripkeEvidence W φ).total = (W.card : ℝ≥0∞) := by
  classical
  have hcardNat :
      W.card =
        Multiset.countP (fun pk : PointedDeonticKripke S => PointedDeonticKripke.satisfies pk φ) W +
          Multiset.countP (fun pk : PointedDeonticKripke S => ¬ PointedDeonticKripke.satisfies pk φ) W := by
    simpa using (Multiset.card_eq_countP_add_countP
      (p := fun pk : PointedDeonticKripke S => PointedDeonticKripke.satisfies pk φ) W)
  have hcard :
      (W.card : ℝ≥0∞) =
        (Multiset.countP (fun pk : PointedDeonticKripke S => PointedDeonticKripke.satisfies pk φ) W : ℝ≥0∞) +
          (Multiset.countP (fun pk : PointedDeonticKripke S => ¬ PointedDeonticKripke.satisfies pk φ) W : ℝ≥0∞) := by
    exact_mod_cast hcardNat
  unfold deonticKripkeEvidence Evidence.total
  simpa using hcard.symm

/-- If each pointed model satisfying `φ` also satisfies `ψ`,
then WM query strength for `φ` is bounded by that of `ψ`. -/
theorem queryStrength_le_of_pointwise
    (W : Multiset (PointedDeonticKripke S)) (φ ψ : DeonticQuery)
    (himp : ∀ pk : PointedDeonticKripke S, pk.satisfies φ → pk.satisfies ψ) :
    WorldModel.queryStrength (State := Multiset (PointedDeonticKripke S)) (Query := DeonticQuery) W φ ≤
      WorldModel.queryStrength (State := Multiset (PointedDeonticKripke S)) (Query := DeonticQuery) W ψ := by
  let pφ : PointedDeonticKripke S → Prop :=
    fun pk => PointedDeonticKripke.satisfies pk φ
  let pψ : PointedDeonticKripke S → Prop :=
    fun pk => PointedDeonticKripke.satisfies pk ψ
  letI : DecidablePred pφ := Classical.decPred pφ
  letI : DecidablePred pψ := Classical.decPred pψ
  have hφ :
      WorldModel.queryStrength (State := Multiset (PointedDeonticKripke S)) (Query := DeonticQuery) W φ =
        if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP pφ W : ℝ≥0∞) / (W.card : ℝ≥0∞) := by
    unfold WorldModel.queryStrength Evidence.toStrength
    change (if (deonticKripkeEvidence W φ).total = 0 then 0
      else (deonticKripkeEvidence W φ).pos / (deonticKripkeEvidence W φ).total)
        = if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP pφ W : ℝ≥0∞) / (W.card : ℝ≥0∞)
    rw [deonticKripkeEvidence_total (W := W) (φ := φ)]
    simp [deonticKripkeEvidence, pφ]
  have hψ :
      WorldModel.queryStrength (State := Multiset (PointedDeonticKripke S)) (Query := DeonticQuery) W ψ =
        if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP pψ W : ℝ≥0∞) / (W.card : ℝ≥0∞) := by
    unfold WorldModel.queryStrength Evidence.toStrength
    change (if (deonticKripkeEvidence W ψ).total = 0 then 0
      else (deonticKripkeEvidence W ψ).pos / (deonticKripkeEvidence W ψ).total)
        = if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP pψ W : ℝ≥0∞) / (W.card : ℝ≥0∞)
    rw [deonticKripkeEvidence_total (W := W) (φ := ψ)]
    simp [deonticKripkeEvidence, pψ]
  by_cases hcard : (W.card : ℝ≥0∞) = 0
  · rw [hφ, hψ, hcard]
    simp
  · rw [hφ, hψ]
    simp [hcard]
    have hcountNat :
        Multiset.countP pφ W ≤ Multiset.countP pψ W :=
      countP_le_countP_of_imp (W := W) (p := pφ) (q := pψ) (by
        intro pk hp
        exact himp pk (by simpa [pφ] using hp))
    have hcount :
        (Multiset.countP pφ W : ℝ≥0∞) ≤
          (Multiset.countP pψ W : ℝ≥0∞) := by
      exact_mod_cast hcountNat
    exact ENNReal.div_le_div_right hcount (W.card : ℝ≥0∞)

/-- WM lift of `rexist_reflexive_bridge` over multiset deontic Kripke states. -/
theorem wm_rexist_reflexive_strength_le
    (W : Multiset (PointedDeonticKripke S)) (φ : DeonticQuery)
    (hrefl : ∀ pk : PointedDeonticKripke S, ∀ s, pk.lts.trans s .rexist s) :
    WorldModel.queryStrength (State := Multiset (PointedDeonticKripke S)) (Query := DeonticQuery)
        W (rexistFormula φ) ≤
      WorldModel.queryStrength (State := Multiset (PointedDeonticKripke S)) (Query := DeonticQuery)
        W φ := by
  apply queryStrength_le_of_pointwise (W := W) (φ := rexistFormula φ) (ψ := φ)
  intro pk hsat
  exact rexist_reflexive_bridge pk.lts (hrefl pk) pk.env φ pk.world
    (by simpa [PointedDeonticKripke.satisfies] using hsat)

/-- WM lift of `dts_ob_pe_modal` over multiset deontic Kripke states. -/
theorem wm_dts_ob_pe_strength_le
    (W : Multiset (PointedDeonticKripke S)) (φ : DeonticQuery)
    (hser : ∀ pk : PointedDeonticKripke S, DeonticSeriality pk.lts)
    (htotal : ∀ pk : PointedDeonticKripke S, ∀ s, ∃ s', pk.lts.trans s .obligatory s') :
    WorldModel.queryStrength (State := Multiset (PointedDeonticKripke S)) (Query := DeonticQuery)
        W (obFormula φ) ≤
      WorldModel.queryStrength (State := Multiset (PointedDeonticKripke S)) (Query := DeonticQuery)
        W (peFormula φ) := by
  apply queryStrength_le_of_pointwise (W := W) (φ := obFormula φ) (ψ := peFormula φ)
  intro pk hsat
  exact dts_ob_pe_modal pk.lts (hser pk) (htotal pk) pk.env φ pk.world
    (by simpa [PointedDeonticKripke.satisfies] using hsat)

/-- Consequence rule packaging for `rexist_reflexive_bridge`. -/
def wmRexistReflexiveConsequenceRule (φ : DeonticQuery) :
    WMConsequenceRule (Multiset (PointedDeonticKripke S)) DeonticQuery where
  side := ∀ pk : PointedDeonticKripke S, ∀ s, pk.lts.trans s .rexist s
  premise := rexistFormula φ
  conclusion := φ
  sound := by
    intro hside W
    exact wm_rexist_reflexive_strength_le (W := W) (φ := φ) hside

/-- Consequence rule packaging for `dts_ob_pe_modal`. -/
def wmDtsObPeConsequenceRule (φ : DeonticQuery) :
    WMConsequenceRule (Multiset (PointedDeonticKripke S)) DeonticQuery where
  side :=
    (∀ pk : PointedDeonticKripke S, DeonticSeriality pk.lts) ∧
      (∀ pk : PointedDeonticKripke S, ∀ s, ∃ s', pk.lts.trans s .obligatory s')
  premise := obFormula φ
  conclusion := peFormula φ
  sound := by
    intro hside W
    rcases hside with ⟨hser, htotal⟩
    exact wm_dts_ob_pe_strength_le (W := W) (φ := φ) hser htotal

end Mettapedia.Logic.PLNWorldModelKripkeConsequence
