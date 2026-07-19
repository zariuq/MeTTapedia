/-
# Certified semantic masks preserve GSLT search recall

Hard pruning is admissible only when a mask proves that every observable
big-step emission is allowed.  This module packages that obligation once and
derives target-level recall preservation, then instantiates it with the
existing sign/parity and mod-k analyzers.
-/

import Mettapedia.GSLT.LanguageDef.Gauthier.BigStepGSLT
import Mettapedia.GSLT.LanguageDef.Gauthier.BigStepGSLTE2
import Mettapedia.OSLF.Framework.GauthierOEISModKPruning

namespace Mettapedia.OSLF.Framework.GauthierOEISCertifiedMask

open Mettapedia.GSLT.LanguageDef.GauthierE1
open Mettapedia.GSLT.LanguageDef.GauthierBigStepGSLT
open Mettapedia.GSLT.LanguageDef.GauthierE2BigStepGSLT
open Mettapedia.GSLT.LanguageDef.GauthierProperties
open Mettapedia.OSLF.Framework.GauthierOEISPruningSoundness
open Mettapedia.OSLF.Framework.GauthierOEISModKPruning

/-- Existing evaluator reproduction is exactly existential GSLT emission. -/
theorem reproducesAt_iff_exists_emitsAt (program : Prog) (obs : ObservedTerm) :
    ReproducesAt program obs ↔
      ∃ fuel, EmitsAt orgE1Signature fuel program obs.seedValue obs.value := by
  constructor
  · rintro ⟨fuel, finalStore, heval⟩
    refine ⟨fuel, ?_⟩
    rw [emitsAt_iff]
    exact ⟨finalStore, heval⟩
  · rintro ⟨fuel, hemits⟩
    rw [emitsAt_iff] at hemits
    rcases hemits with ⟨finalStore, heval⟩
    exact ⟨fuel, finalStore, heval⟩

/-- A fuel-indexed observation boundary shared by scalar and memo GSLTs. -/
structure FuelObservationSemantics (Program Observation : Type) where
  emitsAt : Nat → Program → Observation → Prop

def SemanticReproducesAt {Program Observation : Type}
    (semantics : FuelObservationSemantics Program Observation)
    (program : Program) (obs : Observation) : Prop :=
  ∃ fuel, semantics.emitsAt fuel program obs

def SemanticReproduces {Program Observation : Type}
    (semantics : FuelObservationSemantics Program Observation)
    (program : Program) (target : List Observation) : Prop :=
  ∀ obs, obs ∈ target → SemanticReproducesAt semantics program obs

/--
A hard mask is certified by a proof that it admits every observation emitted
by its chosen semantics.  Uncertified scores cannot inhabit this structure and
therefore remain soft search guidance.
-/
structure CertifiedSemanticMask {Program Observation : Type}
    (semantics : FuelObservationSemantics Program Observation) where
  allows : Program → Observation → Prop
  emissionAllowed :
    ∀ (program : Program) (obs : Observation) (fuel : Nat),
      semantics.emitsAt fuel program obs →
      allows program obs

def RejectedBy {Program Observation : Type}
    {semantics : FuelObservationSemantics Program Observation}
    (mask : CertifiedSemanticMask semantics) (program : Program)
    (target : List Observation) : Prop :=
  ∃ obs, obs ∈ target ∧ ¬ mask.allows program obs

/-- Pointwise recall: every true reproduction is retained by every certified mask. -/
theorem reproduced_observation_allowed {Program Observation : Type}
    {semantics : FuelObservationSemantics Program Observation}
    (mask : CertifiedSemanticMask semantics)
    {program : Program} {obs : Observation}
    (hreproduces : SemanticReproducesAt semantics program obs) :
    mask.allows program obs := by
  rcases hreproduces with ⟨fuel, hemits⟩
  exact mask.emissionAllowed program obs fuel hemits

/-- T4 crown: a certified hard mask cannot reject any true target reproducer. -/
theorem certifiedMask_recall_preserving {Program Observation : Type}
    {semantics : FuelObservationSemantics Program Observation}
    (mask : CertifiedSemanticMask semantics)
    {program : Program} {target : List Observation}
    (hrejects : RejectedBy mask program target) :
    ¬ SemanticReproduces semantics program target := by
  intro hreproduces
  rcases hrejects with ⟨obs, hmem, hreject⟩
  exact hreject (reproduced_observation_allowed mask (hreproduces obs hmem))

/-- Scalar E1 observation boundary, retained as a compatibility instance. -/
def e1Semantics : FuelObservationSemantics Prog ObservedTerm where
  emitsAt := fun fuel program obs =>
    EmitsAt orgE1Signature fuel program obs.seedValue obs.value

theorem e1SemanticReproducesAt_iff (program : Prog) (obs : ObservedTerm) :
    SemanticReproducesAt e1Semantics program obs ↔ ReproducesAt program obs := by
  exact (reproducesAt_iff_exists_emitsAt program obs).symm

theorem e1SemanticReproduces_iff (program : Prog) (target : List ObservedTerm) :
    SemanticReproduces e1Semantics program target ↔ Reproduces program target := by
  constructor
  · intro h obs hmem
    exact (e1SemanticReproducesAt_iff program obs).mp (h obs hmem)
  · intro h obs hmem
    exact (e1SemanticReproducesAt_iff program obs).mpr (h obs hmem)

/-- The existing sign/parity analyzer as one certified semantic mask. -/
def signParityMask : CertifiedSemanticMask e1Semantics where
  allows := fun program obs => SignCompatible program obs ∧ ParityCompatible program obs
  emissionAllowed := by
    intro program obs fuel hemits
    change EmitsAt orgE1Signature fuel program obs.seedValue obs.value at hemits
    rw [emitsAt_iff] at hemits
    rcases hemits with ⟨finalStore, heval⟩
    exact
      ⟨Seal.certified_sign_sound obs.seed_nonneg heval,
        Seal.certified_parity_sound heval⟩

/-- The existing residue analyzer as a certified semantic mask for every modulus. -/
def modKMask (k : Nat) : CertifiedSemanticMask e1Semantics where
  allows := ModKCompatible k
  emissionAllowed := by
    intro program obs fuel hemits
    change EmitsAt orgE1Signature fuel program obs.seedValue obs.value at hemits
    rw [emitsAt_iff] at hemits
    rcases hemits with ⟨finalStore, heval⟩
    exact certified_modk_sound (k := k) heval

theorem analysisIncompatible_iff_rejectedBy_signParity {program : Prog}
    {target : List ObservedTerm} :
    AnalysisIncompatible program target ↔
      RejectedBy signParityMask program target := by
  constructor
  · rintro ⟨obs, hmem, hsign | hparity⟩
    · exact ⟨obs, hmem, fun hboth => hsign hboth.1⟩
    · exact ⟨obs, hmem, fun hboth => hparity hboth.2⟩
  · rintro ⟨obs, hmem, hboth⟩
    refine ⟨obs, hmem, ?_⟩
    by_cases hsign : SignCompatible program obs
    · exact Or.inr (fun hparity => hboth ⟨hsign, hparity⟩)
    · exact Or.inl hsign

theorem modKIncompatible_iff_rejectedBy {k : Nat} {program : Prog}
    {target : List ObservedTerm} :
    ModKIncompatible k program target ↔
      RejectedBy (modKMask k) program target :=
  Iff.rfl

/-- Existing sign/parity admissibility recovered from the generic GSLT schema. -/
theorem certified_property_pruning_via_mask {program : Prog}
    {target : List ObservedTerm}
    (hbad : AnalysisIncompatible program target) :
    ¬ Reproduces program target :=
  fun hreproduces =>
    certifiedMask_recall_preserving signParityMask
      (analysisIncompatible_iff_rejectedBy_signParity.mp hbad)
      ((e1SemanticReproduces_iff program target).mpr hreproduces)

/-- Existing mod-k admissibility recovered from the generic GSLT schema. -/
theorem certified_modk_pruning_via_mask {k : Nat} {program : Prog}
    {target : List ObservedTerm}
    (hbad : ModKIncompatible k program target) :
    ¬ Reproduces program target :=
  fun hreproduces =>
    certifiedMask_recall_preserving (modKMask k)
      (modKIncompatible_iff_rejectedBy.mp hbad)
      ((e1SemanticReproduces_iff program target).mpr hreproduces)

/-! Positive and negative canaries for hard-mask certification. -/

example : (modKMask 3).allows oneProg observedOneAt0 :=
  one_mod3_compatible_with_one_observation

example : ¬ (modKMask 3).allows zeroProg observedOneAt0 :=
  zero_mod3_incompatible_with_one_observation

example : RejectedBy (modKMask 3) zeroProg oneTarget :=
  (modKIncompatible_iff_rejectedBy.mp ⟨observedOneAt0, by simp [oneTarget],
    zero_mod3_incompatible_with_one_observation⟩)

example : ¬ Reproduces zeroProg oneTarget :=
  certified_modk_pruning_via_mask
    ⟨observedOneAt0, by simp [oneTarget],
      zero_mod3_incompatible_with_one_observation⟩

/-! ## Live E2 memo semantics -/

/--
On the scalar core fragment, the existing residue analyzer also soundly
over-approximates the head emitted by the live E2 memo evaluator.  The theorem
allows arbitrary nonempty memo inputs and arbitrary tails: the analysis tracks
their heads, while E2 arithmetic may retain the left tail.
-/
theorem CoreProg.memo_modk_sound {k : Nat} {program : Prog}
    (hprogram : CoreProg program) :
    ∀ (analysisFuel evalFuel : Nat) (xInfo yInfo : ResidueInfo k)
      (xHead yHead : Int) (xTail yTail : List Int)
      (world : Mettapedia.GSLT.LanguageDef.GauthierE2.World)
      (values : List Int) (value : Int),
      xInfo.denote xHead →
      yInfo.denote yHead →
      Mettapedia.GSLT.LanguageDef.GauthierE2.eval evalFuel
          Mettapedia.GSLT.LanguageDef.GauthierE2.intlSignature program
          (xHead :: xTail) (yHead :: yTail) world = some values →
      Mettapedia.GSLT.LanguageDef.GauthierE2.head? values = some value →
      (modkAnalyzeFuel k analysisFuel xInfo yInfo program).denote value := by
  induction hprogram with
  | zero =>
      intro analysisFuel evalFuel xInfo yInfo xHead yHead xTail yTail world values value
        hx hy heval hhead
      cases analysisFuel with
      | zero => simp [modkAnalyzeFuel, ResidueInfo.top]
      | succ analysisFuel =>
          cases evalFuel with
          | zero =>
              simp [Mettapedia.GSLT.LanguageDef.GauthierE2.eval] at heval
          | succ evalFuel =>
              simp [Mettapedia.GSLT.LanguageDef.GauthierE2.eval,
                Mettapedia.GSLT.LanguageDef.GauthierE2.intlSignature,
                Mettapedia.GSLT.LanguageDef.GauthierE2.orgSignature,
                Mettapedia.GSLT.LanguageDef.GauthierE2.listOps,
                Mettapedia.GSLT.LanguageDef.GauthierE1.entryAt,
                Mettapedia.GSLT.LanguageDef.GauthierE1.listGet?,
                Mettapedia.GSLT.LanguageDef.GauthierE1.entry] at heval
              subst values
              simp [Mettapedia.GSLT.LanguageDef.GauthierE2.head?] at hhead
              subst value
              exact ResidueInfo.exact_self k 0
  | one =>
      intro analysisFuel evalFuel xInfo yInfo xHead yHead xTail yTail world values value
        hx hy heval hhead
      cases analysisFuel with
      | zero => simp [modkAnalyzeFuel, ResidueInfo.top]
      | succ analysisFuel =>
          cases evalFuel with
          | zero =>
              simp [Mettapedia.GSLT.LanguageDef.GauthierE2.eval] at heval
          | succ evalFuel =>
              simp [Mettapedia.GSLT.LanguageDef.GauthierE2.eval,
                Mettapedia.GSLT.LanguageDef.GauthierE2.intlSignature,
                Mettapedia.GSLT.LanguageDef.GauthierE2.orgSignature,
                Mettapedia.GSLT.LanguageDef.GauthierE2.listOps,
                Mettapedia.GSLT.LanguageDef.GauthierE1.entryAt,
                Mettapedia.GSLT.LanguageDef.GauthierE1.listGet?,
                Mettapedia.GSLT.LanguageDef.GauthierE1.entry] at heval
              subst values
              simp [Mettapedia.GSLT.LanguageDef.GauthierE2.head?] at hhead
              subst value
              exact ResidueInfo.exact_self k 1
  | two =>
      intro analysisFuel evalFuel xInfo yInfo xHead yHead xTail yTail world values value
        hx hy heval hhead
      cases analysisFuel with
      | zero => simp [modkAnalyzeFuel, ResidueInfo.top]
      | succ analysisFuel =>
          cases evalFuel with
          | zero =>
              simp [Mettapedia.GSLT.LanguageDef.GauthierE2.eval] at heval
          | succ evalFuel =>
              simp [Mettapedia.GSLT.LanguageDef.GauthierE2.eval,
                Mettapedia.GSLT.LanguageDef.GauthierE2.intlSignature,
                Mettapedia.GSLT.LanguageDef.GauthierE2.orgSignature,
                Mettapedia.GSLT.LanguageDef.GauthierE2.listOps,
                Mettapedia.GSLT.LanguageDef.GauthierE1.entryAt,
                Mettapedia.GSLT.LanguageDef.GauthierE1.listGet?,
                Mettapedia.GSLT.LanguageDef.GauthierE1.entry] at heval
              subst values
              simp [Mettapedia.GSLT.LanguageDef.GauthierE2.head?] at hhead
              subst value
              exact ResidueInfo.exact_self k 2
  | add ha hb iha ihb =>
      rename_i a b
      intro analysisFuel evalFuel xInfo yInfo xHead yHead xTail yTail world values value
        hx hy heval hhead
      cases analysisFuel with
      | zero => simp [modkAnalyzeFuel, ResidueInfo.top]
      | succ analysisFuel =>
          cases evalFuel with
          | zero =>
              simp [Mettapedia.GSLT.LanguageDef.GauthierE2.eval] at heval
          | succ evalFuel =>
              simp only [Mettapedia.GSLT.LanguageDef.GauthierE2.eval] at heval
              change
                ((Mettapedia.GSLT.LanguageDef.GauthierE2.eval evalFuel
                    Mettapedia.GSLT.LanguageDef.GauthierE2.intlSignature a
                    (xHead :: xTail) (yHead :: yTail) world).bind fun aValues =>
                  (Mettapedia.GSLT.LanguageDef.GauthierE2.eval evalFuel
                    Mettapedia.GSLT.LanguageDef.GauthierE2.intlSignature b
                    (xHead :: xTail) (yHead :: yTail) world).bind fun bValues =>
                  Mettapedia.GSLT.LanguageDef.GauthierE2.mkE
                    Mettapedia.GSLT.LanguageDef.GauthierE2.add? aValues bValues) =
                  some values at heval
              cases haEval : Mettapedia.GSLT.LanguageDef.GauthierE2.eval evalFuel
                  Mettapedia.GSLT.LanguageDef.GauthierE2.intlSignature a
                  (xHead :: xTail) (yHead :: yTail) world with
              | none =>
                  simp [haEval] at heval
              | some aValues =>
                  cases hbEval : Mettapedia.GSLT.LanguageDef.GauthierE2.eval evalFuel
                      Mettapedia.GSLT.LanguageDef.GauthierE2.intlSignature b
                      (xHead :: xTail) (yHead :: yTail) world with
                  | none =>
                      simp [haEval, hbEval] at heval
                  | some bValues =>
                      cases aValues with
                      | nil =>
                          simp [haEval, hbEval,
                            Mettapedia.GSLT.LanguageDef.GauthierE2.mkE] at heval
                      | cons aHead aMemo =>
                          cases bValues with
                          | nil =>
                              simp [haEval, hbEval,
                                Mettapedia.GSLT.LanguageDef.GauthierE2.mkE] at heval
                          | cons bHead bMemo =>
                              have hvalues : values = (aHead + bHead) :: aMemo := by
                                simpa [haEval, hbEval,
                                  Mettapedia.GSLT.LanguageDef.GauthierE2.mkE,
                                  Mettapedia.GSLT.LanguageDef.GauthierE2.add?] using heval.symm
                              subst values
                              simp [Mettapedia.GSLT.LanguageDef.GauthierE2.head?] at hhead
                              subst value
                              have haSound := iha analysisFuel evalFuel xInfo yInfo
                                xHead yHead xTail yTail world (aHead :: aMemo) aHead
                                hx hy haEval rfl
                              have hbSound := ihb analysisFuel evalFuel xInfo yInfo
                                xHead yHead xTail yTail world (bHead :: bMemo) bHead
                                hx hy hbEval rfl
                              simpa [modkAnalyzeFuel, orgE1Signature, entryAt, listGet?, entry]
                                using ResidueInfo.add_sound haSound hbSound
  | diff ha hb iha ihb =>
      rename_i a b
      intro analysisFuel evalFuel xInfo yInfo xHead yHead xTail yTail world values value
        hx hy heval hhead
      cases analysisFuel with
      | zero => simp [modkAnalyzeFuel, ResidueInfo.top]
      | succ analysisFuel =>
          cases evalFuel with
          | zero =>
              simp [Mettapedia.GSLT.LanguageDef.GauthierE2.eval] at heval
          | succ evalFuel =>
              simp only [Mettapedia.GSLT.LanguageDef.GauthierE2.eval] at heval
              change
                ((Mettapedia.GSLT.LanguageDef.GauthierE2.eval evalFuel
                    Mettapedia.GSLT.LanguageDef.GauthierE2.intlSignature a
                    (xHead :: xTail) (yHead :: yTail) world).bind fun aValues =>
                  (Mettapedia.GSLT.LanguageDef.GauthierE2.eval evalFuel
                    Mettapedia.GSLT.LanguageDef.GauthierE2.intlSignature b
                    (xHead :: xTail) (yHead :: yTail) world).bind fun bValues =>
                  Mettapedia.GSLT.LanguageDef.GauthierE2.mkE
                    Mettapedia.GSLT.LanguageDef.GauthierE2.sub? aValues bValues) =
                  some values at heval
              cases haEval : Mettapedia.GSLT.LanguageDef.GauthierE2.eval evalFuel
                  Mettapedia.GSLT.LanguageDef.GauthierE2.intlSignature a
                  (xHead :: xTail) (yHead :: yTail) world with
              | none =>
                  simp [haEval] at heval
              | some aValues =>
                  cases hbEval : Mettapedia.GSLT.LanguageDef.GauthierE2.eval evalFuel
                      Mettapedia.GSLT.LanguageDef.GauthierE2.intlSignature b
                      (xHead :: xTail) (yHead :: yTail) world with
                  | none =>
                      simp [haEval, hbEval] at heval
                  | some bValues =>
                      cases aValues with
                      | nil =>
                          simp [haEval, hbEval,
                            Mettapedia.GSLT.LanguageDef.GauthierE2.mkE] at heval
                      | cons aHead aMemo =>
                          cases bValues with
                          | nil =>
                              simp [haEval, hbEval,
                                Mettapedia.GSLT.LanguageDef.GauthierE2.mkE] at heval
                          | cons bHead bMemo =>
                              have hvalues : values = (aHead - bHead) :: aMemo := by
                                simpa [haEval, hbEval,
                                  Mettapedia.GSLT.LanguageDef.GauthierE2.mkE,
                                  Mettapedia.GSLT.LanguageDef.GauthierE2.sub?] using heval.symm
                              subst values
                              simp [Mettapedia.GSLT.LanguageDef.GauthierE2.head?] at hhead
                              subst value
                              have haSound := iha analysisFuel evalFuel xInfo yInfo
                                xHead yHead xTail yTail world (aHead :: aMemo) aHead
                                hx hy haEval rfl
                              have hbSound := ihb analysisFuel evalFuel xInfo yInfo
                                xHead yHead xTail yTail world (bHead :: bMemo) bHead
                                hx hy hbEval rfl
                              simpa [modkAnalyzeFuel, orgE1Signature, entryAt, listGet?, entry]
                                using ResidueInfo.diff_sound haSound hbSound
  | mult ha hb iha ihb =>
      rename_i a b
      intro analysisFuel evalFuel xInfo yInfo xHead yHead xTail yTail world values value
        hx hy heval hhead
      cases analysisFuel with
      | zero => simp [modkAnalyzeFuel, ResidueInfo.top]
      | succ analysisFuel =>
          cases evalFuel with
          | zero =>
              simp [Mettapedia.GSLT.LanguageDef.GauthierE2.eval] at heval
          | succ evalFuel =>
              simp only [Mettapedia.GSLT.LanguageDef.GauthierE2.eval] at heval
              change
                ((Mettapedia.GSLT.LanguageDef.GauthierE2.eval evalFuel
                    Mettapedia.GSLT.LanguageDef.GauthierE2.intlSignature a
                    (xHead :: xTail) (yHead :: yTail) world).bind fun aValues =>
                  (Mettapedia.GSLT.LanguageDef.GauthierE2.eval evalFuel
                    Mettapedia.GSLT.LanguageDef.GauthierE2.intlSignature b
                    (xHead :: xTail) (yHead :: yTail) world).bind fun bValues =>
                  Mettapedia.GSLT.LanguageDef.GauthierE2.mkE
                    Mettapedia.GSLT.LanguageDef.GauthierE2.mul? aValues bValues) =
                  some values at heval
              cases haEval : Mettapedia.GSLT.LanguageDef.GauthierE2.eval evalFuel
                  Mettapedia.GSLT.LanguageDef.GauthierE2.intlSignature a
                  (xHead :: xTail) (yHead :: yTail) world with
              | none =>
                  simp [haEval] at heval
              | some aValues =>
                  cases hbEval : Mettapedia.GSLT.LanguageDef.GauthierE2.eval evalFuel
                      Mettapedia.GSLT.LanguageDef.GauthierE2.intlSignature b
                      (xHead :: xTail) (yHead :: yTail) world with
                  | none =>
                      simp [haEval, hbEval] at heval
                  | some bValues =>
                      cases aValues with
                      | nil =>
                          simp [haEval, hbEval,
                            Mettapedia.GSLT.LanguageDef.GauthierE2.mkE] at heval
                      | cons aHead aMemo =>
                          cases bValues with
                          | nil =>
                              simp [haEval, hbEval,
                                Mettapedia.GSLT.LanguageDef.GauthierE2.mkE] at heval
                          | cons bHead bMemo =>
                              have hvalues : values = (aHead * bHead) :: aMemo := by
                                simpa [haEval, hbEval,
                                  Mettapedia.GSLT.LanguageDef.GauthierE2.mkE,
                                  Mettapedia.GSLT.LanguageDef.GauthierE2.mul?] using heval.symm
                              subst values
                              simp [Mettapedia.GSLT.LanguageDef.GauthierE2.head?] at hhead
                              subst value
                              have haSound := iha analysisFuel evalFuel xInfo yInfo
                                xHead yHead xTail yTail world (aHead :: aMemo) aHead
                                hx hy haEval rfl
                              have hbSound := ihb analysisFuel evalFuel xInfo yInfo
                                xHead yHead xTail yTail world (bHead :: bMemo) bHead
                                hx hy hbEval rfl
                              simpa [modkAnalyzeFuel, orgE1Signature, entryAt, listGet?, entry]
                                using ResidueInfo.mult_sound haSound hbSound
  | cond hc ht he ihc iht ihe =>
      rename_i c t e
      intro analysisFuel evalFuel xInfo yInfo xHead yHead xTail yTail world values value
        hx hy heval hhead
      cases analysisFuel with
      | zero => simp [modkAnalyzeFuel, ResidueInfo.top]
      | succ analysisFuel =>
          cases evalFuel with
          | zero =>
              simp [Mettapedia.GSLT.LanguageDef.GauthierE2.eval] at heval
          | succ evalFuel =>
              simp only [Mettapedia.GSLT.LanguageDef.GauthierE2.eval] at heval
              change
                ((Mettapedia.GSLT.LanguageDef.GauthierE2.eval evalFuel
                    Mettapedia.GSLT.LanguageDef.GauthierE2.intlSignature c
                    (xHead :: xTail) (yHead :: yTail) world).bind fun cValues =>
                  (Mettapedia.GSLT.LanguageDef.GauthierE2.head? cValues).bind fun cHead =>
                  if cHead ≤ 0 then
                    Mettapedia.GSLT.LanguageDef.GauthierE2.eval evalFuel
                      Mettapedia.GSLT.LanguageDef.GauthierE2.intlSignature t
                      (xHead :: xTail) (yHead :: yTail) world
                  else
                    Mettapedia.GSLT.LanguageDef.GauthierE2.eval evalFuel
                      Mettapedia.GSLT.LanguageDef.GauthierE2.intlSignature e
                      (xHead :: xTail) (yHead :: yTail) world) = some values at heval
              cases hcEval : Mettapedia.GSLT.LanguageDef.GauthierE2.eval evalFuel
                  Mettapedia.GSLT.LanguageDef.GauthierE2.intlSignature c
                  (xHead :: xTail) (yHead :: yTail) world with
              | none =>
                  simp [hcEval] at heval
              | some cValues =>
                  cases cValues with
                  | nil =>
                      simp [hcEval, Mettapedia.GSLT.LanguageDef.GauthierE2.head?] at heval
                  | cons cHead cMemo =>
                      simp [hcEval, Mettapedia.GSLT.LanguageDef.GauthierE2.head?] at heval
                      by_cases hbranch : cHead ≤ 0
                      · simp [hbranch] at heval
                        have htSound := iht analysisFuel evalFuel xInfo yInfo
                          xHead yHead xTail yTail world values value hx hy heval hhead
                        simpa [modkAnalyzeFuel, orgE1Signature, entryAt, listGet?, entry,
                          ResidueInfo.join]
                          using (Or.inl htSound)
                      · simp [hbranch] at heval
                        have heSound := ihe analysisFuel evalFuel xInfo yInfo
                          xHead yHead xTail yTail world values value hx hy heval hhead
                        simpa [modkAnalyzeFuel, orgE1Signature, entryAt, listGet?, entry,
                          ResidueInfo.join]
                          using (Or.inr heSound)
  | x =>
      intro analysisFuel evalFuel xInfo yInfo xHead yHead xTail yTail world values value
        hx hy heval hhead
      cases analysisFuel with
      | zero => simp [modkAnalyzeFuel, ResidueInfo.top]
      | succ analysisFuel =>
          cases evalFuel with
          | zero =>
              simp [Mettapedia.GSLT.LanguageDef.GauthierE2.eval] at heval
          | succ evalFuel =>
              simp [Mettapedia.GSLT.LanguageDef.GauthierE2.eval,
                Mettapedia.GSLT.LanguageDef.GauthierE2.intlSignature,
                Mettapedia.GSLT.LanguageDef.GauthierE2.orgSignature,
                Mettapedia.GSLT.LanguageDef.GauthierE2.listOps,
                Mettapedia.GSLT.LanguageDef.GauthierE1.entryAt,
                Mettapedia.GSLT.LanguageDef.GauthierE1.listGet?,
                Mettapedia.GSLT.LanguageDef.GauthierE1.entry] at heval
              subst values
              simp [Mettapedia.GSLT.LanguageDef.GauthierE2.head?] at hhead
              subst value
              simpa [modkAnalyzeFuel, orgE1Signature, entryAt, listGet?, entry] using hx
  | y =>
      intro analysisFuel evalFuel xInfo yInfo xHead yHead xTail yTail world values value
        hx hy heval hhead
      cases analysisFuel with
      | zero => simp [modkAnalyzeFuel, ResidueInfo.top]
      | succ analysisFuel =>
          cases evalFuel with
          | zero =>
              simp [Mettapedia.GSLT.LanguageDef.GauthierE2.eval] at heval
          | succ evalFuel =>
              simp [Mettapedia.GSLT.LanguageDef.GauthierE2.eval,
                Mettapedia.GSLT.LanguageDef.GauthierE2.intlSignature,
                Mettapedia.GSLT.LanguageDef.GauthierE2.orgSignature,
                Mettapedia.GSLT.LanguageDef.GauthierE2.listOps,
                Mettapedia.GSLT.LanguageDef.GauthierE1.entryAt,
                Mettapedia.GSLT.LanguageDef.GauthierE1.listGet?,
                Mettapedia.GSLT.LanguageDef.GauthierE1.entry] at heval
              subst values
              simp [Mettapedia.GSLT.LanguageDef.GauthierE2.head?] at hhead
              subst value
              simpa [modkAnalyzeFuel, orgE1Signature, entryAt, listGet?, entry] using hy

/-- The actual E2 `intlSignature` observation boundary used by GSLT2GSLT. -/
def e2Semantics : FuelObservationSemantics Prog ObservedTerm where
  emitsAt := fun fuel program obs =>
    Mettapedia.GSLT.LanguageDef.GauthierE2BigStepGSLT.MemoEmitsAt
      Mettapedia.GSLT.LanguageDef.GauthierE2.intlSignature fuel program
      obs.seedValue obs.value

abbrev MemoReproducesAt (program : Prog) (obs : ObservedTerm) : Prop :=
  SemanticReproducesAt e2Semantics program obs

abbrev MemoReproduces (program : Prog) (target : List ObservedTerm) : Prop :=
  SemanticReproduces e2Semantics program target

/--
The scalar residue analysis is a hard E2 constraint only on its proved core
fragment.  Outside that fragment the implication is vacuous, so the mask
conservatively allows the candidate rather than extrapolating a theorem.
-/
def MemoCoreModKCompatible (k : Nat) (program : Prog) (obs : ObservedTerm) : Prop :=
  coreOnly program = true → ModKCompatible k program obs

/-- Certified mod-k hard mask for the proved E2 core fragment. -/
def memoCoreModKMask (k : Nat) : CertifiedSemanticMask e2Semantics where
  allows := MemoCoreModKCompatible k
  emissionAllowed := by
    intro program obs fuel hemits hcore
    change Mettapedia.GSLT.LanguageDef.GauthierE2BigStepGSLT.MemoEmitsAt
      Mettapedia.GSLT.LanguageDef.GauthierE2.intlSignature fuel program
      obs.seedValue obs.value at hemits
    rw [Mettapedia.GSLT.LanguageDef.GauthierE2BigStepGSLT.memoEmitsAt_iff] at hemits
    rcases hemits with ⟨values, heval, hhead⟩
    unfold ModKCompatible certifiedModKAnalysis modkAnalyzeWith
    exact CoreProg.memo_modk_sound (CoreProg.of_coreOnly hcore)
      (progHeight program + 1) fuel
      (ResidueInfo.exact k obs.seedValue) (ResidueInfo.exact k 0)
      obs.seedValue 0 [] []
      Mettapedia.GSLT.LanguageDef.GauthierE2.defaultWorld values obs.value
      (ResidueInfo.exact_self k obs.seedValue) (ResidueInfo.exact_self k 0)
      heval hhead

def MemoModKIncompatible (k : Nat) (program : Prog)
    (target : List ObservedTerm) : Prop :=
  ∃ obs, obs ∈ target ∧ ¬ MemoCoreModKCompatible k program obs

theorem memoModKIncompatible_iff_rejectedBy {k : Nat} {program : Prog}
    {target : List ObservedTerm} :
    MemoModKIncompatible k program target ↔
      RejectedBy (memoCoreModKMask k) program target :=
  Iff.rfl

/--
T4 E2 crown: certified core-fragment mod-k pruning cannot remove a program
that reproduces every requested observation under the live memo evaluator.
-/
theorem memo_certified_modk_pruning_via_mask {k : Nat} {program : Prog}
    {target : List ObservedTerm}
    (hbad : MemoModKIncompatible k program target) :
    ¬ MemoReproduces program target :=
  certifiedMask_recall_preserving (memoCoreModKMask k)
    (memoModKIncompatible_iff_rejectedBy.mp hbad)

/-! E2 positive, negative, and conservative-fallback canaries. -/

example : (memoCoreModKMask 3).allows oneProg observedOneAt0 := by
  intro _hcore
  exact one_mod3_compatible_with_one_observation

example : ¬ (memoCoreModKMask 3).allows zeroProg observedOneAt0 := by
  intro hallows
  exact zero_mod3_incompatible_with_one_observation (hallows rfl)

example : (memoCoreModKMask 3).allows
    (.node 14 [.node 1 [], .node 1 []]) observedOneAt0 := by
  intro hcore
  simp [coreOnly] at hcore

example : MemoReproducesAt oneProg observedOneAt0 := by
  refine ⟨2, ?_⟩
  change Mettapedia.GSLT.LanguageDef.GauthierE2BigStepGSLT.MemoEmitsAt
    Mettapedia.GSLT.LanguageDef.GauthierE2.intlSignature 2 oneProg 0 1
  rw [Mettapedia.GSLT.LanguageDef.GauthierE2BigStepGSLT.memoEmitsAt_iff]
  refine ⟨[1], ?_, rfl⟩
  simp [oneProg, Mettapedia.GSLT.LanguageDef.GauthierE2.eval,
    Mettapedia.GSLT.LanguageDef.GauthierE2.intlSignature,
    Mettapedia.GSLT.LanguageDef.GauthierE2.orgSignature,
    Mettapedia.GSLT.LanguageDef.GauthierE2.listOps,
    Mettapedia.GSLT.LanguageDef.GauthierE1.entryAt,
    Mettapedia.GSLT.LanguageDef.GauthierE1.listGet?,
    Mettapedia.GSLT.LanguageDef.GauthierE1.entry]

example : ¬ MemoReproduces zeroProg oneTarget :=
  memo_certified_modk_pruning_via_mask
    ⟨observedOneAt0, by simp [oneTarget], fun hallows =>
      zero_mod3_incompatible_with_one_observation (hallows rfl)⟩

end Mettapedia.OSLF.Framework.GauthierOEISCertifiedMask
