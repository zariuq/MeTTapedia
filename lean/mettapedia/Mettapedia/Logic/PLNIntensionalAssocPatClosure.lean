import Mettapedia.Logic.PLNCanonicalAPI

/-!
# Chapter-12 ASSOC+PAT Closure

This module adds theorem-level closure for mixed ASSOC+PAT inheritance channels:

1. Generic WM→OSLF threshold endpoint for 3-ary mixed laws.
2. Model-based endpoint that consumes a concrete `AssocPatSemanticModel`.
3. A concrete nontrivial ASSOC+PAT semantic model where PAT contributes materially,
   together with end-to-end threshold acceptance.
-/

namespace Mettapedia.Logic.PLNCanonical

/-- Mixed (extensional+ASSOC+PAT) rewrite-to-threshold endpoint under selected ITV semantics. -/
theorem intensional_mixed_assocPat_threshold_atom_of_interval
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query]
    (i : WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (ctx : CtxOfInterval i)
    (enc : InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query)
    (combine : Evidence → Evidence → Evidence → Evidence)
    (Side : Prop)
    (hSound : Side →
      PLNIntensionalWorldModel.InheritanceQueryBuilder.MixedPolicyAssocPat
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc combine)
    (W : State)
    (a0 : String) (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : ITV → ℝ) (tau : ℝ)
    (hSide : Side)
    (hTau : tau ≤ coord ((semanticsOfInterval i).eval ctx
      (combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.intensionalAssocEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.intensionalPATEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)))) :
    Mettapedia.OSLF.Formula.sem R
      (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
        (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Query)
        (Ctx := CtxOfInterval i)
        (semanticsOfInterval i) ctx W tau coord
        (patternInheritanceQueryOfAtom_mixed enc))
      (.atom a0) p := by
  simpa [patternInheritanceQueryOfAtom_mixed] using
    (PLNWMOSLFBridgeITVTyped.wmRewriteRuleSigma_itv_threshold_atom
      (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Query)
      (Ctx := CtxOfInterval i)
      R (semanticsOfInterval i) ctx tau coord
      (r := PLNIntensionalWorldModel.InheritanceQueryBuilder.mixedRewriteRule_of_assoc_pat
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query)
        enc combine Side hSound (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
      hSide W
      (queryOfAtom := patternInheritanceQueryOfAtom_mixed enc)
      (a := a0) (p := p) (hEnc := rfl) hTau)

/-- Model-based mixed (ASSOC+PAT) endpoint: discharges side conditions via
`AssocPatSemanticModel`. -/
theorem intensional_mixed_assocPat_threshold_atom_of_interval_of_assocPatSemanticModel
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query]
    (i : WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (ctx : CtxOfInterval i)
    (enc : InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query)
    (model : PLNIntensionalWorldModel.InheritanceQueryBuilder.AssocPatSemanticModel
      (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) (Query := Query) enc)
    (W : State)
    (a0 : String) (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : ITV → ℝ) (tau : ℝ)
    (hTau : tau ≤ coord ((semanticsOfInterval i).eval ctx
      (model.combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (model.scoreModel.scoreToEvidence
          (model.scoreModel.assocScore W (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p))
        (model.scoreModel.scoreToEvidence
          (model.scoreModel.patScore W (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p))))) :
    Mettapedia.OSLF.Formula.sem R
      (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
        (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Query)
        (Ctx := CtxOfInterval i)
        (semanticsOfInterval i) ctx W tau coord
        (patternInheritanceQueryOfAtom_mixed enc))
      (.atom a0) p := by
  have hAssoc :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.intensionalAssocEvidence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) W enc
        (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p =
      model.scoreModel.scoreToEvidence
        (model.scoreModel.assocScore W (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p) :=
    model.scoreModel.assoc_sound W (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p
  have hPat :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.intensionalPATEvidence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) W enc
        (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p =
      model.scoreModel.scoreToEvidence
        (model.scoreModel.patScore W (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p) :=
    model.scoreModel.pat_sound W (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p
  have hTau' : tau ≤ coord ((semanticsOfInterval i).eval ctx
      (model.combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.intensionalAssocEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.intensionalPATEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p))) := by
    simpa [hAssoc, hPat] using hTau
  exact intensional_mixed_assocPat_threshold_atom_of_interval
    (State := State) (Query := Query)
    i R ctx enc model.combine True
    (by
      intro _
      exact PLNIntensionalWorldModel.InheritanceQueryBuilder.mixedPolicyAssocPat_of_assocPatSemanticModel
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc model)
    W a0 p coord tau trivial hTau'

/-- Bayes-normal selector wrapper for the model-based ASSOC+PAT endpoint. -/
theorem intensional_mixed_assocPat_threshold_atom_bayesNormal_of_assocPatSemanticModel
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query]
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (ctx : CtxOfInterval .bayesNormal)
    (enc : InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query)
    (model : PLNIntensionalWorldModel.InheritanceQueryBuilder.AssocPatSemanticModel
      (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) (Query := Query) enc)
    (W : State)
    (a0 : String) (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : ITV → ℝ) (tau : ℝ)
    (hTau : tau ≤ coord ((semanticsOfInterval .bayesNormal).eval ctx
      (model.combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (model.scoreModel.scoreToEvidence
          (model.scoreModel.assocScore W (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p))
        (model.scoreModel.scoreToEvidence
          (model.scoreModel.patScore W (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p))))) :
    Mettapedia.OSLF.Formula.sem R
      (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
        (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Query)
        (Ctx := CtxOfInterval .bayesNormal)
        (semanticsOfInterval .bayesNormal) ctx W tau coord
        (patternInheritanceQueryOfAtom_mixed enc))
      (.atom a0) p :=
  intensional_mixed_assocPat_threshold_atom_of_interval_of_assocPatSemanticModel
    (State := State) (Query := Query)
    .bayesNormal R ctx enc model W a0 p coord tau hTau

/-- Bayes-exact selector wrapper for the model-based ASSOC+PAT endpoint. -/
theorem intensional_mixed_assocPat_threshold_atom_bayesExact_of_assocPatSemanticModel
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query]
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (ctx : CtxOfInterval .bayesExact)
    (enc : InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query)
    (model : PLNIntensionalWorldModel.InheritanceQueryBuilder.AssocPatSemanticModel
      (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) (Query := Query) enc)
    (W : State)
    (a0 : String) (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : ITV → ℝ) (tau : ℝ)
    (hTau : tau ≤ coord ((semanticsOfInterval .bayesExact).eval ctx
      (model.combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (model.scoreModel.scoreToEvidence
          (model.scoreModel.assocScore W (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p))
        (model.scoreModel.scoreToEvidence
          (model.scoreModel.patScore W (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p))))) :
    Mettapedia.OSLF.Formula.sem R
      (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
        (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Query)
        (Ctx := CtxOfInterval .bayesExact)
        (semanticsOfInterval .bayesExact) ctx W tau coord
        (patternInheritanceQueryOfAtom_mixed enc))
      (.atom a0) p :=
  intensional_mixed_assocPat_threshold_atom_of_interval_of_assocPatSemanticModel
    (State := State) (Query := Query)
    .bayesExact R ctx enc model W a0 p coord tau hTau

/-- Walley-IDM selector wrapper for the model-based ASSOC+PAT endpoint. -/
theorem intensional_mixed_assocPat_threshold_atom_walley_of_assocPatSemanticModel
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query]
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (ctx : CtxOfInterval .walleyIDM)
    (enc : InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query)
    (model : PLNIntensionalWorldModel.InheritanceQueryBuilder.AssocPatSemanticModel
      (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) (Query := Query) enc)
    (W : State)
    (a0 : String) (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : ITV → ℝ) (tau : ℝ)
    (hTau : tau ≤ coord ((semanticsOfInterval .walleyIDM).eval ctx
      (model.combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (model.scoreModel.scoreToEvidence
          (model.scoreModel.assocScore W (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p))
        (model.scoreModel.scoreToEvidence
          (model.scoreModel.patScore W (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p))))) :
    Mettapedia.OSLF.Formula.sem R
      (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
        (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Query)
        (Ctx := CtxOfInterval .walleyIDM)
        (semanticsOfInterval .walleyIDM) ctx W tau coord
        (patternInheritanceQueryOfAtom_mixed enc))
      (.atom a0) p :=
  intensional_mixed_assocPat_threshold_atom_of_interval_of_assocPatSemanticModel
    (State := State) (Query := Query)
    .walleyIDM R ctx enc model W a0 p coord tau hTau

end Mettapedia.Logic.PLNCanonical

namespace Mettapedia.Logic.PLNIntensionalAssocPatConcrete

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNIntensionalWorldModel
open Mettapedia.OSLF.MeTTaIL.Syntax
open scoped ENNReal

/-- Query family with an explicit mixed channel. -/
inductive ConcreteQuery where
  | ext : Pattern → Pattern → ConcreteQuery
  | assoc : Pattern → Pattern → ConcreteQuery
  | pat : Pattern → Pattern → ConcreteQuery
  | mix : Pattern → Pattern → ConcreteQuery
  deriving DecidableEq, Repr

/-- Nonnegative score channel used for ext/ASSOC/PAT components. -/
abbrev ScoreChannel := Pattern → Pattern → NNReal

/-- Triple score state: (extensional, ASSOC, PAT). -/
abbrev ConcreteState := ScoreChannel × ScoreChannel × ScoreChannel

noncomputable instance : EvidenceType ConcreteState where
  toAddCommMonoid := inferInstance

/-- Evidence embedding for nonnegative scores. -/
def scoreToEvidenceNNReal (r : NNReal) : EvidenceQuantale.Evidence := ⟨(r : ℝ≥0∞), 0⟩

/-- Real-valued evidence embedding (used by score-model interfaces). -/
def scoreToEvidenceReal (s : ℝ) : EvidenceQuantale.Evidence := ⟨ENNReal.ofReal s, 0⟩

@[simp] theorem scoreToEvidenceReal_ofNNReal (r : NNReal) :
    scoreToEvidenceReal (r : ℝ) = scoreToEvidenceNNReal r := by
  ext <;> simp [scoreToEvidenceReal, scoreToEvidenceNNReal]

/-- Nontrivial mixed law: extensional + ASSOC + PAT evidence aggregation. -/
noncomputable def combineAssocPatSum
    (eExt eAssoc ePat : EvidenceQuantale.Evidence) : EvidenceQuantale.Evidence :=
  eExt + eAssoc + ePat

noncomputable instance : WorldModel ConcreteState ConcreteQuery where
  evidence W q :=
    match q with
    | .ext a b => scoreToEvidenceNNReal (W.1 a b)
    | .assoc a b => scoreToEvidenceNNReal (W.2.1 a b)
    | .pat a b => scoreToEvidenceNNReal (W.2.2 a b)
    | .mix a b =>
        combineAssocPatSum
          (scoreToEvidenceNNReal (W.1 a b))
          (scoreToEvidenceNNReal (W.2.1 a b))
          (scoreToEvidenceNNReal (W.2.2 a b))
  evidence_add W₁ W₂ q := by
    cases q <;> ext <;>
      simp [scoreToEvidenceNNReal, combineAssocPatSum, add_assoc, add_left_comm]

/-- Canonical query builder into the concrete 4-channel query family. -/
def enc : PLNIntensionalWorldModel.InheritanceQueryBuilder Pattern ConcreteQuery where
  extensional := ConcreteQuery.ext
  intensionalAssoc := ConcreteQuery.assoc
  intensionalPAT := ConcreteQuery.pat
  mixed := ConcreteQuery.mix

/-- Canonical ASSOC/PAT score model for the concrete state. -/
noncomputable def scoreModel :
    PLNIntensionalWorldModel.InheritanceQueryBuilder.IntensionalScoreModel
      (State := ConcreteState) (Atom := Pattern) (Query := ConcreteQuery) enc where
  assocScore := fun W a b => (W.2.1 a b : ℝ)
  patScore := fun W a b => (W.2.2 a b : ℝ)
  scoreToEvidence := scoreToEvidenceReal
  scoreToEvidence_mono := by
      intro x y hxy
      exact ⟨ENNReal.ofReal_le_ofReal hxy, le_rfl⟩
  assoc_sound := by
    intro W a b
    change scoreToEvidenceNNReal (W.2.1 a b) = scoreToEvidenceReal (W.2.1 a b : ℝ)
    simp [scoreToEvidenceReal_ofNNReal]
  pat_sound := by
    intro W a b
    change scoreToEvidenceNNReal (W.2.2 a b) = scoreToEvidenceReal (W.2.2 a b : ℝ)
    simp [scoreToEvidenceReal_ofNNReal]

/-- The concrete mixed channel is exactly ext+ASSOC+PAT under the score model. -/
theorem mixed_sound :
    PLNIntensionalWorldModel.InheritanceQueryBuilder.MixedAssocPatScoreCorrespondence
      (State := ConcreteState) (Atom := Pattern) (Query := ConcreteQuery)
      enc combineAssocPatSum
      scoreModel.assocScore scoreModel.patScore scoreModel.scoreToEvidence := by
  intro W a b
  change combineAssocPatSum
      (scoreToEvidenceNNReal (W.1 a b))
      (scoreToEvidenceNNReal (W.2.1 a b))
      (scoreToEvidenceNNReal (W.2.2 a b))
    =
    combineAssocPatSum
      (scoreToEvidenceNNReal (W.1 a b))
      (scoreToEvidenceReal (W.2.1 a b : ℝ))
      (scoreToEvidenceReal (W.2.2 a b : ℝ))
  simp [scoreToEvidenceReal_ofNNReal]

/-- Concrete nontrivial ASSOC+PAT semantic package for Chapter 12. -/
noncomputable def assocPatModel :
    PLNIntensionalWorldModel.InheritanceQueryBuilder.AssocPatSemanticModel
      (State := ConcreteState) (Atom := Pattern) (Query := ConcreteQuery) enc where
  scoreModel := scoreModel
  combine := combineAssocPatSum
  mixed_sound := mixed_sound

/-- Derived policy law from the concrete semantic package. -/
theorem mixedPolicy_assocPat :
    PLNIntensionalWorldModel.InheritanceQueryBuilder.MixedPolicyAssocPat
      (State := ConcreteState) (Atom := Pattern) (Query := ConcreteQuery)
      enc combineAssocPatSum :=
  PLNIntensionalWorldModel.InheritanceQueryBuilder.mixedPolicyAssocPat_of_assocPatSemanticModel
    (State := ConcreteState) (Atom := Pattern) (Query := ConcreteQuery)
    enc assocPatModel

/-- Constant score channel helper. -/
def constScore (r : NNReal) : ScoreChannel := fun _ _ => r

/-- Concrete witness state with nonzero PAT contribution. -/
def Wdemo : ConcreteState :=
  (constScore 3, constScore 2, constScore 1)

/-- PAT channel contributes nontrivially in the concrete model. -/
theorem pat_channel_nontrivial :
    PLNIntensionalWorldModel.InheritanceQueryBuilder.intensionalPATEvidence
        (State := ConcreteState) (Atom := Pattern) (Query := ConcreteQuery)
        Wdemo enc (Pattern.fvar "a0") (Pattern.fvar "p") ≠ 0 := by
  have h1 : scoreToEvidenceNNReal 1 ≠ (0 : EvidenceQuantale.Evidence) := by
    intro h
    have h10 := congrArg EvidenceQuantale.Evidence.pos h
    change (1 : ℝ≥0∞) = 0 at h10
    exact one_ne_zero h10
  simpa [Wdemo, constScore, scoreToEvidenceNNReal,
    PLNIntensionalWorldModel.InheritanceQueryBuilder.intensionalPATEvidence,
    PLNIntensionalWorldModel.InheritanceQueryBuilder.patQ, enc] using h1

/-- Mixed channel is strictly richer than ext+ASSOC when PAT is nonzero. -/
theorem mixed_not_assoc_only :
    PLNIntensionalWorldModel.InheritanceQueryBuilder.mixedEvidence
        (State := ConcreteState) (Atom := Pattern) (Query := ConcreteQuery)
        Wdemo enc (Pattern.fvar "a0") (Pattern.fvar "p") ≠
      PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
        (State := ConcreteState) (Atom := Pattern) (Query := ConcreteQuery)
        Wdemo enc (Pattern.fvar "a0") (Pattern.fvar "p") +
      PLNIntensionalWorldModel.InheritanceQueryBuilder.intensionalAssocEvidence
        (State := ConcreteState) (Atom := Pattern) (Query := ConcreteQuery)
        Wdemo enc (Pattern.fvar "a0") (Pattern.fvar "p") := by
  intro hEq
  have hmix :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.mixedEvidence
        (State := ConcreteState) (Atom := Pattern) (Query := ConcreteQuery)
        Wdemo enc (Pattern.fvar "a0") (Pattern.fvar "p")
      = (scoreToEvidenceNNReal 3 + scoreToEvidenceNNReal 2) + scoreToEvidenceNNReal 1 := by
    rfl
  have hext :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
        (State := ConcreteState) (Atom := Pattern) (Query := ConcreteQuery)
        Wdemo enc (Pattern.fvar "a0") (Pattern.fvar "p")
      = scoreToEvidenceNNReal 3 := by
    rfl
  have hassoc :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.intensionalAssocEvidence
        (State := ConcreteState) (Atom := Pattern) (Query := ConcreteQuery)
        Wdemo enc (Pattern.fvar "a0") (Pattern.fvar "p")
      = scoreToEvidenceNNReal 2 := by
    rfl
  have hEq'' :
      (scoreToEvidenceNNReal 3 + scoreToEvidenceNNReal 2) + scoreToEvidenceNNReal 1 =
        scoreToEvidenceNNReal 3 + scoreToEvidenceNNReal 2 := by
    simpa [hmix, hext, hassoc] using hEq
  have h65 : (6 : ℝ≥0∞) = 5 := by
    simpa [scoreToEvidenceNNReal, Evidence.hplus_def, add_assoc, add_left_comm, add_comm] using
      congrArg EvidenceQuantale.Evidence.pos hEq''
  norm_num at h65

/-- End-to-end Chapter-12 ASSOC+PAT theorem:
Bayes-normal selector, lower threshold, concrete semantic model. -/
theorem end_to_end_assocPat_bayesNormal_lower :
    Mettapedia.OSLF.Formula.sem (fun _ _ => True)
      (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
        (State := ConcreteState)
        (Srt := PLNIntensionalWorldModel.InheritanceSort)
        (Query := PLNIntensionalWorldModel.InheritanceQueryFamily ConcreteQuery)
        (Ctx := Mettapedia.Logic.PLNCanonical.CtxOfInterval .bayesNormal)
        (Mettapedia.Logic.PLNCanonical.semanticsOfInterval .bayesNormal)
        BinaryContext.uniform Wdemo
        0 (fun itv => itv.lower)
        (Mettapedia.Logic.PLNCanonical.patternInheritanceQueryOfAtom_mixed enc))
      (.atom "a0") (Pattern.fvar "p") := by
  have hTau :
      0 ≤ (fun itv => itv.lower)
        ((Mettapedia.Logic.PLNCanonical.semanticsOfInterval .bayesNormal).eval BinaryContext.uniform
          (assocPatModel.combine
            (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
              (State := ConcreteState) (Atom := Pattern) (Query := ConcreteQuery)
              Wdemo enc (Pattern.fvar "a0") (Pattern.fvar "p"))
            (assocPatModel.scoreModel.scoreToEvidence
              (assocPatModel.scoreModel.assocScore Wdemo (Pattern.fvar "a0") (Pattern.fvar "p")))
            (assocPatModel.scoreModel.scoreToEvidence
              (assocPatModel.scoreModel.patScore Wdemo (Pattern.fvar "a0") (Pattern.fvar "p"))))) := by
    simpa using
      (((Mettapedia.Logic.PLNCanonical.semanticsOfInterval .bayesNormal).eval BinaryContext.uniform
        (assocPatModel.combine
          (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
            (State := ConcreteState) (Atom := Pattern) (Query := ConcreteQuery)
            Wdemo enc (Pattern.fvar "a0") (Pattern.fvar "p"))
          (assocPatModel.scoreModel.scoreToEvidence
            (assocPatModel.scoreModel.assocScore Wdemo (Pattern.fvar "a0") (Pattern.fvar "p")))
          (assocPatModel.scoreModel.scoreToEvidence
            (assocPatModel.scoreModel.patScore Wdemo (Pattern.fvar "a0") (Pattern.fvar "p"))))).lower_in_unit.1)
  exact Mettapedia.Logic.PLNCanonical.intensional_mixed_assocPat_threshold_atom_bayesNormal_of_assocPatSemanticModel
    (State := ConcreteState) (Query := ConcreteQuery)
    (R := fun _ _ => True) BinaryContext.uniform enc assocPatModel
    Wdemo "a0" (Pattern.fvar "p") (fun itv => itv.lower) 0 hTau

/-- End-to-end Chapter-12 ASSOC+PAT theorem:
Bayes-exact selector, lower threshold, concrete semantic model. -/
theorem end_to_end_assocPat_bayesExact_lower :
    Mettapedia.OSLF.Formula.sem (fun _ _ => True)
      (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
        (State := ConcreteState)
        (Srt := PLNIntensionalWorldModel.InheritanceSort)
        (Query := PLNIntensionalWorldModel.InheritanceQueryFamily ConcreteQuery)
        (Ctx := Mettapedia.Logic.PLNCanonical.CtxOfInterval .bayesExact)
        (Mettapedia.Logic.PLNCanonical.semanticsOfInterval .bayesExact)
        BinaryContext.uniform Wdemo
        0 (fun itv => itv.lower)
        (Mettapedia.Logic.PLNCanonical.patternInheritanceQueryOfAtom_mixed enc))
      (.atom "a0") (Pattern.fvar "p") := by
  have hTau :
      0 ≤ (fun itv => itv.lower)
        ((Mettapedia.Logic.PLNCanonical.semanticsOfInterval .bayesExact).eval BinaryContext.uniform
          (assocPatModel.combine
            (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
              (State := ConcreteState) (Atom := Pattern) (Query := ConcreteQuery)
              Wdemo enc (Pattern.fvar "a0") (Pattern.fvar "p"))
            (assocPatModel.scoreModel.scoreToEvidence
              (assocPatModel.scoreModel.assocScore Wdemo (Pattern.fvar "a0") (Pattern.fvar "p")))
            (assocPatModel.scoreModel.scoreToEvidence
              (assocPatModel.scoreModel.patScore Wdemo (Pattern.fvar "a0") (Pattern.fvar "p"))))) := by
    simpa using
      (((Mettapedia.Logic.PLNCanonical.semanticsOfInterval .bayesExact).eval BinaryContext.uniform
        (assocPatModel.combine
          (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
            (State := ConcreteState) (Atom := Pattern) (Query := ConcreteQuery)
            Wdemo enc (Pattern.fvar "a0") (Pattern.fvar "p"))
          (assocPatModel.scoreModel.scoreToEvidence
            (assocPatModel.scoreModel.assocScore Wdemo (Pattern.fvar "a0") (Pattern.fvar "p")))
          (assocPatModel.scoreModel.scoreToEvidence
            (assocPatModel.scoreModel.patScore Wdemo (Pattern.fvar "a0") (Pattern.fvar "p"))))).lower_in_unit.1)
  exact Mettapedia.Logic.PLNCanonical.intensional_mixed_assocPat_threshold_atom_bayesExact_of_assocPatSemanticModel
    (State := ConcreteState) (Query := ConcreteQuery)
    (R := fun _ _ => True) BinaryContext.uniform enc assocPatModel
    Wdemo "a0" (Pattern.fvar "p") (fun itv => itv.lower) 0 hTau

/-- End-to-end Chapter-12 ASSOC+PAT theorem:
Walley selector, lower threshold, concrete semantic model. -/
theorem end_to_end_assocPat_walley_lower :
    Mettapedia.OSLF.Formula.sem (fun _ _ => True)
      (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
        (State := ConcreteState)
        (Srt := PLNIntensionalWorldModel.InheritanceSort)
        (Query := PLNIntensionalWorldModel.InheritanceQueryFamily ConcreteQuery)
        (Ctx := Mettapedia.Logic.PLNCanonical.CtxOfInterval .walleyIDM)
        (Mettapedia.Logic.PLNCanonical.semanticsOfInterval .walleyIDM)
        Mettapedia.Logic.PLNWorldModel.IDMPredictiveContext.default Wdemo
        0 (fun itv => itv.lower)
        (Mettapedia.Logic.PLNCanonical.patternInheritanceQueryOfAtom_mixed enc))
      (.atom "a0") (Pattern.fvar "p") := by
  have hTau :
      0 ≤ (fun itv => itv.lower)
        ((Mettapedia.Logic.PLNCanonical.semanticsOfInterval .walleyIDM).eval
          Mettapedia.Logic.PLNWorldModel.IDMPredictiveContext.default
          (assocPatModel.combine
            (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
              (State := ConcreteState) (Atom := Pattern) (Query := ConcreteQuery)
              Wdemo enc (Pattern.fvar "a0") (Pattern.fvar "p"))
            (assocPatModel.scoreModel.scoreToEvidence
              (assocPatModel.scoreModel.assocScore Wdemo (Pattern.fvar "a0") (Pattern.fvar "p")))
            (assocPatModel.scoreModel.scoreToEvidence
              (assocPatModel.scoreModel.patScore Wdemo (Pattern.fvar "a0") (Pattern.fvar "p"))))) := by
    simpa using
      (((Mettapedia.Logic.PLNCanonical.semanticsOfInterval .walleyIDM).eval
        Mettapedia.Logic.PLNWorldModel.IDMPredictiveContext.default
        (assocPatModel.combine
          (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
            (State := ConcreteState) (Atom := Pattern) (Query := ConcreteQuery)
            Wdemo enc (Pattern.fvar "a0") (Pattern.fvar "p"))
          (assocPatModel.scoreModel.scoreToEvidence
            (assocPatModel.scoreModel.assocScore Wdemo (Pattern.fvar "a0") (Pattern.fvar "p")))
          (assocPatModel.scoreModel.scoreToEvidence
            (assocPatModel.scoreModel.patScore Wdemo (Pattern.fvar "a0") (Pattern.fvar "p"))))).lower_in_unit.1)
  exact Mettapedia.Logic.PLNCanonical.intensional_mixed_assocPat_threshold_atom_walley_of_assocPatSemanticModel
    (State := ConcreteState) (Query := ConcreteQuery)
    (R := fun _ _ => True) Mettapedia.Logic.PLNWorldModel.IDMPredictiveContext.default enc assocPatModel
    Wdemo "a0" (Pattern.fvar "p") (fun itv => itv.lower) 0 hTau

end Mettapedia.Logic.PLNIntensionalAssocPatConcrete
