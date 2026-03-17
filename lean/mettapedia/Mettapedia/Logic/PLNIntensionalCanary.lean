import Mettapedia.Logic.PLNIntensionalWorldModel
import Mettapedia.Logic.PLNCanonicalAPI

/-!
# Chapter 12 Intensional-Inheritance Canaries

Executable fixture theorems for Chapter-12 mixed-channel behavior:

1. Positive: extensional-projection mixed policy returns extensional evidence.
2. Positive: ASSOC-projection mixed policy returns ASSOC evidence.
3. Negative: these two projections are not equivalent on a split-evidence fixture.
-/

namespace Mettapedia.Logic.PLNIntensionalCanary

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNIntensionalWorldModel
open Mettapedia.OSLF.MeTTaIL.Syntax
open scoped ENNReal

/-- Toy untyped query family for Chapter-12 inheritance channels. -/
inductive ToyInheritanceQuery where
  | ext : Bool → Bool → ToyInheritanceQuery
  | assoc : Bool → Bool → ToyInheritanceQuery
  | pat : Bool → Bool → ToyInheritanceQuery
  deriving DecidableEq, Repr

/-- Triple-state fixture: extensional / ASSOC / PAT evidence channels. -/
abbrev ToyState := BinaryEvidence × BinaryEvidence × BinaryEvidence

noncomputable instance : EvidenceType ToyState where
  toAddCommMonoid := inferInstance

instance : BinaryWorldModel ToyState ToyInheritanceQuery where
  evidence W q :=
    match q with
    | .ext _ _ => W.1
    | .assoc _ _ => W.2.1
    | .pat _ _ => W.2.2
  evidence_add W₁ W₂ q := by
    cases q <;> simp [Prod.fst_add, Prod.snd_add]

def toyExt (a b : Bool) : ToyInheritanceQuery := .ext a b
def toyAssoc (a b : Bool) : ToyInheritanceQuery := .assoc a b
def toyPat (a b : Bool) : ToyInheritanceQuery := .pat a b

/-- Mixed-query policy that projects to the extensional channel. -/
def encMixedExtensional :
    InheritanceQueryBuilder Bool ToyInheritanceQuery :=
  InheritanceQueryBuilder.mixedAsExtensional toyExt toyAssoc toyPat

/-- Mixed-query policy that projects to the ASSOC channel. -/
def encMixedAssoc :
    InheritanceQueryBuilder Bool ToyInheritanceQuery :=
  InheritanceQueryBuilder.mixedAsAssoc toyExt toyAssoc toyPat

/-- Split fixture: extensional and ASSOC channels intentionally disagree. -/
def Wsplit : ToyState := (⟨3, 1⟩, ⟨1, 4⟩, ⟨0, 2⟩)

/-- Positive canary: extensional-projection mixed policy equals extensional evidence. -/
theorem canary_ch12_mixed_extensional_projection :
    InheritanceQueryBuilder.mixedEvidence
        (State := ToyState) (Atom := Bool) (Query := ToyInheritanceQuery)
        Wsplit encMixedExtensional true false
      =
    InheritanceQueryBuilder.extensionalEvidence
        (State := ToyState) (Atom := Bool) (Query := ToyInheritanceQuery)
        Wsplit encMixedExtensional true false := by
  rfl

/-- Positive canary: ASSOC-projection mixed policy equals ASSOC evidence. -/
theorem canary_ch12_mixed_assoc_projection :
    InheritanceQueryBuilder.mixedEvidence
        (State := ToyState) (Atom := Bool) (Query := ToyInheritanceQuery)
        Wsplit encMixedAssoc true false
      =
    InheritanceQueryBuilder.intensionalAssocEvidence
        (State := ToyState) (Atom := Bool) (Query := ToyInheritanceQuery)
        Wsplit encMixedAssoc true false := by
  rfl

/-- Negative canary (non-equivalence):
on `Wsplit`, extensional-projection and ASSOC-projection mixed policies diverge. -/
theorem canary_ch12_mixed_projection_non_equivalent :
    InheritanceQueryBuilder.mixedEvidence
        (State := ToyState) (Atom := Bool) (Query := ToyInheritanceQuery)
        Wsplit encMixedExtensional true false
      ≠
    InheritanceQueryBuilder.mixedEvidence
        (State := ToyState) (Atom := Bool) (Query := ToyInheritanceQuery)
        Wsplit encMixedAssoc true false := by
  intro hEq
  have hpos : (3 : ℝ≥0∞) = 1 := by
    exact congrArg BinaryEvidence.pos (by simpa [Wsplit, encMixedExtensional, encMixedAssoc,
      InheritanceQueryBuilder.mixedEvidence, InheritanceQueryBuilder.mixedQ,
      InheritanceQueryBuilder.mixedAsExtensional, InheritanceQueryBuilder.mixedAsAssoc,
      toyExt, toyAssoc] using hEq)
  norm_num at hpos

/-- Pattern-indexed query family for a concrete Ch.12 WM→OSLF threshold fixture. -/
inductive ToyPatternInheritanceQuery where
  | ext : Pattern → Pattern → ToyPatternInheritanceQuery
  | assoc : Pattern → Pattern → ToyPatternInheritanceQuery
  | pat : Pattern → Pattern → ToyPatternInheritanceQuery
  deriving DecidableEq, Repr

instance : BinaryWorldModel ToyState ToyPatternInheritanceQuery where
  evidence W q :=
    match q with
    | .ext _ _ => W.1
    | .assoc _ _ => W.2.1
    | .pat _ _ => W.2.2
  evidence_add W₁ W₂ q := by
    cases q <;> simp [Prod.fst_add, Prod.snd_add]

def toyPatternExt (a b : Pattern) : ToyPatternInheritanceQuery := .ext a b
def toyPatternAssoc (a b : Pattern) : ToyPatternInheritanceQuery := .assoc a b
def toyPatternPat (a b : Pattern) : ToyPatternInheritanceQuery := .pat a b

def encPatternMixedExtensional :
    InheritanceQueryBuilder Pattern ToyPatternInheritanceQuery :=
  InheritanceQueryBuilder.mixedAsExtensional toyPatternExt toyPatternAssoc toyPatternPat

def WsplitPattern : ToyState := Wsplit

/-- Concrete finite Ch.12 endpoint:
Bayes-normal selector + lower-threshold gate over the extensional-projection
mixed policy, composed through WM rewrite and OSLF truth transport. -/
theorem canary_ch12_end_to_end_bayesNormal_lower_threshold :
    Mettapedia.OSLF.Formula.sem (fun _ _ => True)
      (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
        (State := ToyState) (Srt := InheritanceSort)
        (Query := InheritanceQueryFamily ToyPatternInheritanceQuery)
        (Ctx := Mettapedia.Logic.PLNCanonical.CtxOfInterval .bayesNormal)
        (Mettapedia.Logic.PLNCanonical.semanticsOfInterval .bayesNormal)
        BinaryContext.uniform WsplitPattern
        0 (fun itv => itv.lower)
        (Mettapedia.Logic.PLNCanonical.patternInheritanceQueryOfAtom_mixed
          encPatternMixedExtensional))
      (.atom "a0") (Pattern.fvar "p") := by
  refine Mettapedia.Logic.PLNCanonical.intensional_mixed_assoc_threshold_atom_of_interval
    (State := ToyState) (Query := ToyPatternInheritanceQuery)
    .bayesNormal (R := fun _ _ => True) BinaryContext.uniform
    encPatternMixedExtensional (fun e _ => e) True ?_ WsplitPattern
    "a0" (Pattern.fvar "p") (fun itv => itv.lower) 0 trivial ?_
  · intro _
    exact InheritanceQueryBuilder.mixedPolicyAssoc_mixedAsExtensional
      (State := ToyState) (Atom := Pattern) (Query := ToyPatternInheritanceQuery)
      toyPatternExt toyPatternAssoc toyPatternPat
  · simpa [encPatternMixedExtensional, WsplitPattern,
      Mettapedia.Logic.PLNCanonical.patternInheritanceQueryOfAtom_mixed] using
      (((Mettapedia.Logic.PLNCanonical.semanticsOfInterval .bayesNormal).eval
        BinaryContext.uniform
        ((InheritanceQueryBuilder.extensionalEvidence
          (State := ToyState) (Atom := Pattern) (Query := ToyPatternInheritanceQuery)
          WsplitPattern encPatternMixedExtensional (Pattern.fvar "a0") (Pattern.fvar "p")))).lower_in_unit.1)

/-- Concrete finite Ch.12 endpoint:
Bayes-exact selector + lower-threshold gate over the extensional-projection
mixed policy, composed through WM rewrite and OSLF truth transport. -/
theorem canary_ch12_end_to_end_bayesExact_lower_threshold :
    Mettapedia.OSLF.Formula.sem (fun _ _ => True)
      (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
        (State := ToyState) (Srt := InheritanceSort)
        (Query := InheritanceQueryFamily ToyPatternInheritanceQuery)
        (Ctx := Mettapedia.Logic.PLNCanonical.CtxOfInterval .bayesExact)
        (Mettapedia.Logic.PLNCanonical.semanticsOfInterval .bayesExact)
        BinaryContext.uniform WsplitPattern
        0 (fun itv => itv.lower)
        (Mettapedia.Logic.PLNCanonical.patternInheritanceQueryOfAtom_mixed
          encPatternMixedExtensional))
      (.atom "a0") (Pattern.fvar "p") := by
  refine Mettapedia.Logic.PLNCanonical.intensional_mixed_assoc_threshold_atom_of_interval
    (State := ToyState) (Query := ToyPatternInheritanceQuery)
    .bayesExact (R := fun _ _ => True) BinaryContext.uniform
    encPatternMixedExtensional (fun e _ => e) True ?_ WsplitPattern
    "a0" (Pattern.fvar "p") (fun itv => itv.lower) 0 trivial ?_
  · intro _
    exact InheritanceQueryBuilder.mixedPolicyAssoc_mixedAsExtensional
      (State := ToyState) (Atom := Pattern) (Query := ToyPatternInheritanceQuery)
      toyPatternExt toyPatternAssoc toyPatternPat
  · simpa [encPatternMixedExtensional, WsplitPattern,
      Mettapedia.Logic.PLNCanonical.patternInheritanceQueryOfAtom_mixed] using
      (((Mettapedia.Logic.PLNCanonical.semanticsOfInterval .bayesExact).eval
        BinaryContext.uniform
        ((InheritanceQueryBuilder.extensionalEvidence
          (State := ToyState) (Atom := Pattern) (Query := ToyPatternInheritanceQuery)
          WsplitPattern encPatternMixedExtensional (Pattern.fvar "a0") (Pattern.fvar "p")))).lower_in_unit.1)

/-- Concrete finite Ch.12 endpoint:
Walley selector + lower-threshold gate over the extensional-projection
mixed policy, composed through WM rewrite and OSLF truth transport. -/
theorem canary_ch12_end_to_end_walley_lower_threshold :
    Mettapedia.OSLF.Formula.sem (fun _ _ => True)
      (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
        (State := ToyState) (Srt := InheritanceSort)
        (Query := InheritanceQueryFamily ToyPatternInheritanceQuery)
        (Ctx := Mettapedia.Logic.PLNCanonical.CtxOfInterval .walleyIDM)
        (Mettapedia.Logic.PLNCanonical.semanticsOfInterval .walleyIDM)
        Mettapedia.Logic.PLNWorldModel.IDMPredictiveContext.default WsplitPattern
        0 (fun itv => itv.lower)
        (Mettapedia.Logic.PLNCanonical.patternInheritanceQueryOfAtom_mixed
          encPatternMixedExtensional))
      (.atom "a0") (Pattern.fvar "p") := by
  refine Mettapedia.Logic.PLNCanonical.intensional_mixed_assoc_threshold_atom_of_interval
    (State := ToyState) (Query := ToyPatternInheritanceQuery)
    .walleyIDM (R := fun _ _ => True) Mettapedia.Logic.PLNWorldModel.IDMPredictiveContext.default
    encPatternMixedExtensional (fun e _ => e) True ?_ WsplitPattern
    "a0" (Pattern.fvar "p") (fun itv => itv.lower) 0 trivial ?_
  · intro _
    exact InheritanceQueryBuilder.mixedPolicyAssoc_mixedAsExtensional
      (State := ToyState) (Atom := Pattern) (Query := ToyPatternInheritanceQuery)
      toyPatternExt toyPatternAssoc toyPatternPat
  · simpa [encPatternMixedExtensional, WsplitPattern,
      Mettapedia.Logic.PLNCanonical.patternInheritanceQueryOfAtom_mixed] using
      (((Mettapedia.Logic.PLNCanonical.semanticsOfInterval .walleyIDM).eval
        Mettapedia.Logic.PLNWorldModel.IDMPredictiveContext.default
        ((InheritanceQueryBuilder.extensionalEvidence
          (State := ToyState) (Atom := Pattern) (Query := ToyPatternInheritanceQuery)
          WsplitPattern encPatternMixedExtensional (Pattern.fvar "a0") (Pattern.fvar "p")))).lower_in_unit.1)

end Mettapedia.Logic.PLNIntensionalCanary
