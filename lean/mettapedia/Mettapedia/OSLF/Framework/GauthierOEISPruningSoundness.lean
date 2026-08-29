import Mettapedia.OSLF.Framework.GauthierOEISNativeTypes

/-!
# Gauthier OEIS Property-Pruning Soundness

This file states and proves the admissibility theorem for pruning a candidate
program when its certified sign/parity analysis is incompatible with observed
target terms.
-/

namespace Mettapedia.OSLF.Framework.GauthierOEISPruningSoundness

open Mettapedia.GSLT.LanguageDef.GauthierE1
open Mettapedia.GSLT.LanguageDef.GauthierProperties
open Mettapedia.OSLF.Framework.GauthierOEISNativeTypes

/-- One observed target term at OEIS input `n`. -/
structure ObservedTerm where
  n : Nat
  value : Int
  deriving Repr

namespace ObservedTerm

/-- The concrete E1 seed value for this observation. -/
def seedValue (obs : ObservedTerm) : Int :=
  Int.ofNat obs.n

theorem seed_nonneg (obs : ObservedTerm) : 0 <= obs.seedValue := by
  exact Int.natCast_nonneg obs.n

end ObservedTerm

/-- A program reproduces one observed target term when the real E1 evaluator
returns exactly that value from the zero store, at some fuel. -/
def ReproducesAt (p : Prog) (obs : ObservedTerm) : Prop :=
  ∃ fuel st',
    eval fuel orgE1Signature p (seed obs.seedValue) Store.zero = some (obs.value, st')

/-- A program reproduces an observed target prefix when it reproduces every
listed observation. -/
def Reproduces (p : Prog) (target : List ObservedTerm) : Prop :=
  ∀ obs, obs ∈ target -> ReproducesAt p obs

/-- The certified analyzer allows this observed value by sign. -/
def SignCompatible (p : Prog) (obs : ObservedTerm) : Prop :=
  (certifiedSignAnalysis p).denote obs.value

/-- The certified analyzer allows this observed value by parity. -/
def ParityCompatible (p : Prog) (obs : ObservedTerm) : Prop :=
  (certifiedParityAnalysis p).denote obs.value

/-- A target is incompatible when at least one observed term violates the
certified sign or parity over-approximation for the candidate. -/
def AnalysisIncompatible (p : Prog) (target : List ObservedTerm) : Prop :=
  ∃ obs, obs ∈ target ∧ (¬ SignCompatible p obs ∨ ¬ ParityCompatible p obs)

/-- Native-type version of the same pruning check: a reproduced observation
must inhabit both certified observation native types. -/
def NativeIncompatible (p : Prog) (target : List ObservedTerm) : Prop :=
  ∃ obs, obs ∈ target ∧
    (¬ signNativeType.pred (evalObsPattern p obs.value) ∨
      ¬ parityNativeType.pred (evalObsPattern p obs.value))

theorem reproducesAt_sign_native {p : Prog} {obs : ObservedTerm}
    (h : ReproducesAt p obs) :
    signNativeType.pred (evalObsPattern p obs.value) := by
  rcases h with ⟨fuel, st', heval⟩
  exact signNativeType_sound obs.seed_nonneg heval

theorem reproducesAt_parity_native {p : Prog} {obs : ObservedTerm}
    (h : ReproducesAt p obs) :
    parityNativeType.pred (evalObsPattern p obs.value) := by
  rcases h with ⟨fuel, st', heval⟩
  exact parityNativeType_sound heval

/-- Native-type pruning is admissible: if a target observation cannot inhabit
the certified sign/parity native type, the candidate cannot reproduce the
target. -/
theorem native_property_pruning_admissible {p : Prog} {target : List ObservedTerm}
    (hbad : NativeIncompatible p target) :
    ¬ Reproduces p target := by
  intro hrep
  rcases hbad with ⟨obs, hmem, hobs⟩
  have hAt := hrep obs hmem
  rcases hobs with hsign | hparity
  · exact hsign (reproducesAt_sign_native hAt)
  · exact hparity (reproducesAt_parity_native hAt)

/-- Certified-analysis pruning is admissible: if the candidate's certified
sign/parity analysis is incompatible with any observed target term, pruning it
cannot discard a true reproducer. -/
theorem certified_property_pruning_admissible {p : Prog} {target : List ObservedTerm}
    (hbad : AnalysisIncompatible p target) :
    ¬ Reproduces p target := by
  intro hrep
  rcases hbad with ⟨obs, hmem, hobs⟩
  rcases hrep obs hmem with ⟨fuel, st', heval⟩
  rcases hobs with hsign | hparity
  · exact hsign (Seal.certified_sign_sound obs.seed_nonneg heval)
  · exact hparity (Seal.certified_parity_sound heval)

/-! ## Non-vacuity Canaries -/

def zeroProg : Prog := .node 0 []
def oneProg : Prog := .node 1 []

def observedZeroAt0 : ObservedTerm := { n := 0, value := 0 }
def observedOneAt0 : ObservedTerm := { n := 0, value := 1 }

def zeroTarget : List ObservedTerm := [observedZeroAt0]
def oneTarget : List ObservedTerm := [observedOneAt0]

/-- Local canary fact: the certified analyzer classifies constant zero as even. -/
theorem certifiedParity_zero : certifiedParityAnalysis zeroProg = .even := by
  simp [certifiedParityAnalysis, certifiedAnalyze, analysisSupported, analysisCert?,
    analysisCertFuel?, zeroProg, progHeight, coreOnly, analyze, analyzeWith, analyzeFuel,
    AbsVal.zero]

/-- Local canary fact: the certified analyzer classifies constant one as positive. -/
theorem certifiedSign_one : certifiedSignAnalysis oneProg = .pos := by
  simp [certifiedSignAnalysis, certifiedAnalyze, analysisSupported, analysisCert?,
    analysisCertFuel?, oneProg, progHeight, coreOnly, analyze, analyzeWith, analyzeFuel,
    AbsVal.one]

/-- Local canary fact: the certified analyzer classifies constant one as odd. -/
theorem certifiedParity_one : certifiedParityAnalysis oneProg = .odd := by
  simp [certifiedParityAnalysis, certifiedAnalyze, analysisSupported, analysisCert?,
    analysisCertFuel?, oneProg, progHeight, coreOnly, analyze, analyzeWith, analyzeFuel,
    AbsVal.one]

/-- The observed first value `1` is incompatible with constant-zero parity. -/
theorem zero_incompatible_with_one_observation :
    ¬ ParityCompatible zeroProg observedOneAt0 := by
  intro h
  rw [ParityCompatible, certifiedParity_zero] at h
  simp [observedOneAt0, ParityInfo.denote, EvenInt] at h
  rcases h with ⟨k, hk⟩
  omega

/-- The observed first value `1` is compatible with constant-one sign. -/
theorem one_sign_compatible_with_one_observation :
    SignCompatible oneProg observedOneAt0 := by
  rw [SignCompatible, certifiedSign_one]
  simp [observedOneAt0, SignInfo.denote]

/-- The observed first value `1` is compatible with constant-one parity. -/
theorem one_parity_compatible_with_one_observation :
    ParityCompatible oneProg observedOneAt0 := by
  rw [ParityCompatible, certifiedParity_one]
  simp [observedOneAt0, ParityInfo.denote, OddInt]

/-- Positive pruning canary: the constant-zero program is incompatible with
a target whose first observed value is `1`. -/
example : AnalysisIncompatible zeroProg oneTarget := by
  refine ⟨observedOneAt0, by simp [oneTarget], ?_⟩
  exact Or.inr zero_incompatible_with_one_observation

/-- The incompatible constant-zero candidate cannot reproduce the one-valued
target. -/
example : ¬ Reproduces zeroProg oneTarget :=
  certified_property_pruning_admissible
    (p := zeroProg) (target := oneTarget)
    (by
      refine ⟨observedOneAt0, by simp [oneTarget], ?_⟩
      exact Or.inr zero_incompatible_with_one_observation)

/-- Negative pruning canary: the constant-one program is compatible with the
one-valued target. -/
example : ¬ AnalysisIncompatible oneProg oneTarget := by
  intro hbad
  rcases hbad with ⟨obs, hmem, hobs⟩
  simp [oneTarget] at hmem
  subst obs
  rcases hobs with hsign | hparity
  · exact hsign one_sign_compatible_with_one_observation
  · exact hparity one_parity_compatible_with_one_observation

/-- The retained constant-one candidate really reproduces the one-valued
target. -/
example : Reproduces oneProg oneTarget := by
  intro obs hmem
  simp [oneTarget] at hmem
  subst obs
  refine ⟨1, Store.zero, ?_⟩
  simp [oneProg, observedOneAt0, ObservedTerm.seedValue, eval, orgE1Signature,
    entryAt, listGet?, entry, seed]

end Mettapedia.OSLF.Framework.GauthierOEISPruningSoundness
