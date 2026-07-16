import Mettapedia.GSLT.LanguageDef.CheckedSource

/-!
# Explicit conversion certificates through the generic checker

Conversion steps remain ordinary judgments and ordinary proof trees in the
validated presentation.  This module only checks that an explicit sequence of
such steps has the requested endpoints.  It adds no source-specific rule
branch and does not interpret certificate rejection as proof of inequality.
-/

namespace Mettapedia.GSLT.LanguageDef.ConversionCertificate

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CheckedSource

/-- Selects the ordinary binary judgment used for conversion steps. -/
structure ConversionProfile where
  judgmentHead : String
deriving Repr, DecidableEq

def ConversionProfile.judgment (profile : ConversionProfile)
    (source target : Pattern) : Pattern :=
  .apply profile.judgmentHead [source, target]

/-- Untrusted, finite evidence for a reflexive-transitive conversion path. -/
inductive RawConversionCertificate where
  | refl
  | step : (next : Pattern) → RawProof → RawConversionCertificate →
      RawConversionCertificate
deriving Repr

/-- Structurally total certificate replay.  Every non-reflexive edge is
accepted by the same generic checker as every other hosted judgment. -/
def check (checked : CheckedGSLT) (profile : ConversionProfile) :
    Pattern → Pattern → RawConversionCertificate → Bool
  | source, target, .refl => decide (source = target)
  | source, target, .step next proof tail =>
      checked.checkRaw (profile.judgment source next) proof &&
        check checked profile next target tail
termination_by _ _ certificate => sizeOf certificate

/-- Proof-relevant semantics of an accepted conversion certificate. -/
inductive ConversionDerivation (checked : CheckedGSLT)
    (profile : ConversionProfile) : Pattern → Pattern → Type where
  | refl (term : Pattern) : ConversionDerivation checked profile term term
  | step {source next target : Pattern} :
      Derivation checked.presentation (profile.judgment source next) →
      ConversionDerivation checked profile next target →
      ConversionDerivation checked profile source target

def ConversionDerivation.erase
    {checked : CheckedGSLT} {profile : ConversionProfile}
    {source target : Pattern} :
    ConversionDerivation checked profile source target →
      RawConversionCertificate
  | .refl _ => .refl
  | .step (next := next) head tail =>
      .step next head.erase tail.erase

/-- Certificate acceptance always reconstructs a proof-relevant path. -/
theorem check_soundness {checked : CheckedGSLT}
    {profile : ConversionProfile} {source target : Pattern}
    {certificate : RawConversionCertificate}
    (hcheck : check checked profile source target certificate = true) :
    Nonempty (ConversionDerivation checked profile source target) := by
  induction certificate generalizing source with
  | refl =>
      simp only [check, decide_eq_true_eq] at hcheck
      subst target
      exact ⟨.refl source⟩
  | step next proof tail ih =>
      simp only [check, Bool.and_eq_true] at hcheck
      rcases CheckedGSLT.checkRaw_soundness hcheck.1 with ⟨head⟩
      rcases ih hcheck.2 with ⟨tailDerivation⟩
      exact ⟨.step head tailDerivation⟩

/-- Erasing a typed conversion derivation yields an accepted certificate. -/
theorem check_erase {checked : CheckedGSLT}
    {profile : ConversionProfile} {source target : Pattern}
    (derivation : ConversionDerivation checked profile source target) :
    check checked profile source target derivation.erase = true := by
  induction derivation with
  | refl term => simp [ConversionDerivation.erase, check]
  | step head tail ih =>
      simp [ConversionDerivation.erase, check,
        CheckedGSLT.checkRaw_erase head, ih]

/-- Accepted raw certificates are exactly erasures of typed paths, including
the exact intermediate terms and raw edge proofs supplied by the producer. -/
theorem check_exists_derivation_with_exact_erasure
    {checked : CheckedGSLT} {profile : ConversionProfile}
    {source target : Pattern} {certificate : RawConversionCertificate}
    (hcheck : check checked profile source target certificate = true) :
    ∃ derivation : ConversionDerivation checked profile source target,
      derivation.erase = certificate := by
  induction certificate generalizing source with
  | refl =>
      simp only [check, decide_eq_true_eq] at hcheck
      subst target
      exact ⟨.refl source, rfl⟩
  | step next proof tail ih =>
      simp only [check, Bool.and_eq_true] at hcheck
      rcases CheckedGSLT.checkRaw_exists_derivation_with_exact_erasure hcheck.1 with
        ⟨head, hhead⟩
      rcases ih hcheck.2 with ⟨tailDerivation, htail⟩
      refine ⟨.step head tailDerivation, ?_⟩
      simp [ConversionDerivation.erase, hhead, htail]

/-! ## Positive and negative certificate fixtures -/

private def datumConstructor (head : String) : GrammarRule :=
  { label := head
    category := "Datum"
    params := []
    syntaxPattern := [] }

private def conversionLanguage : LanguageDef :=
  { name := "conversion-certificate-fixture"
    types := [TypeDecl.plain "Datum"]
    terms := [datumConstructor "A", datumConstructor "B", datumConstructor "C"]
    equations := []
    rewrites := [] }

private def conversionProfile : ConversionProfile :=
  { judgmentHead := "Converts" }

private def a : Pattern := .apply "A" []
private def b : Pattern := .apply "B" []
private def c : Pattern := .apply "C" []

private def abRule : RuleSchema :=
  { id := ⟨"A-to-B"⟩
    metavariables := []
    premises := []
    conclusion := conversionProfile.judgment a b }

private def bcRule : RuleSchema :=
  { id := ⟨"B-to-C"⟩
    metavariables := []
    premises := []
    conclusion := conversionProfile.judgment b c }

private def conversionPresentation : Presentation :=
  { language := conversionLanguage
    judgments := [{ head := "Converts", arity := 2 }]
    rules := [abRule, bcRule] }

private def conversionSource : GSLTSource :=
  { identity :=
      { systemId := "conversion-fixture"
        revision := "v1"
        artifactDigest := "sha256:conversion-fixture" }
    assumptions := { entries := [] }
    profiles :=
      { entries :=
          [{ name := "conversion"
             version := "v1"
             payload := .apply "ExplicitCertificates" [] }] }
    presentation := conversionPresentation }

private def conversionChecked : CheckedGSLT :=
  { source := conversionSource
    identityValid := by native_decide
    assumptionsValid := by native_decide
    profilesValid := by native_decide
    presentationValid := by native_decide }

private def abProof : RawProof :=
  .node { ruleId := ⟨"A-to-B"⟩, arguments := [] } []

private def bcProof : RawProof :=
  .node { ruleId := ⟨"B-to-C"⟩, arguments := [] } []

private def acCertificate : RawConversionCertificate :=
  .step b abProof (.step c bcProof .refl)

/-- Positive: two ordinary checked edges form an exact conversion path. -/
example : check conversionChecked conversionProfile a c acCertificate = true := by
  native_decide

/-- Positive: reflexivity is literal endpoint equality and needs no rule. -/
example :
    check conversionChecked conversionProfile a a .refl = true := by
  native_decide

/-- Negative: omitting a required edge cannot reach the requested endpoint. -/
example :
    check conversionChecked conversionProfile a c
      (.step b abProof .refl) = false := by
  native_decide

/-- Negative: reordering edge evidence fails at its exact local judgment. -/
example :
    check conversionChecked conversionProfile a c
      (.step b bcProof (.step c abProof .refl)) = false := by
  native_decide

/-- Negative: certificate rejection is not exposed as mathematical
inequality; it is only failure to establish the requested path. -/
example : check conversionChecked conversionProfile c a .refl = false := by
  native_decide

end Mettapedia.GSLT.LanguageDef.ConversionCertificate
