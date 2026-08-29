import Mettapedia.GSLT.LanguageDef.LF.RootedBetaEtaCorrespondence

/-!
# Expressiveness boundary of the first rooted LF conversion presentation

The rooted beta-eta presentation validates and its direct beta and eta rules
are executable.  Its original product and abstraction congruence rules,
however, place a conversion between raw `Pattern.lambda` wrappers in a premise.
No rule in that presentation has such a wrapper as the left endpoint of its
conclusion.

This file proves the resulting boundary:

* direct beta still has a generic proof derivation;
* every raw proof whose conversion source is a product is rejected;
* an accepted conversion certificate starting at a product is necessarily
  reflexive;
* LF reduction nevertheless contains a non-reflexive beta contraction under a
  product body.

Thus successful normalization of an LF term cannot by itself supply a rooted
generic proof for the corresponding contextual reduction.  A replacement
presentation must make ambient binder depth part of its proof interface rather
than treating normalization equality as a proof certificate.
-/

namespace Mettapedia.GSLT.LanguageDef.LFRootedBetaEtaAdequacyBoundary

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFBetaEta
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CheckedSource
open Mettapedia.GSLT.LanguageDef.ConversionCertificate
open Mettapedia.GSLT.LanguageDef.LFRootedBetaEtaConversion
open Mettapedia.GSLT.LanguageDef.LFRootedBetaEtaCorrespondence
open Mettapedia.OSLF.MeTTaIL.Syntax

private theorem rule_mem_of_lookup {ruleInstance : RuleInstance}
    {rule : RuleSchema}
    (lookup :
      checked.presentation.1.lookupRule? ruleInstance.ruleId = some rule) :
    rule ∈
      [betaRule, etaRule, appCongruenceRule, piCongruenceRule,
        lamCongruenceRule] := by
  unfold CalculusLanguageDef.lookupRule? at lookup
  simpa [CheckedGSLT.definition, checked, source, presentation, language] using
    (List.mem_of_find?_eq_some lookup)

private theorem instantiates_apply_head_eq
    {formals : List (String × Nat)} {arguments : List Pattern}
    {depth : Nat} {schemaHead resultHead : String}
    {schemas results : List Pattern}
    (hinstantiates :
      InstantiatesAt formals arguments depth (.apply schemaHead schemas)
        (.apply resultHead results)) :
    schemaHead = resultHead := by
  cases hinstantiates
  rfl

private theorem no_apply_instantiates_lambda
    {formals : List (String × Nat)} {arguments : List Pattern}
    {depth : Nat} {head : String} {schemas : List Pattern}
    {binder : Option String} {body : Pattern} :
    ¬ InstantiatesAt formals arguments depth (.apply head schemas)
      (.lambda binder body) := by
  intro hinstantiates
  cases hinstantiates

private theorem instantiates_two_lambdas_shape
    {formals : List (String × Nat)} {arguments : List Pattern}
    {depth : Nat} {leftSchema rightSchema result : Pattern}
    (hinstantiates :
      InstantiatesAt formals arguments depth
        (.apply "Converts"
          [.lambda none leftSchema, .lambda none rightSchema])
        result) :
    ∃ leftResult rightResult,
      result =
        .apply "Converts"
          [.lambda none leftResult, .lambda none rightResult] := by
  cases hinstantiates with
  | apply items =>
      cases items with
      | cons leftInstantiates tail =>
          cases tail with
          | cons rightInstantiates nilTail =>
              cases nilTail
              cases leftInstantiates with
              | lambda leftInner =>
                  cases rightInstantiates with
                  | lambda rightInner =>
                      exact ⟨_, _, rfl⟩

private theorem arguments_four
    {firstName secondName thirdName fourthName : String}
    {firstDepth secondDepth thirdDepth fourthDepth : Nat}
    {arguments : List Pattern}
    (harguments :
      argumentsValidAt
        [(firstName, firstDepth), (secondName, secondDepth),
          (thirdName, thirdDepth), (fourthName, fourthDepth)]
        arguments = true) :
    ∃ first second third fourth,
      arguments = [first, second, third, fourth] := by
  cases arguments with
  | nil => simp [argumentsValidAt] at harguments
  | cons first rest =>
      cases rest with
      | nil => simp [argumentsValidAt] at harguments
      | cons second rest =>
          cases rest with
          | nil => simp [argumentsValidAt] at harguments
          | cons third rest =>
              cases rest with
              | nil => simp [argumentsValidAt] at harguments
              | cons fourth rest =>
                  cases rest with
                  | nil => exact ⟨first, second, third, fourth, rfl⟩
                  | cons fifth rest =>
                      simp [argumentsValidAt] at harguments

/-- Positive boundary: the direct rooted beta edge is genuinely represented
by a proof-relevant derivation reconstructed by the generic checker. -/
theorem beta_rule_has_derivation :
    Nonempty
      (Derivation checked.presentation (converts betaSource typeTerm)) := by
  have hcheck := beta_certificate_accepts
  simp only [betaCertificate, check, Bool.and_eq_true,
    decide_eq_true_eq] at hcheck
  exact CheckedGSLT.checkRaw_soundness hcheck.1

/-- None of the five original rule conclusions can instantiate to a conversion
whose left endpoint is a raw binder wrapper. -/
theorem no_lambda_left_rule_application
    {body target : Pattern} {ruleInstance : RuleInstance}
    {premises : List Pattern}
    (application :
      RuleApplication checked.presentation ruleInstance premises
        (converts (.lambda none body) target)) :
    False := by
  rcases application with
    ⟨rule, lookup, argumentsValid, sideConditionsValid,
      premisesInstantiate, conclusionInstantiates⟩
  have membership := rule_mem_of_lookup lookup
  simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [betaRule, etaRule, appCongruenceRule, piCongruenceRule,
      lamCongruenceRule, converts] at conclusionInstantiates
    cases conclusionInstantiates with
    | apply items =>
        cases items with
        | cons sourceInstantiates rest =>
            exact no_apply_instantiates_lambda sourceInstantiates

/-- Consequently no generic proof derivation can establish such a wrapper
conversion. -/
theorem no_lambda_left_derivation (body target : Pattern) :
    ¬ Nonempty
      (Derivation checked.presentation
        (converts (.lambda none body) target)) := by
  rintro ⟨derivation⟩
  cases derivation with
  | byRule ruleInstance application children =>
      exact no_lambda_left_rule_application application

/-- The product congruence rule is unusable in the original presentation:
its second child has exactly the impossible wrapper-conversion shape.  The
other four rules cannot instantiate to a product-headed source. -/
theorem no_pi_left_derivation (domain body target : Pattern) :
    ¬ Nonempty
      (Derivation checked.presentation
        (converts (pi domain body) target)) := by
  rintro ⟨derivation⟩
  cases derivation with
  | @byRule ruleInstance premises conclusion application children =>
      rcases application with
        ⟨rule, lookup, argumentsValid, sideConditionsValid,
          premisesInstantiate, conclusionInstantiates⟩
      have membership := rule_mem_of_lookup lookup
      simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
      rcases membership with hbeta | heta | happ | hpi | hlam
      · subst rule
        simp only [betaRule, converts, pi, app, lam] at conclusionInstantiates
        cases conclusionInstantiates with
        | apply items =>
            cases items with
            | cons sourceInstantiates rest =>
                have hhead :=
                  instantiates_apply_head_eq sourceInstantiates
                simp at hhead
      · subst rule
        simp only [etaRule, converts, pi, app, lam] at conclusionInstantiates
        cases conclusionInstantiates with
        | apply items =>
            cases items with
            | cons sourceInstantiates rest =>
                have hhead :=
                  instantiates_apply_head_eq sourceInstantiates
                simp at hhead
      · subst rule
        simp only [appCongruenceRule, converts, pi, app] at conclusionInstantiates
        cases conclusionInstantiates with
        | apply items =>
            cases items with
            | cons sourceInstantiates rest =>
                have hhead :=
                  instantiates_apply_head_eq sourceInstantiates
                simp at hhead
      · subst rule
        rcases arguments_four argumentsValid with
          ⟨actualDomain, actualDomainResult, actualBody, actualBodyResult,
            harguments⟩
        rw [harguments] at premisesInstantiate
        simp only [piCongruenceRule, converts] at premisesInstantiate
        cases premisesInstantiate with
        | cons domainInstantiates tail =>
            cases tail with
            | cons bodyInstantiates nilTail =>
                cases nilTail
                rcases instantiates_two_lambdas_shape bodyInstantiates with
                  ⟨leftBody, rightBody, hshape⟩
                cases children with
                | cons domainChild childrenTail =>
                    cases childrenTail with
                    | cons bodyChild childrenNil =>
                        rw [hshape] at bodyChild
                        exact no_lambda_left_derivation _ _ ⟨bodyChild⟩
      · subst rule
        simp only [lamCongruenceRule, converts, pi, lam] at conclusionInstantiates
        cases conclusionInstantiates with
        | apply items =>
            cases items with
            | cons sourceInstantiates rest =>
                have hhead :=
                  instantiates_apply_head_eq sourceInstantiates
                simp at hhead

/-- Every raw proof at a product-headed source fails at the Boolean boundary,
not merely at the proof-relevant interpretation. -/
theorem every_pi_raw_proof_rejected
    (domain body target : Pattern) (proof : RawProof) :
    checked.checkRaw (converts (pi domain body) target) proof = false := by
  cases hcheck :
      checked.checkRaw (converts (pi domain body) target) proof with
  | false => rfl
  | true =>
      exact False.elim
        (no_pi_left_derivation domain body target
          (CheckedGSLT.checkRaw_soundness hcheck))

/-- An accepted path starting from a product can only be the certificate-level
reflexive case. -/
theorem accepted_pi_certificate_is_reflexive
    {domain body target : Pattern}
    {certificate : RawConversionCertificate}
    (hcheck :
      check checked rootedConversion (pi domain body) target certificate =
        true) :
    pi domain body = target := by
  cases certificate with
  | refl =>
      simpa only [check, decide_eq_true_eq] using hcheck
  | step next proof tail =>
      simp only [check, Bool.and_eq_true] at hcheck
      have hrejected :=
        every_pi_raw_proof_rejected domain body next proof
      have hhead :
          checked.checkRaw (converts (pi domain body) next) proof = true := by
        simpa [RootedConversion.judgment, rootedConversion,
          conversionDeclaration, converts] using hcheck.1
      rw [hrejected] at hhead
      simp at hhead

/-- Certificate existence at a product is therefore equivalent to syntactic
equality, exposing the missing non-reflexive congruence coverage. -/
theorem exists_accepted_pi_certificate_iff
    (domain body target : Pattern) :
    (∃ certificate,
      check checked rootedConversion (pi domain body) target certificate =
        true) ↔
      pi domain body = target := by
  constructor
  · rintro ⟨certificate, hcheck⟩
    exact accepted_pi_certificate_is_reflexive hcheck
  · intro hequal
    subst target
    exact ⟨.refl, by simp [check]⟩

private def runtimeType : LF.Term := .srt .type
private def runtimeIdentity : LF.Term :=
  .lam runtimeType (.var 0)
private def runtimePiBetaSource : LF.Term :=
  .pi runtimeType (.app runtimeIdentity runtimeType)
private def runtimePiBetaTarget : LF.Term :=
  .pi runtimeType runtimeType

/-- Negative completeness fixture: LF semantics does reduce a beta redex under
a product body. -/
theorem runtime_pi_body_beta_reduces :
    LFBetaEta.Reduces [] runtimePiBetaSource runtimePiBetaTarget := by
  exact .pi .refl .beta

theorem encode_runtime_pi_beta_source :
    encodeTerm runtimePiBetaSource = pi typeTerm betaSource := by
  rfl

theorem encode_runtime_pi_beta_target :
    encodeTerm runtimePiBetaTarget = pi typeTerm typeTerm := by
  rfl

/-- Yet no certificate in the original rooted presentation can represent that
non-reflexive contextual reduction. -/
theorem runtime_pi_body_beta_has_no_rooted_certificate :
    ¬ ∃ certificate,
      check checked rootedConversion
        (encodeTerm runtimePiBetaSource)
        (encodeTerm runtimePiBetaTarget)
        certificate = true := by
  rw [encode_runtime_pi_beta_source, encode_runtime_pi_beta_target,
    exists_accepted_pi_certificate_iff]
  simp [betaSource, identity, pi, app, lam, typeTerm, srt, sortType]

#print axioms beta_rule_has_derivation
#print axioms no_lambda_left_rule_application
#print axioms no_lambda_left_derivation
#print axioms no_pi_left_derivation
#print axioms every_pi_raw_proof_rejected
#print axioms accepted_pi_certificate_is_reflexive
#print axioms exists_accepted_pi_certificate_iff
#print axioms runtime_pi_body_beta_reduces
#print axioms runtime_pi_body_beta_has_no_rooted_certificate

end Mettapedia.GSLT.LanguageDef.LFRootedBetaEtaAdequacyBoundary
