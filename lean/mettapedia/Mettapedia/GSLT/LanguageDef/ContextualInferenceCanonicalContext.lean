import Mettapedia.GSLT.LanguageDef.ContextualInferenceSemantics
import Mettapedia.GSLT.LanguageDef.CalculusLanguageExtension

/-!
# Canonical context certificates for open contextual inference

An open contextual rule lowers ambient contexts such as `Gamma` and `Delta`
to ordinary checker metavariables.  Groundness alone does not ensure that an
argument at one of those positions is a canonical context encoding.

This module supplies that missing proof-calculus boundary without extending
the trusted checker.  A unary formula asserts that a wire is a canonical
context.  Two independently meaningful rules generate exactly the empty and
extension cases.  Their semantic interpretation is successful decoding into
`ContextSchema`, not checker acceptance.

Calculi using open contexts may require these certificates as ordinary proof
premises.  The certificates are proof-only and can be erased after semantic
soundness and no-crossing have been established.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ContextualInferenceCanonicalContext

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.ContextualInference

/-! ## Syntax -/

/-- Proof-calculus formula classifying canonical context encodings. -/
def contextCodeTerm : GrammarRule where
  label := "$gslt:context:canonical"
  category := formulaType.name
  params := [.simple "context" (.base contextType.name)]
  syntaxPattern := []

/-- Formula asserting that `wire` is a canonical context encoding. -/
def claim (wire : Pattern) : Pattern :=
  .apply contextCodeTerm.label [wire]

/-- Closed contextual sequent carrying one canonical-context claim. -/
def sequent (wire : Pattern) : Sequent where
  variableContext := .empty
  relationContext := .empty
  conclusion := claim wire

/-- Reusable premise certifying one ambient context metavariable. -/
def premise (name : String) : Sequent :=
  sequent (.fvar name)

/-- The empty context is canonical. -/
def nilRule : RuleSchema where
  id := ⟨"$gslt:context:canonical-nil"⟩
  metavariables := []
  premises := []
  conclusion := lowerSequent (sequent (encodeContext .empty))
  sideConditions := []

/-- Extending a canonical tail by one formula yields a canonical context. -/
def consRule : RuleSchema where
  id := ⟨"$gslt:context:canonical-cons"⟩
  metavariables := [("formula", 0), ("tail", 0)]
  premises := [lowerSequent (premise "tail")]
  conclusion := lowerSequent (sequent
    (.apply extendContextTerm.label [.fvar "formula", .fvar "tail"]))
  sideConditions := []

/-- Generic proof-only extension supplying context certificates. -/
def extension : CalculusLanguageExtension where
  newTerms := [contextCodeTerm]
  newRules := [nilRule, consRule]

/-- The extension deliberately adds derivations to the shared contextual
judgment and declares that policy explicitly. -/
def validatedExtension :
    ValidatedCalculusLanguageExtension ContextualInference.validated where
  extension := extension
  policy := .extendsBaseJudgments [contextualJudgment.head]
  disjoint := by decide +kernel
  policyHolds := by decide +kernel
  valid := by decide +kernel

/-- One ordinary validated calculus containing the shared contextual syntax
and its canonical-context certificates. -/
def validated : ValidatedCalculusLanguageDef :=
  validatedExtension.target

/-! ## Independent semantics -/

/-- Decode exactly the generated canonical-context formula. -/
def decodeClaim? : Pattern → Option Pattern
  | .apply head [wire] =>
      if head = contextCodeTerm.label then some wire else none
  | _ => none

@[simp] theorem decodeClaim?_claim (wire : Pattern) :
    decodeClaim? (claim wire) = some wire := by
  simp [decodeClaim?, claim]

/-- Successful decoding reconstructs the exact formula wire. -/
theorem claim_of_decodeClaim?_eq_some
    {formula wire : Pattern} (decoded : decodeClaim? formula = some wire) :
    claim wire = formula := by
  cases formula with
  | apply head arguments =>
      cases arguments with
      | nil => simp [decodeClaim?] at decoded
      | cons first rest =>
          cases rest with
          | nil =>
              simp only [decodeClaim?] at decoded
              split at decoded
              next equal =>
                cases decoded
                subst head
                rfl
              next different => simp at decoded
          | cons second more => simp [decodeClaim?] at decoded
  | _ => simp [decodeClaim?] at decoded

/-- Independent canonicality: a wire must be the exact encoding of an
authored `ContextSchema`. -/
def Canonical (wire : Pattern) : Prop :=
  ∃ context, encodeContext context = wire

/-- Canonicality is exactly successful context decoding. -/
theorem canonical_iff_decode_isSome (wire : Pattern) :
    Canonical wire ↔ (decodeContext? wire).isSome := by
  constructor
  · rintro ⟨context, rfl⟩
    simp
  · intro decoded
    obtain ⟨context, exact⟩ := Option.isSome_iff_exists.mp decoded
    exact ⟨context, encodeContext_of_decodeContext?_eq_some exact⟩

/-- Independent meaning of certificate judgments.  Both the outer sequent
and inner claim decode fail closed. -/
def Meaning (judgment : Pattern) : Prop :=
  match decodeSequent? judgment with
  | none => False
  | some decodedSequent =>
      match decodeClaim? decodedSequent.conclusion with
      | none => False
      | some wire => Canonical wire

@[simp] theorem meaning_lowerSequent (wire : Pattern) :
    Meaning (lowerSequent (sequent wire)) ↔ Canonical wire := by
  simp [Meaning, sequent, decodeClaim?, claim]

/-! ## Rule soundness -/

/-- Every checker instance of the empty-context rule has exactly its
independent canonical meaning. -/
theorem nil_instance_sound
    {arguments premises : List Pattern} {conclusion : Pattern}
    (argumentsValid :
      argumentsValidAt nilRule.metavariables arguments = true)
    (premisesInstantiate :
      InstantiatesList nilRule.metavariables arguments nilRule.premises
        premises)
    (conclusionInstantiates :
      Instantiates nilRule.metavariables arguments nilRule.conclusion
        conclusion) :
    premises = [] ∧ Meaning conclusion := by
  have argumentsEmpty : arguments = [] := by
    cases arguments <;>
      simp [nilRule, argumentsValidAt] at argumentsValid ⊢
  subst arguments
  have premisesComputed :=
    instantiateSchemasAt?_complete premisesInstantiate
  have conclusionComputed :=
    instantiateSchemaAt?_complete conclusionInstantiates
  have premisesEmpty : premises = [] := by
    simpa [nilRule, instantiateSchemas?, instantiateSchemasAt?] using
      premisesComputed.symm
  have conclusionExact :
      lowerSequent (sequent (encodeContext .empty)) = conclusion := by
    simpa [nilRule, sequent, claim, lowerSequent, encodeContext,
      instantiateSchema?, instantiateSchemaAt?, instantiateSchemasAt?,
      lookupArgumentAt?] using conclusionComputed
  subst conclusion
  refine ⟨premisesEmpty, (meaning_lowerSequent _).2 ?_⟩
  exact ⟨.empty, rfl⟩

/-- Every checker instance of context extension preserves independent
canonicality from its exact tail premise. -/
theorem cons_instance_sound
    {arguments premises : List Pattern} {conclusion : Pattern}
    (argumentsValid :
      argumentsValidAt consRule.metavariables arguments = true)
    (premisesInstantiate :
      InstantiatesList consRule.metavariables arguments consRule.premises
        premises)
    (conclusionInstantiates :
      Instantiates consRule.metavariables arguments consRule.conclusion
        conclusion)
    (premisesMeaning : ∀ premise ∈ premises, Meaning premise) :
    Meaning conclusion := by
  obtain ⟨formula, tail, argumentsExact⟩ :
      ∃ formula tail, arguments = [formula, tail] := by
    cases arguments with
    | nil => simp [consRule, argumentsValidAt] at argumentsValid
    | cons formula rest =>
        cases rest with
        | nil => simp [consRule, argumentsValidAt] at argumentsValid
        | cons tail rest =>
            cases rest with
            | nil => exact ⟨formula, tail, rfl⟩
            | cons extra more =>
                simp [consRule, argumentsValidAt] at argumentsValid
  subst arguments
  have premisesComputed :=
    instantiateSchemasAt?_complete premisesInstantiate
  have conclusionComputed :=
    instantiateSchemaAt?_complete conclusionInstantiates
  have premisesExact :
      premises = [lowerSequent (sequent tail)] := by
    have forward : [lowerSequent (sequent tail)] = premises := by
      simpa [consRule, premise, sequent, claim, lowerSequent, encodeContext,
        instantiateSchemas?, instantiateSchema?, instantiateSchemaAt?,
        instantiateSchemasAt?, lookupArgumentAt?] using premisesComputed
    exact forward.symm
  have conclusionExact :
      conclusion = lowerSequent (sequent
        (.apply extendContextTerm.label [formula, tail])) := by
    have forward :
        lowerSequent (sequent
          (.apply extendContextTerm.label [formula, tail])) = conclusion := by
      simpa [consRule, premise, sequent, claim, lowerSequent, encodeContext,
        instantiateSchema?, instantiateSchemaAt?, instantiateSchemasAt?,
        lookupArgumentAt?] using conclusionComputed
    exact forward.symm
  subst premises
  subst conclusion
  have tailMeaning : Meaning (lowerSequent (sequent tail)) :=
    premisesMeaning _ (by simp)
  obtain ⟨tailContext, tailExact⟩ :=
    (meaning_lowerSequent tail).mp tailMeaning
  apply (meaning_lowerSequent _).2
  exact ⟨.extend formula tailContext, by
    simp [encodeContext, tailExact, extendContextTerm]⟩

/-- Both generated certificate rules are sound for arbitrary checker
applications, not only for the concrete examples below. -/
theorem ruleApplication_sound
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {conclusion : Pattern}
    (application : RuleApplication validated ruleInstance premises conclusion)
    (premisesMeaning : ∀ premise ∈ premises, Meaning premise) :
    Meaning conclusion := by
  cases application with
  | intro rule lookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
      have member : rule ∈ validated.1.rules :=
        List.mem_of_find?_eq_some lookup
      have classified : rule = nilRule ∨ rule = consRule := by
        change rule ∈
          ContextualInference.definition.rules ++ [nilRule, consRule]
          at member
        simpa [ContextualInference.definition] using member
      rcases classified with rfl | rfl
      · exact (nil_instance_sound argumentsValid premisesInstantiate
          conclusionInstantiates).2
      · exact cons_instance_sound argumentsValid premisesInstantiate
          conclusionInstantiates premisesMeaning

/-- Arbitrary proof trees in the certificate calculus have the independent
canonical-context meaning. -/
theorem derivation_sound {goal : Pattern}
    (derivation : Derivation validated goal) : Meaning goal :=
  derivation.sound_of_ruleApplications Meaning
    (fun _ruleInstance _premises _conclusion application premisesMeaning =>
      ruleApplication_sound application premisesMeaning)

/-! ## Positive and negative controls -/

private def sampleFormula : Pattern :=
  claim (encodeContext .empty)

private def sampleContext : ContextSchema :=
  .extend sampleFormula .empty

private def nilDerivation :
    Derivation validated (lowerSequent (sequent (encodeContext .empty))) :=
  .byRule
    { ruleId := nilRule.id
      arguments := [] }
    (by
      apply instantiateRule?_eq_some_iff_application.mp
      decide +kernel)
    .nil

private theorem sampleConsApplication :
    RuleApplication validated
      { ruleId := consRule.id
        arguments := [sampleFormula, encodeContext .empty] }
      [lowerSequent (sequent (encodeContext .empty))]
      (lowerSequent (sequent (encodeContext sampleContext))) := by
  apply instantiateRule?_eq_some_iff_application.mp
  decide +kernel

/-- A concrete one-element canonical context has a checked proof. -/
def sampleDerivation :
    Derivation validated (lowerSequent (sequent (encodeContext sampleContext))) :=
  .byRule
    { ruleId := consRule.id
      arguments := [sampleFormula, encodeContext .empty] }
    sampleConsApplication
    (.cons nilDerivation .nil)

private def malformedContext : Pattern :=
  .apply "$gslt:context:canonical:not-a-context" []

theorem malformedContext_not_canonical :
    ¬ Canonical malformedContext := by
  rintro ⟨context, exact⟩
  cases context <;>
    simp [malformedContext, encodeContext, emptyContextTerm,
      extendContextTerm] at exact

/-- Independent semantics rules out a proof of a generated-looking claim
whose payload is not a canonical context. -/
theorem malformedContext_not_derivable :
    ¬ Nonempty
      (Derivation validated (lowerSequent (sequent malformedContext))) := by
  rintro ⟨derivation⟩
  exact malformedContext_not_canonical
    ((meaning_lowerSequent malformedContext).mp
      (derivation_sound derivation))

#print axioms claim_of_decodeClaim?_eq_some
#print axioms canonical_iff_decode_isSome
#print axioms nil_instance_sound
#print axioms cons_instance_sound
#print axioms ruleApplication_sound
#print axioms derivation_sound
#print axioms sampleDerivation
#print axioms malformedContext_not_canonical
#print axioms malformedContext_not_derivable

end Mettapedia.GSLT.LanguageDef.ContextualInferenceCanonicalContext
