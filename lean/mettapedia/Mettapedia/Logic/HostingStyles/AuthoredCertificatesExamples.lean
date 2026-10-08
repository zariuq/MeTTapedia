import Mettapedia.Logic.HostingStyles.AuthoredCertificates

/-!
# Certificates and derivations in the smallest authored calculus

The calculus with one judgment `J`, one rule with no premise that concludes
it, and no authored computation.

* Positive: `J` has an accepted raw certificate (`axiomProof_accepted`), hence
  a derivation, and the accepted raw certificates of `J` are in bijection with
  its derivations (the instance of `BootstrapCell.checkedEquiv`).
* Negative: among compact certificates, the raw tree taken as a replay leaf
  and the same rule written as a node are two accepted certificates
  (`two_accepted`) that stand for one derivation (`two_one_reading`).  So
  compact certificates are not in bijection with derivations, and with
  certificates compared by identity the theory of certificates is not
  exhausted by the derivations (`unit_not_exhausting`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AuthoredCertificatesExamples

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceComputedLeaves (CompactProof check checkChildren)
open Mettapedia.GSLT.LanguageDef.Authored

/-- The one judgment. -/
def axiomJudgment : Pattern := .apply "J" []

/-- The one rule: `J`, from nothing. -/
def axiomRule : RuleSchema :=
  { id := ⟨"ax"⟩, metavariables := [], premises := [], conclusion := axiomJudgment }

def unitDefinition : CalculusLanguageDef :=
  { toLanguageDef := LanguageDef.empty "unit-calculus"
    judgments := [{ head := "J", arity := 0 }]
    rules := [axiomRule] }

theorem unitDefinition_valid : unitDefinition.isValid = true := by
  have emptyValid : (LanguageDef.empty "unit-calculus").validate = [] := by
    apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
      simp [LanguageDef.empty, LanguageDef.typeNames]
  simp [unitDefinition, CalculusLanguageDef.isValid,
    CalculusLanguageDef.judgmentSignatureValid, CalculusLanguageDef.judgmentHeads,
    CalculusLanguageDef.hasValidLocalRules, CalculusLanguageDef.ruleIds,
    emptyValid, axiomRule, axiomJudgment,
    RuleSchema.isValidIn, CalculusLanguageDef.judgmentSchemaValid,
    CalculusLanguageDef.lookupJudgment?, RuleSchema.isLocallyValid,
    RuleSchema.metavariableNames, RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    fixedConstructorListsValid,
    Pattern.zipHead, Pattern.mapHead, Pattern.evalHead,
    Pattern.isWellScoped, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList]
  decide

def unitValidated : ValidatedCalculusLanguageDef := ⟨unitDefinition, unitDefinition_valid⟩

/-- The family with no authored computation. -/
def emptyFamily : AuthoredFamily where
  Index := Empty
  Query := fun index => index.elim
  Answer := fun index => index.elim
  computation := fun index => index.elim
  judgment := fun index => index.elim

/-- **The smallest authored calculus.** -/
def unitCalculus : AuthoredCalculus := ⟨unitValidated, emptyFamily⟩

/-- The rule instance of the one rule. -/
def axiomInstance : RuleInstance := { ruleId := ⟨"ax"⟩, arguments := [] }

/-- The raw certificate of `J`. -/
def axiomProof : RawProof := .node axiomInstance []

theorem axiomInstance_instantiates :
    instantiateRule? unitValidated axiomInstance = some ([], axiomJudgment) := by
  simp [instantiateRule?, unitValidated, unitDefinition, axiomRule, axiomInstance, axiomJudgment,
    CalculusLanguageDef.lookupRule?, argumentsValidAt, RuleSchema.sideConditionsHold,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?]

/-- **Positive**: the raw certificate is accepted. -/
theorem axiomProof_accepted : checkRaw unitCalculus.definition axiomJudgment axiomProof = true := by
  show checkRaw unitValidated axiomJudgment (.node axiomInstance []) = true
  simp [checkRaw, checkRawChildren, axiomInstance_instantiates]

/-- So `J` has a derivation in the signature of the calculus. -/
theorem axiomJudgment_derivable :
    Nonempty ((derivationSignature unitCalculus).Proof axiomJudgment) :=
  ⟨read unitCalculus ((certificateSignature unitCalculus).node
    (.replay axiomProof axiomProof_accepted) fun position => position.elim0)⟩

/-- **Negative**: two compact proofs are accepted for `J`, the raw tree taken
as a replay leaf and the rule written as a node. -/
theorem two_accepted :
    check unitCalculus.definition unitCalculus.family.evaluate axiomJudgment
        (.replay axiomProof) = true ∧
      check unitCalculus.definition unitCalculus.family.evaluate axiomJudgment
        (.node axiomInstance []) = true ∧
      (CompactProof.replay axiomProof : CompactProof unitCalculus.family.Leaf) ≠
        .node axiomInstance [] := by
  refine ⟨?_, ?_, fun same => by cases same⟩
  · simpa only [check] using axiomProof_accepted
  · show check unitValidated emptyFamily.evaluate axiomJudgment (.node axiomInstance []) = true
    simp [check, checkChildren, axiomInstance_instantiates]

/-- They stand for one derivation: the certificate with the replay leaf
differs from the certificate written from its reading and reads the same. -/
theorem two_one_reading :
    let certificate := (certificateSignature unitCalculus).node
      (.replay axiomProof axiomProof_accepted) fun position => position.elim0
    write unitCalculus (read unitCalculus certificate) ≠ certificate ∧
      read unitCalculus (write unitCalculus (read unitCalculus certificate)) =
        read unitCalculus certificate :=
  replay_ne_write_read unitCalculus axiomProof axiomProof_accepted

/-- **With certificates compared by identity, the derivations do not exhaust
them.** -/
theorem unit_not_exhausting : ¬ (writeStrictMap unitCalculus).Exhausting :=
  writeStrictMap_not_exhausting unitCalculus axiomProof axiomProof_accepted

/-- Compared by their reading, they do: the general theorem at this
calculus. -/
theorem unit_hosts_derivations :
    HostsExhaustively
      ((certificateSignature unitCalculus).proofTheory (readCongruence unitCalculus))
      ((derivationSignature unitCalculus).proofTheory (RuleSignature.ProofCongruence.identity _)) :=
  authoredCalculus_hosts_derivations unitCalculus

#print axioms axiomProof_accepted
#print axioms two_accepted
#print axioms two_one_reading
#print axioms unit_not_exhausting

end Mettapedia.Logic.HostingStyles.AuthoredCertificatesExamples
