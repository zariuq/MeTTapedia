import Mettapedia.GSLT.LanguageDef.CertificateGSLTUltrafilterSemanticAuthority

/-!
# A non-principal semantic-authority canary

One validated calculus proves `C` and has no rule concluding `D`.  Its
coordinate semantics makes `C` true everywhere and makes `D` true at every
nonzero coordinate.  Selecting the principal view at zero therefore denies
`D`, while selecting the free hyperfilter affirms `D`.

The two generated NIK authorities use the same calculus, native checker, and
certificate representation, but own genuinely different independent meaning
predicates.  There is an identity-on-syntax semantic embedding from the
principal authority to the free authority, while an identity-on-syntax map in
the reverse direction is impossible.  The free authority also demonstrates
that semantic meaning may properly exceed native proof scope: `D` is true at
the free perspective but remains underivable.

This is not a claim that one ultrafilter is the universal foundation.  It is a
minimal proof that an ultrafilter-relative meaning face can inhabit the same
NIK authority architecture as ordinary semantic faces without redefining or
weakening the checker.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLTUltrafilterSemanticAuthorityCanary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.CertificateGSLTAuthorityFunctor
open Mettapedia.GSLT.LanguageDef.CertificateGSLTHeterogeneousAuthority
open Mettapedia.GSLT.LanguageDef.CertificateGSLTUltrafilterSemanticAuthority
open Mettapedia.Logic.Metaphysics

private def claimC : Pattern := .apply "ultrafilter-authority-C" []
private def claimD : Pattern := .apply "ultrafilter-authority-D" []

private def ruleC : RuleSchema :=
  { id := ⟨"ultrafilter-authority-c"⟩
    metavariables := []
    premises := []
    conclusion := claimC }

private def definition : CalculusLanguageDef :=
  CalculusLanguageDef.extend
    (LanguageDef.empty "ultrafilter-semantic-authority-canary")
    { judgments :=
        [{ head := "ultrafilter-authority-C", arity := 0 },
         { head := "ultrafilter-authority-D", arity := 0 }]
      rules := [ruleC] }

private theorem emptyLanguage_validate (name : String) :
    (LanguageDef.empty name).validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [LanguageDef.empty, LanguageDef.typeNames]

private theorem emptyLanguage_terms (name : String) :
    (LanguageDef.empty name).terms = [] :=
  rfl

private theorem definition_valid : definition.isValid = true := by
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  simp [definition, emptyLanguage_validate, emptyLanguage_terms, ruleC,
    claimC, CalculusLanguageDef.judgmentSignatureValid,
    CalculusLanguageDef.judgmentHeads, CalculusLanguageDef.ruleIds,
    RuleSchema.isValidIn, CalculusLanguageDef.judgmentSchemaValid,
    CalculusLanguageDef.lookupJudgment?, fixedConstructorListsValid,
    RuleSchema.isLocallyValid, RuleSchema.metavariableNames,
    RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    Pattern.zipHead, Pattern.mapHead, Pattern.evalHead,
    Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList,
    CalculusLanguageDef.conversionDeclarationValid]
  decide

private def validated : ValidatedCalculusLanguageDef :=
  ⟨definition, definition_valid⟩

private def object : CertificateGSLT.Object := ⟨validated⟩

private def instanceC : RuleInstance :=
  ⟨⟨"ultrafilter-authority-c"⟩, []⟩

private theorem c_instantiates :
    instantiateRule? validated instanceC = some ([], claimC) := by
  simp [instantiateRule?, validated, definition, ruleC, instanceC, claimC,
    CalculusLanguageDef.lookupRule?, argumentsValidAt,
    RuleSchema.sideConditionsHold, instantiateSchemas?, instantiateSchema?,
    instantiateSchemasAt?, instantiateSchemaAt?]

/-- Every rule application in the fixture concludes `C`. -/
private theorem application_conclusion
    (ruleInstance : RuleInstance) {premises : List Pattern}
    {conclusion : Pattern}
    (application : RuleApplication validated ruleInstance premises conclusion) :
    conclusion = claimC := by
  rcases ruleInstance with ⟨⟨ruleId⟩, arguments⟩
  cases application with
  | intro rule lookup argumentsValid sideConditions premisesInstantiate
      conclusionInstantiates =>
      simp [validated, definition, ruleC, CalculusLanguageDef.lookupRule?]
        at lookup
      rcases lookup with ⟨ruleIdShape, ruleShape⟩
      subst ruleId
      subst rule
      cases arguments with
      | cons argument arguments =>
          simp [argumentsValidAt] at argumentsValid
      | nil =>
          have reconstructed :
              RuleApplication validated instanceC premises conclusion :=
            .intro ruleC (by rfl) argumentsValid sideConditions
              premisesInstantiate conclusionInstantiates
          have canonical :
              RuleApplication validated instanceC [] claimC :=
            instantiateRule?_eq_some_iff_application.mp c_instantiates
          exact (reconstructed.outputs_unique canonical).2

/-! ## Coordinate semantics and selected perspectives -/

/-- `C` is invariant; `D` is the genuinely perspectival coordinate verdict. -/
private def meaningAt (index : ℕ) (claim : Pattern) : Prop :=
  claim = claimC ∨ (claim = claimD ∧ index ≠ 0)

/-- A finite variant makes `D` true at coordinate zero as well. -/
private def meaningWithDAtZero (_index : ℕ) (claim : Pattern) : Prop :=
  claim = claimC ∨ claim = claimD

private theorem coordinate_rules_sound :
    CoordinateRulesSound object meaningAt := by
  intro ruleInstance premises conclusion application index _premisesMeaning
  exact Or.inl (application_conclusion ruleInstance application)

private def perspectivePresentation : PerspectivePresentation ℕ where
  object := object
  meaningAt := meaningAt
  rulesSoundAt := coordinate_rules_sound

private def principalPresentation : SemanticPresentation :=
  perspectivePresentation.select (pure 0)

private noncomputable def freePresentation : SemanticPresentation :=
  perspectivePresentation.select (Filter.hyperfilter ℕ)

theorem claimC_meaning_at_every_coordinate :
    ∀ index, meaningAt index claimC := by
  intro index
  exact Or.inl rfl

theorem claimC_principal_meaning : principalPresentation.Meaning claimC := by
  change UltraMeaning (pure 0) meaningAt claimC
  rw [ultraMeaning_pure]
  exact claimC_meaning_at_every_coordinate 0

theorem claimC_free_meaning : freePresentation.Meaning claimC := by
  change UltraMeaning (Filter.hyperfilter ℕ) meaningAt claimC
  exact Filter.Eventually.of_forall claimC_meaning_at_every_coordinate

/-- The free perspective affirms the cofinite coordinate verdict `D`. -/
theorem claimD_free_meaning : freePresentation.Meaning claimD := by
  change UltraMeaning (Filter.hyperfilter ℕ) meaningAt claimD
  exact hyperfilter_pure_disagree.1.mono (by
    intro index nonzero
    exact Or.inr ⟨rfl, nonzero⟩)

/-- The principal perspective at zero denies the same coordinate verdict. -/
theorem claimD_not_principal_meaning :
    ¬ principalPresentation.Meaning claimD := by
  change ¬ UltraMeaning (pure 0) meaningAt claimD
  rw [ultraMeaning_pure]
  simp [meaningAt, claimC, claimD]

/-- Reindexing a principal view reads the transported coordinate semantics:
the successor image of coordinate zero reads coordinate one, where `D` is
true.  This is a concrete naturality canary, not a new proof rule. -/
theorem claimD_reindexed_principal_meaning :
    UltraMeaning ((pure 0 : Ultrafilter ℕ).map Nat.succ) meaningAt claimD := by
  rw [ultraMeaning_map, ultraMeaning_pure]
  simp [reindexMeaning, meaningAt, claimC, claimD]

/-- The two coordinate semantics disagree about `D` at exactly one index. -/
theorem claimD_coordinate_disagreement_finite :
    {index : ℕ |
      ¬ (meaningAt index claimD ↔ meaningWithDAtZero index claimD)}.Finite := by
  have disagreementIsZero :
      {index : ℕ |
        ¬ (meaningAt index claimD ↔ meaningWithDAtZero index claimD)} =
        {0} := by
    ext index
    simp [meaningAt, meaningWithDAtZero, claimC, claimD]
  rw [disagreementIsZero]
  exact Set.finite_singleton 0

/-- The free perspective cannot observe that one-coordinate change. -/
theorem finite_coordinate_change_preserves_free_claimD :
    UltraMeaning (Filter.hyperfilter ℕ) meaningAt claimD ↔
      UltraMeaning (Filter.hyperfilter ℕ) meaningWithDAtZero claimD :=
  ultraMeaning_hyperfilter_congr_of_finite_disagreement
    meaningAt meaningWithDAtZero claimD claimD_coordinate_disagreement_finite

/-- The principal perspective at the changed coordinate does observe it. -/
theorem finite_coordinate_change_visible_to_principal :
    ¬ (UltraMeaning (pure 0) meaningAt claimD ↔
      UltraMeaning (pure 0) meaningWithDAtZero claimD) := by
  simp [meaningAt, meaningWithDAtZero, claimC, claimD]

/-- Selecting a perspective really changes independent meaning, even though
syntax and checking remain fixed. -/
theorem selected_meanings_differ :
    principalPresentation.Meaning ≠ freePresentation.Meaning := by
  intro equalMeanings
  apply claimD_not_principal_meaning
  rw [equalMeanings]
  exact claimD_free_meaning

/-! ## Directional semantic transport -/

private def principalToFree :
    SemanticEmbedding principalPresentation freePresentation where
  proof := JudgmentEmbedding.identity object
  meaning_preserved := by
    intro claim principalMeaning
    change UltraMeaning (pure 0) meaningAt claim at principalMeaning
    have atZero : meaningAt 0 claim :=
      (ultraMeaning_pure 0 meaningAt claim).mp principalMeaning
    have equalC : claim = claimC := by
      rcases atZero with equalC | ⟨_equalD, nonzero⟩
      · exact equalC
      · exact False.elim (nonzero rfl)
    subst claim
    exact claimC_free_meaning

/-- The semantic direction cannot be reversed while retaining every claim's
spelling: `D` would have to become meaningful at the zero coordinate. -/
theorem no_identity_semantic_embedding_free_to_principal :
    ¬ ∃ translation : SemanticEmbedding freePresentation principalPresentation,
      translation.proof.mapClaim = id := by
  rintro ⟨translation, identityMap⟩
  have principalD :=
    translation.meaning_preserved claimD claimD_free_meaning
  have mapsD : translation.proof.mapClaim claimD = claimD :=
    congrFun identityMap claimD
  rw [mapsD] at principalD
  exact claimD_not_principal_meaning principalD

/-! ## Generated authorities: same checker, selected meaning -/

private def closedC : (derivationClone object).Hom [] claimC :=
  .byRule instanceC
    (instantiateRule?_eq_some_iff_application.mp c_instantiates) .nil

private def principalCertificate :
    (contract principalPresentation).Certificate () :=
  ⟨claimC, closedC⟩

private noncomputable def generatedTranslation := map principalToFree

/-- Changing the selected semantics does not change the native checker. -/
theorem selected_view_changes_meaning_not_checker :
    ((contract principalPresentation).checker ()).check claimC
        principalCertificate =
      ((contract freePresentation).checker ()).check claimC
        principalCertificate :=
  rfl

theorem principal_certificate_accepted :
    ((contract principalPresentation).checker ()).check claimC
      principalCertificate = true :=
  rfl

/-- The exact authority square transports the certificate into the free
semantic authority and preserves its positive verdict. -/
theorem translated_free_certificate_accepted :
    ((contract freePresentation).checker ()).check claimC
        (generatedTranslation.mapCertificate () principalCertificate) = true := by
  calc
    _ = ((contract principalPresentation).checker ()).check claimC
          principalCertificate :=
      generatedTranslation.check_commutes () claimC principalCertificate
    _ = true := principal_certificate_accepted

/-- The transported `C` certificate remains rejected when submitted as `D`. -/
theorem translated_certificate_rejects_claimD :
    ((contract freePresentation).checker ()).check claimD
        (generatedTranslation.mapCertificate () principalCertificate) = false :=
  mapped_certificate_rejects_wrong_claim principalToFree (by
    simp [claimC]) closedC

/-- A closed proof in this fixture can only conclude `C`. -/
private theorem closed_derivation_concludes_C {goal : Pattern}
    (derivation : (derivationClone object).Hom [] goal) : goal = claimC := by
  cases derivation with
  | assumption index => exact Fin.elim0 index
  | byRule ruleInstance application children =>
      exact application_conclusion ruleInstance application

/-- At the free perspective `D` has semantic meaning but no generated native
proof.  NIK's meaning face therefore does not collapse into derivability. -/
theorem free_claimD_meaning_but_not_scope :
    freePresentation.Meaning claimD ∧
      ¬ (theory freePresentation).Scope () claimD := by
  refine ⟨claimD_free_meaning, ?_⟩
  rintro ⟨judgedProof⟩
  have closedD : (derivationClone object).Hom [] claimD :=
    (closedProofFibreEquiv (derivationClone object) claimD).symm judgedProof
  have impossible := closed_derivation_concludes_C closedD
  simp [claimC, claimD] at impossible

#print axioms coordinate_rules_sound
#print axioms claimD_free_meaning
#print axioms claimD_not_principal_meaning
#print axioms claimD_reindexed_principal_meaning
#print axioms finite_coordinate_change_preserves_free_claimD
#print axioms finite_coordinate_change_visible_to_principal
#print axioms selected_meanings_differ
#print axioms no_identity_semantic_embedding_free_to_principal
#print axioms translated_free_certificate_accepted
#print axioms translated_certificate_rejects_claimD
#print axioms free_claimD_meaning_but_not_scope

end Mettapedia.GSLT.LanguageDef.CertificateGSLTUltrafilterSemanticAuthorityCanary
