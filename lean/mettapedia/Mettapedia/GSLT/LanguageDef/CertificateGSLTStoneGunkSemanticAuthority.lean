import Mettapedia.GSLT.LanguageDef.CertificateGSLTHeterogeneousAuthority
import Mettapedia.GSLT.LanguageDef.KernelAuthority
import Mettapedia.Logic.Metaphysics.UltrainfinitismTwoSemantics

/-!
# A concrete Stone-gunk semantic authority

This module instantiates heterogeneous CertificateGSLT authority generation
with the clopen Boolean algebra of Cantor space.  Four ground judgments name
independently defined semantic facts:

* the Cantor clopen algebra is gunky (atomless);
* its standard monadic-second-order model satisfies the free-ultrafilter
  sentence;
* its Stone space is perfect; and
* its Boolean algebra has an atom.

The authored calculus contains a witnessed gunk judgment followed by the
semantic implication chain

`gunk -> free ultrafilters -> perfect Stone space`.

Primitive-rule soundness is proved against the existing mereological, MSO,
and Stone-duality semantics.  The generated checker remains the ordinary
finite CertificateGSLT clone checker.  In particular, model existence and
semantic implication are not presented as a decision procedure for the full
theory.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLTStoneGunkSemanticAuthority

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.CertificateGSLTAuthorityFunctor
open Mettapedia.GSLT.LanguageDef.CertificateGSLTHeterogeneousAuthority
open Mettapedia.Foundations.Gunk
open Mettapedia.Logic.Metaphysics

/-- The concrete Boolean algebra used by the semantic authority. -/
abbrev CantorAlgebra := TopologicalSpace.Clopens (ℕ → Bool)

/-! ## Ground judgment vocabulary -/

def gunkClaim : Pattern := .apply "stone-gunk" []
def freeUltrafilterClaim : Pattern := .apply "stone-free-ultrafilters" []
def perfectStoneClaim : Pattern := .apply "stone-perfect-space" []
def atomicClaim : Pattern := .apply "stone-has-atom" []

private def witnessGunkRule : RuleSchema :=
  { id := ⟨"stone-gunk-witness"⟩
    metavariables := []
    premises := []
    conclusion := gunkClaim }

private def gunkToFreeRule : RuleSchema :=
  { id := ⟨"stone-gunk-to-free-ultrafilters"⟩
    metavariables := []
    premises := [gunkClaim]
    conclusion := freeUltrafilterClaim }

private def freeToPerfectRule : RuleSchema :=
  { id := ⟨"stone-free-ultrafilters-to-perfect"⟩
    metavariables := []
    premises := [freeUltrafilterClaim]
    conclusion := perfectStoneClaim }

def definition : CalculusLanguageDef :=
  CalculusLanguageDef.extend
    (LanguageDef.empty "stone-gunk-semantic-authority")
    { judgments :=
        [{ head := "stone-gunk", arity := 0 },
         { head := "stone-free-ultrafilters", arity := 0 },
         { head := "stone-perfect-space", arity := 0 },
         { head := "stone-has-atom", arity := 0 }]
      rules := [witnessGunkRule, gunkToFreeRule, freeToPerfectRule] }

private theorem emptyLanguage_validate (name : String) :
    (LanguageDef.empty name).validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [LanguageDef.empty, LanguageDef.typeNames]

private theorem emptyLanguage_terms (name : String) :
    (LanguageDef.empty name).terms = [] :=
  rfl

theorem definition_valid : definition.isValid = true := by
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  simp [definition, emptyLanguage_validate, emptyLanguage_terms,
    witnessGunkRule, gunkToFreeRule, freeToPerfectRule,
    gunkClaim, freeUltrafilterClaim, perfectStoneClaim,
    CalculusLanguageDef.judgmentSignatureValid,
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

def validated : ValidatedCalculusLanguageDef :=
  ⟨definition, definition_valid⟩

def object : CertificateGSLT.Object := ⟨validated⟩

private def witnessGunkInstance : RuleInstance :=
  ⟨⟨"stone-gunk-witness"⟩, []⟩

private def gunkToFreeInstance : RuleInstance :=
  ⟨⟨"stone-gunk-to-free-ultrafilters"⟩, []⟩

private def freeToPerfectInstance : RuleInstance :=
  ⟨⟨"stone-free-ultrafilters-to-perfect"⟩, []⟩

private theorem witness_gunk_instantiates :
    instantiateRule? validated witnessGunkInstance =
      some ([], gunkClaim) := by
  simp [instantiateRule?, validated, definition, witnessGunkRule,
    gunkToFreeRule, freeToPerfectRule, witnessGunkInstance, gunkClaim,
    CalculusLanguageDef.lookupRule?, argumentsValidAt,
    RuleSchema.sideConditionsHold, instantiateSchemas?, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemasAt?]

private theorem gunk_to_free_instantiates :
    instantiateRule? validated gunkToFreeInstance =
      some ([gunkClaim], freeUltrafilterClaim) := by
  simp [instantiateRule?, validated, definition, witnessGunkRule,
    gunkToFreeRule, freeToPerfectRule, gunkToFreeInstance, gunkClaim,
    freeUltrafilterClaim, CalculusLanguageDef.lookupRule?, argumentsValidAt,
    RuleSchema.sideConditionsHold, instantiateSchemas?, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemasAt?]

private theorem free_to_perfect_instantiates :
    instantiateRule? validated freeToPerfectInstance =
      some ([freeUltrafilterClaim], perfectStoneClaim) := by
  simp [instantiateRule?, validated, definition, witnessGunkRule,
    gunkToFreeRule, freeToPerfectRule, freeToPerfectInstance,
    freeUltrafilterClaim, perfectStoneClaim,
    CalculusLanguageDef.lookupRule?, argumentsValidAt,
    RuleSchema.sideConditionsHold, instantiateSchemas?, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemasAt?]

/-! ## Independent semantics -/

/-- Meaning is supplied by the existing Cantor-clopen model rather than by
generated derivability. -/
def Meaning (claim : Pattern) : Prop :=
  (claim = gunkClaim ∧ IsGunky CantorAlgebra) ∨
  (claim = freeUltrafilterClaim ∧
    SatSentence (Set.univ : Set (Set CantorAlgebra)) freeUFAx) ∨
  (claim = perfectStoneClaim ∧
    PerfectSpace (StoneSpace CantorAlgebra)) ∨
  (claim = atomicClaim ∧ ∃ atom : CantorAlgebra, IsAtom atom)

@[simp] theorem meaning_gunk_iff :
    Meaning gunkClaim ↔ IsGunky CantorAlgebra := by
  simp [Meaning, gunkClaim, freeUltrafilterClaim, perfectStoneClaim,
    atomicClaim]

@[simp] theorem meaning_freeUltrafilter_iff :
    Meaning freeUltrafilterClaim ↔
      SatSentence (Set.univ : Set (Set CantorAlgebra)) freeUFAx := by
  simp [Meaning, gunkClaim, freeUltrafilterClaim, perfectStoneClaim,
    atomicClaim]

@[simp] theorem meaning_perfectStone_iff :
    Meaning perfectStoneClaim ↔
      PerfectSpace (StoneSpace CantorAlgebra) := by
  simp [Meaning, gunkClaim, freeUltrafilterClaim, perfectStoneClaim,
    atomicClaim]

@[simp] theorem meaning_atomic_iff :
    Meaning atomicClaim ↔ ∃ atom : CantorAlgebra, IsAtom atom := by
  simp [Meaning, gunkClaim, freeUltrafilterClaim, perfectStoneClaim,
    atomicClaim]

/-! ## Exact primitive-rule shapes -/

theorem application_shape
    (ruleInstance : RuleInstance) {premises : List Pattern}
    {conclusion : Pattern}
    (application : RuleApplication validated ruleInstance premises conclusion) :
    (premises = [] ∧ conclusion = gunkClaim) ∨
      (premises = [gunkClaim] ∧ conclusion = freeUltrafilterClaim) ∨
      (premises = [freeUltrafilterClaim] ∧
        conclusion = perfectStoneClaim) := by
  rcases ruleInstance with ⟨⟨ruleId⟩, arguments⟩
  cases application with
  | intro rule lookup argumentsValid sideConditions premisesInstantiate
      conclusionInstantiates =>
      simp [validated, definition, witnessGunkRule, gunkToFreeRule,
        freeToPerfectRule, CalculusLanguageDef.lookupRule?] at lookup
      rcases lookup with ⟨ruleIdShape, rfl⟩ | ⟨_, remaining⟩
      · subst ruleId
        cases arguments with
        | cons argument arguments =>
            simp [argumentsValidAt] at argumentsValid
        | nil =>
            have reconstructed :
                RuleApplication validated witnessGunkInstance premises
                  conclusion :=
              .intro witnessGunkRule (by rfl) argumentsValid sideConditions
                premisesInstantiate conclusionInstantiates
            have canonical :
                RuleApplication validated witnessGunkInstance [] gunkClaim :=
              instantiateRule?_eq_some_iff_application.mp
                witness_gunk_instantiates
            exact Or.inl (reconstructed.outputs_unique canonical)
      · rcases remaining with ⟨ruleIdShape, rfl⟩ | ⟨_, ruleIdShape, rfl⟩
        · subst ruleId
          cases arguments with
          | cons argument arguments =>
              simp [argumentsValidAt] at argumentsValid
          | nil =>
              have reconstructed :
                  RuleApplication validated gunkToFreeInstance premises
                    conclusion :=
                .intro gunkToFreeRule (by rfl) argumentsValid sideConditions
                  premisesInstantiate conclusionInstantiates
              have canonical :
                  RuleApplication validated gunkToFreeInstance [gunkClaim]
                    freeUltrafilterClaim :=
                instantiateRule?_eq_some_iff_application.mp
                  gunk_to_free_instantiates
              exact Or.inr (Or.inl
                (reconstructed.outputs_unique canonical))
        · subst ruleId
          cases arguments with
          | cons argument arguments =>
              simp [argumentsValidAt] at argumentsValid
          | nil =>
              have reconstructed :
                  RuleApplication validated freeToPerfectInstance premises
                    conclusion :=
                .intro freeToPerfectRule (by rfl) argumentsValid sideConditions
                  premisesInstantiate conclusionInstantiates
              have canonical :
                  RuleApplication validated freeToPerfectInstance
                    [freeUltrafilterClaim] perfectStoneClaim :=
                instantiateRule?_eq_some_iff_application.mp
                  free_to_perfect_instantiates
              exact Or.inr (Or.inr
                (reconstructed.outputs_unique canonical))

theorem rules_sound : RulesSound object Meaning := by
  intro ruleInstance premises conclusion application premisesMeaning
  change RuleApplication validated ruleInstance premises conclusion at application
  rcases application_shape ruleInstance application with
      ⟨premisesShape, conclusionShape⟩ |
      ⟨premisesShape, conclusionShape⟩ |
      ⟨premisesShape, conclusionShape⟩
  · subst premises
    subst conclusion
    exact meaning_gunk_iff.mpr isGunky_clopens_cantor
  · subst premises
    subst conclusion
    have gunky : IsGunky CantorAlgebra :=
      meaning_gunk_iff.mp (premisesMeaning gunkClaim (by simp))
    exact meaning_freeUltrafilter_iff.mpr
      (sat_freeUFAx_iff_isGunky.mpr gunky)
  · subst premises
    subst conclusion
    have freeMeaning :
        SatSentence (Set.univ : Set (Set CantorAlgebra)) freeUFAx :=
      meaning_freeUltrafilter_iff.mp
        (premisesMeaning freeUltrafilterClaim (by simp))
    exact meaning_perfectStone_iff.mpr
      (sat_freeUFAx_iff_perfect_stoneSpace.mp freeMeaning)

def presentation : SemanticPresentation where
  object := object
  Meaning := Meaning
  rulesSound := rules_sound

def authority := generatedAuthority presentation

/-! ## The concrete proof path and semantic controls -/

def closedGunk : (derivationClone object).Hom [] gunkClaim :=
  .byRule witnessGunkInstance
    (instantiateRule?_eq_some_iff_application.mp witness_gunk_instantiates) .nil

def closedFreeUltrafilter :
    (derivationClone object).Hom [] freeUltrafilterClaim :=
  .byRule gunkToFreeInstance
    (instantiateRule?_eq_some_iff_application.mp gunk_to_free_instantiates)
    (.cons closedGunk .nil)

def closedPerfectStone :
    (derivationClone object).Hom [] perfectStoneClaim :=
  .byRule freeToPerfectInstance
    (instantiateRule?_eq_some_iff_application.mp free_to_perfect_instantiates)
    (.cons closedFreeUltrafilter .nil)

def perfectStoneCertificate : (contract presentation).Certificate () :=
  ⟨perfectStoneClaim, closedPerfectStone⟩

theorem gunk_has_independent_meaning : Meaning gunkClaim :=
  meaning_gunk_iff.mpr isGunky_clopens_cantor

theorem freeUltrafilter_has_independent_meaning :
    Meaning freeUltrafilterClaim :=
  meaning_freeUltrafilter_iff.mpr
    (sat_freeUFAx_iff_isGunky.mpr isGunky_clopens_cantor)

theorem perfectStone_has_independent_meaning : Meaning perfectStoneClaim :=
  meaning_perfectStone_iff.mpr
    (isGunky_iff_perfect_stoneSpace.mp isGunky_clopens_cantor)

theorem atomic_lacks_independent_meaning : ¬ Meaning atomicClaim := by
  rw [meaning_atomic_iff]
  rintro ⟨atom, isAtom⟩
  exact (isGunky_iff_no_isAtom.mp isGunky_clopens_cantor atom) isAtom

/-- Exact characterization of this deliberately finite selected semantic
interface.  This theorem does not characterize all MSO sentences of the
Cantor-clopen model. -/
theorem meaning_iff_selected_positive_claims (claim : Pattern) :
    Meaning claim ↔
      claim = gunkClaim ∨ claim = freeUltrafilterClaim ∨
        claim = perfectStoneClaim := by
  constructor
  · intro meaningful
    rcases meaningful with gunk | free | perfect | atomic
    · exact Or.inl gunk.1
    · exact Or.inr (Or.inl free.1)
    · exact Or.inr (Or.inr perfect.1)
    · rcases atomic.2 with ⟨atom, isAtom⟩
      exact False.elim
        ((isGunky_iff_no_isAtom.mp isGunky_clopens_cantor atom) isAtom)
  · rintro (equal | equal | equal)
    · subst claim
      exact gunk_has_independent_meaning
    · subst claim
      exact freeUltrafilter_has_independent_meaning
    · subst claim
      exact perfectStone_has_independent_meaning

/-- Direct decision is available for the four-judgment selected interface.
It recognizes three semantically proved positive claims and rejects every
other pattern.  No claim about deciding the full atomless Boolean-algebra or
MSO theory is made. -/
def selectedFragmentDecisionKernel :
    Mettapedia.GSLT.LanguageDef.KernelAuthority.Checker.DecisionKernel
      Pattern Meaning where
  decide claim := decide
    (claim = gunkClaim ∨ claim = freeUltrafilterClaim ∨
      claim = perfectStoneClaim)
  correct claim := by
    rw [decide_eq_true_iff]
    exact (meaning_iff_selected_positive_claims claim).symm

@[simp] theorem selectedFragment_decides_perfectStone :
    selectedFragmentDecisionKernel.decide perfectStoneClaim = true := by
  simp [selectedFragmentDecisionKernel]

@[simp] theorem selectedFragment_rejects_atomic :
    selectedFragmentDecisionKernel.decide atomicClaim = false := by
  simp [selectedFragmentDecisionKernel, atomicClaim, gunkClaim,
    freeUltrafilterClaim, perfectStoneClaim]

theorem perfectStone_derivation_has_three_rule_nodes :
    closedPerfectStone.ruleCount = 3 :=
  rfl

theorem perfectStone_certificate_accepted :
    ((contract presentation).checker ()).check perfectStoneClaim
      perfectStoneCertificate = true :=
  generated_checker_accepts_exact_claim presentation.toSoundPresentation
    closedPerfectStone

theorem perfectStone_certificate_rejected_at_atomic_claim :
    ((contract presentation).checker ()).check atomicClaim
      perfectStoneCertificate = false := by
  change decide (perfectStoneClaim = atomicClaim) = false
  decide

/-- Every native closed derivation concludes one of the three selected
semantic judgments. -/
theorem closed_derivation_conclusion {goal : Pattern}
    (derivation : (derivationClone object).Hom [] goal) :
    goal = gunkClaim ∨ goal = freeUltrafilterClaim ∨
      goal = perfectStoneClaim := by
  cases derivation with
  | assumption index => exact Fin.elim0 index
  | byRule ruleInstance application children =>
      rcases application_shape ruleInstance application with
          ⟨_, conclusionShape⟩ |
          ⟨_, conclusionShape⟩ |
          ⟨_, conclusionShape⟩
      · exact Or.inl conclusionShape
      · exact Or.inr (Or.inl conclusionShape)
      · exact Or.inr (Or.inr conclusionShape)

/-- No native closed derivation can conclude the semantically false atomic
claim. -/
theorem no_closed_atomic_derivation :
    ¬ Nonempty ((derivationClone object).Hom [] atomicClaim) := by
  rintro ⟨derivation⟩
  rcases closed_derivation_conclusion derivation with
      conclusionShape | conclusionShape | conclusionShape <;>
    simp [atomicClaim, gunkClaim, freeUltrafilterClaim,
      perfectStoneClaim] at conclusionShape

theorem atomic_outside_generated_scope :
    ¬ (theory presentation).Scope () atomicClaim := by
  rintro ⟨judgedProof⟩
  exact no_closed_atomic_derivation ⟨
    (closedProofFibreEquiv (derivationClone object) atomicClaim).symm
      judgedProof⟩

/-- A closed native derivation supplies generated proof scope. -/
theorem scope_of_closed {claim : Pattern}
    (derivation : (derivationClone object).Hom [] claim) :
    (theory presentation).Scope () claim :=
  ⟨(closedProofFibreEquiv (derivationClone object) claim) derivation⟩

/-- On this finite selected interface, the three-rule calculus is not only
sound but complete for the independently supplied semantics. -/
theorem meaning_iff_generated_scope (claim : Pattern) :
    Meaning claim ↔ (theory presentation).Scope () claim := by
  constructor
  · intro meaningful
    rcases (meaning_iff_selected_positive_claims claim).mp meaningful with
        equal | equal | equal
    · subst claim
      exact scope_of_closed closedGunk
    · subst claim
      exact scope_of_closed closedFreeUltrafilter
    · subst claim
      exact scope_of_closed closedPerfectStone
  · intro inScope
    exact (theory presentation).scope_sound () claim inScope

/-- The proof-carrying checker is also exact for selected semantic meaning,
not merely for native proof scope, because scope and meaning coincide on this
finite interface. -/
theorem certificate_semantic_authority :
    ((contract presentation).checker ()).Authority Meaning := by
  have scopeAuthority := (contract presentation).scopeAuthority ()
  constructor
  · intro claim certificate accepted
    exact (meaning_iff_generated_scope claim).mpr
      (scopeAuthority.sound claim certificate accepted)
  · intro claim meaningful
    exact scopeAuthority.complete claim
      ((meaning_iff_generated_scope claim).mp meaningful)

/-- The same selected semantics admits both direct decision and retained
proof-carrying replay.  These are two interfaces to one finite semantic
fragment, not an identification of decision with proof identity. -/
theorem selected_fragment_has_decision_and_certificate_authority :
    Nonempty
        (Mettapedia.GSLT.LanguageDef.KernelAuthority.Checker.DecisionKernel
          Pattern Meaning) ∧
      ((contract presentation).checker ()).Authority Meaning :=
  ⟨⟨selectedFragmentDecisionKernel⟩, certificate_semantic_authority⟩

#print axioms definition_valid
#print axioms rules_sound
#print axioms perfectStone_has_independent_meaning
#print axioms atomic_lacks_independent_meaning
#print axioms meaning_iff_selected_positive_claims
#print axioms selectedFragmentDecisionKernel
#print axioms perfectStone_certificate_accepted
#print axioms perfectStone_certificate_rejected_at_atomic_claim
#print axioms closed_derivation_conclusion
#print axioms atomic_outside_generated_scope
#print axioms meaning_iff_generated_scope
#print axioms certificate_semantic_authority
#print axioms selected_fragment_has_decision_and_certificate_authority

end Mettapedia.GSLT.LanguageDef.CertificateGSLTStoneGunkSemanticAuthority
