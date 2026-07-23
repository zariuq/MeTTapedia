import Mettapedia.Languages.Metamath.InferenceProjectionInvariants

/-!
# Generated active-hypothesis leaves

An active hypothesis retained by a successful prefix projection determines an
exact zero-premise source rule and a root-pinned typed leaf.  This static
module contains no proof-state execution theorem, so recursive native-proof
structure can depend on it without importing the live-step agreement layer.

The root-pinned wrapper is intentional.  An arbitrary
`Derivation target (proves formula)` does not by itself reveal whether its root
is an active-hypothesis rule or an assertion rule.  Reflecting arbitrary
`Proves` derivations therefore remains a separate source-rule-classification
obligation; no such reflection is assumed here.
-/

namespace Mettapedia.Languages.Metamath.InferenceHypothesisStepAgreement

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection

/-! ## Exact generated leaf -/

/-- The unique argument-free instance intended for an active hypothesis. -/
def activeHypothesisRuleInstance (hypothesis : HypothesisView) : RuleInstance :=
  { ruleId := ⟨hypothesis.label⟩
    arguments := [] }

private theorem length_eraseDups_le {alpha : Type} [BEq alpha]
    (values : List alpha) :
    values.eraseDups.length ≤ values.length := by
  induction hlength : values.length using Nat.strong_induction_on
      generalizing values with
  | h size ih =>
      cases values with
      | nil => simp
      | cons value values =>
          simp only [List.length_cons] at hlength
          subst size
          rw [List.eraseDups_cons]
          simp only [List.length_cons]
          apply Nat.succ_le_succ
          exact
            (ih _ (by
              have :=
                List.length_filter_le (fun candidate => !candidate == value)
                  values
              omega) _ rfl).trans
              (List.length_filter_le _ _)

private theorem find?_eq_some_of_mem_of_map_eraseDups_length_eq
    {alpha beta : Type} [BEq beta] [LawfulBEq beta] [DecidableEq beta]
    (key : alpha → beta) (values : List alpha) (target : alpha)
    (hunique : (values.map key).eraseDups.length = values.length)
    (hmem : target ∈ values) :
    values.find? (fun value => decide (key value = key target)) =
      some target := by
  induction values with
  | nil => simp at hmem
  | cons head tail ih =>
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · simp [List.find?]
      · rw [List.map_cons, List.eraseDups_cons] at hunique
        simp only [List.length_cons, Nat.succ.injEq] at hunique
        have heraseLe :=
          length_eraseDups_le
            ((tail.map key).filter fun value => !value == key head)
        have hfilterLe := List.length_filter_le
          (fun value => !value == key head) (tail.map key)
        have htailLeFilter :
            (tail.map key).length ≤
              ((tail.map key).filter fun value =>
                !value == key head).length := by
          simp only [List.length_map]
          rw [← hunique]
          exact heraseLe
        have hfilterLength :
            ((tail.map key).filter fun value => !value == key head).length =
              (tail.map key).length :=
          Nat.le_antisymm hfilterLe htailLeFilter
        have hall := List.length_filter_eq_length_iff.mp hfilterLength
        have hheadNe : key head ≠ key target := by
          intro heq
          have htarget : key target ∈ tail.map key :=
            List.mem_map_of_mem hmem
          have hkept := hall (key target) htarget
          simp [heq] at hkept
        have htailUnique :
            (tail.map key).eraseDups.length = tail.length := by
          have hfilterEq :
              (tail.map key).filter (fun value => !value == key head) =
                tail.map key :=
            List.filter_eq_self.mpr hall
          rw [hfilterEq] at hunique
          exact hunique
        rw [List.find?_cons]
        simp [hheadNe, ih htailUnique hmem]

private theorem lookupRule?_eq_some_of_mem
    (presentation : ValidatedPresentation) {rule : RuleSchema}
    (hmem : rule ∈ presentation.1.rules) :
    presentation.1.lookupRule? rule.id = some rule := by
  have hvalid := presentation.2
  simp only [Presentation.isValidV2, Presentation.isValidV1,
    Bool.and_eq_true, beq_iff_eq] at hvalid
  have hunique :
      (presentation.1.rules.map RuleSchema.id).eraseDups.length =
        presentation.1.rules.length := by
    simpa [Presentation.ruleIds] using hvalid.1.1.1.2
  simpa [Presentation.lookupRule?] using
    find?_eq_some_of_mem_of_map_eraseDups_length_eq
      RuleSchema.id presentation.1.rules rule hunique hmem

/-- Active-hypothesis membership selects its exact generated schema. -/
theorem lookup_activeHypothesisRule_of_projection
    (projection : PrefixProjection) (target : ValidatedPresentation)
    (hprojection :
      presentationOfProjection? projection = some target.1)
    {hypothesis : HypothesisView}
    (hmember : hypothesis ∈ projection.activeHypotheses) :
    target.1.lookupRule? ⟨hypothesis.label⟩ =
      some (activeHypothesisRule hypothesis) := by
  have hruleMember :
      activeHypothesisRule hypothesis ∈ target.1.rules := by
    rw [rules_eq_of_presentationOfProjection?_eq_some
      projection target.1 hprojection]
    apply List.mem_append.mpr
    apply Or.inr
    unfold generatedSourceRules
    apply List.mem_append.mpr
    apply Or.inl
    exact List.mem_map.mpr ⟨hypothesis, hmember, rfl⟩
  change target.1.lookupRule? (activeHypothesisRule hypothesis).id =
    some (activeHypothesisRule hypothesis)
  exact lookupRule?_eq_some_of_mem target hruleMember

mutual

private theorem instantiateSchemaAt?_ground_identity
    (formals : List (String × Nat)) (arguments : List Pattern)
    (depth : Nat) (schema : Pattern)
    (hground : schema.isGroundAt depth = true) :
    instantiateSchemaAt? formals arguments depth schema = some schema := by
  cases schema with
  | bvar index => simp [instantiateSchemaAt?]
  | fvar name => simp [Pattern.isGroundAt] at hground
  | apply constructor schemas =>
      simp only [Pattern.isGroundAt] at hground
      simp [instantiateSchemaAt?,
        instantiateSchemasAt?_ground_identity formals arguments depth schemas
          hground]
  | lambda binder body =>
      simp only [Pattern.isGroundAt] at hground
      simp [instantiateSchemaAt?, instantiateSchemaAt?_ground_identity
        formals arguments (depth + 1) body hground]
  | multiLambda arity binders body =>
      simp only [Pattern.isGroundAt] at hground
      simp [instantiateSchemaAt?, instantiateSchemaAt?_ground_identity
        formals arguments (depth + arity) body hground]
  | subst body replacement =>
      simp only [Pattern.isGroundAt, Bool.and_eq_true] at hground
      simp [instantiateSchemaAt?, instantiateSchemaAt?_ground_identity
        formals arguments (depth + 1) body hground.1,
        instantiateSchemaAt?_ground_identity formals arguments depth replacement
          hground.2]
  | collection collectionType schemas rest =>
      simp only [Pattern.isGroundAt, Bool.and_eq_true] at hground
      cases rest with
      | some restName => simp at hground
      | none =>
          simp [instantiateSchemaAt?,
            instantiateSchemasAt?_ground_identity formals arguments depth
              schemas hground.1]
termination_by sizeOf schema

private theorem instantiateSchemasAt?_ground_identity
    (formals : List (String × Nat)) (arguments : List Pattern)
    (depth : Nat) (schemas : List Pattern)
    (hground : Pattern.isGroundListAt depth schemas = true) :
    instantiateSchemasAt? formals arguments depth schemas = some schemas := by
  cases schemas with
  | nil => simp [instantiateSchemasAt?]
  | cons schema schemas =>
      simp only [Pattern.isGroundListAt, Bool.and_eq_true] at hground
      simp [instantiateSchemasAt?, instantiateSchemaAt?_ground_identity
        formals arguments depth schema hground.1,
        instantiateSchemasAt?_ground_identity formals arguments depth schemas
          hground.2]
termination_by sizeOf schemas

end


@[simp] private theorem encodeSym_isGroundAt (depth : Nat)
    (symbol : RuntimeSym) :
    (encodeSym symbol).isGroundAt depth = true := by
  cases symbol <;>
    simp [encodeSym, encodeString, Builder.constSym, Builder.varSym,
      Builder.encodedString, Builder.rawString, Pattern.isGroundAt,
      Pattern.isGroundListAt]

@[simp] private theorem encodeListWith_encodeSym_isGroundAt
    (depth : Nat) (body : List RuntimeSym) :
    (encodeListWith encodeSym body).isGroundAt depth = true := by
  induction body with
  | nil =>
      simp [encodeListWith, Builder.nil,
        Pattern.isGroundAt, Pattern.isGroundListAt]
  | cons symbol body ih =>
      simp [encodeListWith, Builder.cons,
        Pattern.isGroundAt, Pattern.isGroundListAt, ih]

@[simp] private theorem encodeFormula_isGroundAt (depth : Nat)
    (formula : ConstantHeadedFormula) :
    (encodeFormula formula).isGroundAt depth = true := by
  rcases formula with ⟨typecode, body⟩
  simp [encodeFormula, Builder.formula, encodeString,
    Builder.encodedString, Builder.rawString, Pattern.isGroundAt,
    Pattern.isGroundListAt]

@[simp] private theorem proves_encodeFormula_isGroundAt (depth : Nat)
    (formula : ConstantHeadedFormula) :
    (proves (encodeFormula formula)).isGroundAt depth = true := by
  simp [proves, Pattern.isGroundAt, Pattern.isGroundListAt]

/-- The canonical active-hypothesis instance has no premises and concludes
the exact encoded formula retained by the projection. -/
theorem activeHypothesisRule_application
    (projection : PrefixProjection) (target : ValidatedPresentation)
    (hprojection :
      presentationOfProjection? projection = some target.1)
    {hypothesis : HypothesisView}
    (hmember : hypothesis ∈ projection.activeHypotheses) :
    RuleApplication target (activeHypothesisRuleInstance hypothesis) []
      (proves (encodeFormula hypothesis.formula)) := by
  apply instantiateRule?_eq_some_iff_application.mp
  have hlookup := lookup_activeHypothesisRule_of_projection
    projection target hprojection hmember
  have hconclusion :
      instantiateSchema? [] [] (proves (encodeFormula hypothesis.formula)) =
        some (proves (encodeFormula hypothesis.formula)) := by
    exact instantiateSchemaAt?_ground_identity [] [] 0
      (proves (encodeFormula hypothesis.formula)) (by simp)
  simp [instantiateRule?, activeHypothesisRuleInstance,
    activeHypothesisRule, hlookup, argumentsValidAt,
    instantiateSchemas?, instantiateSchemasAt?, hconclusion]

/-- Root-pinned proof-relevant evidence for exactly one generated active
hypothesis leaf.  Unlike a bare `Derivation`, this records which source rule
is at the root. -/
structure GeneratedActiveHypothesisLeaf
    (target : ValidatedPresentation) (hypothesis : HypothesisView) : Type where
  application :
    RuleApplication target (activeHypothesisRuleInstance hypothesis) []
      (proves (encodeFormula hypothesis.formula))

/-- Forget the root-pinning only after constructing the exact zero-child
leaf. -/
def GeneratedActiveHypothesisLeaf.toDerivation
    {target : ValidatedPresentation} {hypothesis : HypothesisView}
    (leaf : GeneratedActiveHypothesisLeaf target hypothesis) :
    Derivation target (proves (encodeFormula hypothesis.formula)) :=
  .byRule (activeHypothesisRuleInstance hypothesis) leaf.application .nil

/-- Projection membership constructs the exact root-pinned generated leaf. -/
def generatedActiveHypothesisLeaf
    (projection : PrefixProjection) (target : ValidatedPresentation)
    (hprojection :
      presentationOfProjection? projection = some target.1)
    {hypothesis : HypothesisView}
    (hmember : hypothesis ∈ projection.activeHypotheses) :
    GeneratedActiveHypothesisLeaf target hypothesis :=
  ⟨activeHypothesisRule_application projection target hprojection hmember⟩

/-- Stable convenience API for recursive source-pinned proof structure. -/
def activeHypothesisDerivation
    (projection : PrefixProjection) (target : ValidatedPresentation)
    (hprojection :
      presentationOfProjection? projection = some target.1)
    {hypothesis : HypothesisView}
    (hmember : hypothesis ∈ projection.activeHypotheses) :
    Derivation target (proves (encodeFormula hypothesis.formula)) :=
  (generatedActiveHypothesisLeaf projection target hprojection hmember).toDerivation

@[simp] theorem GeneratedActiveHypothesisLeaf.erase_toDerivation
    {target : ValidatedPresentation} {hypothesis : HypothesisView}
    (leaf : GeneratedActiveHypothesisLeaf target hypothesis) :
    leaf.toDerivation.erase =
      .node (activeHypothesisRuleInstance hypothesis) [] := by
  simp [GeneratedActiveHypothesisLeaf.toDerivation, Derivation.erase,
    DerivationList.erase]

/-- Any application of the same explicit zero-argument source instance has
the canonical empty premise vector and canonical encoded conclusion.  This is
local-rule identification, not reflection of arbitrary `Proves` trees. -/
theorem activeHypothesisRule_application_outputs
    (projection : PrefixProjection) (target : ValidatedPresentation)
    (hprojection :
      presentationOfProjection? projection = some target.1)
    {hypothesis : HypothesisView}
    (hmember : hypothesis ∈ projection.activeHypotheses)
    {premises : List Pattern} {conclusion : Pattern}
    (application : RuleApplication target
      (activeHypothesisRuleInstance hypothesis) premises conclusion) :
    premises = [] ∧
      conclusion = proves (encodeFormula hypothesis.formula) := by
  exact application.outputs_unique
    (activeHypothesisRule_application projection target hprojection hmember)

/-! ## Positive and negative boundaries -/

/-- Positive: active membership constructs a typed, zero-child leaf. -/
example (projection : PrefixProjection) (target : ValidatedPresentation)
    (hprojection :
      presentationOfProjection? projection = some target.1)
    (hypothesis : HypothesisView)
    (hmember : hypothesis ∈ projection.activeHypotheses) :
    Derivation target (proves (encodeFormula hypothesis.formula)) :=
  activeHypothesisDerivation projection target hprojection hmember

/-- Negative: the pinned active-hypothesis instance cannot acquire a
nonempty premise vector. -/
theorem not_activeHypothesisRule_application_of_nonempty_premises
    (projection : PrefixProjection) (target : ValidatedPresentation)
    (hprojection :
      presentationOfProjection? projection = some target.1)
    {hypothesis : HypothesisView}
    (hmember : hypothesis ∈ projection.activeHypotheses)
    {premises : List Pattern} {conclusion : Pattern}
    (hpremises : premises ≠ []) :
    ¬ RuleApplication target (activeHypothesisRuleInstance hypothesis)
      premises conclusion := by
  intro application
  exact hpremises
    (activeHypothesisRule_application_outputs projection target hprojection
      hmember application).1

end Mettapedia.Languages.Metamath.InferenceHypothesisStepAgreement
