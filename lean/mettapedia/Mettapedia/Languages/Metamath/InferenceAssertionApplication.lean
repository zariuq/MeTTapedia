import Mettapedia.Languages.Metamath.InferenceProjectionSideConservativity
import Mettapedia.Languages.Metamath.InferenceProjectionInvariants
import Mettapedia.Languages.Metamath.InferenceSideConditionsSemantics

/-!
# Independent Metamath assertion-application semantics

This module characterizes one generated assertion-rule node.  The independent
relation records ordered mandatory-hypothesis instances, the exact finite
substitution contributed by floating hypotheses, essential-hypothesis
substitution, disjoint-variable checking, and the exact substituted result.

The generated-node witness contains the local `RuleApplication` and derivations
of its side premises.  Proofs of the leading `Proves` premises remain an
explicit input to a separate assembly operation; this module does not invent
them and does not discuss runtime `stepNormal`.
-/

namespace Mettapedia.Languages.Metamath.InferenceProjection.AssertionApplication

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceSideConditions
open Mettapedia.Languages.Metamath.InferenceSideConditionsSemantics
open Mettapedia.Languages.Metamath.InferenceProjection

/-! ## Independent relation -/

/-- Mandatory hypotheses and actual formulas in exact appearance order.
Floating hypotheses contribute one ordered substitution binding; essential
hypotheses contribute none.  Every actual retains its authored typecode. -/
inductive HypothesisInstances :
    List HypothesisView → List ConstantHeadedFormula →
      FiniteSubstitution → Prop where
  | nil : HypothesisInstances [] [] []
  | floating {label typecode variableName : String}
      {actual : ConstantHeadedFormula}
      {hypotheses : List HypothesisView}
      {actuals : List ConstantHeadedFormula}
      {substitution : FiniteSubstitution}
      (typecode_eq : actual.typecode = typecode)
      (tail : HypothesisInstances hypotheses actuals substitution) :
      HypothesisInstances
        (.floating label typecode variableName :: hypotheses)
        (actual :: actuals)
        (⟨variableName, actual⟩ :: substitution)
  | essential {label : String} {formula actual : ConstantHeadedFormula}
      {hypotheses : List HypothesisView}
      {actuals : List ConstantHeadedFormula}
      {substitution : FiniteSubstitution}
      (typecode_eq : actual.typecode = formula.typecode)
      (tail : HypothesisInstances hypotheses actuals substitution) :
      HypothesisInstances
        (.essential label formula :: hypotheses)
        (actual :: actuals) substitution

/-- Independent semantic checks for essential hypotheses, in their original
order and against the completed substitution. -/
def EssentialMatches (substitution : FiniteSubstitution) :
    List HypothesisView → List ConstantHeadedFormula → Prop
  | [], [] => True
  | .floating _ _ _ :: hypotheses, _ :: actuals =>
      EssentialMatches substitution hypotheses actuals
  | .essential _ formula :: hypotheses, actual :: actuals =>
      FormulaSubstitutionSemantics substitution formula actual ∧
        EssentialMatches substitution hypotheses actuals
  | _, _ => False

/-- Proof-tree-independent meaning of applying one stored assertion. -/
def AssertionApplicationSemantics (callerFrame : RuntimeFrame)
    (assertion : AssertionView) (actuals : List ConstantHeadedFormula)
    (result : ConstantHeadedFormula) : Prop :=
  ∃ substitution,
    HypothesisInstances assertion.hypotheses actuals substitution ∧
      EssentialMatches substitution assertion.hypotheses actuals ∧
      DVOKSemantics substitution callerFrame assertion.frame ∧
      FormulaSubstitutionSemantics substitution assertion.formula result

theorem HypothesisInstances.lengths
    {hypotheses : List HypothesisView}
    {actuals : List ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    (instances : HypothesisInstances hypotheses actuals substitution) :
    hypotheses.length = actuals.length := by
  induction instances with
  | nil => rfl
  | floating _ _ ih | essential _ _ ih => simp [ih]

private theorem assertionHypothesisFormalsFrom_length
    (index : Nat) (hypotheses : List HypothesisView) :
    (assertionHypothesisFormalsFrom index hypotheses).length =
      hypotheses.length := by
  induction hypotheses generalizing index with
  | nil => rfl
  | cons hypothesis hypotheses ih =>
      cases hypothesis <;>
        simp [assertionHypothesisFormalsFrom, ih]

theorem not_assertionApplicationSemantics_of_result_typecode_ne
    {callerFrame : RuntimeFrame} {assertion : AssertionView}
    {actuals : List ConstantHeadedFormula}
    {result : ConstantHeadedFormula}
    (hne : assertion.formula.typecode ≠ result.typecode) :
    ¬ AssertionApplicationSemantics callerFrame assertion actuals result := by
  rintro ⟨substitution, _, _, _, hresult⟩
  exact hne hresult.1

theorem not_assertionApplicationSemantics_of_length_ne
    {callerFrame : RuntimeFrame} {assertion : AssertionView}
    {actuals : List ConstantHeadedFormula}
    {result : ConstantHeadedFormula}
    (hne : assertion.hypotheses.length ≠ actuals.length) :
    ¬ AssertionApplicationSemantics callerFrame assertion actuals result := by
  rintro ⟨substitution, instances, _⟩
  exact hne instances.lengths

/-! ## Canonical generated-node data -/

def formulaBodyPattern (formula : ConstantHeadedFormula) : Pattern :=
  encodeListWith encodeSym formula.body

def assertionRuleArguments (actuals : List ConstantHeadedFormula)
    (result : ConstantHeadedFormula) : List Pattern :=
  actuals.map formulaBodyPattern ++ [formulaBodyPattern result]

def assertionProvesPremises
    (actuals : List ConstantHeadedFormula) : List Pattern :=
  actuals.map fun actual => proves (encodeFormula actual)

def assertionEssentialPremises (substitution : FiniteSubstitution) :
    List HypothesisView → List ConstantHeadedFormula → List Pattern
  | [], [] => []
  | .floating _ _ _ :: hypotheses, _ :: actuals =>
      assertionEssentialPremises substitution hypotheses actuals
  | .essential _ formula :: hypotheses, actual :: actuals =>
      applySubst (encodeSubstitution substitution) (encodeFormula formula)
        (encodeFormula actual) ::
          assertionEssentialPremises substitution hypotheses actuals
  | _, _ => []

def assertionSidePremises (substitution : FiniteSubstitution)
    (callerFrame : RuntimeFrame) (assertion : AssertionView)
    (actuals : List ConstantHeadedFormula)
    (result : ConstantHeadedFormula) : List Pattern :=
  assertionEssentialPremises substitution assertion.hypotheses actuals ++
    [ dvOK (encodeSubstitution substitution) (encodeFrame callerFrame)
        (encodeFrame assertion.frame)
    , applySubst (encodeSubstitution substitution)
        (encodeFormula assertion.formula) (encodeFormula result) ]

def assertionPremises (substitution : FiniteSubstitution)
    (callerFrame : RuntimeFrame) (assertion : AssertionView)
    (actuals : List ConstantHeadedFormula)
    (result : ConstantHeadedFormula) : List Pattern :=
  assertionProvesPremises actuals ++
    assertionSidePremises substitution callerFrame assertion actuals result

def assertionRuleInstance (assertion : AssertionView)
    (actuals : List ConstantHeadedFormula)
    (result : ConstantHeadedFormula) : RuleInstance :=
  { ruleId := ⟨assertion.label⟩
    arguments := assertionRuleArguments actuals result }

/-! ## Exact projected rule lookup -/

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
    simpa [Presentation.ruleIds] using hvalid.1.1.2
  simpa [Presentation.lookupRule?] using
    find?_eq_some_of_mem_of_map_eraseDups_length_eq
      RuleSchema.id presentation.1.rules rule hunique hmem

/-- Assertion membership in an exact successful projection determines the
schema selected by the assertion label. -/
theorem lookup_assertionRule_of_projection
    (projection : PrefixProjection) (target : ValidatedPresentation)
    (hprojection :
      presentationOfProjection? projection = some target.1)
    {assertion : AssertionView} (hassertion : assertion ∈ projection.assertions) :
    target.1.lookupRule? ⟨assertion.label⟩ =
      some (assertionRule projection.callerFrame assertion) := by
  have hmem :
      assertionRule projection.callerFrame assertion ∈ target.1.rules := by
    rw [rules_eq_of_presentationOfProjection?_eq_some
      projection target.1 hprojection]
    apply List.mem_append.mpr
    apply Or.inr
    unfold generatedSourceRules
    apply List.mem_append.mpr
    apply Or.inr
    exact List.mem_map.mpr ⟨assertion, hassertion, rfl⟩
  change target.1.lookupRule?
      (assertionRule projection.callerFrame assertion).id =
    some (assertionRule projection.callerFrame assertion)
  exact lookupRule?_eq_some_of_mem target hmem

private theorem assertionRuleFormalNames_nodup_of_lookup
    (target : ValidatedPresentation) (callerFrame : RuntimeFrame)
    (assertion : AssertionView)
    (hlookup :
      target.1.lookupRule? ⟨assertion.label⟩ =
        some (assertionRule callerFrame assertion)) :
    ((assertionRule callerFrame assertion).metavariables.map Prod.fst).Nodup := by
  have hvalidIn := rule_isValidIn_of_lookup target hlookup
  have hvalidV1 : (assertionRule callerFrame assertion).isValidV1 = true := by
    simp only [RuleSchema.isValidIn, Bool.and_eq_true] at hvalidIn
    exact hvalidIn.1
  have hunique :
      ((assertionRule callerFrame assertion).metavariableNames.eraseDups).length =
        (assertionRule callerFrame assertion).metavariableNames.length := by
    simp only [RuleSchema.isValidV1, Bool.and_eq_true, beq_iff_eq] at hvalidV1
    exact hvalidV1.1.1.1.1.1.2
  have hnames :
      (assertionRule callerFrame assertion).metavariableNames.Nodup :=
    nodup_of_eraseDups_length_eq _ hunique
  simpa [RuleSchema.metavariableNames] using hnames

private theorem assertionHypothesisFormalNames_nodup_of_lookup
    (target : ValidatedPresentation) (callerFrame : RuntimeFrame)
    (assertion : AssertionView)
    (hlookup :
      target.1.lookupRule? ⟨assertion.label⟩ =
        some (assertionRule callerFrame assertion)) :
    ((assertionHypothesisFormalsFrom 0 assertion.hypotheses).map
      Prod.fst).Nodup := by
  have hnames := assertionRuleFormalNames_nodup_of_lookup target callerFrame
    assertion hlookup
  have hsubFormals :
      List.Sublist
        (assertionHypothesisFormalsFrom 0 assertion.hypotheses)
        (assertionRule callerFrame assertion).metavariables := by
    rw [show (assertionRule callerFrame assertion).metavariables =
        assertionHypothesisFormalsFrom 0 assertion.hypotheses ++
          [(conclusionBodyFormalName, 0)] by rfl]
    exact List.sublist_append_left _ _
  exact hnames.sublist (hsubFormals.map Prod.fst)

/-! ## Exact assertion-schema instantiation -/

@[simp] private theorem encodeSym_isGroundAt (depth : Nat)
    (symbol : RuntimeSym) :
    (encodeSym symbol).isGroundAt depth = true := by
  cases symbol <;>
    simp [encodeSym, encodeString, Builder.constSym, Builder.varSym,
      Builder.encodedString, Builder.rawString, Pattern.isGroundAt,
      Pattern.isGroundListAt]

@[simp] private theorem formulaBodyPattern_isGroundAt (depth : Nat)
    (formula : ConstantHeadedFormula) :
    (formulaBodyPattern formula).isGroundAt depth = true := by
  rcases formula with ⟨typecode, body⟩
  induction body with
  | nil =>
      simp [formulaBodyPattern, encodeListWith, Builder.nil,
        Pattern.isGroundAt, Pattern.isGroundListAt]
  | cons symbol body ih =>
      simp [formulaBodyPattern, encodeListWith, Builder.cons,
        Pattern.isGroundAt, Pattern.isGroundListAt]

@[simp] private theorem encodeFormula_isGroundAt (depth : Nat)
    (formula : ConstantHeadedFormula) :
    (encodeFormula formula).isGroundAt depth = true := by
  rcases formula with ⟨typecode, body⟩
  simp [encodeFormula, Builder.formula, Pattern.isGroundAt,
    Pattern.isGroundListAt]

@[simp] private theorem encodeString_isGroundAt (depth : Nat)
    (value : String) :
    (encodeString value).isGroundAt depth = true := by
  simp [encodeString, Builder.encodedString, Builder.rawString,
    Pattern.isGroundAt, Pattern.isGroundListAt]

@[simp] private theorem encodeDVPair_isGroundAt (depth : Nat)
    (pair : String × String) :
    (encodeDVPair pair).isGroundAt depth = true := by
  rcases pair with ⟨left, right⟩
  simp [encodeDVPair, Builder.dvPair, Pattern.isGroundAt,
    Pattern.isGroundListAt]

@[simp] private theorem encodeFrame_isGroundAt (depth : Nat)
    (frame : RuntimeFrame) :
    (encodeFrame frame).isGroundAt depth = true := by
  rcases frame with ⟨dj, hyps⟩
  simp [encodeFrame, Builder.frame, Pattern.isGroundAt,
    Pattern.isGroundListAt]

@[simp] private theorem encodeSym_hasCanonicalBinderMetadata
    (symbol : RuntimeSym) :
    (encodeSym symbol).hasCanonicalBinderMetadata = true := by
  cases symbol <;>
    simp [encodeSym, encodeString, Builder.constSym, Builder.varSym,
      Builder.encodedString, Builder.rawString,
      Pattern.hasCanonicalBinderMetadata,
      Pattern.hasCanonicalBinderMetadataList]

@[simp] private theorem formulaBodyPattern_hasCanonicalBinderMetadata
    (formula : ConstantHeadedFormula) :
    (formulaBodyPattern formula).hasCanonicalBinderMetadata = true := by
  rcases formula with ⟨typecode, body⟩
  induction body with
  | nil =>
      simp [formulaBodyPattern, encodeListWith, Builder.nil,
        Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList]
  | cons symbol body ih =>
      simp [formulaBodyPattern, encodeListWith, Builder.cons,
        Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList]

private theorem assertionRule_argumentsValid_from_instances
    {hypotheses : List HypothesisView}
    {actuals : List ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    (instances : HypothesisInstances hypotheses actuals substitution)
    (index : Nat) (result : ConstantHeadedFormula) :
    argumentsValidAt
      (assertionHypothesisFormalsFrom index hypotheses ++
        [(conclusionBodyFormalName, 0)])
      (actuals.map formulaBodyPattern ++ [formulaBodyPattern result]) = true := by
  induction instances generalizing index with
  | nil =>
      simp [assertionHypothesisFormalsFrom, argumentsValidAt,
        argumentValidAt]
  | floating typecode_eq tail ih =>
      simp [assertionHypothesisFormalsFrom, argumentsValidAt,
        argumentValidAt, ih]
  | essential typecode_eq tail ih =>
      simp [assertionHypothesisFormalsFrom, argumentsValidAt,
        argumentValidAt, ih]

private theorem lookupArgumentAt?_append_last
    {formals : List (String × Nat)} {arguments : List Pattern}
    {formal : String × Nat} {argument : Pattern}
    (hlength : formals.length = arguments.length)
    (hnot : formal ∉ formals) :
    lookupArgumentAt? (formals ++ [formal]) (arguments ++ [argument])
      formal.1 formal.2 = some argument := by
  induction formals generalizing arguments with
  | nil =>
      simp only [List.length_nil] at hlength
      cases arguments with
      | nil => simp [lookupArgumentAt?]
      | cons argument arguments => simp at hlength
  | cons head formals ih =>
      cases arguments with
      | nil => simp at hlength
      | cons first arguments =>
          simp only [List.length_cons, Nat.succ.injEq] at hlength
          simp only [List.mem_cons, not_or] at hnot
          simp [lookupArgumentAt?, Ne.symm hnot.1, ih hlength hnot.2]

mutual

private theorem InstantiatesAt.cons_unused
    {formals : List (String × Nat)} {arguments : List Pattern}
    {formal : String × Nat} {argument schema result : Pattern} {depth : Nat}
    (instantiation :
      InstantiatesAt formals arguments depth schema result)
    (hnot : formal ∉ patternMetavariableOccurrencesAt depth schema) :
    InstantiatesAt (formal :: formals) (argument :: arguments)
      depth schema result := by
  cases instantiation with
  | bvar => exact .bvar _ _
  | fvar lookup =>
      simp only [patternMetavariableOccurrencesAt, List.mem_singleton] at hnot
      exact .fvar (by simpa [lookupArgumentAt?, hnot] using lookup)
  | apply items =>
      exact .apply (InstantiatesListAt.cons_unused items
        (by simpa only [patternMetavariableOccurrencesAt] using hnot))
  | lambda inner =>
      exact .lambda (InstantiatesAt.cons_unused inner
        (by simpa only [patternMetavariableOccurrencesAt] using hnot))
  | multiLambda inner =>
      exact .multiLambda (InstantiatesAt.cons_unused inner
        (by simpa only [patternMetavariableOccurrencesAt] using hnot))
  | subst left right =>
      simp only [patternMetavariableOccurrencesAt, List.mem_append,
        not_or] at hnot
      exact .subst (InstantiatesAt.cons_unused left hnot.1)
        (InstantiatesAt.cons_unused right hnot.2)
  | collection items =>
      exact .collection (InstantiatesListAt.cons_unused items
        (by simpa only [patternMetavariableOccurrencesAt] using hnot))

private theorem InstantiatesListAt.cons_unused
    {formals : List (String × Nat)} {arguments : List Pattern}
    {formal : String × Nat} {argument : Pattern}
    {schemas results : List Pattern} {depth : Nat}
    (instantiation :
      InstantiatesListAt formals arguments depth schemas results)
    (hnot : formal ∉ patternsMetavariableOccurrencesAt depth schemas) :
    InstantiatesListAt (formal :: formals) (argument :: arguments)
      depth schemas results := by
  cases instantiation with
  | nil => exact .nil _
  | cons head tail =>
      simp only [patternsMetavariableOccurrencesAt, List.mem_append,
        not_or] at hnot
      exact .cons (InstantiatesAt.cons_unused head hnot.1)
        (InstantiatesListAt.cons_unused tail hnot.2)

end

mutual

private theorem InstantiatesAt.drop_unused
    {formals : List (String × Nat)} {arguments : List Pattern}
    {formal : String × Nat} {argument schema result : Pattern} {depth : Nat}
    (instantiation :
      InstantiatesAt (formal :: formals) (argument :: arguments)
        depth schema result)
    (hnot : formal ∉ patternMetavariableOccurrencesAt depth schema) :
    InstantiatesAt formals arguments depth schema result := by
  cases instantiation with
  | bvar => exact .bvar _ _
  | fvar lookup =>
      simp only [patternMetavariableOccurrencesAt, List.mem_singleton] at hnot
      exact .fvar (by simpa [lookupArgumentAt?, hnot] using lookup)
  | apply items =>
      exact .apply (InstantiatesListAt.drop_unused items
        (by simpa only [patternMetavariableOccurrencesAt] using hnot))
  | lambda inner =>
      exact .lambda (InstantiatesAt.drop_unused inner
        (by simpa only [patternMetavariableOccurrencesAt] using hnot))
  | multiLambda inner =>
      exact .multiLambda (InstantiatesAt.drop_unused inner
        (by simpa only [patternMetavariableOccurrencesAt] using hnot))
  | subst left right =>
      simp only [patternMetavariableOccurrencesAt, List.mem_append,
        not_or] at hnot
      exact .subst (InstantiatesAt.drop_unused left hnot.1)
        (InstantiatesAt.drop_unused right hnot.2)
  | collection items =>
      exact .collection (InstantiatesListAt.drop_unused items
        (by simpa only [patternMetavariableOccurrencesAt] using hnot))

private theorem InstantiatesListAt.drop_unused
    {formals : List (String × Nat)} {arguments : List Pattern}
    {formal : String × Nat} {argument : Pattern}
    {schemas results : List Pattern} {depth : Nat}
    (instantiation :
      InstantiatesListAt (formal :: formals) (argument :: arguments)
        depth schemas results)
    (hnot : formal ∉ patternsMetavariableOccurrencesAt depth schemas) :
    InstantiatesListAt formals arguments depth schemas results := by
  cases instantiation with
  | nil => exact .nil _
  | cons head tail =>
      simp only [patternsMetavariableOccurrencesAt, List.mem_append,
        not_or] at hnot
      exact .cons (InstantiatesAt.drop_unused head hnot.1)
        (InstantiatesListAt.drop_unused tail hnot.2)

end

private theorem instantiateSchemaAt?_cons_of_not_mem_occurrences
    {formals : List (String × Nat)} {arguments : List Pattern}
    {formal : String × Nat} {argument schema : Pattern} {depth : Nat}
    (hnot : formal ∉ patternMetavariableOccurrencesAt depth schema) :
    instantiateSchemaAt? (formal :: formals) (argument :: arguments)
        depth schema =
      instantiateSchemaAt? formals arguments depth schema := by
  cases htail : instantiateSchemaAt? formals arguments depth schema with
  | none =>
      cases hhead : instantiateSchemaAt? (formal :: formals)
          (argument :: arguments) depth schema with
      | none => rfl
      | some result =>
          have instantiation := InstantiatesAt.drop_unused
            (instantiateSchemaAt?_sound hhead) hnot
          have := instantiateSchemaAt?_complete instantiation
          simp [htail] at this
  | some result =>
      have instantiation := InstantiatesAt.cons_unused
        (argument := argument) (instantiateSchemaAt?_sound htail) hnot
      rw [instantiateSchemaAt?_complete instantiation]

private theorem instantiateSchemasAt?_cons_of_not_mem_occurrences
    {formals : List (String × Nat)} {arguments : List Pattern}
    {formal : String × Nat} {argument : Pattern}
    {schemas : List Pattern} {depth : Nat}
    (hnot : formal ∉ patternsMetavariableOccurrencesAt depth schemas) :
    instantiateSchemasAt? (formal :: formals) (argument :: arguments)
        depth schemas =
      instantiateSchemasAt? formals arguments depth schemas := by
  cases htail : instantiateSchemasAt? formals arguments depth schemas with
  | none =>
      cases hhead : instantiateSchemasAt? (formal :: formals)
          (argument :: arguments) depth schemas with
      | none => rfl
      | some results =>
          have instantiation := InstantiatesListAt.drop_unused
            (instantiateSchemasAt?_sound hhead) hnot
          have := instantiateSchemasAt?_complete instantiation
          simp [htail] at this
  | some results =>
      have instantiation := InstantiatesListAt.cons_unused
        (argument := argument) (instantiateSchemasAt?_sound htail) hnot
      rw [instantiateSchemasAt?_complete instantiation]

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

private theorem instantiateSchemasAt?_append
    {formals : List (String × Nat)} {arguments : List Pattern}
    {depth : Nat} {leftSchemas leftResults rightSchemas rightResults :
      List Pattern}
    (left : instantiateSchemasAt? formals arguments depth leftSchemas =
      some leftResults)
    (right : instantiateSchemasAt? formals arguments depth rightSchemas =
      some rightResults) :
    instantiateSchemasAt? formals arguments depth
      (leftSchemas ++ rightSchemas) = some (leftResults ++ rightResults) := by
  induction leftSchemas generalizing leftResults with
  | nil =>
      simp only [instantiateSchemasAt?, Option.some.injEq] at left
      subst leftResults
      simpa using right
  | cons schema schemas ih =>
      simp only [instantiateSchemasAt?] at left ⊢
      cases hhead : instantiateSchemaAt? formals arguments depth schema with
      | none => simp [hhead] at left
      | some result =>
          cases htail : instantiateSchemasAt? formals arguments depth schemas with
          | none => simp [hhead, htail] at left
          | some results =>
              have heq : result :: results = leftResults := by
                simpa [hhead, htail] using left
              subst leftResults
              simp [instantiateSchemasAt?, hhead, ih htail]

private theorem instantiatesListAt_append
    {formals : List (String × Nat)} {arguments : List Pattern}
    {depth : Nat} {leftSchemas leftResults rightSchemas rightResults :
      List Pattern}
    (left : InstantiatesListAt formals arguments depth
      leftSchemas leftResults)
    (right : InstantiatesListAt formals arguments depth
      rightSchemas rightResults) :
    InstantiatesListAt formals arguments depth
      (leftSchemas ++ rightSchemas) (leftResults ++ rightResults) := by
  apply instantiateSchemasAt?_sound
  exact instantiateSchemasAt?_append
    (instantiateSchemasAt?_complete left)
    (instantiateSchemasAt?_complete right)

private theorem formal_not_mem_assertionBindingsList_occurrences
    (hypotheses : List HypothesisView) (index : Nat) {name : String}
    (hnot :
      name ∉
        (assertionHypothesisFormalsFrom index hypotheses).map Prod.fst) :
    (name, 0) ∉
      patternMetavariableOccurrencesAt 0
        (encodeListWith id (assertionBindingsFrom index hypotheses)) := by
  induction hypotheses generalizing index with
  | nil =>
      simp [assertionBindingsFrom, encodeListWith, Builder.nil,
        patternMetavariableOccurrencesAt,
        patternsMetavariableOccurrencesAt]
  | cons hypothesis hypotheses ih =>
      simp only [assertionHypothesisFormalsFrom, List.map_cons,
        List.mem_cons, not_or] at hnot
      cases hypothesis with
      | floating label typecode variableName =>
          have hpair :
              (name, 0) ≠ (hypothesisBodyFormalName index, 0) := by
            intro heq
            exact hnot.1 (congrArg Prod.fst heq)
          have hbinding :
              (name, 0) ∉ patternMetavariableOccurrencesAt 0
                (Builder.binding (encodeString variableName)
                  (Builder.formula (encodeString typecode)
                    (.fvar (hypothesisBodyFormalName index)))) := by
            simpa [Builder.binding, Builder.formula, encodeString,
              Builder.encodedString, Builder.rawString,
              patternMetavariableOccurrencesAt,
              patternsMetavariableOccurrencesAt] using hpair
          rw [show assertionBindingsFrom index
              (.floating label typecode variableName :: hypotheses) =
              Builder.binding (encodeString variableName)
                  (Builder.formula (encodeString typecode)
                    (.fvar (hypothesisBodyFormalName index))) ::
                assertionBindingsFrom (index + 1) hypotheses by rfl]
          simp only [encodeListWith, Builder.cons,
            Builder.binding, Builder.formula, encodeString,
            Builder.encodedString, Builder.rawString,
            patternMetavariableOccurrencesAt,
            patternsMetavariableOccurrencesAt, List.mem_append,
            List.mem_nil_iff, not_false_eq_true, not_or, and_true]
          exact ⟨hbinding, ih (index := index + 1) hnot.2⟩
      | essential label formula =>
          simpa [assertionBindingsFrom] using
            ih (index := index + 1) hnot.2

private theorem formal_not_mem_assertionBindings_occurrences
    (hypotheses : List HypothesisView) (index : Nat) {name : String}
    (hnot :
      name ∉
        (assertionHypothesisFormalsFrom index hypotheses).map Prod.fst) :
    (name, 0) ∉
      patternMetavariableOccurrencesAt 0
        (Builder.substitution
          (encodeListWith id (assertionBindingsFrom index hypotheses))) := by
  simpa [Builder.substitution, patternMetavariableOccurrencesAt,
    patternsMetavariableOccurrencesAt] using
      formal_not_mem_assertionBindingsList_occurrences hypotheses index hnot

private theorem formal_not_mem_assertionHypothesisProves_occurrences
    (hypotheses : List HypothesisView) (index : Nat) {name : String}
    (hnot :
      name ∉
        (assertionHypothesisFormalsFrom index hypotheses).map Prod.fst) :
    (name, 0) ∉
      patternsMetavariableOccurrencesAt 0
        (assertionHypothesisProvesFrom index hypotheses) := by
  induction hypotheses generalizing index with
  | nil =>
      simp [assertionHypothesisProvesFrom,
        patternsMetavariableOccurrencesAt]
  | cons hypothesis hypotheses ih =>
      simp only [assertionHypothesisFormalsFrom, List.map_cons,
        List.mem_cons, not_or] at hnot
      have hpair :
          (name, 0) ≠ (hypothesisBodyFormalName index, 0) := by
        intro heq
        exact hnot.1 (congrArg Prod.fst heq)
      rw [show assertionHypothesisProvesFrom index
          (hypothesis :: hypotheses) =
          proves
              (Builder.formula (encodeString hypothesis.typecode)
                (.fvar (hypothesisBodyFormalName index))) ::
            assertionHypothesisProvesFrom (index + 1) hypotheses by rfl]
      have hhead :
          (name, 0) ∉ patternMetavariableOccurrencesAt 0
            (proves
              (Builder.formula (encodeString hypothesis.typecode)
                (.fvar (hypothesisBodyFormalName index)))) := by
        simpa [proves, Builder.formula, encodeString,
          Builder.encodedString, Builder.rawString,
          patternMetavariableOccurrencesAt,
          patternsMetavariableOccurrencesAt] using hpair
      simp only [patternsMetavariableOccurrencesAt, List.mem_append,
        not_or]
      exact ⟨hhead, ih (index := index + 1) hnot.2⟩

private theorem instantiate_assertionHypothesisProvesFrom_from_instances
    {hypotheses : List HypothesisView}
    {actuals : List ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    (instances : HypothesisInstances hypotheses actuals substitution)
    (index : Nat) (result : ConstantHeadedFormula)
    (hformals :
      ((assertionHypothesisFormalsFrom index hypotheses).map Prod.fst).Nodup) :
    instantiateSchemas?
      (assertionHypothesisFormalsFrom index hypotheses ++
        [(conclusionBodyFormalName, 0)])
      (actuals.map formulaBodyPattern ++ [formulaBodyPattern result])
      (assertionHypothesisProvesFrom index hypotheses) =
      some (assertionProvesPremises actuals) := by
  induction instances generalizing index with
  | nil =>
      simp [assertionHypothesisFormalsFrom,
        assertionHypothesisProvesFrom, assertionProvesPremises,
        instantiateSchemas?, instantiateSchemasAt?]
  | @floating label typecode variableName actual hypotheses actuals
      substitution typecode_eq tail ih =>
      rw [show assertionHypothesisFormalsFrom index
          (.floating label typecode variableName :: hypotheses) =
          (hypothesisBodyFormalName index, 0) ::
            assertionHypothesisFormalsFrom (index + 1) hypotheses by rfl]
        at hformals ⊢
      rw [show (actual :: actuals).map formulaBodyPattern =
          formulaBodyPattern actual :: actuals.map formulaBodyPattern by rfl]
        at ⊢
      rw [show assertionHypothesisProvesFrom index
          (.floating label typecode variableName :: hypotheses) =
          proves
              (Builder.formula (encodeString typecode)
                (.fvar (hypothesisBodyFormalName index))) ::
            assertionHypothesisProvesFrom (index + 1) hypotheses by rfl]
        at ⊢
      simp only [List.map_cons, List.nodup_cons] at hformals
      have htail := ih (index + 1) hformals.2
      have hweaken :=
        instantiateSchemasAt?_cons_of_not_mem_occurrences
          (formal_not_mem_assertionHypothesisProves_occurrences hypotheses
            (index + 1) hformals.1)
          (formals :=
            assertionHypothesisFormalsFrom (index + 1) hypotheses ++
              [(conclusionBodyFormalName, 0)])
          (arguments :=
            actuals.map formulaBodyPattern ++ [formulaBodyPattern result])
          (argument := formulaBodyPattern actual)
      have htailFull := hweaken.trans (by
        simpa [instantiateSchemas?] using htail)
      simp [instantiateSchemas?, instantiateSchemasAt?, instantiateSchemaAt?,
        lookupArgumentAt?, proves, Builder.formula, encodeString,
        formulaBodyPattern, encodeFormula, typecode_eq,
        assertionProvesPremises]
      simpa [instantiateSchemas?, formulaBodyPattern,
        assertionProvesPremises, proves, encodeFormula, encodeString]
        using htailFull
  | @essential label formula actual hypotheses actuals substitution
      typecode_eq tail ih =>
      rw [show assertionHypothesisFormalsFrom index
          (.essential label formula :: hypotheses) =
          (hypothesisBodyFormalName index, 0) ::
            assertionHypothesisFormalsFrom (index + 1) hypotheses by rfl]
        at hformals ⊢
      rw [show (actual :: actuals).map formulaBodyPattern =
          formulaBodyPattern actual :: actuals.map formulaBodyPattern by rfl]
        at ⊢
      rw [show assertionHypothesisProvesFrom index
          (.essential label formula :: hypotheses) =
          proves
              (Builder.formula (encodeString formula.typecode)
                (.fvar (hypothesisBodyFormalName index))) ::
            assertionHypothesisProvesFrom (index + 1) hypotheses by rfl]
        at ⊢
      simp only [List.map_cons, List.nodup_cons] at hformals
      have htail := ih (index + 1) hformals.2
      have hweaken :=
        instantiateSchemasAt?_cons_of_not_mem_occurrences
          (formal_not_mem_assertionHypothesisProves_occurrences hypotheses
            (index + 1) hformals.1)
          (formals :=
            assertionHypothesisFormalsFrom (index + 1) hypotheses ++
              [(conclusionBodyFormalName, 0)])
          (arguments :=
            actuals.map formulaBodyPattern ++ [formulaBodyPattern result])
          (argument := formulaBodyPattern actual)
      have htailFull := hweaken.trans (by
        simpa [instantiateSchemas?] using htail)
      simp [instantiateSchemas?, instantiateSchemasAt?, instantiateSchemaAt?,
        lookupArgumentAt?, proves, Builder.formula, encodeString,
        formulaBodyPattern, encodeFormula, typecode_eq,
        assertionProvesPremises]
      simpa [instantiateSchemas?, formulaBodyPattern,
        assertionProvesPremises, proves, encodeFormula, encodeString]
        using htailFull

/-! The next evidence records only instantiation of the ordered hypothesis-body
metavariables.  It is internal plumbing for the essential side schemas; it is
not a proof of any `Proves` premise. -/
inductive HypothesisBodyInstantiations
    (formals : List (String × Nat)) (arguments : List Pattern) :
    Nat → List HypothesisView → List ConstantHeadedFormula → Prop where
  | nil (index : Nat) :
      HypothesisBodyInstantiations formals arguments index [] []
  | cons {index : Nat} {hypothesis : HypothesisView}
      {hypotheses : List HypothesisView}
      {actual : ConstantHeadedFormula}
      {actuals : List ConstantHeadedFormula}
      (head : Instantiates formals arguments
        (.fvar (hypothesisBodyFormalName index))
        (formulaBodyPattern actual))
      (tail : HypothesisBodyInstantiations formals arguments
        (index + 1) hypotheses actuals) :
      HypothesisBodyInstantiations formals arguments index
        (hypothesis :: hypotheses) (actual :: actuals)

private theorem HypothesisBodyInstantiations.cons_unused
    {formals : List (String × Nat)} {arguments : List Pattern}
    {formal : String × Nat} {argument : Pattern}
    {index : Nat} {hypotheses : List HypothesisView}
    {actuals : List ConstantHeadedFormula}
    (instantiations : HypothesisBodyInstantiations formals arguments
      index hypotheses actuals)
    (hnot :
      formal.1 ∉
        (assertionHypothesisFormalsFrom index hypotheses).map Prod.fst) :
    HypothesisBodyInstantiations (formal :: formals) (argument :: arguments)
      index hypotheses actuals := by
  induction instantiations with
  | nil => exact .nil _
  | @cons index hypothesis hypotheses actual actuals head tail ih =>
      simp only [assertionHypothesisFormalsFrom, List.map_cons,
        List.mem_cons, not_or] at hnot
      have hpair :
          formal ≠ (hypothesisBodyFormalName index, 0) := by
        intro heq
        exact hnot.1 (congrArg Prod.fst heq)
      refine .cons (InstantiatesAt.cons_unused head ?_) (ih hnot.2)
      simpa [patternMetavariableOccurrencesAt] using hpair

private theorem hypothesisBodyInstantiations_from_instances
    {hypotheses : List HypothesisView}
    {actuals : List ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    (instances : HypothesisInstances hypotheses actuals substitution)
    (index : Nat) (result : ConstantHeadedFormula)
    (hformals :
      ((assertionHypothesisFormalsFrom index hypotheses).map Prod.fst).Nodup) :
    HypothesisBodyInstantiations
      (assertionHypothesisFormalsFrom index hypotheses ++
        [(conclusionBodyFormalName, 0)])
      (actuals.map formulaBodyPattern ++ [formulaBodyPattern result])
      index hypotheses actuals := by
  induction instances generalizing index with
  | nil => exact .nil index
  | @floating label typecode variableName actual hypotheses actuals
      substitution typecode_eq tail ih =>
      rw [show assertionHypothesisFormalsFrom index
          (.floating label typecode variableName :: hypotheses) =
          (hypothesisBodyFormalName index, 0) ::
            assertionHypothesisFormalsFrom (index + 1) hypotheses by rfl]
        at hformals ⊢
      rw [show (actual :: actuals).map formulaBodyPattern =
          formulaBodyPattern actual :: actuals.map formulaBodyPattern by rfl]
        at ⊢
      simp only [List.map_cons, List.nodup_cons] at hformals
      refine .cons (.fvar ?_) ?_
      · simp [lookupArgumentAt?]
      · exact (ih (index + 1) hformals.2).cons_unused hformals.1
  | @essential label formula actual hypotheses actuals substitution
      typecode_eq tail ih =>
      rw [show assertionHypothesisFormalsFrom index
          (.essential label formula :: hypotheses) =
          (hypothesisBodyFormalName index, 0) ::
            assertionHypothesisFormalsFrom (index + 1) hypotheses by rfl]
        at hformals ⊢
      rw [show (actual :: actuals).map formulaBodyPattern =
          formulaBodyPattern actual :: actuals.map formulaBodyPattern by rfl]
        at ⊢
      simp only [List.map_cons, List.nodup_cons] at hformals
      refine .cons (.fvar ?_) ?_
      · simp [lookupArgumentAt?]
      · exact (ih (index + 1) hformals.2).cons_unused hformals.1

private theorem essentialCheck_instantiates
    {formals : List (String × Nat)} {arguments : List Pattern}
    {substitutionSchema : Pattern} {substitution : FiniteSubstitution}
    {formula actual : ConstantHeadedFormula} {index : Nat}
    (hsubstitution :
      Instantiates formals arguments substitutionSchema
        (encodeSubstitution substitution))
    (hbody : Instantiates formals arguments
      (.fvar (hypothesisBodyFormalName index))
      (formulaBodyPattern actual))
    (htypecode : actual.typecode = formula.typecode) :
    Instantiates formals arguments
      (applySubst substitutionSchema (encodeFormula formula)
        (Builder.formula (encodeString formula.typecode)
          (.fvar (hypothesisBodyFormalName index))))
      (applySubst (encodeSubstitution substitution) (encodeFormula formula)
        (encodeFormula actual)) := by
  apply instantiateSchemaAt?_sound
  have hsubstitution' := instantiateSchemaAt?_complete hsubstitution
  have hbody' := instantiateSchemaAt?_complete hbody
  have hsourceBody := instantiateSchemaAt?_ground_identity formals arguments 0
    (formulaBodyPattern formula) (formulaBodyPattern_isGroundAt 0 formula)
  have hsourceBody' :
      instantiateSchemaAt? formals arguments 0
          (encodeListWith encodeSym formula.body) =
        some (encodeListWith encodeSym formula.body) := by
    simpa [formulaBodyPattern] using hsourceBody
  simp [applySubst, instantiateSchemaAt?,
    instantiateSchemasAt?, hsubstitution', hbody', hsourceBody',
    Builder.formula, encodeFormula, encodeString, formulaBodyPattern,
    htypecode]

private theorem ground_instantiates
    (formals : List (String × Nat)) (arguments : List Pattern)
    (schema : Pattern) (hground : schema.isGround = true) :
    Instantiates formals arguments schema schema :=
  instantiateSchemaAt?_sound
    (instantiateSchemaAt?_ground_identity formals arguments 0 schema hground)

private theorem formulaWithBody_instantiates
    {formals : List (String × Nat)} {arguments : List Pattern}
    {declaredTypecode : String} {bodySchema : Pattern}
    {actual : ConstantHeadedFormula}
    (hbody : Instantiates formals arguments bodySchema
      (formulaBodyPattern actual))
    (htypecode : actual.typecode = declaredTypecode) :
    Instantiates formals arguments
      (Builder.formula (encodeString declaredTypecode) bodySchema)
      (encodeFormula actual) := by
  have htypecodeInstantiates :
      Instantiates formals arguments (encodeString declaredTypecode)
        (encodeString declaredTypecode) :=
    ground_instantiates formals arguments (encodeString declaredTypecode)
      (encodeString_isGroundAt 0 declaredTypecode)
  have hformula :
      Instantiates formals arguments
        (.apply formulaHead [encodeString declaredTypecode, bodySchema])
        (.apply formulaHead
          [encodeString declaredTypecode, formulaBodyPattern actual]) :=
    InstantiatesAt.apply
      (InstantiatesListAt.cons htypecodeInstantiates
        (InstantiatesListAt.cons hbody (InstantiatesListAt.nil 0)))
  simpa [Builder.formula, encodeFormula, formulaBodyPattern, htypecode]
    using hformula

private theorem proves_instantiates
    {formals : List (String × Nat)} {arguments : List Pattern}
    {schema result : Pattern}
    (hformula : Instantiates formals arguments schema result) :
    Instantiates formals arguments (proves schema) (proves result) := by
  simpa [proves] using InstantiatesAt.apply
    (InstantiatesListAt.cons hformula (InstantiatesListAt.nil 0))

private theorem applySubst_instantiates
    {formals : List (String × Nat)} {arguments : List Pattern}
    {substitutionSchema substitutionResult sourceSchema sourceResult
      resultSchema resultResult : Pattern}
    (hsubstitution : Instantiates formals arguments
      substitutionSchema substitutionResult)
    (hsource : Instantiates formals arguments sourceSchema sourceResult)
    (hresult : Instantiates formals arguments resultSchema resultResult) :
    Instantiates formals arguments
      (applySubst substitutionSchema sourceSchema resultSchema)
      (applySubst substitutionResult sourceResult resultResult) := by
  simpa [applySubst] using InstantiatesAt.apply
    (InstantiatesListAt.cons hsubstitution
      (InstantiatesListAt.cons hsource
        (InstantiatesListAt.cons hresult (InstantiatesListAt.nil 0))))

private theorem dvOK_instantiates
    {formals : List (String × Nat)} {arguments : List Pattern}
    {substitutionSchema substitutionResult callerSchema callerResult
      calleeSchema calleeResult : Pattern}
    (hsubstitution : Instantiates formals arguments
      substitutionSchema substitutionResult)
    (hcaller : Instantiates formals arguments callerSchema callerResult)
    (hcallee : Instantiates formals arguments calleeSchema calleeResult) :
    Instantiates formals arguments
      (dvOK substitutionSchema callerSchema calleeSchema)
      (dvOK substitutionResult callerResult calleeResult) := by
  simpa [dvOK] using InstantiatesAt.apply
    (InstantiatesListAt.cons hsubstitution
      (InstantiatesListAt.cons hcaller
        (InstantiatesListAt.cons hcallee (InstantiatesListAt.nil 0))))

private theorem assertionResultFormula_instantiates
    {callerFrame : RuntimeFrame} {assertion : AssertionView}
    {actuals : List ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    {result : ConstantHeadedFormula}
    (instances :
      HypothesisInstances assertion.hypotheses actuals substitution)
    (hfullNames :
      ((assertionRule callerFrame assertion).metavariables.map Prod.fst).Nodup)
    (htypecode : result.typecode = assertion.formula.typecode) :
    Instantiates
      (assertionHypothesisFormalsFrom 0 assertion.hypotheses ++
        [(conclusionBodyFormalName, 0)])
      (actuals.map formulaBodyPattern ++ [formulaBodyPattern result])
      (Builder.formula (encodeString assertion.formula.typecode)
        (.fvar conclusionBodyFormalName))
      (encodeFormula result) := by
  have hfullNames' :
      (((assertionHypothesisFormalsFrom 0 assertion.hypotheses).map Prod.fst) ++
        [conclusionBodyFormalName]).Nodup := by
    rw [show (assertionRule callerFrame assertion).metavariables =
        assertionHypothesisFormalsFrom 0 assertion.hypotheses ++
          [(conclusionBodyFormalName, 0)] by rfl] at hfullNames
    simpa using hfullNames
  have hcross :
      ∀ (formal : String × Nat),
        formal ∈ assertionHypothesisFormalsFrom 0 assertion.hypotheses →
          formal.1 ≠ conclusionBodyFormalName := by
    have hdecomp :
        ((assertionHypothesisFormalsFrom 0 assertion.hypotheses).map
            Prod.fst).Nodup ∧
          ∀ (name : String),
            name ∈ (assertionHypothesisFormalsFrom 0
                assertion.hypotheses).map Prod.fst →
              name ≠ conclusionBodyFormalName := by
      simpa [List.nodup_append] using hfullNames'
    intro formal hformal
    exact hdecomp.2 formal.1 (List.mem_map_of_mem hformal)
  have hformalNotMem :
      (conclusionBodyFormalName, 0) ∉
        assertionHypothesisFormalsFrom 0 assertion.hypotheses := by
    intro hmem
    exact hcross _ hmem rfl
  have hformalsLength :
      (assertionHypothesisFormalsFrom 0 assertion.hypotheses).length =
        (actuals.map formulaBodyPattern).length := by
    simp [assertionHypothesisFormalsFrom_length, instances.lengths]
  have hlookup := lookupArgumentAt?_append_last
    hformalsLength
    hformalNotMem
    (argument := formulaBodyPattern result)
  exact formulaWithBody_instantiates (.fvar hlookup) htypecode

private theorem assertionEssentialChecksFrom_instantiates
    {formals : List (String × Nat)} {arguments : List Pattern}
    {substitutionSchema : Pattern}
    {instanceSubstitution fullSubstitution : FiniteSubstitution}
    {hypotheses : List HypothesisView}
    {actuals : List ConstantHeadedFormula} {index : Nat}
    (instances :
      HypothesisInstances hypotheses actuals instanceSubstitution)
    (bodies : HypothesisBodyInstantiations formals arguments
      index hypotheses actuals)
    (hsubstitution : Instantiates formals arguments substitutionSchema
      (encodeSubstitution fullSubstitution)) :
    InstantiatesList formals arguments
      (assertionEssentialChecksFrom substitutionSchema index hypotheses)
      (assertionEssentialPremises fullSubstitution hypotheses actuals) := by
  induction instances generalizing index with
  | nil =>
      cases bodies
      exact .nil _
  | @floating label typecode variableName actual hypotheses actuals
      substitution typecode_eq tail ih =>
      cases bodies with
      | cons head bodyTail =>
          simpa [assertionEssentialChecksFrom,
            assertionEssentialPremises] using
              ih bodyTail
  | @essential label formula actual hypotheses actuals substitution
      typecode_eq tail ih =>
      cases bodies with
      | cons head bodyTail =>
          rw [show assertionEssentialChecksFrom substitutionSchema index
              (.essential label formula :: hypotheses) =
              applySubst substitutionSchema (encodeFormula formula)
                  (Builder.formula (encodeString formula.typecode)
                    (.fvar (hypothesisBodyFormalName index))) ::
                assertionEssentialChecksFrom substitutionSchema
                  (index + 1) hypotheses by rfl]
          simpa [
            assertionEssentialPremises] using
              InstantiatesListAt.cons
                (essentialCheck_instantiates hsubstitution head typecode_eq)
                (ih bodyTail)

private theorem instantiate_assertionBindingsList_from_instances
    {hypotheses : List HypothesisView}
    {actuals : List ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    (instances : HypothesisInstances hypotheses actuals substitution)
    (index : Nat) (result : ConstantHeadedFormula)
    (hformals :
      ((assertionHypothesisFormalsFrom index hypotheses).map Prod.fst).Nodup) :
    instantiateSchema?
      (assertionHypothesisFormalsFrom index hypotheses ++
        [(conclusionBodyFormalName, 0)])
      (actuals.map formulaBodyPattern ++ [formulaBodyPattern result])
      (encodeListWith id (assertionBindingsFrom index hypotheses)) =
      some (encodeListWith encodeBinding substitution) := by
  induction instances generalizing index with
  | nil =>
      simp [assertionHypothesisFormalsFrom, assertionBindingsFrom,
        instantiateSchema?, instantiateSchemaAt?, instantiateSchemasAt?,
        encodeListWith]
  | @floating label typecode variableName actual hypotheses actuals
      substitution typecode_eq tail ih =>
      rw [show assertionHypothesisFormalsFrom index
          (.floating label typecode variableName :: hypotheses) =
          (hypothesisBodyFormalName index, 0) ::
            assertionHypothesisFormalsFrom (index + 1) hypotheses by rfl]
        at hformals ⊢
      rw [show (actual :: actuals).map formulaBodyPattern =
          formulaBodyPattern actual :: actuals.map formulaBodyPattern by rfl]
        at ⊢
      rw [show assertionBindingsFrom index
          (.floating label typecode variableName :: hypotheses) =
          Builder.binding (encodeString variableName)
              (Builder.formula (encodeString typecode)
                (.fvar (hypothesisBodyFormalName index))) ::
            assertionBindingsFrom (index + 1) hypotheses by rfl]
        at ⊢
      simp only [List.map_cons, List.nodup_cons] at hformals
      have htail := ih (index + 1) hformals.2
      have hweaken :=
        instantiateSchemaAt?_cons_of_not_mem_occurrences
          (formal_not_mem_assertionBindingsList_occurrences hypotheses
            (index + 1) hformals.1)
          (formals :=
            assertionHypothesisFormalsFrom (index + 1) hypotheses ++
              [(conclusionBodyFormalName, 0)])
          (arguments :=
            actuals.map formulaBodyPattern ++ [formulaBodyPattern result])
          (argument := formulaBodyPattern actual)
      have htailFull := hweaken.trans (by
        simpa [instantiateSchema?] using htail)
      simp [instantiateSchema?, instantiateSchemaAt?, instantiateSchemasAt?,
        lookupArgumentAt?, encodeListWith, encodeBinding, Builder.cons,
        Builder.binding, Builder.formula, encodeString, formulaBodyPattern,
        encodeFormula, typecode_eq]
      simpa [formulaBodyPattern] using htailFull
  | @essential label formula actual hypotheses actuals substitution
      typecode_eq tail ih =>
      rw [show assertionHypothesisFormalsFrom index
          (.essential label formula :: hypotheses) =
          (hypothesisBodyFormalName index, 0) ::
            assertionHypothesisFormalsFrom (index + 1) hypotheses by rfl]
        at hformals ⊢
      rw [show (actual :: actuals).map formulaBodyPattern =
          formulaBodyPattern actual :: actuals.map formulaBodyPattern by rfl]
        at ⊢
      simp only [List.map_cons, List.nodup_cons] at hformals
      have htail := ih (index + 1) hformals.2
      have hweaken :=
        instantiateSchemaAt?_cons_of_not_mem_occurrences
          (formal_not_mem_assertionBindingsList_occurrences hypotheses
            (index + 1) hformals.1)
          (formals :=
            assertionHypothesisFormalsFrom (index + 1) hypotheses ++
              [(conclusionBodyFormalName, 0)])
          (arguments :=
            actuals.map formulaBodyPattern ++ [formulaBodyPattern result])
          (argument := formulaBodyPattern actual)
      simpa [assertionHypothesisFormalsFrom, assertionBindingsFrom,
        instantiateSchema?] using hweaken.trans htail

private theorem instantiate_assertionSubstitution_from_instances
    {hypotheses : List HypothesisView}
    {actuals : List ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    (instances : HypothesisInstances hypotheses actuals substitution)
    (index : Nat) (result : ConstantHeadedFormula)
    (hformals :
      ((assertionHypothesisFormalsFrom index hypotheses).map Prod.fst).Nodup) :
    instantiateSchema?
      (assertionHypothesisFormalsFrom index hypotheses ++
        [(conclusionBodyFormalName, 0)])
      (actuals.map formulaBodyPattern ++ [formulaBodyPattern result])
      (Builder.substitution
        (encodeListWith id (assertionBindingsFrom index hypotheses))) =
      some (encodeSubstitution substitution) := by
  have hbindings := instantiate_assertionBindingsList_from_instances
    instances index result hformals
  simpa [instantiateSchema?, Builder.substitution, encodeSubstitution,
    instantiateSchemaAt?, instantiateSchemasAt?] using hbindings

/-- Exact forward local application: the generated schema consumes the
ordered hypothesis bodies and conclusion body, and produces precisely the
canonical ordered premise vector. -/
theorem assertionRuleApplication_of_instances
    (projection : PrefixProjection) (target : ValidatedPresentation)
    (hprojection : presentationOfProjection? projection = some target.1)
    {assertion : AssertionView}
    (hassertion : assertion ∈ projection.assertions)
    {actuals : List ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    {result : ConstantHeadedFormula}
    (instances :
      HypothesisInstances assertion.hypotheses actuals substitution)
    (hresultTypecode : result.typecode = assertion.formula.typecode) :
    RuleApplication target
      (assertionRuleInstance assertion actuals result)
      (assertionPremises substitution projection.callerFrame assertion
        actuals result)
      (proves (encodeFormula result)) := by
  have hlookup := lookup_assertionRule_of_projection projection target
    hprojection hassertion
  have hhypothesisNames :=
    assertionHypothesisFormalNames_nodup_of_lookup target
      projection.callerFrame assertion hlookup
  have hfullNames := assertionRuleFormalNames_nodup_of_lookup target
    projection.callerFrame assertion hlookup
  have harguments := assertionRule_argumentsValid_from_instances
    instances 0 result
  have hproves := instantiateSchemasAt?_sound
    (instantiate_assertionHypothesisProvesFrom_from_instances
      instances 0 result hhypothesisNames)
  have hsubstitution := instantiateSchemaAt?_sound
    (instantiate_assertionSubstitution_from_instances
      instances 0 result hhypothesisNames)
  have hbodies := hypothesisBodyInstantiations_from_instances
    instances 0 result hhypothesisNames
  have hessential := assertionEssentialChecksFrom_instantiates
    instances hbodies hsubstitution
  have hcaller : Instantiates
      (assertionRule projection.callerFrame assertion).metavariables
      (assertionRuleArguments actuals result)
      (encodeFrame projection.callerFrame)
      (encodeFrame projection.callerFrame) :=
    ground_instantiates _ _ _
      (encodeFrame_isGroundAt 0 projection.callerFrame)
  have hcallee : Instantiates
      (assertionRule projection.callerFrame assertion).metavariables
      (assertionRuleArguments actuals result)
      (encodeFrame assertion.frame) (encodeFrame assertion.frame) :=
    ground_instantiates _ _ _ (encodeFrame_isGroundAt 0 assertion.frame)
  have hresultFormula := assertionResultFormula_instantiates
    instances hfullNames hresultTypecode
  have hsource : Instantiates
      (assertionRule projection.callerFrame assertion).metavariables
      (assertionRuleArguments actuals result)
      (encodeFormula assertion.formula) (encodeFormula assertion.formula) :=
    ground_instantiates _ _ _ (encodeFormula_isGroundAt 0 assertion.formula)
  have hdv := dvOK_instantiates hsubstitution hcaller hcallee
  have hfinal := applySubst_instantiates hsubstitution hsource hresultFormula
  have hpremises := instantiatesListAt_append
    (instantiatesListAt_append hproves hessential)
    (InstantiatesListAt.cons hdv
      (InstantiatesListAt.cons hfinal (InstantiatesListAt.nil 0)))
  have hconclusion := proves_instantiates hresultFormula
  have hmetavariables :
      (assertionRule projection.callerFrame assertion).metavariables =
        assertionHypothesisFormalsFrom 0 assertion.hypotheses ++
          [(conclusionBodyFormalName, 0)] := by
    rfl
  have hpremiseSchemas :
      (assertionRule projection.callerFrame assertion).premises =
        assertionHypothesisProvesFrom 0 assertion.hypotheses ++
          assertionEssentialChecksFrom
              (Builder.substitution
                (encodeListWith id
                  (assertionBindingsFrom 0 assertion.hypotheses)))
              0 assertion.hypotheses ++
          [ dvOK
              (Builder.substitution
                (encodeListWith id
                  (assertionBindingsFrom 0 assertion.hypotheses)))
              (encodeFrame projection.callerFrame)
              (encodeFrame assertion.frame)
          , applySubst
              (Builder.substitution
                (encodeListWith id
                  (assertionBindingsFrom 0 assertion.hypotheses)))
              (encodeFormula assertion.formula)
              (Builder.formula (encodeString assertion.formula.typecode)
                (.fvar conclusionBodyFormalName)) ] := by
    rfl
  have hconclusionSchema :
      (assertionRule projection.callerFrame assertion).conclusion =
        proves
          (Builder.formula (encodeString assertion.formula.typecode)
            (.fvar conclusionBodyFormalName)) := by
    rfl
  exact RuleApplication.intro
    (assertionRule projection.callerFrame assertion)
    (by simpa [assertionRuleInstance] using hlookup)
    (by
      rw [hmetavariables]
      simpa [assertionRuleInstance, assertionRuleArguments] using harguments)
    (by
      rw [hmetavariables, hpremiseSchemas]
      simpa [assertionRuleInstance, assertionRuleArguments,
        assertionPremises, assertionSidePremises,
        List.append_assoc] using hpremises)
    (by
      rw [hmetavariables, hconclusionSchema]
      simpa [assertionRuleInstance, assertionRuleArguments]
        using hconclusion)

/-! ## Exact reverse characterization of the local application -/

/-- Replace only the constant head, retaining the exact body. -/
def withTypecode (typecode : String)
    (formula : ConstantHeadedFormula) : ConstantHeadedFormula :=
  ⟨typecode, formula.body⟩

/-- Canonical mandatory-hypothesis actuals determined by the authored
hypothesis typecodes and the supplied bodies.  The mismatch cases are
irrelevant under the length equality proved from a rule application. -/
def canonicalActuals : List HypothesisView →
    List ConstantHeadedFormula → List ConstantHeadedFormula
  | [], [] => []
  | .floating _ typecode _ :: hypotheses, actual :: actuals =>
      withTypecode typecode actual :: canonicalActuals hypotheses actuals
  | .essential _ formula :: hypotheses, actual :: actuals =>
      withTypecode formula.typecode actual ::
        canonicalActuals hypotheses actuals
  | _, _ => []

/-- Canonical finite substitution contributed, in order, by floating
hypotheses. -/
def canonicalSubstitution : List HypothesisView →
    List ConstantHeadedFormula → FiniteSubstitution
  | [], [] => []
  | .floating _ typecode variableName :: hypotheses, actual :: actuals =>
      ⟨variableName, withTypecode typecode actual⟩ ::
        canonicalSubstitution hypotheses actuals
  | .essential _ _ :: hypotheses, _ :: actuals =>
      canonicalSubstitution hypotheses actuals
  | _, _ => []

def canonicalResult (assertion : AssertionView)
    (result : ConstantHeadedFormula) : ConstantHeadedFormula :=
  withTypecode assertion.formula.typecode result

private theorem canonical_hypothesisInstances
    {hypotheses : List HypothesisView}
    {actuals : List ConstantHeadedFormula}
    (hlength : hypotheses.length = actuals.length) :
    HypothesisInstances hypotheses
      (canonicalActuals hypotheses actuals)
      (canonicalSubstitution hypotheses actuals) := by
  induction hypotheses generalizing actuals with
  | nil =>
      cases actuals with
      | nil => exact .nil
      | cons actual actuals => simp at hlength
  | cons hypothesis hypotheses ih =>
      cases actuals with
      | nil => simp at hlength
      | cons actual actuals =>
          have htailLength : hypotheses.length = actuals.length := by
            simpa using hlength
          cases hypothesis with
          | floating label typecode variableName =>
              exact .floating (by rfl) (ih htailLength)
          | essential label formula =>
              exact .essential (by rfl) (ih htailLength)

@[simp] private theorem formulaBodyPattern_withTypecode
    (typecode : String) (formula : ConstantHeadedFormula) :
    formulaBodyPattern (withTypecode typecode formula) =
      formulaBodyPattern formula := rfl

private theorem canonicalActuals_bodyPatterns
    {hypotheses : List HypothesisView}
    {actuals : List ConstantHeadedFormula}
    (hlength : hypotheses.length = actuals.length) :
    (canonicalActuals hypotheses actuals).map formulaBodyPattern =
      actuals.map formulaBodyPattern := by
  induction hypotheses generalizing actuals with
  | nil =>
      cases actuals with
      | nil => rfl
      | cons actual actuals => simp at hlength
  | cons hypothesis hypotheses ih =>
      cases actuals with
      | nil => simp at hlength
      | cons actual actuals =>
          have htailLength : hypotheses.length = actuals.length := by
            simpa using hlength
          cases hypothesis <;>
            simp [canonicalActuals, ih htailLength]

@[simp] private theorem formulaBodyPattern_canonicalResult
    (assertion : AssertionView) (result : ConstantHeadedFormula) :
    formulaBodyPattern (canonicalResult assertion result) =
      formulaBodyPattern result := rfl

private theorem argumentsValidAt_length_eq_local
    {formals : List (String × Nat)} {arguments : List Pattern}
    (hvalid : argumentsValidAt formals arguments = true) :
    arguments.length = formals.length := by
  induction formals generalizing arguments with
  | nil =>
      cases arguments <;> simp [argumentsValidAt] at hvalid ⊢
  | cons formal formals ih =>
      cases arguments with
      | nil => simp [argumentsValidAt] at hvalid
      | cons argument arguments =>
          simp only [argumentsValidAt, Bool.and_eq_true] at hvalid
          simp [ih hvalid.2]

private theorem assertionRuleApplication_length
    (projection : PrefixProjection) (target : ValidatedPresentation)
    (hprojection : presentationOfProjection? projection = some target.1)
    {assertion : AssertionView}
    (hassertion : assertion ∈ projection.assertions)
    {actuals : List ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    {result : ConstantHeadedFormula}
    (application : RuleApplication target
      (assertionRuleInstance assertion actuals result)
      (assertionPremises substitution projection.callerFrame assertion
        actuals result)
      (proves (encodeFormula result))) :
    assertion.hypotheses.length = actuals.length := by
  rcases application with
    ⟨rule, hlookup, harguments, hpremises, hconclusion⟩
  have hexact := lookup_assertionRule_of_projection projection target
    hprojection hassertion
  have hrule : rule = assertionRule projection.callerFrame assertion := by
    exact Option.some.inj (hlookup.symm.trans hexact)
  subst rule
  have hmetavariables :
      (assertionRule projection.callerFrame assertion).metavariables =
        assertionHypothesisFormalsFrom 0 assertion.hypotheses ++
          [(conclusionBodyFormalName, 0)] := by
    rfl
  rw [hmetavariables] at harguments
  have hlength := argumentsValidAt_length_eq_local harguments
  simpa [assertionRuleInstance, assertionRuleArguments,
    assertionHypothesisFormalsFrom_length] using hlength.symm

private theorem assertionRuleInstance_canonical
    (assertion : AssertionView)
    {actuals : List ConstantHeadedFormula}
    (result : ConstantHeadedFormula)
    (hlength : assertion.hypotheses.length = actuals.length) :
    assertionRuleInstance assertion
        (canonicalActuals assertion.hypotheses actuals)
        (canonicalResult assertion result) =
      assertionRuleInstance assertion actuals result := by
  simp [assertionRuleInstance, assertionRuleArguments,
    canonicalActuals_bodyPatterns hlength]

private theorem assertionPremises_take_proves
    (substitution : FiniteSubstitution) (callerFrame : RuntimeFrame)
    (assertion : AssertionView) (actuals : List ConstantHeadedFormula)
    (result : ConstantHeadedFormula) :
    (assertionPremises substitution callerFrame assertion actuals result).take
        actuals.length =
      assertionProvesPremises actuals := by
  simp [assertionPremises, assertionProvesPremises]

private theorem assertionPremises_getLast?
    (substitution : FiniteSubstitution) (callerFrame : RuntimeFrame)
    (assertion : AssertionView) (actuals : List ConstantHeadedFormula)
    (result : ConstantHeadedFormula) :
    (assertionPremises substitution callerFrame assertion actuals result).getLast? =
      some (applySubst (encodeSubstitution substitution)
        (encodeFormula assertion.formula) (encodeFormula result)) := by
  simp [assertionPremises, assertionSidePremises]

private theorem provesEncodeFormula_injective :
    Function.Injective
      (fun formula : ConstantHeadedFormula => proves (encodeFormula formula)) := by
  intro first second heq
  apply encodeFormula_injective
  simpa [proves] using heq

private theorem applySubst_left_injective
    {first second source result : Pattern}
    (heq : applySubst first source result =
      applySubst second source result) :
    first = second := by
  exact (List.cons.inj (Pattern.apply.inj heq).2).1

/-- The local generated-rule application carries exactly the independently
defined mandatory-hypothesis instances and the assertion result typecode. -/
theorem assertionRuleApplication_iff_instances
    (projection : PrefixProjection) (target : ValidatedPresentation)
    (hprojection : presentationOfProjection? projection = some target.1)
    {assertion : AssertionView}
    (hassertion : assertion ∈ projection.assertions)
    {actuals : List ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    {result : ConstantHeadedFormula} :
    RuleApplication target
        (assertionRuleInstance assertion actuals result)
        (assertionPremises substitution projection.callerFrame assertion
          actuals result)
        (proves (encodeFormula result)) ↔
      HypothesisInstances assertion.hypotheses actuals substitution ∧
        result.typecode = assertion.formula.typecode := by
  constructor
  · intro application
    have hlength := assertionRuleApplication_length projection target
      hprojection hassertion application
    let canonicalActuals' :=
      canonicalActuals assertion.hypotheses actuals
    let canonicalSubstitution' :=
      canonicalSubstitution assertion.hypotheses actuals
    let canonicalResult' := canonicalResult assertion result
    have canonicalInstances :
        HypothesisInstances assertion.hypotheses canonicalActuals'
          canonicalSubstitution' := by
      exact canonical_hypothesisInstances hlength
    have canonicalApplication := assertionRuleApplication_of_instances
      projection target hprojection hassertion canonicalInstances
      (by rfl : canonicalResult'.typecode = assertion.formula.typecode)
    have hinstance :
        assertionRuleInstance assertion canonicalActuals' canonicalResult' =
          assertionRuleInstance assertion actuals result := by
      exact assertionRuleInstance_canonical assertion result hlength
    rw [hinstance] at canonicalApplication
    have houtputs := application.outputs_unique canonicalApplication
    have hresult : result = canonicalResult' := by
      apply provesEncodeFormula_injective
      exact houtputs.2
    have hpremisePrefix := congrArg
      (fun premises : List Pattern => premises.take actuals.length)
      houtputs.1
    have hcanonicalLength : canonicalActuals'.length = actuals.length :=
      canonicalInstances.lengths.symm.trans hlength
    have hcanonicalPrefix :
        (assertionPremises canonicalSubstitution'
            projection.callerFrame assertion canonicalActuals'
            canonicalResult').take actuals.length =
          assertionProvesPremises canonicalActuals' := by
      rw [← hcanonicalLength]
      exact assertionPremises_take_proves canonicalSubstitution'
        projection.callerFrame assertion canonicalActuals' canonicalResult'
    have hproves :
        assertionProvesPremises actuals =
          assertionProvesPremises canonicalActuals' := by
      calc
        assertionProvesPremises actuals =
            (assertionPremises substitution projection.callerFrame assertion
              actuals result).take actuals.length :=
          (assertionPremises_take_proves substitution
            projection.callerFrame assertion actuals result).symm
        _ = (assertionPremises canonicalSubstitution'
              projection.callerFrame assertion canonicalActuals'
              canonicalResult').take actuals.length := hpremisePrefix
        _ = assertionProvesPremises canonicalActuals' := hcanonicalPrefix
    have hactuals : actuals = canonicalActuals' := by
      apply provesEncodeFormula_injective.list_map
      simpa [assertionProvesPremises] using hproves
    have hpremiseLast := congrArg List.getLast? houtputs.1
    have hsubstitutionEncoded :
        encodeSubstitution substitution =
          encodeSubstitution canonicalSubstitution' := by
      apply applySubst_left_injective
      simpa [assertionPremises_getLast?, hresult] using hpremiseLast
    have hsubstitution : substitution = canonicalSubstitution' :=
      encodeSubstitution_injective hsubstitutionEncoded
    have hinstances :
        HypothesisInstances assertion.hypotheses actuals substitution := by
      rw [hactuals, hsubstitution]
      exact canonicalInstances
    refine ⟨hinstances, ?_⟩
    simpa [canonicalResult', canonicalResult, withTypecode] using
      congrArg ConstantHeadedFormula.typecode hresult
  · rintro ⟨instances, hresultTypecode⟩
    exact assertionRuleApplication_of_instances projection target
      hprojection hassertion instances hresultTypecode

/-! ## Proof-relevant side evidence -/

/-- Ordered derivations of precisely the essential-hypothesis substitution
judgments.  The list index records both order and exact formulas. -/
structure EssentialPremiseEvidence (target : ValidatedPresentation)
    (substitution : FiniteSubstitution) (hypotheses : List HypothesisView)
    (actuals : List ConstantHeadedFormula) : Type where
  derivations : DerivationList target
    (assertionEssentialPremises substitution hypotheses actuals)

def EssentialPremiseEvidence.toDerivationList
    {target : ValidatedPresentation} {substitution : FiniteSubstitution}
    {hypotheses : List HypothesisView}
    {actuals : List ConstantHeadedFormula}
    (evidence : EssentialPremiseEvidence target substitution
      hypotheses actuals) :
    DerivationList target
      (assertionEssentialPremises substitution hypotheses actuals) :=
  evidence.derivations

def EssentialPremiseEvidence.ofDerivationList
    {target : ValidatedPresentation} {substitution : FiniteSubstitution}
    {hypotheses : List HypothesisView}
    {actuals : List ConstantHeadedFormula}
    (derivations : DerivationList target
      (assertionEssentialPremises substitution hypotheses actuals)) :
    EssentialPremiseEvidence target substitution hypotheses actuals :=
  ⟨derivations⟩

@[simp] theorem EssentialPremiseEvidence.to_of
    {target : ValidatedPresentation} {substitution : FiniteSubstitution}
    {hypotheses : List HypothesisView}
    {actuals : List ConstantHeadedFormula}
    (derivations : DerivationList target
      (assertionEssentialPremises substitution hypotheses actuals)) :
    (EssentialPremiseEvidence.ofDerivationList derivations).toDerivationList =
      derivations := rfl

@[simp] theorem EssentialPremiseEvidence.of_to
    {target : ValidatedPresentation} {substitution : FiniteSubstitution}
    {hypotheses : List HypothesisView}
    {actuals : List ConstantHeadedFormula}
    (evidence : EssentialPremiseEvidence target substitution
      hypotheses actuals) :
    EssentialPremiseEvidence.ofDerivationList evidence.toDerivationList =
      evidence := by
  cases evidence
  rfl

/-- Concatenate ordered derivation vectors without changing any tree. -/
def appendDerivationLists {presentation : ValidatedPresentation}
    {left right : List Pattern} :
    DerivationList presentation left →
      DerivationList presentation right →
        DerivationList presentation (left ++ right)
  | .nil, rightDerivations => rightDerivations
  | .cons head tail, rightDerivations =>
      .cons head (appendDerivationLists tail rightDerivations)

/-- Split an indexed derivation vector at an exact list prefix. -/
def splitDerivationLists {presentation : ValidatedPresentation}
    : (left right : List Pattern) →
      DerivationList presentation (left ++ right) →
        DerivationList presentation left ×
          DerivationList presentation right
  | [], _, derivations => ⟨.nil, derivations⟩
  | _ :: left, right, .cons head tail =>
      let split := splitDerivationLists left right tail
      ⟨.cons head split.1, split.2⟩

@[simp] theorem splitDerivationLists_append
    {presentation : ValidatedPresentation}
    {left right : List Pattern}
    (leftDerivations : DerivationList presentation left)
    (rightDerivations : DerivationList presentation right) :
    splitDerivationLists left right
        (appendDerivationLists leftDerivations rightDerivations) =
      ⟨leftDerivations, rightDerivations⟩ := by
  induction left with
  | nil =>
      cases leftDerivations
      rfl
  | cons premise premises ih =>
      cases leftDerivations with
      | cons head tail =>
          simp [appendDerivationLists, splitDerivationLists, ih]

@[simp] theorem appendDerivationLists_split
    {presentation : ValidatedPresentation}
    (left right : List Pattern)
    (derivations : DerivationList presentation (left ++ right)) :
    appendDerivationLists
        (splitDerivationLists left right derivations).1
        (splitDerivationLists left right derivations).2 =
      derivations := by
  induction left with
  | nil => rfl
  | cons premise premises ih =>
      cases derivations with
      | cons head tail =>
          simp [splitDerivationLists, appendDerivationLists, ih]

/-- All side-condition evidence carried by one generated assertion node.
The three fields retain the essential prefix, DV check, and final result check
as distinct proof-relevant data. -/
structure AssertionSideEvidence (target : ValidatedPresentation)
    (substitution : FiniteSubstitution) (callerFrame : RuntimeFrame)
    (assertion : AssertionView) (actuals : List ConstantHeadedFormula)
    (result : ConstantHeadedFormula) : Type where
  essential : EssentialPremiseEvidence target substitution
    assertion.hypotheses actuals
  dv : Derivation target
    (dvOK (encodeSubstitution substitution) (encodeFrame callerFrame)
      (encodeFrame assertion.frame))
  result : Derivation target
    (applySubst (encodeSubstitution substitution)
      (encodeFormula assertion.formula) (encodeFormula result))

def AssertionSideEvidence.toDerivationList
    {target : ValidatedPresentation} {substitution : FiniteSubstitution}
    {callerFrame : RuntimeFrame} {assertion : AssertionView}
    {actuals : List ConstantHeadedFormula}
    {result : ConstantHeadedFormula}
    (evidence : AssertionSideEvidence target substitution callerFrame
      assertion actuals result) :
    DerivationList target
      (assertionSidePremises substitution callerFrame assertion actuals
        result) := by
  change DerivationList target
    (assertionEssentialPremises substitution assertion.hypotheses actuals ++
      [ dvOK (encodeSubstitution substitution) (encodeFrame callerFrame)
          (encodeFrame assertion.frame)
      , applySubst (encodeSubstitution substitution)
          (encodeFormula assertion.formula) (encodeFormula result) ])
  exact appendDerivationLists evidence.essential.toDerivationList
    (.cons evidence.dv (.cons evidence.result .nil))

def AssertionSideEvidence.ofDerivationList
    {target : ValidatedPresentation} {substitution : FiniteSubstitution}
    {callerFrame : RuntimeFrame} {assertion : AssertionView}
    {actuals : List ConstantHeadedFormula}
    {result : ConstantHeadedFormula}
    (derivations : DerivationList target
      (assertionSidePremises substitution callerFrame assertion actuals
        result)) :
    AssertionSideEvidence target substitution callerFrame assertion
      actuals result := by
  change DerivationList target
    (assertionEssentialPremises substitution assertion.hypotheses actuals ++
      [ dvOK (encodeSubstitution substitution) (encodeFrame callerFrame)
          (encodeFrame assertion.frame)
      , applySubst (encodeSubstitution substitution)
          (encodeFormula assertion.formula) (encodeFormula result) ]) at derivations
  rcases splitDerivationLists
      (assertionEssentialPremises substitution assertion.hypotheses actuals)
      [ dvOK (encodeSubstitution substitution) (encodeFrame callerFrame)
          (encodeFrame assertion.frame)
      , applySubst (encodeSubstitution substitution)
          (encodeFormula assertion.formula) (encodeFormula result) ]
      derivations with ⟨essential, suffix⟩
  cases suffix with
  | cons dv tail =>
      cases tail with
      | cons result tail =>
          cases tail with
          | nil => exact ⟨⟨essential⟩, dv, result⟩

private theorem applySubst_isSideJudgment_local
    (substitution source result : Pattern) :
    IsSideJudgment (applySubst substitution source result) := by
  simp [IsSideJudgment, applySubst, reservedJudgmentHeads]

private theorem dvOK_isSideJudgment_local
    (substitution callerFrame calleeFrame : Pattern) :
    IsSideJudgment (dvOK substitution callerFrame calleeFrame) := by
  simp [IsSideJudgment, dvOK, reservedJudgmentHeads]

private theorem applySubst_projection_derivation_iff_semantics
    (projection : PrefixProjection) (target : ValidatedPresentation)
    (hprojection : presentationOfProjection? projection = some target.1)
    (substitution : FiniteSubstitution)
    (source result : ConstantHeadedFormula) :
    Nonempty (Derivation target
        (applySubst (encodeSubstitution substitution) (encodeFormula source)
          (encodeFormula result))) ↔
      FormulaSubstitutionSemantics substitution source result :=
  (sideDerivation_nonempty_iff_projection projection target hprojection
      (applySubst_isSideJudgment_local _ _ _)).symm.trans
    (applySubst_derivation_iff substitution source result)

private theorem dvOK_projection_derivation_iff_semantics
    (projection : PrefixProjection) (target : ValidatedPresentation)
    (hprojection : presentationOfProjection? projection = some target.1)
    (substitution : FiniteSubstitution)
    (callerFrame calleeFrame : RuntimeFrame) :
    Nonempty (Derivation target
        (dvOK (encodeSubstitution substitution) (encodeFrame callerFrame)
          (encodeFrame calleeFrame))) ↔
      DVOKSemantics substitution callerFrame calleeFrame :=
  (sideDerivation_nonempty_iff_projection projection target hprojection
      (dvOK_isSideJudgment_local _ _ _)).symm.trans
    (dvOK_derivation_iff substitution callerFrame calleeFrame)

private theorem essentialEvidence_nonempty_iff_matches
    (projection : PrefixProjection) (target : ValidatedPresentation)
    (hprojection : presentationOfProjection? projection = some target.1)
    {hypotheses : List HypothesisView}
    {actuals : List ConstantHeadedFormula}
    {instanceSubstitution substitution : FiniteSubstitution}
    (instances : HypothesisInstances hypotheses actuals
      instanceSubstitution) :
    Nonempty (EssentialPremiseEvidence target substitution
        hypotheses actuals) ↔
      EssentialMatches substitution hypotheses actuals := by
  induction instances with
  | nil =>
      constructor
      · intro _
        trivial
      · intro _
        exact ⟨⟨.nil⟩⟩
  | @floating label typecode variableName actual hypotheses actuals
      instanceSubstitution typecode_eq tail ih =>
      constructor
      · rintro ⟨⟨derivations⟩⟩
        exact ih.mp ⟨⟨derivations⟩⟩
      · intro hmatches
        rcases ih.mpr hmatches with ⟨⟨derivations⟩⟩
        exact ⟨⟨derivations⟩⟩
  | @essential label formula actual hypotheses actuals
      instanceSubstitution typecode_eq tail ih =>
      constructor
      · rintro ⟨⟨derivations⟩⟩
        cases derivations with
        | cons head tailDerivations =>
            refine ⟨
              (applySubst_projection_derivation_iff_semantics
                projection target hprojection substitution formula actual).mp
                  ⟨head⟩,
              ?_⟩
            exact ih.mp ⟨⟨tailDerivations⟩⟩
      · rintro ⟨headSemantics, tailSemantics⟩
        rcases (applySubst_projection_derivation_iff_semantics
          projection target hprojection substitution formula actual).mpr
            headSemantics with ⟨head⟩
        rcases ih.mpr tailSemantics with ⟨⟨tailDerivations⟩⟩
        exact ⟨⟨.cons head tailDerivations⟩⟩

theorem assertionSideEvidence_nonempty_iff_semantics
    (projection : PrefixProjection) (target : ValidatedPresentation)
    (hprojection : presentationOfProjection? projection = some target.1)
    {assertion : AssertionView}
    {actuals : List ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    {result : ConstantHeadedFormula}
    (instances : HypothesisInstances assertion.hypotheses actuals
      substitution) :
    Nonempty (AssertionSideEvidence target substitution
        projection.callerFrame assertion actuals result) ↔
      EssentialMatches substitution assertion.hypotheses actuals ∧
        DVOKSemantics substitution projection.callerFrame assertion.frame ∧
        FormulaSubstitutionSemantics substitution assertion.formula result := by
  constructor
  · rintro ⟨evidence⟩
    exact ⟨
      (essentialEvidence_nonempty_iff_matches projection target hprojection
        instances).mp ⟨evidence.essential⟩,
      (dvOK_projection_derivation_iff_semantics projection target hprojection
        substitution projection.callerFrame assertion.frame).mp
          ⟨evidence.dv⟩,
      (applySubst_projection_derivation_iff_semantics projection target
        hprojection substitution assertion.formula result).mp
          ⟨evidence.result⟩⟩
  · rintro ⟨essentialSemantics, dvSemantics, resultSemantics⟩
    rcases (essentialEvidence_nonempty_iff_matches projection target
      hprojection instances).mpr essentialSemantics with ⟨essential⟩
    rcases (dvOK_projection_derivation_iff_semantics projection target
      hprojection substitution projection.callerFrame assertion.frame).mpr
        dvSemantics with ⟨dv⟩
    rcases (applySubst_projection_derivation_iff_semantics projection target
      hprojection substitution assertion.formula result).mpr
        resultSemantics with ⟨result⟩
    exact ⟨⟨essential, dv, result⟩⟩

/-! ## Exact generated assertion nodes -/

/-- One exact local assertion-rule node plus proof-relevant evidence for all
and only its side premises.  Leading `Proves` premise derivations are
deliberately absent and must be supplied by the caller during assembly. -/
structure GeneratedAssertionNode (projection : PrefixProjection)
    (target : ValidatedPresentation) (assertion : AssertionView)
    (actuals : List ConstantHeadedFormula)
    (result : ConstantHeadedFormula)
    (substitution : FiniteSubstitution) : Type where
  application : RuleApplication target
    (assertionRuleInstance assertion actuals result)
    (assertionPremises substitution projection.callerFrame assertion
      actuals result)
    (proves (encodeFormula result))
  sideEvidence : AssertionSideEvidence target substitution
    projection.callerFrame assertion actuals result

/-- Assemble the full derivation only after the caller provides ordered
proofs of every `Proves` premise.  This is the explicit recursive-proof
boundary: a local generated node never fabricates those witnesses. -/
def GeneratedAssertionNode.assemble
    {projection : PrefixProjection} {target : ValidatedPresentation}
    {assertion : AssertionView}
    {actuals : List ConstantHeadedFormula}
    {result : ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    (node : GeneratedAssertionNode projection target assertion actuals
      result substitution)
    (provesEvidence : DerivationList target
      (assertionProvesPremises actuals)) :
    Derivation target (proves (encodeFormula result)) := by
  apply Derivation.byRule
    (assertionRuleInstance assertion actuals result)
    node.application
  simpa [assertionPremises] using
    appendDerivationLists provesEvidence
      node.sideEvidence.toDerivationList

/-- Exact equivalence between a proof-relevant generated assertion node and
the independent assertion-application semantics.  This theorem concerns one
local generated rule node, not arbitrary `Proves` derivations and not runtime
reduction. -/
theorem generatedAssertionNode_nonempty_iff_semantics
    (projection : PrefixProjection) (target : ValidatedPresentation)
    (hprojection : presentationOfProjection? projection = some target.1)
    {assertion : AssertionView}
    (hassertion : assertion ∈ projection.assertions)
    (actuals : List ConstantHeadedFormula)
    (result : ConstantHeadedFormula) :
    Nonempty
        (Σ substitution : FiniteSubstitution,
          GeneratedAssertionNode projection target assertion actuals result
            substitution) ↔
      AssertionApplicationSemantics projection.callerFrame assertion
        actuals result := by
  constructor
  · rintro ⟨⟨substitution, node⟩⟩
    rcases (assertionRuleApplication_iff_instances projection target
      hprojection hassertion).mp node.application with
      ⟨instances, hresultTypecode⟩
    rcases (assertionSideEvidence_nonempty_iff_semantics projection target
      hprojection instances).mp ⟨node.sideEvidence⟩ with
      ⟨essentialMatches, dvSemantics, resultSemantics⟩
    exact ⟨substitution, instances, essentialMatches, dvSemantics,
      resultSemantics⟩
  · rintro ⟨substitution, instances, essentialMatches, dvSemantics,
      resultSemantics⟩
    have application := assertionRuleApplication_of_instances
      projection target hprojection hassertion instances
        resultSemantics.1.symm
    rcases (assertionSideEvidence_nonempty_iff_semantics projection target
      hprojection instances).mpr
        ⟨essentialMatches, dvSemantics, resultSemantics⟩ with
      ⟨sideEvidence⟩
    exact ⟨⟨substitution, ⟨application, sideEvidence⟩⟩⟩

/-! ## Small independent examples -/

namespace Examples

private def emptyFrame : RuntimeFrame := ⟨#[], #[]⟩

private def emptyFormula : ConstantHeadedFormula := ⟨"|-", []⟩

private def emptyAssertion : AssertionView :=
  { label := "ax-empty"
    formula := emptyFormula
    frame := emptyFrame
    hypotheses := [] }

/-- Positive: an empty-body assertion with no mandatory hypotheses, DV pairs,
or substitution bindings has the independent application semantics. -/
example :
    AssertionApplicationSemantics emptyFrame emptyAssertion []
      emptyFormula := by
  refine ⟨[], .nil, trivial, ?_, ?_⟩
  · change DVListsSemantics [] ([] : List (String × String)) []
    intro pair hmem
    simp at hmem
  · exact ⟨rfl, .nil⟩

/-- Positive: one floating hypothesis contributes its exact ordered binding. -/
example :
    HypothesisInstances
      [.floating "wph" "wff" "ph"]
      [⟨"wff", [.const "T"]⟩]
      [⟨"ph", ⟨"wff", [.const "T"]⟩⟩] :=
  .floating rfl .nil

/-- Negative: changing the result typecode invalidates the otherwise
body-identical empty assertion application. -/
example :
    ¬ AssertionApplicationSemantics emptyFrame emptyAssertion []
      ⟨"wff", []⟩ :=
  not_assertionApplicationSemantics_of_result_typecode_ne (by decide)

/-- Negative: omitting an authored floating hypothesis actual is rejected. -/
example (result : ConstantHeadedFormula) :
    ¬ AssertionApplicationSemantics emptyFrame
      { emptyAssertion with
        hypotheses := [.floating "wph" "wff" "ph"] }
      [] result :=
  not_assertionApplicationSemantics_of_length_ne (by decide)

end Examples

end Mettapedia.Languages.Metamath.InferenceProjection.AssertionApplication
