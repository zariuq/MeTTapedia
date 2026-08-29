import Mettapedia.Languages.Metamath.InferenceProjectionProvesRuleInversion
import Mettapedia.Languages.Metamath.InferenceProjectionInvariants

/-!
# Raw syntactic shape of projected assertion applications

Root-rule inversion identifies an assertion schema but intentionally does not
interpret its instance arguments as encoded Metamath formulas.  This module
continues at that same syntactic level.  It splits the instance arguments into
one raw body per authored mandatory hypothesis followed by one raw result
body, then computes the exact ordered instantiated premise vector.

Every body remains an arbitrary `Pattern`.  Formula decoding belongs to the
recursive child-reflection layer: leading `Proves` children and the final
`ApplySubst` child provide the evidence needed there.
-/

namespace Mettapedia.Languages.Metamath.InferenceProjection

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceSideConditions

/-! ## Direct raw-body syntax -/

/-- A formula-shaped pattern with an authored typecode and an uninterpreted
body. -/
def rawFormulaPattern (typecode : String) (body : Pattern) : Pattern :=
  Builder.formula (encodeString typecode) body

/-- One leading `Proves` judgment per mandatory hypothesis, in authored
order.  Mismatched lists are deliberately fail-closed; the normal-form
theorem proves exact length alignment before using this function. -/
def rawAssertionProvesPremises :
    List HypothesisView → List Pattern → List Pattern
  | [], [] => []
  | hypothesis :: hypotheses, body :: bodies =>
      proves (rawFormulaPattern hypothesis.typecode body) ::
        rawAssertionProvesPremises hypotheses bodies
  | _, _ => []

/-- Ordered substitution bindings contributed only by floating hypotheses. -/
def rawAssertionBindings :
    List HypothesisView → List Pattern → List Pattern
  | [], [] => []
  | .floating _ typecode variableName :: hypotheses, body :: bodies =>
      Builder.binding (encodeString variableName)
          (rawFormulaPattern typecode body) ::
        rawAssertionBindings hypotheses bodies
  | .essential _ _ :: hypotheses, _ :: bodies =>
      rawAssertionBindings hypotheses bodies
  | _, _ => []

def rawAssertionSubstitution
    (hypotheses : List HypothesisView) (bodies : List Pattern) : Pattern :=
  Builder.substitution (encodeListWith id
    (rawAssertionBindings hypotheses bodies))

/-- Essential-hypothesis checks in authored order, all sharing the complete
raw substitution assembled from the floating hypotheses. -/
def rawAssertionEssentialPremises (substitution : Pattern) :
    List HypothesisView → List Pattern → List Pattern
  | [], [] => []
  | .floating _ _ _ :: hypotheses, _ :: bodies =>
      rawAssertionEssentialPremises substitution hypotheses bodies
  | .essential _ formula :: hypotheses, body :: bodies =>
      applySubst substitution (encodeFormula formula)
          (rawFormulaPattern formula.typecode body) ::
        rawAssertionEssentialPremises substitution hypotheses bodies
  | _, _ => []

def rawAssertionSidePremises (callerFrame : RuntimeFrame)
    (assertion : AssertionView) (bodies : List Pattern)
    (resultBody : Pattern) : List Pattern :=
  let substitution :=
    rawAssertionSubstitution assertion.hypotheses bodies
  rawAssertionEssentialPremises substitution assertion.hypotheses bodies ++
    [ dvOK substitution (encodeFrame callerFrame)
        (encodeFrame assertion.frame)
    , applySubst substitution (encodeFormula assertion.formula)
        (rawFormulaPattern assertion.formula.typecode resultBody) ]

/-- Exact raw premise order of a projected assertion schema. -/
def rawAssertionPremises (callerFrame : RuntimeFrame)
    (assertion : AssertionView) (bodies : List Pattern)
    (resultBody : Pattern) : List Pattern :=
  rawAssertionProvesPremises assertion.hypotheses bodies ++
    rawAssertionSidePremises callerFrame assertion bodies resultBody

def rawAssertionConclusion (assertion : AssertionView)
    (resultBody : Pattern) : Pattern :=
  proves (rawFormulaPattern assertion.formula.typecode resultBody)

/-! ## Reusable normal-form proposition -/

/-- Full raw root shape.  Besides the normalized equations, it retains the
ordinary schema-instantiation witnesses so callers can reconstruct the exact
`AssertionApplicationView` without assuming an inverse to syntax decoding. -/
def AssertionRawApplicationShape
    (projection : PrefixProjection) (target : ValidatedCalculusLanguageDef)
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (formulaPattern : Pattern) : Prop :=
  ∃ assertion : AssertionView, ∃ bodies : List Pattern, ∃ resultBody : Pattern,
    assertion ∈ projection.assertions ∧
    target.1.lookupRule? ruleInstance.ruleId =
      some (assertionRule projection.callerFrame assertion) ∧
    argumentsValidAt
      (assertionRule projection.callerFrame assertion).metavariables
      ruleInstance.arguments = true ∧
    InstantiatesList
      (assertionRule projection.callerFrame assertion).metavariables
      ruleInstance.arguments
      (assertionRule projection.callerFrame assertion).premises premises ∧
    Instantiates
      (assertionRule projection.callerFrame assertion).metavariables
      ruleInstance.arguments
      (assertionRule projection.callerFrame assertion).conclusion
      (proves formulaPattern) ∧
    ruleInstance.ruleId = ⟨assertion.label⟩ ∧
    ruleInstance.arguments = bodies ++ [resultBody] ∧
    bodies.length = assertion.hypotheses.length ∧
    premises = rawAssertionPremises projection.callerFrame assertion
      bodies resultBody ∧
    formulaPattern =
      rawFormulaPattern assertion.formula.typecode resultBody

/-! ## Generic finite-list plumbing -/

private theorem argumentsValidAt_length_eq
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

private theorem assertionHypothesisFormalsFrom_length
    (index : Nat) (hypotheses : List HypothesisView) :
    (assertionHypothesisFormalsFrom index hypotheses).length =
      hypotheses.length := by
  induction hypotheses generalizing index with
  | nil => rfl
  | cons hypothesis hypotheses ih =>
      cases hypothesis <;>
        simp [assertionHypothesisFormalsFrom, ih]

private theorem ruleId_eq_of_lookup
    {presentation : CalculusLanguageDef} {ruleId : RuleId} {rule : RuleSchema}
    (hlookup : presentation.lookupRule? ruleId = some rule) :
    ruleId = rule.id := by
  have hfind :
      presentation.rules.find?
          (fun candidate => decide (candidate.id = ruleId)) = some rule := by
    simpa [CalculusLanguageDef.lookupRule?] using hlookup
  have hid : decide (rule.id = ruleId) = true := by
    exact List.find?_some
      (p := fun candidate : RuleSchema => decide (candidate.id = ruleId))
      hfind
  exact (of_decide_eq_true hid).symm

private theorem assertionRuleFormalNames_nodup_of_lookup
    (target : ValidatedCalculusLanguageDef) (callerFrame : RuntimeFrame)
    (assertion : AssertionView)
    (hlookup :
      target.1.lookupRule? ⟨assertion.label⟩ =
        some (assertionRule callerFrame assertion)) :
    ((assertionRule callerFrame assertion).metavariables.map Prod.fst).Nodup := by
  have hvalidIn := rule_isValidIn_of_lookup target hlookup
  have hvalidV1 :
      RuleSchema.isLocallyValid (assertionRule callerFrame assertion) = true := by
    simp only [RuleSchema.isValidIn, Bool.and_eq_true] at hvalidIn
    exact hvalidIn.1
  have hunique :
      ((RuleSchema.metavariableNames
          (assertionRule callerFrame assertion)).eraseDups).length =
        (RuleSchema.metavariableNames
          (assertionRule callerFrame assertion)).length := by
    simp only [RuleSchema.isLocallyValid, Bool.and_eq_true, beq_iff_eq] at hvalidV1
    exact hvalidV1.1.1.1.1.1.2
  exact nodup_of_eraseDups_length_eq _ (by
    simpa [RuleSchema.metavariableNames] using hunique)

private theorem assertionHypothesisFormalNames_nodup
    {callerFrame : RuntimeFrame} {assertion : AssertionView}
    (hfull :
      ((assertionRule callerFrame assertion).metavariables.map Prod.fst).Nodup) :
    ((assertionHypothesisFormalsFrom 0 assertion.hypotheses).map
      Prod.fst).Nodup := by
  have hsub :
      List.Sublist
        (assertionHypothesisFormalsFrom 0 assertion.hypotheses)
        (assertionRule callerFrame assertion).metavariables := by
    rw [show (assertionRule callerFrame assertion).metavariables =
        assertionHypothesisFormalsFrom 0 assertion.hypotheses ++
          [(conclusionBodyFormalName, 0)] by rfl]
    exact List.sublist_append_left _ _
  exact hfull.sublist (hsub.map Prod.fst)

private theorem nonempty_of_length_eq_succ
    {alpha : Type} {values : List alpha} {length : Nat}
    (hlength : values.length = length + 1) : values ≠ [] := by
  intro heq
  simp [heq] at hlength

private theorem dropLast_length_of_length_eq_succ
    {alpha : Type} {values : List alpha} {length : Nat}
    (hlength : values.length = length + 1) :
    values.dropLast.length = length := by
  rw [List.length_dropLast]
  omega

/-! ## Instantiation support -/

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

private theorem ground_instantiates
    (formals : List (String × Nat)) (arguments : List Pattern)
    (schema : Pattern) (hground : schema.isGroundAt 0 = true) :
    Instantiates formals arguments schema schema :=
  instantiateSchemaAt?_sound
    (instantiateSchemaAt?_ground_identity formals arguments 0 schema hground)

@[simp] private theorem encodeSym_isGroundAt (depth : Nat)
    (symbol : RuntimeSym) :
    (encodeSym symbol).isGroundAt depth = true := by
  cases symbol <;>
    simp [encodeSym, encodeString, Builder.constSym, Builder.varSym,
      Builder.encodedString, Builder.rawString, Pattern.isGroundAt,
      Pattern.isGroundListAt]

@[simp] private theorem encodeString_isGroundAt (depth : Nat)
    (value : String) :
    (encodeString value).isGroundAt depth = true := by
  simp [encodeString, Builder.encodedString, Builder.rawString,
    Pattern.isGroundAt, Pattern.isGroundListAt]

private theorem encodeListWith_isGroundAt
    {alpha : Type} (encode : alpha → Pattern)
    (hencode : ∀ value, (encode value).isGroundAt depth = true) :
    ∀ values : List alpha,
      (encodeListWith encode values).isGroundAt depth = true
  | [] => by
      simp [encodeListWith, Builder.nil, Pattern.isGroundAt,
        Pattern.isGroundListAt]
  | value :: values => by
      simp [encodeListWith, Builder.cons, Pattern.isGroundAt,
        Pattern.isGroundListAt, hencode value,
        encodeListWith_isGroundAt encode hencode values]

@[simp] private theorem encodeFormula_isGroundAt (depth : Nat)
    (formula : ConstantHeadedFormula) :
    (encodeFormula formula).isGroundAt depth = true := by
  rcases formula with ⟨typecode, body⟩
  simp [encodeFormula, Builder.formula, Pattern.isGroundAt,
    Pattern.isGroundListAt,
    encodeListWith_isGroundAt encodeSym (encodeSym_isGroundAt depth) body]

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
    Pattern.isGroundListAt,
    encodeListWith_isGroundAt encodeDVPair
      (encodeDVPair_isGroundAt depth) dj.toList,
    encodeListWith_isGroundAt encodeString
      (encodeString_isGroundAt depth) hyps.toList]

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

private theorem formula_instantiates
    {formals : List (String × Nat)} {arguments : List Pattern}
    {typecode : String} {bodySchema bodyResult : Pattern}
    (hbody : Instantiates formals arguments bodySchema bodyResult) :
    Instantiates formals arguments
      (rawFormulaPattern typecode bodySchema)
      (rawFormulaPattern typecode bodyResult) := by
  have htypecode : Instantiates formals arguments
      (encodeString typecode) (encodeString typecode) :=
    ground_instantiates formals arguments (encodeString typecode)
      (encodeString_isGroundAt 0 typecode)
  simpa [rawFormulaPattern, Builder.formula] using
    InstantiatesAt.apply
      (InstantiatesListAt.cons htypecode
        (InstantiatesListAt.cons hbody (InstantiatesListAt.nil 0)))

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

/-! ## Aligned raw body slots -/

/-- Instantiation evidence for exactly the hypothesis-body metavariables.
This is syntactic evidence only; the results need not encode formulas. -/
inductive RawHypothesisBodyInstantiations
    (formals : List (String × Nat)) (arguments : List Pattern) :
    Nat → List HypothesisView → List Pattern → Prop where
  | nil (index : Nat) :
      RawHypothesisBodyInstantiations formals arguments index [] []
  | cons {index : Nat} {hypothesis : HypothesisView}
      {hypotheses : List HypothesisView} {body : Pattern}
      {bodies : List Pattern}
      (head : Instantiates formals arguments
        (.fvar (hypothesisBodyFormalName index)) body)
      (tail : RawHypothesisBodyInstantiations formals arguments
        (index + 1) hypotheses bodies) :
      RawHypothesisBodyInstantiations formals arguments index
        (hypothesis :: hypotheses) (body :: bodies)

private theorem RawHypothesisBodyInstantiations.cons_unused
    {formals : List (String × Nat)} {arguments : List Pattern}
    {formal : String × Nat} {argument : Pattern}
    {index : Nat} {hypotheses : List HypothesisView}
    {bodies : List Pattern}
    (instantiations : RawHypothesisBodyInstantiations formals arguments
      index hypotheses bodies)
    (hnot :
      formal.1 ∉
        (assertionHypothesisFormalsFrom index hypotheses).map Prod.fst) :
    RawHypothesisBodyInstantiations (formal :: formals)
      (argument :: arguments) index hypotheses bodies := by
  induction instantiations with
  | nil => exact .nil _
  | @cons index hypothesis hypotheses body bodies head tail ih =>
      simp only [assertionHypothesisFormalsFrom, List.map_cons,
        List.mem_cons, not_or] at hnot
      have hpair :
          formal ≠ (hypothesisBodyFormalName index, 0) := by
        intro heq
        exact hnot.1 (congrArg Prod.fst heq)
      refine .cons (InstantiatesAt.cons_unused head ?_) (ih hnot.2)
      simpa [patternMetavariableOccurrencesAt] using hpair

private theorem rawHypothesisBodyInstantiations
    {hypotheses : List HypothesisView} {bodies : List Pattern}
    (hlength : hypotheses.length = bodies.length)
    (index : Nat) (resultBody : Pattern)
    (hformals :
      ((assertionHypothesisFormalsFrom index hypotheses).map Prod.fst).Nodup) :
    RawHypothesisBodyInstantiations
      (assertionHypothesisFormalsFrom index hypotheses ++
        [(conclusionBodyFormalName, 0)])
      (bodies ++ [resultBody]) index hypotheses bodies := by
  induction hypotheses generalizing bodies index with
  | nil =>
      cases bodies with
      | nil => exact .nil index
      | cons body bodies => simp at hlength
  | cons hypothesis hypotheses ih =>
      cases bodies with
      | nil => simp at hlength
      | cons body bodies =>
          have htailLength : hypotheses.length = bodies.length := by
            simpa using hlength
          rw [show assertionHypothesisFormalsFrom index
              (hypothesis :: hypotheses) =
              (hypothesisBodyFormalName index, 0) ::
                assertionHypothesisFormalsFrom (index + 1) hypotheses by rfl]
            at hformals ⊢
          simp only [List.map_cons, List.nodup_cons] at hformals
          refine .cons (.fvar ?_) ?_
          · simp [lookupArgumentAt?]
          · exact (ih htailLength (index + 1) hformals.2).cons_unused
              hformals.1

/-! ## Raw component instantiation -/

private theorem unary_instantiates
    {formals : List (String × Nat)} {arguments : List Pattern}
    {head : String} {schema result : Pattern}
    (hitem : Instantiates formals arguments schema result) :
    Instantiates formals arguments (.apply head [schema])
      (.apply head [result]) :=
  InstantiatesAt.apply
    (InstantiatesListAt.cons hitem (InstantiatesListAt.nil 0))

private theorem binary_instantiates
    {formals : List (String × Nat)} {arguments : List Pattern}
    {head : String} {leftSchema leftResult rightSchema rightResult : Pattern}
    (hleft : Instantiates formals arguments leftSchema leftResult)
    (hright : Instantiates formals arguments rightSchema rightResult) :
    Instantiates formals arguments
      (.apply head [leftSchema, rightSchema])
      (.apply head [leftResult, rightResult]) :=
  InstantiatesAt.apply
    (InstantiatesListAt.cons hleft
      (InstantiatesListAt.cons hright (InstantiatesListAt.nil 0)))

private theorem binding_instantiates
    {formals : List (String × Nat)} {arguments : List Pattern}
    {variableName typecode : String} {bodySchema bodyResult : Pattern}
    (hbody : Instantiates formals arguments bodySchema bodyResult) :
    Instantiates formals arguments
      (Builder.binding (encodeString variableName)
        (rawFormulaPattern typecode bodySchema))
      (Builder.binding (encodeString variableName)
        (rawFormulaPattern typecode bodyResult)) := by
  have hname := ground_instantiates formals arguments
    (encodeString variableName) (encodeString_isGroundAt 0 variableName)
  simpa [Builder.binding] using
    binary_instantiates hname (formula_instantiates hbody)

private theorem encodedList_cons_instantiates
    {formals : List (String × Nat)} {arguments : List Pattern}
    {headSchema headResult tailSchema tailResult : Pattern}
    (hhead : Instantiates formals arguments headSchema headResult)
    (htail : Instantiates formals arguments tailSchema tailResult) :
    Instantiates formals arguments
      (Builder.cons headSchema tailSchema)
      (Builder.cons headResult tailResult) := by
  simpa [Builder.cons] using binary_instantiates hhead htail

private theorem rawBindingsList_instantiates
    {formals : List (String × Nat)} {arguments : List Pattern}
    {index : Nat} {hypotheses : List HypothesisView}
    {bodies : List Pattern}
    (bodyInstantiations :
      RawHypothesisBodyInstantiations formals arguments index
        hypotheses bodies) :
    Instantiates formals arguments
      (encodeListWith id (assertionBindingsFrom index hypotheses))
      (encodeListWith id (rawAssertionBindings hypotheses bodies)) := by
  induction bodyInstantiations with
  | nil =>
      exact ground_instantiates formals arguments (Builder.nil)
        (by simp [Builder.nil, Pattern.isGroundAt,
          Pattern.isGroundListAt])
  | @cons index hypothesis hypotheses body bodies head tail ih =>
      cases hypothesis with
      | floating label typecode variableName =>
          rw [show assertionBindingsFrom index
              (.floating label typecode variableName :: hypotheses) =
              Builder.binding (encodeString variableName)
                  (rawFormulaPattern typecode
                    (.fvar (hypothesisBodyFormalName index))) ::
                assertionBindingsFrom (index + 1) hypotheses by rfl]
          simpa [rawAssertionBindings, encodeListWith] using
            encodedList_cons_instantiates (binding_instantiates head) ih
      | essential label formula =>
          simpa [assertionBindingsFrom, rawAssertionBindings] using ih

private theorem rawSubstitution_instantiates
    {formals : List (String × Nat)} {arguments : List Pattern}
    {index : Nat} {hypotheses : List HypothesisView}
    {bodies : List Pattern}
    (bodyInstantiations :
      RawHypothesisBodyInstantiations formals arguments index
        hypotheses bodies) :
    Instantiates formals arguments
      (Builder.substitution
        (encodeListWith id (assertionBindingsFrom index hypotheses)))
      (rawAssertionSubstitution hypotheses bodies) := by
  simpa [rawAssertionSubstitution, Builder.substitution] using
    unary_instantiates (rawBindingsList_instantiates bodyInstantiations)

private theorem rawProvesPremises_instantiates
    {formals : List (String × Nat)} {arguments : List Pattern}
    {index : Nat} {hypotheses : List HypothesisView}
    {bodies : List Pattern}
    (bodyInstantiations :
      RawHypothesisBodyInstantiations formals arguments index
        hypotheses bodies) :
    InstantiatesList formals arguments
      (assertionHypothesisProvesFrom index hypotheses)
      (rawAssertionProvesPremises hypotheses bodies) := by
  induction bodyInstantiations with
  | nil => exact .nil 0
  | @cons index hypothesis hypotheses body bodies head tail ih =>
      rw [show assertionHypothesisProvesFrom index
          (hypothesis :: hypotheses) =
          proves (rawFormulaPattern hypothesis.typecode
            (.fvar (hypothesisBodyFormalName index))) ::
              assertionHypothesisProvesFrom (index + 1) hypotheses by rfl]
      exact .cons (by
        simpa [rawAssertionProvesPremises] using
            proves_instantiates (formula_instantiates head)) ih

private theorem rawEssentialPremises_instantiates
    {formals : List (String × Nat)} {arguments : List Pattern}
    {substitutionSchema substitutionResult : Pattern}
    {index : Nat} {hypotheses : List HypothesisView}
    {bodies : List Pattern}
    (bodyInstantiations :
      RawHypothesisBodyInstantiations formals arguments index
        hypotheses bodies)
    (hsubstitution : Instantiates formals arguments
      substitutionSchema substitutionResult) :
    InstantiatesList formals arguments
      (assertionEssentialChecksFrom substitutionSchema index hypotheses)
      (rawAssertionEssentialPremises substitutionResult hypotheses bodies) := by
  induction bodyInstantiations with
  | nil => exact .nil 0
  | @cons index hypothesis hypotheses body bodies head tail ih =>
      cases hypothesis with
      | floating label typecode variableName =>
          simpa [assertionEssentialChecksFrom,
            rawAssertionEssentialPremises] using ih
      | essential label formula =>
          have hsource := ground_instantiates formals arguments
            (encodeFormula formula) (encodeFormula_isGroundAt 0 formula)
          rw [show assertionEssentialChecksFrom substitutionSchema index
              (.essential label formula :: hypotheses) =
              applySubst substitutionSchema (encodeFormula formula)
                  (rawFormulaPattern formula.typecode
                    (.fvar (hypothesisBodyFormalName index))) ::
                assertionEssentialChecksFrom substitutionSchema
                  (index + 1) hypotheses by rfl]
          exact .cons (by
            simpa [rawAssertionEssentialPremises] using
                applySubst_instantiates hsubstitution hsource
                  (formula_instantiates head)) ih

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

private theorem rawResultFormula_instantiates
    {callerFrame : RuntimeFrame} {assertion : AssertionView}
    {bodies : List Pattern} {resultBody : Pattern}
    (hlength : assertion.hypotheses.length = bodies.length)
    (hfullNames :
      ((assertionRule callerFrame assertion).metavariables.map Prod.fst).Nodup) :
    Instantiates
      (assertionRule callerFrame assertion).metavariables
      (bodies ++ [resultBody])
      (Builder.formula (encodeString assertion.formula.typecode)
        (.fvar conclusionBodyFormalName))
      (rawFormulaPattern assertion.formula.typecode resultBody) := by
  have hmetavariables :
      (assertionRule callerFrame assertion).metavariables =
        assertionHypothesisFormalsFrom 0 assertion.hypotheses ++
          [(conclusionBodyFormalName, 0)] := by
    rfl
  have hfullNames' :
      (((assertionHypothesisFormalsFrom 0 assertion.hypotheses).map
          Prod.fst) ++ [conclusionBodyFormalName]).Nodup := by
    rw [hmetavariables] at hfullNames
    simpa using hfullNames
  have hcross :
      ((assertionHypothesisFormalsFrom 0 assertion.hypotheses).map
          Prod.fst).Nodup ∧
        ∀ name : String,
          name ∈ (assertionHypothesisFormalsFrom 0
              assertion.hypotheses).map Prod.fst →
            name ≠ conclusionBodyFormalName := by
    simpa [List.nodup_append] using hfullNames'
  have hnot :
      (conclusionBodyFormalName, 0) ∉
        assertionHypothesisFormalsFrom 0 assertion.hypotheses := by
    intro hmember
    exact hcross.2 conclusionBodyFormalName
      (List.mem_map_of_mem hmember) rfl
  have hformalsLength :
      (assertionHypothesisFormalsFrom 0 assertion.hypotheses).length =
        bodies.length := by
    rw [assertionHypothesisFormalsFrom_length, hlength]
  have hbody : Instantiates
      (assertionHypothesisFormalsFrom 0 assertion.hypotheses ++
        [(conclusionBodyFormalName, 0)])
      (bodies ++ [resultBody])
      (.fvar conclusionBodyFormalName) resultBody :=
    .fvar (lookupArgumentAt?_append_last hformalsLength hnot)
  rw [hmetavariables]
  exact formula_instantiates hbody

private theorem rawAssertionPremises_instantiates
    (callerFrame : RuntimeFrame) (assertion : AssertionView)
    {bodies : List Pattern} {resultBody : Pattern}
    (hbodyInstantiations :
      RawHypothesisBodyInstantiations
        (assertionRule callerFrame assertion).metavariables
        (bodies ++ [resultBody]) 0 assertion.hypotheses bodies)
    (hresult : Instantiates
      (assertionRule callerFrame assertion).metavariables
      (bodies ++ [resultBody])
      (Builder.formula (encodeString assertion.formula.typecode)
        (.fvar conclusionBodyFormalName))
      (rawFormulaPattern assertion.formula.typecode resultBody)) :
    InstantiatesList
      (assertionRule callerFrame assertion).metavariables
      (bodies ++ [resultBody])
      (assertionRule callerFrame assertion).premises
      (rawAssertionPremises callerFrame assertion bodies resultBody) := by
  let substitutionSchema := assertionSubstitution assertion
  let substitutionResult :=
    rawAssertionSubstitution assertion.hypotheses bodies
  have hsubstitution : Instantiates
      (assertionRule callerFrame assertion).metavariables
      (bodies ++ [resultBody]) substitutionSchema substitutionResult := by
    exact rawSubstitution_instantiates hbodyInstantiations
  have hproves := rawProvesPremises_instantiates hbodyInstantiations
  have hessential := rawEssentialPremises_instantiates
    hbodyInstantiations hsubstitution
  have hcaller := ground_instantiates
    (assertionRule callerFrame assertion).metavariables
    (bodies ++ [resultBody]) (encodeFrame callerFrame)
    (encodeFrame_isGroundAt 0 callerFrame)
  have hcallee := ground_instantiates
    (assertionRule callerFrame assertion).metavariables
    (bodies ++ [resultBody]) (encodeFrame assertion.frame)
    (encodeFrame_isGroundAt 0 assertion.frame)
  have hsource := ground_instantiates
    (assertionRule callerFrame assertion).metavariables
    (bodies ++ [resultBody]) (encodeFormula assertion.formula)
    (encodeFormula_isGroundAt 0 assertion.formula)
  have hdv := dvOK_instantiates hsubstitution hcaller hcallee
  have hfinal := applySubst_instantiates hsubstitution hsource hresult
  have htail : InstantiatesList
      (assertionRule callerFrame assertion).metavariables
      (bodies ++ [resultBody])
      (assertionEssentialChecksFrom substitutionSchema 0
          assertion.hypotheses ++
        [ dvOK substitutionSchema (encodeFrame callerFrame)
            (encodeFrame assertion.frame)
        , applySubst substitutionSchema (encodeFormula assertion.formula)
            (Builder.formula (encodeString assertion.formula.typecode)
              (.fvar conclusionBodyFormalName)) ])
      (rawAssertionEssentialPremises substitutionResult
          assertion.hypotheses bodies ++
        [ dvOK substitutionResult (encodeFrame callerFrame)
            (encodeFrame assertion.frame)
        , applySubst substitutionResult (encodeFormula assertion.formula)
            (rawFormulaPattern assertion.formula.typecode resultBody) ]) :=
    instantiatesListAt_append hessential
      (.cons hdv (.cons hfinal (.nil 0)))
  have hpremiseSchemas :
      (assertionRule callerFrame assertion).premises =
        assertionHypothesisProvesFrom 0 assertion.hypotheses ++
          assertionEssentialChecksFrom substitutionSchema 0
              assertion.hypotheses ++
          [ dvOK substitutionSchema (encodeFrame callerFrame)
              (encodeFrame assertion.frame)
          , applySubst substitutionSchema (encodeFormula assertion.formula)
              (Builder.formula (encodeString assertion.formula.typecode)
                (.fvar conclusionBodyFormalName)) ] := by
    rfl
  rw [hpremiseSchemas]
  simpa [assertionSubstitution, substitutionSchema, substitutionResult,
    rawAssertionPremises, rawAssertionSidePremises, List.append_assoc] using
      instantiatesListAt_append hproves htail

/-! ## Exact raw root theorem -/

/-- An assertion-root view is equivalent to its expanded raw syntactic normal
form.  The forward direction contains all substantive alignment and schema
instantiation work; the reverse direction merely forgets the derived normal
form equations. -/
theorem assertionApplicationView_iff_rawShape
    (projection : PrefixProjection) (target : ValidatedCalculusLanguageDef)
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {formulaPattern : Pattern} :
    AssertionApplicationView projection target ruleInstance premises
        formulaPattern ↔
      AssertionRawApplicationShape projection target ruleInstance premises
        formulaPattern := by
  constructor
  · rintro ⟨assertion, hmember, hlookup, harguments,
      hpremises, hconclusion⟩
    have hruleId : ruleInstance.ruleId = ⟨assertion.label⟩ := by
      have hid := ruleId_eq_of_lookup hlookup
      rw [show (assertionRule projection.callerFrame assertion).id =
        (⟨assertion.label⟩ : RuleId) by rfl] at hid
      exact hid
    have hlookupLabel :
        target.1.lookupRule? ⟨assertion.label⟩ =
          some (assertionRule projection.callerFrame assertion) := by
      rw [← hruleId]
      exact hlookup
    have hfullNames := assertionRuleFormalNames_nodup_of_lookup target
      projection.callerFrame assertion hlookupLabel
    have hhypothesisNames :=
      assertionHypothesisFormalNames_nodup hfullNames
    have hargumentLength :
        ruleInstance.arguments.length = assertion.hypotheses.length + 1 := by
      have hmetavariables :
          (assertionRule projection.callerFrame assertion).metavariables =
            assertionHypothesisFormalsFrom 0 assertion.hypotheses ++
              [(conclusionBodyFormalName, 0)] := by
        rfl
      calc
        ruleInstance.arguments.length =
            (assertionRule projection.callerFrame assertion).metavariables.length :=
          argumentsValidAt_length_eq harguments
        _ = assertion.hypotheses.length + 1 := by
          rw [hmetavariables]
          simp [assertionHypothesisFormalsFrom_length]
    have hnonempty : ruleInstance.arguments ≠ [] :=
      nonempty_of_length_eq_succ hargumentLength
    let bodies := ruleInstance.arguments.dropLast
    let resultBody := ruleInstance.arguments.getLast hnonempty
    have hargumentsSplit :
        ruleInstance.arguments = bodies ++ [resultBody] := by
      simpa [bodies, resultBody] using
        (List.dropLast_append_getLast (l := ruleInstance.arguments) hnonempty).symm
    have hbodiesLength : bodies.length = assertion.hypotheses.length :=
      dropLast_length_of_length_eq_succ hargumentLength
    have hbodyInstantiations :
        RawHypothesisBodyInstantiations
          (assertionRule projection.callerFrame assertion).metavariables
          (bodies ++ [resultBody]) 0 assertion.hypotheses bodies := by
      rw [show (assertionRule projection.callerFrame assertion).metavariables =
        assertionHypothesisFormalsFrom 0 assertion.hypotheses ++
          [(conclusionBodyFormalName, 0)] by rfl]
      exact rawHypothesisBodyInstantiations hbodiesLength.symm 0 resultBody
        hhypothesisNames
    have hresult := rawResultFormula_instantiates
      (resultBody := resultBody) hbodiesLength.symm hfullNames
    have hexpectedPremises := rawAssertionPremises_instantiates
      projection.callerFrame assertion hbodyInstantiations hresult
    have hpremisesEq :
        premises = rawAssertionPremises projection.callerFrame assertion
          bodies resultBody := by
      apply InstantiatesListAt.functional hpremises
      rw [hargumentsSplit]
      exact hexpectedPremises
    have hconclusionExpected : Instantiates
        (assertionRule projection.callerFrame assertion).metavariables
        ruleInstance.arguments
        (assertionRule projection.callerFrame assertion).conclusion
        (rawAssertionConclusion assertion resultBody) := by
      rw [hargumentsSplit]
      rw [show (assertionRule projection.callerFrame assertion).conclusion =
        proves (Builder.formula (encodeString assertion.formula.typecode)
          (.fvar conclusionBodyFormalName)) by rfl]
      simpa [rawAssertionConclusion] using proves_instantiates hresult
    have hformulaEq :
        formulaPattern =
          rawFormulaPattern assertion.formula.typecode resultBody := by
      have houtputs := InstantiatesAt.functional hconclusion
        hconclusionExpected
      simpa [rawAssertionConclusion, proves] using houtputs
    exact ⟨assertion, bodies, resultBody, hmember, hlookup, harguments,
      hpremises, hconclusion, hruleId, hargumentsSplit, hbodiesLength,
      hpremisesEq, hformulaEq⟩
  · rintro ⟨assertion, bodies, resultBody, hmember, hlookup, harguments,
      hpremises, hconclusion, _hruleId, _hargumentsSplit, _hbodiesLength,
      _hpremisesEq, _hformulaEq⟩
    exact ⟨assertion, hmember, hlookup, harguments, hpremises, hconclusion⟩

/-! ## Concrete boundaries -/

private def boundaryFrame : RuntimeFrame := ⟨#[], #[]⟩

private def boundaryAssertion : AssertionView :=
  { label := "ax-raw-boundary"
    formula := ⟨"|-", []⟩
    frame := boundaryFrame
    hypotheses :=
      [ .floating "wph" "wff" "ph"
      , .essential "eph" ⟨"|-", [.var "ph"]⟩ ] }

/-- Positive syntax boundary: two authored hypotheses yield two leading
`Proves` premises in the same order, independently of body interpretation. -/
example (firstBody secondBody : Pattern) :
    rawAssertionProvesPremises boundaryAssertion.hypotheses
        [firstBody, secondBody] =
      [ proves (rawFormulaPattern "wff" firstBody)
      , proves (rawFormulaPattern "|-" secondBody) ] := by
  rfl

/-- The same raw vector places the essential check after both leading
`Proves` judgments and before the DV and final-substitution checks. -/
example (firstBody secondBody resultBody : Pattern) :
    (rawAssertionPremises boundaryFrame boundaryAssertion
      [firstBody, secondBody] resultBody).length = 5 := by
  simp [boundaryAssertion, rawAssertionPremises,
    rawAssertionProvesPremises, rawAssertionSidePremises,
    rawAssertionEssentialPremises]

/-- Negative decoding boundary: a ground pattern outside the formula encoding
still passes the generic argument gate for the result-body slot. -/
example :
    argumentsValidAt
      (assertionRule boundaryFrame
        { boundaryAssertion with hypotheses := [] }).metavariables
      [.apply "unclassified-raw-body" []] = true := by
  decide

end Mettapedia.Languages.Metamath.InferenceProjection
