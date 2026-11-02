import Mettapedia.OSLF.MeTTaIL.GeneralVectorInputQuery

/-! Typed constructor/vector provider outputs extend the actual scoped
assignment. A two-input/one-output query constructs a root firing with its
real provider-row position and output matching trace.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

open Syntax Match RuleBinding ScopedRuleMatching GeneralScopedMatch
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem NameCoherent.queryArgument {rule : RewriteRule} {premiseIndex argumentIndex : Nat}
    {relation : String} {arguments : List Pattern} {schema : Pattern}
    (premise : rule.premises[premiseIndex]? = some (.relationQuery relation arguments))
    (argument : arguments[argumentIndex]? = some schema) :
    NameCoherent rule (.premise premiseIndex 0 argumentIndex) [] schema := by
  intro suffix
  simp only [sitePattern?, premise, quantifiedBody?, Option.bind_eq_bind, Option.bind_some, argument, List.nil_append]

theorem vector_typed_scoped_instance {environment : GeneralPremise.Environment} {bound : List TypeExpr}
    {rule : RewriteRule} {spec : RuleBindingSpec} {site : RulePatternSite} {bindings : Bindings}
    {initial : ScopedRuleMatching.Assignment} {schema target : Pattern} {type : TypeExpr}
    (admitted : admittedFor rule spec = true) (zero : GeneralPremise.checkZeroDependencies spec = true)
    (typed : CapturesTyped environment.language environment.free bound rule.typeContext bindings)
    (shape : VectorFirstOrder schema) (coherent : NameCoherent rule site [] schema)
    (defined : Defined bindings schema.freeFvarNames) (instantiated : applyBindings bindings schema = target)
    (targetTyped : OpenPatternWellSorted environment.language environment.free bound type target)
    (before : ScopedCompatible bound.length bindings initial) :
    ∃ final, Matches rule spec bound.length site [] 0 initial schema target final ∧
      ScopedCompatible bound.length bindings final ∧
      GeneralPremise.TypedAssignment environment ⟨0, rule, spec, bound, 0, 0⟩ final := by
  obtain ⟨raw, matched, compatible, _, _⟩ := vector_match_instance bindings shape defined
  rw [instantiated] at matched
  have declared : ∀ name ∈ schema.freeFvarNames, dependencies? spec name = some [] := by
    intro name member
    obtain ⟨body, found⟩ := defined name member
    obtain ⟨expected, declared, _⟩ := typed (name, body) (raw_lookup_member found)
    exact dependencies_empty_of_admitted admitted zero declared
  obtain ⟨final, matching, read⟩ := binderFree_scoped_of_matchRel_admitted admitted
    (GeneralRuleBindingInference.vector_binderFree shape) coherent declared matched compatible
    targetTyped.2.2.2 targetTyped.2.2.1 before
  exact ⟨final, matching, read, read.typed_admitted typed admitted zero⟩

theorem vector_two_input_output_root_construct {environment : GeneralPremise.Environment} {bound : List TypeExpr}
    {type outputType : TypeExpr} {rule : RewriteRule} {spec : RuleBindingSpec} {ordinal rowIndex : Nat}
    {bindings : Bindings} {source target first second answer : Pattern} {relation : String}
    {firstName secondName outputName : String} {signature : GeneralPremise.Signature}
    (selected : environment.language.rewrites[ordinal]? = some rule)
    (specified : GeneralPremise.specification? environment ordinal = some spec)
    (admitted : admittedFor rule spec = true) (zero : GeneralPremise.checkZeroDependencies spec = true)
    (leftShape : VectorFirstOrder rule.left) (rightShape : VectorFirstOrder rule.right)
    (typed : CapturesTyped environment.language environment.free bound rule.typeContext bindings)
    (premise : rule.premises = [.relationQuery relation [.fvar firstName, .fvar secondName, .fvar outputName]])
    (firstBound : firstName ∈ rule.left.freeFvarNames) (secondBound : secondName ∈ rule.left.freeFvarNames)
    (rightBound : ∀ name ∈ rule.right.freeFvarNames, name ∈ rule.left.freeFvarNames ∨ name = outputName)
    (defined : Defined bindings rule.left.freeFvarNames)
    (outputDefined : Defined bindings (Pattern.fvar outputName).freeFvarNames)
    (sourceTyped : OpenPatternWellSorted environment.language environment.free bound type source)
    (targetTyped : OpenPatternWellSorted environment.language environment.free bound type target)
    (answerTyped : OpenPatternWellSorted environment.language environment.free bound outputType answer)
    (input : applyBindings bindings rule.left = source) (output : applyBindings bindings rule.right = target)
    (firstValue : applyBindings bindings (.fvar firstName) = first)
    (secondValue : applyBindings bindings (.fvar secondName) = second)
    (answerValue : applyBindings bindings (.fvar outputName) = answer)
    (row : environment.provider.rows[rowIndex]? = some ⟨relation, [first, second, answer]⟩)
    (signatureFound : GeneralPremise.signature? environment.provider relation 3 = some signature)
    (modes : signature.modes = [.input, .input, .output])
    (rowTyped : GeneralPremise.RowTyped environment.language environment.free bound signature
      ⟨relation, [first, second, answer]⟩) :
    ∃ trace captured completed outputTrace,
      GeneralPremise.RootFiring environment bound type source ordinal trace captured completed
        [.query 0 0 rowIndex [(0, []), (1, []), (2, outputTrace)]] target := by
  obtain ⟨captured, matching, read, capturedTyped⟩ := vector_typed_scoped_instance (environment := environment) (initial := [])
    admitted zero typed leftShape (NameCoherent.left rule) defined input sourceTyped
    (by intro _ member; cases member)
  have declared : ∀ name, Defined bindings (Pattern.fvar name).freeFvarNames → dependencies? spec name = some [] := by
    intro name existsValue
    obtain ⟨body, found⟩ := existsValue name (by simp [Pattern.freeFvarNames])
    obtain ⟨expected, declared, _⟩ := typed (name, body) (raw_lookup_member found)
    exact dependencies_empty_of_admitted admitted zero declared
  have boundNames : GeneralPremise.BoundNames captured rule.left.freeFvarNames :=
    GeneralPremise.matching_bound_names matching
  have rootValues := read.rootValues typed
  have premiseAt : rule.premises[0]? = some (.relationQuery relation [.fvar firstName, .fvar secondName, .fvar outputName]) := by
    rw [premise]
    rfl
  have firstCoherent := NameCoherent.queryArgument premiseAt (show ([Pattern.fvar firstName, .fvar secondName, .fvar outputName])[0]? = _ from rfl)
  have secondCoherent := NameCoherent.queryArgument premiseAt (show ([Pattern.fvar firstName, .fvar secondName, .fvar outputName])[1]? = _ from rfl)
  have outputCoherent := NameCoherent.queryArgument premiseAt (show ([Pattern.fvar firstName, .fvar secondName, .fvar outputName])[2]? = _ from rfl)
  have firstDefined : GeneralPremise.BoundNames captured (Pattern.fvar firstName).freeFvarNames := by
    intro name member
    have same : name = firstName := by simpa only [Pattern.freeFvarNames, List.mem_singleton] using member
    exact same ▸ boundNames firstName firstBound
  have secondDefined : GeneralPremise.BoundNames captured (Pattern.fvar secondName).freeFvarNames := by
    intro name member
    have same : name = secondName := by simpa only [Pattern.freeFvarNames, List.mem_singleton] using member
    exact same ▸ boundNames secondName secondBound
  have firstRead := vector_instantiation_exact (operation := Substitution.instantiateBVar) admitted (.metavariable firstName)
    firstCoherent firstDefined rootValues read (by
      intro name member
      have same : name = firstName := by simpa only [Pattern.freeFvarNames, List.mem_singleton] using member
      subst name
      exact declared firstName (by
        intro actual present
        have same : actual = firstName := by simpa only [Pattern.freeFvarNames, List.mem_singleton] using present
        subst actual
        exact defined firstName firstBound))
  have secondRead := vector_instantiation_exact (operation := Substitution.instantiateBVar) admitted (.metavariable secondName)
    secondCoherent secondDefined rootValues read (by
      intro name member
      have same : name = secondName := by simpa only [Pattern.freeFvarNames, List.mem_singleton] using member
      subst name
      exact declared secondName (by
        intro actual present
        have same : actual = secondName := by simpa only [Pattern.freeFvarNames, List.mem_singleton] using present
        subst actual
        exact defined secondName secondBound))
  rw [firstValue] at firstRead
  rw [secondValue] at secondRead
  obtain ⟨completed, outputMatch, finalRead, finalTyped⟩ := vector_typed_scoped_instance (environment := environment)
    admitted zero typed (.metavariable outputName) outputCoherent outputDefined answerValue answerTyped read
  have rightDefined : GeneralPremise.BoundNames completed rule.right.freeFvarNames := by
    intro name member
    rcases rightBound name member with old | same
    · obtain ⟨body, found⟩ := boundNames name old
      exact ⟨body, outputMatch.extends name body found⟩
    · rw [same]
      exact GeneralPremise.matching_bound_names outputMatch outputName (by simp [Pattern.freeFvarNames])
  have rightDependencies : ∀ name ∈ rule.right.freeFvarNames, dependencies? spec name = some [] := by
    intro name member
    apply declared
    intro actual actualMember
    have same : actual = name := by simpa only [Pattern.freeFvarNames, List.mem_singleton] using actualMember
    subst actual
    rcases rightBound name member with old | same
    · exact defined name old
    · rw [same]
      exact outputDefined outputName (by simp [Pattern.freeFvarNames])
  have reduct := vector_instantiation_exact
    (operation := ScopedReflectiveExecution.binderOperation environment.reflection rule)
    admitted rightShape (NameCoherent.right rule) rightDefined (finalRead.rootValues typed) finalRead rightDependencies
  rw [output] at reduct
  obtain ⟨outputTrace, tracedOutput⟩ := GeneralScopedMatchMachine.matches_trace outputMatch
  let context : GeneralPremise.Context := ⟨ordinal, rule, spec, bound, 0, 0⟩
  have query : GeneralPremise.TracedQuery environment context relation [.fvar firstName, .fvar secondName, .fvar outputName]
      captured rowIndex completed [(0, []), (1, []), (2, outputTrace)] := by
    apply GeneralPremise.TracedQuery.row row signatureFound rowTyped
    · rw [modes]
      exact .input firstRead (.input secondRead (.output tracedOutput .nil))
    · exact finalTyped
  obtain ⟨trace, traced⟩ := GeneralScopedMatchMachine.matches_trace matching
  refine ⟨trace, captured, completed, outputTrace,
    .fire selected specified admitted sourceTyped traced capturedTyped ?_ reduct targetTyped⟩
  rw [premise]
  exact .cons (.query query) .nil

#print axioms NameCoherent.queryArgument
#print axioms vector_typed_scoped_instance
#print axioms vector_two_input_output_root_construct

end Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection
