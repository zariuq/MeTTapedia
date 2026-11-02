import Mettapedia.OSLF.MeTTaIL.GeneralVectorCaptureTyping

/-! Constructor/vector rules with a read-only provider premise construct
actual scoped root firings. Every query argument is instantiated from the
matched source; row position and typed provider evidence are retained.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

open Syntax Match RuleBinding ScopedRuleMatching GeneralScopedMatch
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem vector_input_arguments {context : GeneralPremise.Context}
    {bindings : Bindings} {assignment : ScopedRuleMatching.Assignment} {schemas : List Pattern} {index : Nat}
    (admitted : admittedFor context.rule context.spec = true)
    (shapes : ∀ schema ∈ schemas, VectorFirstOrder schema)
    (coherent : ∀ offset schema, schemas[offset]? = some schema → NameCoherent context.rule (context.site (index + offset)) [] schema)
    (defined : ∀ schema ∈ schemas, GeneralPremise.BoundNames assignment schema.freeFvarNames)
    (roots : GeneralPremise.RootValues context.bound.length assignment)
    (compatible : ScopedCompatible context.bound.length bindings assignment)
    (declared : ∀ schema ∈ schemas, ∀ name ∈ schema.freeFvarNames, dependencies? context.spec name = some []) :
    GeneralPremise.TracedArgumentsHold context index assignment schemas (schemas.map (applyBindings bindings))
      (schemas.map (fun _ => RelationArgMode.input)) assignment
      ((List.range schemas.length).map (fun offset => (index + offset, []))) := by
  induction schemas generalizing index with
  | nil => simpa using (GeneralPremise.TracedArgumentsHold.nil (context := context) (initial := assignment) (index := index))
  | cons schema schemas ih =>
    have instantiated := vector_instantiation_exact (operation := Substitution.instantiateBVar)
      admitted (shapes schema List.mem_cons_self) (by simpa using coherent 0 schema rfl)
      (defined schema List.mem_cons_self) roots compatible (declared schema List.mem_cons_self)
    have rest := ih (index := index + 1)
      (fun child member => shapes child (List.mem_cons_of_mem _ member))
      (by
        intro offset child selected
        have actual := coherent (offset + 1) child (by simpa using selected)
        simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using actual)
      (fun child member => defined child (List.mem_cons_of_mem _ member))
      (fun child member => declared child (List.mem_cons_of_mem _ member))
    have input : GeneralPremise.ordinaryInterpretation.Input
        ⟨context.rule, context.spec, context.bound.length, context.site index, [], 0, assignment,
          schema, applyBindings bindings schema⟩ := instantiated
    convert GeneralPremise.TracedArgumentsHold.input input rest using 1 <;>
      simp only [List.map_cons, List.length_cons, List.range_succ_eq_map, List.map_map, Function.comp_def,
        List.map_cons, Nat.add_zero, List.cons.injEq, true_and]
    congr 1
    funext offset
    congr 1
    omega

theorem vector_input_query_root_construct {environment : GeneralPremise.Environment} {bound : List TypeExpr}
    {type : TypeExpr} {rule : RewriteRule} {spec : RuleBindingSpec} {ordinal rowIndex : Nat}
    {assignment : Bindings} {source target : Pattern} {relation : String} {arguments : List Pattern}
    {signature : GeneralPremise.Signature}
    (selected : environment.language.rewrites[ordinal]? = some rule)
    (specified : GeneralPremise.specification? environment ordinal = some spec)
    (admitted : admittedFor rule spec = true) (zero : GeneralPremise.checkZeroDependencies spec = true)
    (labels : LabelDeterministic environment.language) (choices : CollectionChoiceDeterministic environment.language)
    (leftShape : VectorFirstOrder rule.left) (rightShape : VectorFirstOrder rule.right)
    (schemaTyped : Mettapedia.GSLT.LanguageDef.RestAwareTyping.HasType environment.language
      (FreeTypeContext.ofList rule.typeContext) [] rule.left type)
    (premise : rule.premises = [.relationQuery relation arguments])
    (rightBound : ∀ name ∈ rule.right.freeFvarNames, name ∈ rule.left.freeFvarNames)
    (queryShapes : ∀ argument ∈ arguments, VectorFirstOrder argument)
    (queryBound : ∀ argument ∈ arguments, ∀ name ∈ argument.freeFvarNames, name ∈ rule.left.freeFvarNames)
    (queryCoherent : ∀ index argument, arguments[index]? = some argument →
      NameCoherent rule (.premise 0 0 index) [] argument)
    (defined : Defined assignment rule.left.freeFvarNames)
    (sourceTyped : OpenPatternWellSorted environment.language environment.free bound type source)
    (targetTyped : OpenPatternWellSorted environment.language environment.free bound type target)
    (input : applyBindings assignment rule.left = source) (output : applyBindings assignment rule.right = target)
    (row : environment.provider.rows[rowIndex]? = some ⟨relation, arguments.map (applyBindings assignment)⟩)
    (signatureFound : GeneralPremise.signature? environment.provider relation arguments.length = some signature)
    (modes : signature.modes = arguments.map (fun _ => RelationArgMode.input))
    (rowTyped : GeneralPremise.RowTyped environment.language environment.free bound signature
      ⟨relation, arguments.map (applyBindings assignment)⟩) :
    ∃ trace captured, GeneralPremise.RootFiring environment bound type source ordinal trace captured captured
      [.query 0 0 rowIndex ((List.range arguments.length).map (fun index => (index, [])))] target := by
  obtain ⟨bindings, typed, names, capturesInput⟩ :=
    vector_source_typed_match labels choices leftShape schemaTyped sourceTyped defined input
  have capturesOutput : applyBindings bindings rule.right = target :=
    (vector_rule_output_unique leftShape rightShape rightBound bindings assignment (capturesInput.trans input.symm)).trans output
  have argumentValues : arguments.map (applyBindings bindings) = arguments.map (applyBindings assignment) := by
    apply List.map_congr_left
    intro argument member
    exact vector_rule_output_unique leftShape (queryShapes argument member) (queryBound argument member)
      bindings assignment (capturesInput.trans input.symm)
  have dependencies : ∀ name ∈ rule.left.freeFvarNames, dependencies? spec name = some [] := by
    intro name member
    obtain ⟨body, found⟩ := names name member
    obtain ⟨expected, declared, _⟩ := typed (name, body) (raw_lookup_member found)
    exact dependencies_empty_of_admitted admitted zero declared
  obtain ⟨raw, matched, compatible, _, _⟩ := vector_match_instance bindings leftShape names
  rw [capturesInput] at matched
  obtain ⟨captured, matching, read⟩ := binderFree_scoped_of_matchRel_admitted (initial := []) admitted
    (GeneralRuleBindingInference.vector_binderFree leftShape) (NameCoherent.left rule) dependencies
    matched compatible sourceTyped.2.2.2 sourceTyped.2.2.1 (by intro _ member; cases member)
  have capturedTyped := read.typed_admitted typed admitted zero
  have roots := read.rootValues typed
  have boundNames : GeneralPremise.BoundNames captured rule.left.freeFvarNames :=
    GeneralPremise.matching_bound_names matching
  have rightDefined : GeneralPremise.BoundNames captured rule.right.freeFvarNames :=
    fun name member => boundNames name (rightBound name member)
  have reduct := vector_instantiation_exact
    (operation := ScopedReflectiveExecution.binderOperation environment.reflection rule)
    admitted rightShape (NameCoherent.right rule) rightDefined roots read
    (fun name member => dependencies name (rightBound name member))
  rw [capturesOutput] at reduct
  let context : GeneralPremise.Context := ⟨ordinal, rule, spec, bound, 0, 0⟩
  have queryArguments := vector_input_arguments (context := context)
    (index := 0) admitted queryShapes (by simpa [context, GeneralPremise.Context.site] using queryCoherent)
    (fun argument member name present => boundNames name (queryBound argument member name present)) roots read
    (fun argument member name present => dependencies name (queryBound argument member name present))
  simp only [Nat.zero_add] at queryArguments
  rw [argumentValues, ← modes] at queryArguments
  have query : GeneralPremise.TracedQuery environment context relation arguments captured rowIndex captured
      ((List.range arguments.length).map (fun index => (index, []))) :=
    .row row signatureFound rowTyped queryArguments capturedTyped
  obtain ⟨trace, traced⟩ := GeneralScopedMatchMachine.matches_trace matching
  refine ⟨trace, captured, .fire selected specified admitted sourceTyped traced capturedTyped ?_ reduct targetTyped⟩
  rw [premise]
  exact .cons (.query query) .nil

#print axioms vector_input_arguments
#print axioms vector_input_query_root_construct

end Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection
