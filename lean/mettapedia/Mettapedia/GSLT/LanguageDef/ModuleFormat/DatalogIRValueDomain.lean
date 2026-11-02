import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRReferenceTyping

/-! In the prepared physical context, a sorted value is a registered value
reference. Primitive scalar payload sorts have no object inhabitants there;
their source literals live in the external dictionary, not in runtime terms. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ValueDomain

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

private def scalarSorts : List String := ["DlSymbol","DlInteger","DlUnsigned","DlFloat"]

theorem free_reference (pools : Join.Pools) (name sort : String)
    (found : FreeTypeContext.ofList (Executable.freeTypes pools) name = some (.base sort)) :
    (∃ index, index < pools.relations.length ∧ name = "dl:relation:" ++ toString index ∧ sort = "DlRelation") ∨
    (∃ index, index < pools.literals.length ∧ name = "dl:value:" ++ toString index ∧ sort = "DlValue") := by
  rw [context_ofList_lookup] at found
  obtain ⟨before,after,shape,_⟩ := List.lookup_eq_some_iff.mp found
  have member : (name,TypeExpr.base sort) ∈ Executable.freeTypes pools := by rw [shape]; simp
  rcases List.mem_append.mp member with relation | literal
  · obtain ⟨index,inside,same⟩ := List.mem_map.mp relation
    exact Or.inl ⟨index,List.mem_range.mp inside,(congrArg Prod.fst same).symm,
      (TypeExpr.base.inj (congrArg Prod.snd same)).symm⟩
  · obtain ⟨index,inside,same⟩ := List.mem_map.mp literal
    exact Or.inr ⟨index,List.mem_range.mp inside,(congrArg Prod.fst same).symm,
      (TypeExpr.base.inj (congrArg Prod.snd same)).symm⟩

private theorem scalar_no_constructor : ∀ rule ∈ Query.baseLanguage.terms,
    ∀ sort ∈ scalarSorts, rule.category ≠ sort := by decide +kernel

private theorem no_scalar_type (language : LanguageDef) (terms : language.terms = Query.baseLanguage.terms)
    (pools : Join.Pools) (sort : String) (scalar : sort ∈ scalarSorts)
    (pattern : Pattern) (type : TypeExpr)
    (typed : HasType language (FreeTypeContext.ofList (Executable.freeTypes pools)) [] pattern type)
    (expected : type = .base sort) (object : isObjectPattern pattern = true) : False := by
  cases typed with
  | bvar impossible => simp at impossible
  | fvar found =>
    rw [expected] at found
    rcases free_reference pools _ sort found with ⟨_,_,_,same⟩ | ⟨_,_,_,same⟩ <;>
      simp [scalarSorts,same] at scalar
  | @constructor _ rule arguments declared _ _ =>
    have same := TypeExpr.base.inj expected
    rw [terms] at declared
    exact scalar_no_constructor rule declared sort scalar same
  | lambda _ => cases expected
  | multiLambda _ => cases expected
  | subst _ _ => simp [isObjectPattern] at object
  | collection _ => cases expected
  | @collectionConstructor _ rule _ _ _ _ _ declared _ _ =>
    have same := TypeExpr.base.inj expected
    rw [terms] at declared
    exact scalar_no_constructor rule declared sort scalar same

private theorem value_parameters : ∀ rule ∈ Query.baseLanguage.terms, rule.category = "DlValue" →
    rule.params = [.simple "text" (.base "DlSymbol")] ∨
    rule.params = [.simple "value" (.base "DlInteger")] ∨
    rule.params = [.simple "value" (.base "DlUnsigned")] ∨
    rule.params = [.simple "value" (.base "DlFloat")] := by decide +kernel

private theorem scalar_argument_impossible (language : LanguageDef) (terms : language.terms = Query.baseLanguage.terms)
    (pools : Join.Pools) (name sort : String) (scalar : sort ∈ scalarSorts)
    (arguments : List Pattern)
    (typed : ArgumentsHaveTypes language (FreeTypeContext.ofList (Executable.freeTypes pools)) [] arguments [.simple name (.base sort)])
    (objects : isObjectPatternList arguments = true) : False := by
  cases typed with
  | cons _ expected head _ =>
    have same : TypeExpr.base sort = _ := Option.some.inj expected
    exact no_scalar_type language terms pools sort scalar _ _ head same.symm
      (Bool.and_eq_true_iff.mp objects).1

private theorem value_no_bare (rule : GrammarRule) (member : rule ∈ Query.baseLanguage.terms)
    (category : rule.category = "DlValue") : ¬ UsesBareCollection rule := by
  rintro ⟨name,kind,type,shape⟩
  have parameters := value_parameters rule member category
  rcases parameters with parameters | parameters | parameters | parameters <;>
    cases representation : rule.collectionRepresentation <;>
    simp [GrammarRule.bareParams,representation,parameters] at shape

theorem value_object_reference (language : LanguageDef) (terms : language.terms = Query.baseLanguage.terms)
    (pools : Join.Pools) (pattern : Pattern)
    (typed : HasType language (FreeTypeContext.ofList (Executable.freeTypes pools)) [] pattern (.base "DlValue"))
    (object : isObjectPattern pattern = true) :
    ∃ index, index < pools.literals.length ∧ pattern = Executable.valueRef index := by
  have classify (type : TypeExpr) (raw : HasType language (FreeTypeContext.ofList (Executable.freeTypes pools)) [] pattern type)
      (expected : type = .base "DlValue") (object : isObjectPattern pattern = true) :
      ∃ index, index < pools.literals.length ∧ pattern = Executable.valueRef index := by
    cases raw with
    | bvar impossible => simp at impossible
    | fvar found =>
      rw [expected] at found
      rcases free_reference pools _ "DlValue" found with ⟨_,_,_,impossible⟩ | ⟨index,inside,same,_⟩
      · simp at impossible
      · exact ⟨index,inside,congrArg Pattern.fvar same⟩
    | @constructor _ rule arguments declared _ argumentsTyped =>
      have category := TypeExpr.base.inj expected
      have member : rule ∈ Query.baseLanguage.terms := terms ▸ declared
      have objects : isObjectPatternList arguments = true := object
      rcases value_parameters rule member category with parameters | parameters | parameters | parameters
      all_goals
        rw [parameters] at argumentsTyped
        exact (scalar_argument_impossible language terms pools _ _ (by simp [scalarSorts]) arguments argumentsTyped objects).elim
    | lambda _ => cases expected
    | multiLambda _ => cases expected
    | subst _ _ => simp [isObjectPattern] at object
    | collection _ => cases expected
    | @collectionConstructor _ rule name kind elements rest elementType declared shape _ =>
      have category := TypeExpr.base.inj expected
      have member : rule ∈ Query.baseLanguage.terms := terms ▸ declared
      exact (value_no_bare rule member category ⟨name,kind,elementType,shape⟩).elim
  exact classify _ typed rfl object

theorem value_reference (language : LanguageDef) (terms : language.terms = Query.baseLanguage.terms)
    (pools : Join.Pools) (pattern : Pattern)
    (typed : OpenPatternWellSorted language (FreeTypeContext.ofList (Executable.freeTypes pools)) [] (.base "DlValue") pattern) :
    ∃ index, index < pools.literals.length ∧ pattern = Executable.valueRef index :=
  value_object_reference language terms pools pattern typed.1 typed.2.2.1

private theorem fact_parameters : ∀ rule ∈ Query.baseLanguage.terms, rule.label = "GroundFact" →
    rule.params = [.simple "relation" (.base "DlRelation"),.simple "values" (.base "DlGroundTuple")] := by decide +kernel

private theorem tuple_parameters : ∀ rule ∈ Query.baseLanguage.terms, rule.label = "GroundTuple" →
    rule.params = [.simple "values" (.collection .vec (.base "DlValue"))] := by decide +kernel

private theorem elements_references (language : LanguageDef) (terms : language.terms = Query.baseLanguage.terms)
    (pools : Join.Pools) (values : List Pattern)
    (typed : ElementsHaveType language (FreeTypeContext.ofList (Executable.freeTypes pools)) [] values (.base "DlValue"))
    (objects : isObjectPatternList values = true) :
    ∀ value ∈ values, ∃ index, index < pools.literals.length ∧ value = Executable.valueRef index := by
  induction values with
  | nil => intro _ member; cases member
  | cons value values ih =>
    cases typed with
    | cons first rest =>
      have pieces := Bool.and_eq_true_iff.mp objects
      intro other member
      rcases List.mem_cons.mp member with rfl | later
      · exact value_object_reference language terms pools other first pieces.1
      · exact ih rest pieces.2 other later

theorem fact_values (language : LanguageDef) (terms : language.terms = Query.baseLanguage.terms)
    (pools : Join.Pools) (relation : Pattern) (values : List Pattern)
    (typed : HasType language (FreeTypeContext.ofList (Executable.freeTypes pools)) []
      (.apply "GroundFact" [relation,.apply "GroundTuple" [Join.vector values]]) (.base "DlStatement"))
    (object : isObjectPattern (.apply "GroundFact" [relation,.apply "GroundTuple" [Join.vector values]]) = true) :
    ∀ value ∈ values, ∃ index, index < pools.literals.length ∧ value = Executable.valueRef index := by
  obtain ⟨factRule,declared,label,_,arguments⟩ := application_typing typed
  rw [fact_parameters factRule (terms ▸ declared) label] at arguments
  cases arguments with
  | cons _ _ _ tail =>
    cases tail with
    | cons _ tupleType tupleTyped _ =>
      rw [← Option.some.inj tupleType] at tupleTyped
      obtain ⟨tupleRule,tupleDeclared,tupleLabel,_,tupleArguments⟩ := application_typing tupleTyped
      rw [tuple_parameters tupleRule (terms ▸ tupleDeclared) tupleLabel] at tupleArguments
      cases tupleArguments with
      | cons _ vectorType vectorTyped _ =>
        rw [← Option.some.inj vectorType] at vectorTyped
        cases vectorTyped with
        | collection elements =>
          apply elements_references language terms pools values elements
          simp only [isObjectPattern,isObjectPatternList,Join.vector,Option.isNone_none,
            Bool.true_and,Bool.and_true,Bool.and_eq_true] at object
          exact object.2

#print axioms free_reference
#print axioms value_reference
#print axioms fact_values

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ValueDomain
