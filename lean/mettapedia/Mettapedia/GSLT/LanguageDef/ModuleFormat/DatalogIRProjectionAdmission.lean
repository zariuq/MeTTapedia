import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRFlowAdmission

/-! Compiled premise indices retain their source-body positions. These
positions and schema types discharge the existing static projection checks,
including the ordered whole-rule premise checker. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ProjectionAdmission

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax GeneralRuleBindingInference
open GeneralFirstOrderProjection

theorem premise_origin (pools : Join.Pools) (ordinal : Nat) (clause : Clause) (rule : RewriteRule)
    (compiled : Query.compileClause? pools ordinal clause = some rule)
    (index : Nat) (premise : Syntax.Premise) (selected : rule.premises[index]? = some premise) :
    ∃ source raw, (Join.orderedBody clause)[index]? = some source ∧
      Join.bodyPremise? pools index source = some raw ∧ Query.lowerPremise raw = premise := by
  obtain ⟨_,original,formed,body⟩ := BodyCompilation.compiled_body pools ordinal clause rule compiled
  rw [body,List.getElem?_map] at selected
  obtain ⟨raw,rawAt,same⟩ := Option.map_eq_some_iff.mp selected
  have related := CompilationFlow.mapM_relation _ _ _ formed
  have rawInside := (List.getElem?_eq_some_iff.mp rawAt).1
  have entryInside : index < (Join.orderedBody clause).zipIdx.length := by
    rw [related.length_eq]
    exact rawInside
  have sourceInside : index < (Join.orderedBody clause).length := by simpa only [List.length_zipIdx] using entryInside
  refine ⟨(Join.orderedBody clause)[index],raw,List.getElem?_eq_getElem sourceInside,?_,same⟩
  have actual := related.get entryInside rawInside
  simpa only [List.get_eq_getElem,List.getElem_zipIdx,Nat.zero_add,(List.getElem?_eq_some_iff.mp rawAt).2] using actual

theorem rule_queries (pools : Join.Pools) (ordinal : Nat) (clause : Clause) (rule : RewriteRule)
    (compiled : Query.compileClause? pools ordinal clause = some rule) :
    ∀ premise ∈ rule.premises, ∃ relation arguments, premise = .relationQuery relation arguments := by
  intro premise member
  obtain ⟨index,selected⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨source,raw,_,formed,lowered⟩ := premise_origin pools ordinal clause rule compiled index premise selected
  cases source with
  | atom atom =>
    obtain ⟨code,_,same⟩ := BodyCompilation.atom_premise pools index atom raw formed
    exact ⟨Query.factRelation,[code],lowered.symm.trans same⟩
  | comparison guard =>
    obtain ⟨left,right,_,_,same⟩ := BodyCompilation.guard_premise pools index guard raw formed
    exact ⟨Join.comparisonName guard.operator,[left,right],lowered.symm.trans same⟩

theorem query_schema_typed (language : LanguageDef) (terms : language.terms = Query.baseLanguage.terms)
    (pools : Join.Pools) (ordinal : Nat) (clause : Clause) (rule : RewriteRule)
    (compiled : Query.compileClause? pools ordinal clause = some rule)
    (index : Nat) (relation : String) (arguments : List Pattern)
    (selected : rule.premises[index]? = some (.relationQuery relation arguments))
    (argumentIndex : Nat) (code : Pattern) (atArgument : arguments[argumentIndex]? = some code) :
    VectorFirstOrder code ∧ ∃ type, Mettapedia.GSLT.LanguageDef.WellSorted.HasType language
      (GeneralPremise.lookupRuleType? rule) [] code type := by
  obtain ⟨source,raw,atSource,formed,lowered⟩ := premise_origin pools ordinal clause rule compiled index (.relationQuery relation arguments) selected
  cases source with
  | atom atom =>
    obtain ⟨target,targetFormed,same⟩ := BodyCompilation.atom_premise pools index atom raw formed
    have sameQuery := Syntax.Premise.relationQuery.inj (same.symm.trans lowered)
    obtain ⟨rfl,rfl⟩ := sameQuery
    have codeSame : code = target := by
      cases argumentIndex with
      | zero => exact (Option.some.inj atArgument).symm
      | succ _ => cases atArgument
    subst code
    exact ⟨InstanceMatching.atom_shape pools index atom target targetFormed,.base "DlStatement",
      SchemaAdmission.body_atom_typed language terms pools ordinal clause rule compiled index atom target atSource targetFormed⟩
  | comparison guard =>
    obtain ⟨left,right,leftFormed,rightFormed,same⟩ := BodyCompilation.guard_premise pools index guard raw formed
    have sameQuery := Syntax.Premise.relationQuery.inj (same.symm.trans lowered)
    obtain ⟨rfl,rfl⟩ := sameQuery
    have inClause := (BodyCompilation.ordered_guard clause guard).mp (List.mem_of_getElem? atSource)
    cases argumentIndex with
    | zero =>
      cases Option.some.inj atArgument
      obtain ⟨name,rfl⟩ := ClauseDictionary.argument_variable pools index 0 guard.left _ leftFormed
      exact ⟨.metavariable name,.base "DlValue",
        SchemaAdmission.guard_argument_typed language pools ordinal clause rule compiled guard inClause index 0 guard.left
          (by simp [Comparison.arguments]) _ leftFormed⟩
    | succ other =>
      cases other with
      | zero =>
        cases Option.some.inj atArgument
        obtain ⟨name,rfl⟩ := ClauseDictionary.argument_variable pools index 1 guard.right _ rightFormed
        exact ⟨.metavariable name,.base "DlValue",
          SchemaAdmission.guard_argument_typed language pools ordinal clause rule compiled guard inClause index 1 guard.right
            (by simp [Comparison.arguments]) _ rightFormed⟩
      | succ _ => cases atArgument

theorem query_projection (language : LanguageDef) (terms : language.terms = Query.baseLanguage.terms)
    (pools : Join.Pools) (ordinal : Nat) (clause : Clause) (rule : RewriteRule)
    (compiled : Query.compileClause? pools ordinal clause = some rule)
    (index : Nat) (relation : String) (arguments : List Pattern)
    (selected : rule.premises[index]? = some (.relationQuery relation arguments))
    (argumentIndex : Nat) (code : Pattern) (atArgument : arguments[argumentIndex]? = some code) :
    GeneralPremise.checkRootProjectionSchema rule (inferredSpec rule) (.premise index 0 argumentIndex) [] code = true := by
  obtain ⟨shape,type,typed⟩ := query_schema_typed language terms pools ordinal clause rule compiled index relation arguments selected argumentIndex code atArgument
  exact GeneralPremise.Static.vector_projection_of_typed
    (BindingContext.compiled_context_nodup pools ordinal clause rule compiled) shape
    (GeneralPremise.Static.query_argument_coherent rule index relation arguments selected argumentIndex code atArgument) typed

theorem rule_static (language : LanguageDef) (terms : language.terms = Query.baseLanguage.terms)
    (prepared : Executable.Prepared) (known : List Pattern) (ordinal : Nat) (clause : Clause)
    (source : ProgramGrounding.ClauseAt prepared.source ordinal clause) (rule : RewriteRule)
    (compiled : Query.compileClause? prepared.vocabulary ordinal clause = some rule) :
    GeneralPremise.Static.checkRule language (Executable.snapshot prepared known).provider rule (inferredSpec rule) = true := by
  have raw := FlowAdmission.clause_premises_admitted language terms prepared known ordinal clause source rule compiled
  have parts := Bool.and_eq_true_iff.mp raw
  have transported := GeneralPremise.Static.queryFlow_of_projection language (Executable.snapshot prepared known).provider rule (inferredSpec rule)
    rule.premises 0 rule.left.freeFvarNames (GeneralPremise.Static.initialRefinement rule)
    (fun _ member => member) (rule_queries prepared.vocabulary ordinal clause rule compiled)
    (by
      intro offset relation arguments selected argumentIndex code atArgument
      simpa only [Nat.zero_add] using
        query_projection language terms prepared.vocabulary ordinal clause rule compiled offset relation arguments selected argumentIndex code atArgument)
    parts.1
  have headAvailable := GeneralPremise.Static.namesAvailable_mono transported.2 parts.2
  have zero : GeneralPremise.checkZeroDependencies (inferredSpec rule) = true := by
    simp [GeneralPremise.checkZeroDependencies,inferredSpec]
  simp only [GeneralPremise.Static.checkRule,zero,transported.1,
    SchemaAdmission.head_projection language terms prepared.vocabulary ordinal clause rule compiled,
    headAvailable,Bool.and_self]

#print axioms premise_origin
#print axioms query_projection
#print axioms rule_static

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ProjectionAdmission
