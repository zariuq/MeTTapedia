import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRSchemaAdmission
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRClausePremises

/-! Ordered positive outputs make source variables available before the
comparison inputs and conclusion. The existing premise-flow admission
therefore accepts every compiled clause of the prepared source program. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.FlowAdmission

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax GeneralRuleBindingInference
open Mettapedia.GSLT.LanguageDef.WellSorted

private theorem positive_schema (language : LanguageDef) (terms : language.terms = Query.baseLanguage.terms)
    (prepared : Executable.Prepared) (ordinal : Nat) (clause : Clause) (rule : RewriteRule)
    (compiled : Query.compileClause? prepared.vocabulary ordinal clause = some rule)
    (entry : Mettapedia.Languages.Datalog.Atom × Nat)
    (located : (Join.orderedBody clause)[entry.2]? = some (.atom entry.1))
    (code : Pattern) (formed : Join.atom? prepared.vocabulary entry.2 entry.1 = some code) :
    GeneralPremise.schemaValuesChecked language rule [] [code] [.base "DlStatement"] = true := by
  simp only [GeneralPremise.schemaValuesChecked,Bool.and_true]
  exact GeneralPremise.SchemaTyping.checkSchemaType_complete_of_object
    (SchemaAdmission.body_atom_typed language terms prepared.vocabulary ordinal clause rule compiled _ _ _ located formed)
    (vector_object (InstanceMatching.atom_shape prepared.vocabulary entry.2 entry.1 code formed))

theorem positive_flow (language : LanguageDef) (terms : language.terms = Query.baseLanguage.terms)
    (prepared : Executable.Prepared) (known : List Pattern) (ordinal : Nat) (clause : Clause) (rule : RewriteRule)
    (compiled : Query.compileClause? prepared.vocabulary ordinal clause = some rule)
    (entries : List (Mettapedia.Languages.Datalog.Atom × Nat)) (codes : List Syntax.Premise)
    (related : List.Forall₂ (fun entry premise => ∃ code,
      Join.atom? prepared.vocabulary entry.2 entry.1 = some code ∧
        premise = .relationQuery Query.factRelation [code]) entries codes)
    (located : ∀ entry ∈ entries, (Join.orderedBody clause)[entry.2]? = some (.atom entry.1))
    (available : List String) :
    let flow := GeneralPremise.premisesFlow language (Executable.snapshot prepared known).provider rule (inferredSpec rule) available codes
    flow.supported = true ∧ available ⊆ flow.available ∧
      (entries.flatMap fun entry => entry.1.variables).map Join.logicalVariable ⊆ flow.available := by
  induction related generalizing available with
  | nil => exact ⟨rfl,fun _ member => member,by simp⟩
  | @cons entry premise entries codes first rest ih =>
    obtain ⟨code,formed,rfl⟩ := first
    let next := (code.freeFvarNames ++ available).eraseDups
    have headFlow : GeneralPremise.premiseFlow language (Executable.snapshot prepared known).provider rule (inferredSpec rule)
        available (.relationQuery Query.factRelation [code]) = ⟨next,true⟩ := by
      simp [GeneralPremise.premiseFlow,SnapshotReading.fact_signature,
        GeneralPremise.queryOutputNames,GeneralPremise.queryInputNames,GeneralPremise.namesAvailable,
        positive_schema language terms prepared ordinal clause rule compiled entry (located entry List.mem_cons_self) code formed,next]
    have tail := ih (fun item member => located item (List.mem_cons_of_mem _ member)) next
    simp only [GeneralPremise.premisesFlow,headFlow,Bool.true_and]
    refine ⟨tail.1,?_,?_⟩
    · intro name member
      exact tail.2.1 (List.mem_eraseDups.mpr (List.mem_append_right _ member))
    · intro name member
      simp only [List.flatMap_cons,List.map_append,List.mem_append] at member
      rcases member with fromHead | fromTail
      · obtain ⟨sourceName,used,rfl⟩ := List.mem_map.mp fromHead
        exact tail.2.1 (List.mem_eraseDups.mpr (List.mem_append_left _
          (CompilationFlow.atom_provides prepared.vocabulary entry.2 entry.1 code formed sourceName used)))
      · exact tail.2.2 fromTail

private theorem guard_schema (language : LanguageDef) (prepared : Executable.Prepared) (ordinal : Nat)
    (clause : Clause) (rule : RewriteRule) (compiled : Query.compileClause? prepared.vocabulary ordinal clause = some rule)
    (guard : Comparison) (member : guard ∈ Comparisons.guards clause) (position : Nat) (left right : Pattern)
    (leftFormed : Join.argument? prepared.vocabulary position 0 guard.left = some left)
    (rightFormed : Join.argument? prepared.vocabulary position 1 guard.right = some right) :
    GeneralPremise.schemaValuesChecked language rule [] [left,right] [.base "DlValue",.base "DlValue"] = true := by
  have leftTyped := SchemaAdmission.guard_argument_typed language prepared.vocabulary ordinal clause rule compiled guard member
    position 0 guard.left (by simp [Comparison.arguments]) left leftFormed
  have rightTyped := SchemaAdmission.guard_argument_typed language prepared.vocabulary ordinal clause rule compiled guard member
    position 1 guard.right (by simp [Comparison.arguments]) right rightFormed
  obtain ⟨leftName,rfl⟩ := ClauseDictionary.argument_variable prepared.vocabulary position 0 guard.left left leftFormed
  obtain ⟨rightName,rfl⟩ := ClauseDictionary.argument_variable prepared.vocabulary position 1 guard.right right rightFormed
  simp only [GeneralPremise.schemaValuesChecked,Bool.and_true,Bool.and_eq_true]
  exact ⟨GeneralPremise.SchemaTyping.checkSchemaType_complete_of_object leftTyped rfl,
    GeneralPremise.SchemaTyping.checkSchemaType_complete_of_object rightTyped rfl⟩

theorem guard_flow (language : LanguageDef) (prepared : Executable.Prepared) (known : List Pattern)
    (ordinal : Nat) (clause : Clause) (rule : RewriteRule)
    (compiled : Query.compileClause? prepared.vocabulary ordinal clause = some rule)
    (entries : List (Comparison × Nat)) (codes : List Syntax.Premise)
    (related : List.Forall₂ (fun entry premise => ∃ left right,
      Join.argument? prepared.vocabulary entry.2 0 entry.1.left = some left ∧
      Join.argument? prepared.vocabulary entry.2 1 entry.1.right = some right ∧
      premise = .relationQuery (Join.comparisonName entry.1.operator) [left,right]) entries codes)
    (located : ∀ entry ∈ entries, entry.1 ∈ Comparisons.guards clause ∧ entry.1.operator ∈ Executable.operators prepared.source)
    (available : List String) (provided : BindingAdmission.sourceNames prepared.vocabulary clause ⊆ available) :
    let flow := GeneralPremise.premisesFlow language (Executable.snapshot prepared known).provider rule (inferredSpec rule) available codes
    flow.supported = true ∧ available ⊆ flow.available := by
  have restricted := (BodyCompilation.compiled_body prepared.vocabulary ordinal clause rule compiled).1
  induction related generalizing available with
  | nil => exact ⟨rfl,fun _ member => member⟩
  | @cons entry premise entries codes first rest ih =>
    obtain ⟨left,right,leftFormed,rightFormed,rfl⟩ := first
    have authored := located entry List.mem_cons_self
    have leftAvailable : left.freeFvarNames ⊆ available := fun _ member => provided
      (BindingAdmission.required_argument_names prepared.vocabulary clause restricted entry.2 0 entry.1.left
        (Comparisons.guard_arguments_required authored.1 (by simp [Comparison.arguments])) left leftFormed member)
    have rightAvailable : right.freeFvarNames ⊆ available := fun _ member => provided
      (BindingAdmission.required_argument_names prepared.vocabulary clause restricted entry.2 1 entry.1.right
        (Comparisons.guard_arguments_required authored.1 (by simp [Comparison.arguments])) right rightFormed member)
    have inputs : GeneralPremise.namesAvailable available
        (GeneralPremise.queryInputNames [left,right] [.input,.input]) = true := by
      apply List.all_eq_true.mpr
      intro name member
      simp only [GeneralPremise.queryInputNames,List.zip_cons_cons,List.zip_nil_left,List.flatMap_cons,
        List.flatMap_nil,List.append_nil,List.mem_append] at member
      exact List.contains_iff_mem.mpr (member.elim (fun present => leftAvailable present) (fun present => rightAvailable present))
    let next := available.eraseDups
    have headFlow : GeneralPremise.premiseFlow language (Executable.snapshot prepared known).provider rule (inferredSpec rule)
        available (.relationQuery (Join.comparisonName entry.1.operator) [left,right]) = ⟨next,true⟩ := by
      simp [GeneralPremise.premiseFlow,SnapshotReading.comparison_signature prepared known entry.1.operator authored.2,
        inputs,guard_schema language prepared ordinal clause rule compiled entry.1 authored.1 entry.2 left right leftFormed rightFormed,
        GeneralPremise.queryOutputNames,next]
    have tail := ih (fun item member => located item (List.mem_cons_of_mem _ member)) next
      (fun _ member => List.mem_eraseDups.mpr (provided member))
    simp only [GeneralPremise.premisesFlow,headFlow,Bool.true_and]
    exact ⟨tail.1,fun _ member => tail.2 (List.mem_eraseDups.mpr member)⟩

theorem clause_premises_admitted (language : LanguageDef) (terms : language.terms = Query.baseLanguage.terms)
    (prepared : Executable.Prepared) (known : List Pattern) (ordinal : Nat) (clause : Clause)
    (source : ProgramGrounding.ClauseAt prepared.source ordinal clause) (rule : RewriteRule)
    (compiled : Query.compileClause? prepared.vocabulary ordinal clause = some rule) :
    GeneralPremise.rulePremisesAdmitted language (Executable.snapshot prepared known).provider rule (inferredSpec rule) = true := by
  obtain ⟨restricted,positive,guards,positiveCompiled,guardsCompiled,body⟩ := ClausePremises.compiled_split prepared.vocabulary ordinal clause rule compiled
  have located : ∀ entry ∈ clause.positiveAtoms.zipIdx,
      (Join.orderedBody clause)[entry.2]? = some (.atom entry.1) := by
    intro entry member
    have selected := List.mk_mem_zipIdx_iff_getElem?.mp member
    have inside := (List.getElem?_eq_some_iff.mp selected).1
    rw [BodyCompilation.ordered_body,List.getElem?_append_left (by simpa using inside)]
    simp only [List.getElem?_map,selected,Option.map_some]
  have first := positive_flow language terms prepared known ordinal clause rule compiled _ _ positiveCompiled located rule.left.freeFvarNames
  let middle := (GeneralPremise.premisesFlow language (Executable.snapshot prepared known).provider rule (inferredSpec rule) rule.left.freeFvarNames positive).available
  have allNames : BindingAdmission.sourceNames prepared.vocabulary clause ⊆ middle := by
    intro name member
    rcases List.mem_append.mp member with pool | logical
    · apply first.2.1
      rw [(FiringReading.compiled_fields prepared.vocabulary ordinal clause rule compiled).1]
      simpa only [Join.poolPattern,Join.vector,Pattern.freeFvarNames,List.flatMap_cons,List.flatMap_nil,
        List.flatMap_map,Function.comp_def,List.flatMap_singleton',List.append_nil,Option.toList_none] using pool
    · have names : clause.positiveAtoms.zipIdx.flatMap (fun entry => entry.1.variables) = clause.providedVariables := by
        have same := congrArg (fun atoms : List Mettapedia.Languages.Datalog.Atom => atoms.flatMap (·.variables))
          (List.zipIdx_map_fst 0 clause.positiveAtoms)
        simpa only [List.flatMap_map,Function.comp_def,Clause.providedVariables] using same
      exact first.2.2 (by simpa only [names] using logical)
  have locatedGuards : ∀ entry ∈ (Comparisons.guards clause).zipIdx clause.positiveAtoms.length,
      entry.1 ∈ Comparisons.guards clause ∧ entry.1.operator ∈ Executable.operators prepared.source := by
    intro entry member
    have guardMember := List.fst_mem_of_mem_zipIdx member
    refine ⟨guardMember,?_⟩
    rcases source with atRule | ⟨fact,_,rfl⟩
    · exact Executable.source_guard_operator (List.mem_of_getElem? atRule) guardMember
    · simp [LPBridge.groundClause,Comparisons.guards] at guardMember
  have last := guard_flow language prepared known ordinal clause rule compiled _ _ guardsCompiled locatedGuards middle allNames
  unfold GeneralPremise.rulePremisesAdmitted
  rw [body,GeneralPremise.Static.raw_flow_append]
  simp only [Bool.and_eq_true]
  refine ⟨⟨first.1,last.1⟩,?_⟩
  apply List.all_eq_true.mpr
  intro name member
  exact List.contains_iff_mem.mpr (last.2 (allNames (BindingAdmission.head_names prepared.vocabulary clause restricted rule.right
    (FiringReading.compiled_fields prepared.vocabulary ordinal clause rule compiled).2 member)))

#print axioms positive_flow
#print axioms guard_flow
#print axioms clause_premises_admitted

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.FlowAdmission
