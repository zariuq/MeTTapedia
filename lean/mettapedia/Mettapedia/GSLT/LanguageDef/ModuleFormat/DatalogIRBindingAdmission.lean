import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRBindingUniqueness
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRCompilationFlow
import Mettapedia.OSLF.MeTTaIL.GeneralVectorBindingAdmission

/-! The existing binding inference accepts every successfully compiled
positive clause. Declaration coverage follows from pool bounds and source
range restriction, rather than from an assumed admission result. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.BindingAdmission

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding GeneralRuleBindingInference
open GeneralFirstOrderProjection

private theorem lookup_any (context : List (String × TypeExpr)) (name : String) (type : TypeExpr)
    (found : context.lookup name = some type) : context.any (fun entry => entry.1 == name) = true := by
  obtain ⟨entry,member,same⟩ := List.lookup_isSome_iff.mp (show (context.lookup name).isSome = true by rw [found]; rfl)
  exact List.any_eq_true.mpr ⟨entry,member,by simpa only [beq_iff_eq] using (beq_iff_eq.mp same).symm⟩

private theorem related_member {α β : Type} {relation : α → β → Prop} {inputs : List α} {outputs : List β}
    (related : List.Forall₂ relation inputs outputs) (value : β) (member : value ∈ outputs) :
    ∃ input ∈ inputs, relation input value := by
  induction related with
  | nil => cases member
  | @cons input output inputs outputs first rest ih =>
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨input,List.mem_cons_self,first⟩
    · obtain ⟨source,present,holds⟩ := ih later
      exact ⟨source,List.mem_cons_of_mem _ present,holds⟩

def sourceNames (pools : Join.Pools) (clause : Clause) : List String :=
  Join.relationSlots pools ++ Join.literalSlots pools ++ clause.providedVariables.map Join.logicalVariable

theorem required_argument_names (pools : Join.Pools) (clause : Clause) (restricted : clause.RangeRestricted)
    (position index : Nat) (argument : Argument) (required : argument ∈ clause.requiredArguments)
    (code : Pattern) (compiled : Join.argument? pools position index argument = some code) :
    code.freeFvarNames ⊆ sourceNames pools clause := by
  cases argument with
  | anonymous => exact (restricted.1 _ required rfl).elim
  | var variableName =>
    have same : Pattern.fvar (Join.logicalVariable variableName) = code := Option.some.inj compiled
    subst code
    intro name member
    simp only [Pattern.freeFvarNames] at member
    cases List.mem_singleton.mp member
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨variableName,
      restricted.2 variableName (List.mem_flatMap.mpr ⟨.var variableName,required,by simp [Argument.vars]⟩),rfl⟩
  | literal value =>
    obtain ⟨slot,selected,rfl⟩ := Option.map_eq_some_iff.mp compiled
    intro name member
    simp only [Pattern.freeFvarNames] at member
    cases List.mem_singleton.mp member
    apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨slot,List.mem_range.mpr (List.idxOf?_eq_some_iff.mp selected).1,rfl⟩

theorem head_names (pools : Join.Pools) (clause : Clause) (restricted : clause.RangeRestricted)
    (code : Pattern) (compiled : Join.atom? pools clause.body.length clause.head = some code) :
    code.freeFvarNames ⊆ sourceNames pools clause := by
  change ((Join.relation? pools clause.head.relation).bind fun relation =>
    (clause.head.arguments.zipIdx.mapM fun entry => Join.argument? pools clause.body.length entry.2 entry.1).bind fun arguments =>
      some (Pattern.apply "GroundFact" [relation,.apply "GroundTuple" [Join.vector arguments]])) = some code at compiled
  simp only [Option.bind_eq_some_iff,Option.some.injEq] at compiled
  obtain ⟨relation,named,arguments,argsCompiled,rfl⟩ := compiled
  obtain ⟨slot,selected,rfl⟩ := Option.map_eq_some_iff.mp named
  intro name member
  simp only [Pattern.freeFvarNames,Join.vector,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    Option.toList_none,List.mem_append,List.mem_singleton] at member
  rcases member with relationName | argumentName
  · subst name
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨slot,List.mem_range.mpr (List.idxOf?_eq_some_iff.mp selected).1,rfl⟩
  · obtain ⟨argumentCode,atCode,used⟩ := List.mem_flatMap.mp argumentName
    have related := CompilationFlow.mapM_relation _ _ _ argsCompiled
    obtain ⟨entry,atEntry,formed⟩ := related_member related argumentCode atCode
    exact required_argument_names pools clause restricted _ _ entry.1
      (List.mem_append_left _ (List.fst_mem_of_mem_zipIdx atEntry)) argumentCode formed used

theorem source_name_declared (pools : Join.Pools) (clause : Clause) (name : String)
    (member : name ∈ sourceNames pools clause) :
    (BindingContext.context pools clause).any (fun entry => entry.1 == name) = true := by
  rcases List.mem_append.mp member with pool | logical
  · rcases List.mem_append.mp pool with relation | literal
    · obtain ⟨index,inside,rfl⟩ := List.mem_map.mp relation
      exact lookup_any _ _ _ (BindingContext.relation_declared pools clause index (List.mem_range.mp inside))
    · obtain ⟨index,inside,rfl⟩ := List.mem_map.mp literal
      exact lookup_any _ _ _ (BindingContext.literal_declared pools clause index (List.mem_range.mp inside))
  · obtain ⟨variableName,provided,rfl⟩ := List.mem_map.mp logical
    exact lookup_any _ _ _ (BindingContext.logical_declared pools clause variableName provided)

theorem head_declared (pools : Join.Pools) (clause : Clause) (restricted : clause.RangeRestricted)
    (code : Pattern) (compiled : Join.atom? pools clause.body.length clause.head = some code) :
    ∀ name ∈ code.freeFvarNames,
      (BindingContext.context pools clause).any (fun entry => entry.1 == name) = true := by
  intro name member
  exact source_name_declared pools clause name (head_names pools clause restricted code compiled member)

theorem root_declared (pools : Join.Pools) (ordinal : Nat) (clause : Clause) (rule : RewriteRule)
    (compiled : Query.compileClause? pools ordinal clause = some rule) : rootDeclared rule = true := by
  obtain ⟨left,right⟩ := FiringReading.compiled_fields pools ordinal clause rule compiled
  have restricted := (BodyCompilation.compiled_body pools ordinal clause rule compiled).1
  unfold rootDeclared
  apply List.all_eq_true.mpr
  intro name member
  rw [BindingContext.compiled_context pools ordinal clause rule compiled]
  rcases List.mem_append.mp member with fromLeft | fromRight
  · rw [left] at fromLeft
    have poolsMember : name ∈ Join.relationSlots pools ∨ name ∈ Join.literalSlots pools := by
      simpa only [Join.poolPattern,Join.vector,Pattern.freeFvarNames,List.flatMap_cons,List.flatMap_nil,
        List.flatMap_map,Function.comp_def,List.flatMap_singleton',List.append_nil,Option.toList_none,List.mem_append] using fromLeft
    rcases poolsMember with relation | literal
    · obtain ⟨index,inside,rfl⟩ := List.mem_map.mp relation
      exact lookup_any _ _ _ (BindingContext.relation_declared pools clause index (List.mem_range.mp inside))
    · obtain ⟨index,inside,rfl⟩ := List.mem_map.mp literal
      exact lookup_any _ _ _ (BindingContext.literal_declared pools clause index (List.mem_range.mp inside))
  · exact head_declared pools clause restricted rule.right right name fromRight

theorem compiled_binding_none (pools : Join.Pools) (ordinal : Nat) (clause : Clause) (rule : RewriteRule)
    (compiled : Query.compileClause? pools ordinal clause = some rule) : rule.bindings = none := by
  obtain ⟨original,formed,rfl⟩ := Option.map_eq_some_iff.mp compiled
  unfold Join.compileClause? at formed
  split at formed
  · cases formed
  · simp only [Option.bind_eq_bind,Option.bind_eq_some_iff] at formed
    obtain ⟨_,_,_,_,same⟩ := formed
    cases Option.some.inj same
    rfl

theorem compile_binding (language : LanguageDef) (pools : Join.Pools) (ordinal : Nat) (clause : Clause) (rule : RewriteRule)
    (compiled : Query.compileClause? pools ordinal clause = some rule) :
    compile? language rule = some ⟨inferredSpec rule,.inferredRootInputs⟩ := by
  have left := (FiringReading.compiled_fields pools ordinal clause rule compiled).1
  have root : rootInput 0 rule.left = true := by
    rw [left]
    exact vector_root (RequestInstances.request_shape pools)
  exact compile_root_inputs language rule (compiled_binding_none pools ordinal clause rule compiled) root
    (root_declared pools ordinal clause rule compiled)
    (BindingContext.compiled_context_nodup pools ordinal clause rule compiled)

#print axioms root_declared
#print axioms compile_binding

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.BindingAdmission
