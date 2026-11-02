import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRRequestInstances
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRSourceQueries

/-! Actual compiled atom outputs bind the source variables they provide.
Range restriction then supplies every input guard and conclusion variable;
pool references are retained from the original request match. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.CompilationFlow

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax Match
open GeneralFirstOrderProjection

def PoolsBound (pools : Join.Pools) (assignment : ScopedRuleMatching.Assignment) : Prop :=
  GeneralPremise.BoundNames assignment (Join.relationSlots pools ++ Join.literalSlots pools)

def VariablesBound (names : List String) (assignment : ScopedRuleMatching.Assignment) : Prop :=
  GeneralPremise.BoundNames assignment (names.map Join.logicalVariable)

theorem mapM_relation {α β : Type} (compile : α → Option β)
    (inputs : List α) (outputs : List β) (compiled : inputs.mapM compile = some outputs) :
    List.Forall₂ (fun input output => compile input = some output) inputs outputs := by
  induction inputs generalizing outputs with
  | nil => cases compiled; exact .nil
  | cons head tail ih =>
    rw [List.mapM_cons] at compiled
    change ((compile head).bind fun first => (tail.mapM compile).bind fun rest => some (first :: rest)) = some outputs at compiled
    simp only [Option.bind_eq_some_iff,Option.some.injEq] at compiled
    obtain ⟨first,headRead,rest,tailRead,rfl⟩ := compiled
    exact .cons headRead (ih rest tailRead)

private theorem arguments_provide (pools : Join.Pools) (position : Nat)
    (entries : List (Argument × Nat)) (codes : List Pattern)
    (compiled : List.Forall₂ (fun entry code => Join.argument? pools position entry.2 entry.1 = some code) entries codes) :
    ∀ name ∈ entries.flatMap (fun entry => entry.1.vars),
      Join.logicalVariable name ∈ codes.flatMap Pattern.freeFvarNames := by
  induction compiled with
  | nil => simp
  | @cons entry code entries codes first rest ih =>
    intro name member
    rcases List.mem_append.mp member with firstName | later
    · rcases entry with ⟨argument,index⟩
      cases argument with
      | literal _ => cases firstName
      | anonymous => cases firstName
      | var actual =>
        have same : name = actual := by simpa [Argument.vars] using firstName
        subst actual
        have codeSame : Pattern.fvar (Join.logicalVariable name) = code := Option.some.inj first
        rw [← codeSame]
        exact List.mem_append_left _ (by simp [Pattern.freeFvarNames])
    · exact List.mem_append_right _ (ih name later)

theorem atom_provides (pools : Join.Pools) (position : Nat) (source : Mettapedia.Languages.Datalog.Atom)
    (code : Pattern) (compiled : Join.atom? pools position source = some code) :
    ∀ name ∈ source.variables, Join.logicalVariable name ∈ code.freeFvarNames := by
  change ((Join.relation? pools source.relation).bind fun relation =>
    (source.arguments.zipIdx.mapM fun entry => Join.argument? pools position entry.2 entry.1).bind fun arguments =>
      some (Pattern.apply "GroundFact" [relation,.apply "GroundTuple" [Join.vector arguments]])) = some code at compiled
  simp only [Option.bind_eq_some_iff,Option.some.injEq] at compiled
  obtain ⟨relation,_,arguments,argsCompiled,rfl⟩ := compiled
  have provided := arguments_provide pools position source.arguments.zipIdx arguments
    (mapM_relation _ _ _ argsCompiled)
  intro name member
  have sourceNames : name ∈ source.arguments.zipIdx.flatMap (fun entry => entry.1.vars) := by
    obtain ⟨argument,present,used⟩ := List.mem_flatMap.mp member
    obtain ⟨index,atArgument⟩ := List.mem_iff_getElem?.mp present
    exact List.mem_flatMap.mpr ⟨(argument,index),List.mk_mem_zipIdx_iff_getElem?.mpr atArgument,used⟩
  have actual := provided name sourceNames
  simp only [Pattern.freeFvarNames,List.flatMap_cons,List.flatMap_nil,List.append_nil,Join.vector,Option.toList_none] at *
  exact List.mem_append_right _ actual

theorem output_variables (pools : Join.Pools) (position : Nat) (source : Mettapedia.Languages.Datalog.Atom)
    (code : Pattern) (compiled : Join.atom? pools position source = some code)
    (assignment : ScopedRuleMatching.Assignment) (bound : GeneralPremise.BoundNames assignment code.freeFvarNames) :
    VariablesBound source.variables assignment := by
  intro slot member
  obtain ⟨name,used,rfl⟩ := List.mem_map.mp member
  exact bound _ (atom_provides pools position source code compiled name used)

theorem request_pools (pools : Join.Pools) (assignment : ScopedRuleMatching.Assignment)
    (bound : GeneralPremise.BoundNames assignment (RequestInstances.schema pools).freeFvarNames) :
    PoolsBound pools assignment := by
  simpa only [PoolsBound,RequestInstances.schema,Join.poolPattern,Join.vector,Pattern.freeFvarNames,
    List.flatMap_cons,List.flatMap_nil,List.flatMap_map,Function.comp_def,List.flatMap_singleton',
    Option.toList_none,List.append_nil] using bound

theorem argument_bound (pools : Join.Pools) (position index : Nat) (argument : Argument)
    (code : Pattern) (compiled : Join.argument? pools position index argument = some code)
    (named : argument ≠ .anonymous) (assignment : ScopedRuleMatching.Assignment)
    (poolsBound : PoolsBound pools assignment) (variablesBound : VariablesBound argument.vars assignment) :
    GeneralPremise.BoundNames assignment code.freeFvarNames := by
  cases argument with
  | anonymous => exact (named rfl).elim
  | var name =>
    have same : Pattern.fvar (Join.logicalVariable name) = code := Option.some.inj compiled
    rw [← same]
    simpa only [VariablesBound,Argument.vars,List.map_cons,List.map_nil,Pattern.freeFvarNames] using variablesBound
  | literal value =>
    cases found : pools.literals.idxOf? value with
    | none => simp [Join.argument?,Join.literal?,found] at compiled
    | some slot =>
      have same : Pattern.fvar (Join.literalSlot slot) = code := by simpa [Join.argument?,Join.literal?,found] using compiled
      rw [← same]
      intro name member
      simp only [Pattern.freeFvarNames] at member
      cases List.mem_singleton.mp member
      exact poolsBound _ (List.mem_append_right _ (List.mem_map.mpr
        ⟨slot,List.mem_range.mpr (List.idxOf?_eq_some_iff.mp found).1,rfl⟩))

theorem guard_bound (pools : Join.Pools) (clause : Clause) (restricted : clause.RangeRestricted)
    (comparison : Comparison) (inClause : comparison ∈ Comparisons.guards clause)
    (position index : Nat) (argument : Argument) (inside : argument ∈ comparison.arguments)
    (code : Pattern) (compiled : Join.argument? pools position index argument = some code)
    (assignment : ScopedRuleMatching.Assignment) (poolsBound : PoolsBound pools assignment)
    (variablesBound : VariablesBound clause.providedVariables assignment) :
    GeneralPremise.BoundNames assignment code.freeFvarNames := by
  have required := Comparisons.guard_arguments_required inClause inside
  apply argument_bound pools position index argument code compiled (restricted.1 argument required) assignment poolsBound
  intro slot member
  obtain ⟨name,used,rfl⟩ := List.mem_map.mp member
  exact variablesBound _ (List.mem_map.mpr ⟨name,restricted.2 name (List.mem_flatMap.mpr ⟨argument,required,used⟩),rfl⟩)

private theorem arguments_bound (pools : Join.Pools) (position : Nat)
    (entries : List (Argument × Nat)) (codes : List Pattern)
    (compiled : List.Forall₂ (fun entry code => Join.argument? pools position entry.2 entry.1 = some code) entries codes)
    (named : ∀ entry ∈ entries, entry.1 ≠ .anonymous)
    (assignment : ScopedRuleMatching.Assignment) (poolsBound : PoolsBound pools assignment)
    (variablesBound : VariablesBound (entries.flatMap (fun entry => entry.1.vars)) assignment) :
    GeneralPremise.BoundNames assignment (codes.flatMap Pattern.freeFvarNames) := by
  induction compiled with
  | nil => intro name member; cases member
  | @cons entry code entries codes first rest ih =>
    have firstVars : VariablesBound entry.1.vars assignment := by
      intro slot member
      obtain ⟨name,used,rfl⟩ := List.mem_map.mp member
      exact variablesBound _ (List.mem_map.mpr ⟨name,List.mem_append_left _ used,rfl⟩)
    have tailVars : VariablesBound (entries.flatMap (fun item => item.1.vars)) assignment := by
      intro slot member
      obtain ⟨name,used,rfl⟩ := List.mem_map.mp member
      exact variablesBound _ (List.mem_map.mpr ⟨name,List.mem_append_right _ used,rfl⟩)
    exact (argument_bound pools position entry.2 entry.1 code first (named entry List.mem_cons_self)
      assignment poolsBound firstVars).append
      (ih (fun other member => named other (List.mem_cons_of_mem _ member)) tailVars)

theorem atom_bound (pools : Join.Pools) (position : Nat) (source : Mettapedia.Languages.Datalog.Atom)
    (code : Pattern) (compiled : Join.atom? pools position source = some code)
    (named : ∀ argument ∈ source.arguments, argument ≠ .anonymous)
    (assignment : ScopedRuleMatching.Assignment) (poolsBound : PoolsBound pools assignment)
    (variablesBound : VariablesBound source.variables assignment) :
    GeneralPremise.BoundNames assignment code.freeFvarNames := by
  change ((Join.relation? pools source.relation).bind fun relation =>
    (source.arguments.zipIdx.mapM fun entry => Join.argument? pools position entry.2 entry.1).bind fun arguments =>
      some (Pattern.apply "GroundFact" [relation,.apply "GroundTuple" [Join.vector arguments]])) = some code at compiled
  simp only [Option.bind_eq_some_iff,Option.some.injEq] at compiled
  obtain ⟨relation,relationCompiled,arguments,argsCompiled,rfl⟩ := compiled
  have relationBound : GeneralPremise.BoundNames assignment relation.freeFvarNames := by
    cases found : pools.relations.idxOf? source.relation with
    | none => simp [Join.relation?,found] at relationCompiled
    | some index =>
      have same : Pattern.fvar (Join.relationSlot index) = relation := by simpa [Join.relation?,found] using relationCompiled
      rw [← same]
      intro name member
      simp only [Pattern.freeFvarNames] at member
      cases List.mem_singleton.mp member
      exact poolsBound _ (List.mem_append_left _ (List.mem_map.mpr
        ⟨index,List.mem_range.mpr (List.idxOf?_eq_some_iff.mp found).1,rfl⟩))
  have variableNames : (source.arguments.zipIdx.flatMap fun entry => entry.1.vars) = source.variables := by
    have mapped := congrArg (fun arguments : List Argument => arguments.flatMap Argument.vars)
      (List.zipIdx_map_fst 0 source.arguments)
    simpa only [List.flatMap_map,Function.comp_def,Atom.variables] using mapped
  have argumentBound := arguments_bound pools position source.arguments.zipIdx arguments (mapM_relation _ _ _ argsCompiled)
    (fun entry member => named entry.1 (List.fst_mem_of_mem_zipIdx member)) assignment poolsBound (variableNames ▸ variablesBound)
  simpa only [Pattern.freeFvarNames,List.flatMap_cons,List.flatMap_nil,List.append_nil,Join.vector,Option.toList_none] using
    relationBound.append argumentBound

theorem head_bound (pools : Join.Pools) (clause : Clause) (restricted : clause.RangeRestricted)
    (code : Pattern) (compiled : Join.atom? pools clause.body.length clause.head = some code)
    (assignment : ScopedRuleMatching.Assignment) (poolsBound : PoolsBound pools assignment)
    (variablesBound : VariablesBound clause.providedVariables assignment) :
    GeneralPremise.BoundNames assignment code.freeFvarNames := by
  apply atom_bound pools clause.body.length clause.head code compiled
    (fun argument member => restricted.1 argument (List.mem_append_left _ member)) assignment poolsBound
  intro slot member
  obtain ⟨name,used,rfl⟩ := List.mem_map.mp member
  have required : name ∈ clause.requiredVariables := by
    obtain ⟨argument,member,inArgument⟩ := List.mem_flatMap.mp used
    exact List.mem_flatMap.mpr ⟨argument,List.mem_append_left _ member,inArgument⟩
  exact variablesBound _ (List.mem_map.mpr ⟨name,restricted.2 name required,rfl⟩)

#print axioms atom_provides
#print axioms output_variables
#print axioms request_pools
#print axioms argument_bound
#print axioms guard_bound
#print axioms atom_bound
#print axioms head_bound

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.CompilationFlow
