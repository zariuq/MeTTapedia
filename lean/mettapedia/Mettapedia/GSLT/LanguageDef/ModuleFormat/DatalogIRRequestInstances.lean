import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRPhysicalInstances

/-! The actual InferSnapshot request is an instance of the compiled left
schema under the same substitution used by every source body atom. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.RequestInstances

open Mettapedia.OSLF.MeTTaIL Syntax Match MatchSpec RuleBinding
open GeneralFirstOrderProjection

def schema (pools : Join.Pools) : Pattern := .apply "InferSnapshot"
  [Join.poolPattern (Join.relationSlots pools),Join.poolPattern (Join.literalSlots pools)]

private theorem vector_shape (names : List String) : VectorFirstOrder (Join.poolPattern names) := by
  apply VectorFirstOrder.vector
  intro value member
  obtain ⟨name,_,rfl⟩ := List.mem_map.mp member
  exact .metavariable name

theorem request_shape (pools : Join.Pools) : VectorFirstOrder (schema pools) := by
  apply VectorFirstOrder.constructor
  intro child member
  rcases List.mem_cons.mp member with rfl | member
  · exact vector_shape _
  · cases List.mem_singleton.mp member
    exact vector_shape _

theorem request_instance (pools : Join.Pools) (bindings : Bindings) (read : PhysicalInstances.PoolBindings pools bindings) :
    applyBindings bindings (schema pools) = Executable.request pools := by
  have relations : ((Join.relationSlots pools).map Pattern.fvar).map (applyBindings bindings) =
      (List.range pools.relations.length).map Executable.relationRef := by
    simp only [Join.relationSlots,List.map_map,Function.comp_def]
    apply List.map_congr_left
    intro index member
    rw [apply_variable,read.relations index (List.mem_range.mp member)]
    rfl
  have literals : ((Join.literalSlots pools).map Pattern.fvar).map (applyBindings bindings) =
      (List.range pools.literals.length).map Executable.valueRef := by
    simp only [Join.literalSlots,List.map_map,Function.comp_def]
    apply List.map_congr_left
    intro index member
    rw [apply_variable,read.literals index (List.mem_range.mp member)]
    rfl
  simp only [schema,Executable.request,Query.call,Join.poolPattern,Join.vector,
    applyBindings,List.map_cons,List.map_nil,List.append_nil,relations,literals]

theorem request_defined (pools : Join.Pools) (bindings : Bindings) (read : PhysicalInstances.PoolBindings pools bindings) :
    Defined bindings (schema pools).freeFvarNames := by
  intro name member
  have names : name ∈ Join.relationSlots pools ∨ name ∈ Join.literalSlots pools := by
    simpa only [schema,Join.poolPattern,Join.vector,Pattern.freeFvarNames,List.flatMap_cons,List.flatMap_nil,
      List.flatMap_map,Function.comp_def,List.flatMap_singleton',List.append_nil,Option.toList_none,List.mem_append] using member
  rcases names with relation | literal
  · obtain ⟨index,atRange,rfl⟩ := List.mem_map.mp relation
    exact ⟨Executable.relationRef index,read.relations index (List.mem_range.mp atRange)⟩
  · obtain ⟨index,atRange,rfl⟩ := List.mem_map.mp literal
    exact ⟨Executable.valueRef index,read.literals index (List.mem_range.mp atRange)⟩

theorem request_scoped_witness (pools : Join.Pools) (bindings : Bindings) (read : PhysicalInstances.PoolBindings pools bindings)
    (rule : RewriteRule) (spec : RuleBindingSpec) (left : rule.left = schema pools)
    (admitted : admittedFor rule spec = true)
    (declared : ∀ name ∈ (schema pools).freeFvarNames, dependencies? spec name = some [])
    (scope : (Executable.request pools).isWellScopedAt 0 = true)
    (object : Mettapedia.GSLT.LanguageDef.WellSorted.isObjectPattern (Executable.request pools) = true) :
    ∃ captured, GeneralScopedMatch.Matches rule spec 0 .left [] 0 [] rule.left (Executable.request pools) captured ∧
      ScopedCompatible 0 bindings captured := by
  obtain ⟨raw,matched,compatible,_,_⟩ := vector_match_instance bindings (request_shape pools) (request_defined pools bindings read)
  rw [request_instance pools bindings read] at matched
  have named_free (names : List String) : binderFreeList (names.map Pattern.fvar) = true := by
    induction names with
    | nil => rfl
    | cons _ _ ih => simpa only [List.map_cons,binderFreeList,binderFree,Bool.true_and] using ih
  have free : binderFree (schema pools) = true := by
    simp only [schema,Join.poolPattern,Join.vector,binderFree,binderFreeList,named_free,Bool.true_and]
  have coherent : NameCoherent rule .left [] (schema pools) := by rw [← left]; exact .left rule
  obtain ⟨captured,matching,compatible⟩ := binderFree_scoped_of_matchRel_admitted (initial := []) admitted free coherent declared matched compatible scope object
    (by intro entry member; cases member)
  exact ⟨captured,by simpa only [left] using matching,compatible⟩

#print axioms request_shape
#print axioms request_instance
#print axioms request_defined
#print axioms request_scoped_witness

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.RequestInstances
