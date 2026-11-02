import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRValueDomain
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRPhysicalInstances
import Mathlib.Data.List.Nodup

/-! Sorted physical fact payloads have a canonical source encoding. The
prepared literal pool has no duplicates, so a registered reference denotes
the same index chosen by the ordinary source encoder. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.PhysicalCanonical

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax Match
open Mettapedia.GSLT.LanguageDef.WellSorted

private theorem index_encodes {α : Type} [BEq α] [LawfulBEq α] (items : List α)
    (distinct : items.Nodup) (index : Nat) (inside : index < items.length) :
    items.idxOf? items[index] = some index := by
  apply List.idxOf?_eq_some_iff.mpr
  refine ⟨inside,rfl,?_⟩
  intro other earlier same
  have equal : other = index := distinct.getElem_inj_iff.mp same
  omega

theorem values_encode (pools : Join.Pools) (distinct : pools.literals.Nodup) (codes : List Pattern)
    (references : ∀ code ∈ codes, ∃ index, index < pools.literals.length ∧ code = Executable.valueRef index) :
    ∃ values : List Value, values.mapM (PhysicalInstances.value? pools) = some codes := by
  induction codes with
  | nil => exact ⟨[],rfl⟩
  | cons code codes ih =>
    obtain ⟨index,inside,rfl⟩ := references code List.mem_cons_self
    obtain ⟨values,encoded⟩ := ih (fun other member => references other (List.mem_cons_of_mem _ member))
    refine ⟨pools.literals[index] :: values,?_⟩
    simp only [List.mapM_cons,PhysicalInstances.value?,index_encodes pools.literals distinct index inside]
    change (values.mapM (PhysicalInstances.value? pools)).bind (fun remaining => some (Executable.valueRef index :: remaining)) = _
    rw [encoded]
    rfl

theorem fact_encodes (language : LanguageDef) (terms : language.terms = Query.baseLanguage.terms)
    (pools : Join.Pools) (distinct : pools.literals.Nodup) (relation : QualifiedName) (index : Nat)
    (atRelation : pools.relations.idxOf? relation = some index) (codes : List Pattern)
    (typed : OpenPatternWellSorted language (FreeTypeContext.ofList (Executable.freeTypes pools)) [] (.base "DlStatement")
      (.apply "GroundFact" [Executable.relationRef index,.apply "GroundTuple" [Join.vector codes]])) :
    ∃ fact : GroundFact, Executable.fact? pools fact =
      some (.apply "GroundFact" [Executable.relationRef index,.apply "GroundTuple" [Join.vector codes]]) := by
  obtain ⟨values,encoded⟩ := values_encode pools distinct codes
    (ValueDomain.fact_values language terms pools _ codes typed.1 typed.2.2.1)
  refine ⟨⟨relation,values⟩,?_⟩
  change ((pools.relations.idxOf? relation).bind fun selected =>
    (values.mapM (PhysicalInstances.value? pools)).bind fun outputs =>
      some (Pattern.apply "GroundFact" [Executable.relationRef selected,.apply "GroundTuple" [Join.vector outputs]])) = _
  rw [atRelation,Option.bind_some,encoded,Option.bind_some]

theorem atom_instance_encodes (language : LanguageDef) (terms : language.terms = Query.baseLanguage.terms)
    (pools : Join.Pools) (distinct : pools.literals.Nodup) (bindings : Bindings)
    (poolRead : PhysicalInstances.PoolBindings pools bindings) (position : Nat)
    (source : Mettapedia.Languages.Datalog.Atom) (code : Pattern)
    (compiled : Join.atom? pools position source = some code)
    (typed : OpenPatternWellSorted language (FreeTypeContext.ofList (Executable.freeTypes pools)) [] (.base "DlStatement")
      (applyBindings bindings code)) :
    ∃ fact : GroundFact, Executable.fact? pools fact = some (applyBindings bindings code) := by
  change ((Join.relation? pools source.relation).bind fun relation =>
    (source.arguments.zipIdx.mapM fun entry => Join.argument? pools position entry.2 entry.1).bind fun arguments =>
      some (Pattern.apply "GroundFact" [relation,.apply "GroundTuple" [Join.vector arguments]])) = some code at compiled
  simp only [Option.bind_eq_some_iff,Option.some.injEq] at compiled
  obtain ⟨relation,relationCompiled,arguments,_,rfl⟩ := compiled
  obtain ⟨physical,registered,read⟩ := PhysicalInstances.relation_instance pools bindings poolRead source.relation relation relationCompiled
  obtain ⟨index,atRelation,rfl⟩ := Option.map_eq_some_iff.mp registered
  have normalized : applyBindings bindings (.apply "GroundFact" [relation,.apply "GroundTuple" [Join.vector arguments]]) =
      .apply "GroundFact" [Executable.relationRef index,.apply "GroundTuple" [Join.vector (arguments.map (applyBindings bindings))]] := by
    simp only [applyBindings,List.map_cons,List.map_nil,Join.vector,List.append_nil,read]
  rw [normalized] at typed ⊢
  exact fact_encodes language terms pools distinct source.relation index atRelation _ typed

#print axioms values_encode
#print axioms fact_encodes
#print axioms atom_instance_encodes

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.PhysicalCanonical
