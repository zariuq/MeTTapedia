import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRClauseDictionary
import Mettapedia.OSLF.MeTTaIL.GeneralVectorMatchInstance
import Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderScopedInstance

/-! Compiled atom instances admit real relational and scoped matches.
Fixed-vector tuples use ordered matching and retain repeated-variable constraints. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.InstanceMatching

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax Match MatchSpec RuleBinding GeneralScopedMatch
open GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem atom_shape (pools : Join.Pools) (position : Nat) (source : Mettapedia.Languages.Datalog.Atom)
    (code : Pattern) (compiled : Join.atom? pools position source = some code) : VectorFirstOrder code := by
  change ((Join.relation? pools source.relation).bind fun name =>
    (source.arguments.zipIdx.mapM fun entry => Join.argument? pools position entry.2 entry.1).bind fun arguments =>
      some (Pattern.apply "GroundFact" [name,.apply "GroundTuple" [Join.vector arguments]])) = some code at compiled
  simp only [Option.bind_eq_some_iff,Option.some.injEq] at compiled
  obtain ⟨name,named,arguments,argsCompiled,rfl⟩ := compiled
  obtain ⟨slot,rfl⟩ := ClauseDictionary.relation_variable pools source.relation name named
  apply VectorFirstOrder.constructor
  intro child member
  rcases List.mem_cons.mp member with rfl | member
  · exact .metavariable slot
  · have same : child = .apply "GroundTuple" [Join.vector arguments] := List.mem_singleton.mp member
    subst child
    apply VectorFirstOrder.constructor
    intro child member
    cases List.mem_singleton.mp member
    apply VectorFirstOrder.vector
    intro argument member
    obtain ⟨slot,rfl⟩ := ClauseDictionary.compiled_arguments_are_variables pools position source.arguments arguments argsCompiled argument member
    exact .metavariable slot

theorem atom_instance (pools : Join.Pools) (position : Nat) (source : Mettapedia.Languages.Datalog.Atom)
    (code : Pattern) (compiled : Join.atom? pools position source = some code)
    (environment : Bindings) (defined : Defined environment code.freeFvarNames) :
    ∃ bindings, MatchRel code (applyBindings environment code) bindings ∧ Compatible environment bindings ∧
      (bindings.map Prod.fst).Nodup ∧ SameNames bindings code.freeFvarNames :=
  vector_match_instance environment (atom_shape pools position source code compiled) defined

theorem atom_scoped_instance (pools : Join.Pools) (position : Nat) (source : Mettapedia.Languages.Datalog.Atom)
    (code : Pattern) (compiled : Join.atom? pools position source = some code)
    {rule : RewriteRule} {ambient : Nat} {site : RulePatternSite} {path : List Nat}
    (coherent : NameCoherent rule site path code)
    (declared : ∀ name ∈ code.freeFvarNames, dependencies? (GeneralRuleBindingInference.inferredSpec rule) name = some [])
    (environment : Bindings) (defined : Defined environment code.freeFvarNames)
    (scope : (applyBindings environment code).isWellScopedAt ambient = true)
    (object : isObjectPattern (applyBindings environment code) = true)
    {initial : ScopedRuleMatching.Assignment} (before : ScopedCompatible ambient environment initial) :
    ∃ final, Matches rule (GeneralRuleBindingInference.inferredSpec rule) ambient site path 0 initial code
      (applyBindings environment code) final ∧ ScopedCompatible ambient environment final := by
  obtain ⟨bindings,matched,compatible,_,_⟩ := atom_instance pools position source code compiled environment defined
  exact binderFree_scoped_of_matchRel (ClauseDictionary.atom_binderFree pools position source code compiled)
    coherent declared matched compatible scope object before

#print axioms atom_shape
#print axioms atom_instance
#print axioms atom_scoped_instance

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.InstanceMatching
