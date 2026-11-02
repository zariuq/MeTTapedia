import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRBindings
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRBindingContext
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRReferenceTyping

/-! Restrict the finite source substitution once to the actual declaration
context. Every retained reference then has its declared role sort in the
provider free context; no capture-typing hypothesis is introduced. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.BindingTyping

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax Match
open GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted

abbrev SourceEnvironment := Mettapedia.Languages.Datalog.Join.Environment

def restrict (context : List (String × TypeExpr)) (bindings : Bindings) : Bindings :=
  bindings.filter fun entry => (context.lookup entry.1).isSome

theorem restrict_lookup (context : List (String × TypeExpr)) (bindings : Bindings) (name : String)
    (declared : (context.lookup name).isSome = true) :
    (restrict context bindings).lookup name = bindings.lookup name := by
  have predicate : (fun entry : String × Pattern => decide ((context.lookup entry.1).isSome = true ∧ (entry.1 == name) = true)) =
      (fun entry => entry.1 == name) := by
    funext entry
    by_cases same : entry.1 = name
    · simp [same,declared]
    · simp [same]
  simp only [restrict,Bindings.lookup,List.find?_filter]
  rw [predicate]

private theorem relation_bound (pools : Join.Pools) (environment : SourceEnvironment) (chosen : List GroundFact)
    (index : Nat) (member : Names.Role.relation index ∈ Bindings.domain pools environment chosen) :
    index < pools.relations.length := by
  simpa [Bindings.domain,List.mem_flatMap] using member

private theorem literal_bound (pools : Join.Pools) (environment : SourceEnvironment) (chosen : List GroundFact)
    (index : Nat) (member : Names.Role.literal index ∈ Bindings.domain pools environment chosen) :
    index < pools.literals.length := by
  simpa [Bindings.domain,List.mem_flatMap] using member

private theorem value_encoded_open (language : LanguageDef) (pools : Join.Pools) (value : Value) (encoded : Pattern)
    (formed : PhysicalInstances.value? pools value = some encoded) :
    OpenPatternWellSorted language (FreeTypeContext.ofList (Executable.freeTypes pools)) [] (.base "DlValue") encoded := by
  obtain ⟨index,selected,rfl⟩ := Option.map_eq_some_iff.mp formed
  exact ReferenceTyping.value_open language pools index (List.idxOf?_eq_some_iff.mp selected).1

private theorem role_value_typed (language : LanguageDef) (pools : Join.Pools) (environment : SourceEnvironment)
    (chosen : List GroundFact) (role : Names.Role) (value : Pattern)
    (member : role ∈ Bindings.domain pools environment chosen)
    (formed : Bindings.values pools environment chosen role = some value) :
    OpenPatternWellSorted language (FreeTypeContext.ofList (Executable.freeTypes pools)) [] (BindingContext.roleType role) value := by
  cases role with
  | relation index =>
    have same : Executable.relationRef index = value := Option.some.inj formed
    subst value
    exact ReferenceTyping.relation_open language pools index (relation_bound pools environment chosen index member)
  | literal index =>
    have same : Executable.valueRef index = value := Option.some.inj formed
    subst value
    exact ReferenceTyping.value_open language pools index (literal_bound pools environment chosen index member)
  | logical name =>
    change (environment.lookup name).bind (PhysicalInstances.value? pools) = some value at formed
    obtain ⟨source,_,encoded⟩ := Option.bind_eq_some_iff.mp formed
    exact value_encoded_open language pools source value encoded
  | anonymous position index =>
    simp only [Bindings.values,Option.bind_eq_bind,Option.bind_eq_some_iff] at formed
    obtain ⟨fact,_,source,_,encoded⟩ := formed
    exact value_encoded_open language pools source value encoded

theorem restricted_typed (language : LanguageDef) (pools : Join.Pools) (clause : Clause)
    (environment : SourceEnvironment) (chosen : List GroundFact) :
    CapturesTyped language (FreeTypeContext.ofList (Executable.freeTypes pools)) [] (BindingContext.context pools clause)
      (restrict (BindingContext.context pools clause) (Bindings.ofInstance pools environment chosen)) := by
  intro entry retained
  have filtered : entry ∈ Bindings.ofInstance pools environment chosen ∧
      ((BindingContext.context pools clause).lookup entry.1).isSome = true := List.mem_filter.mp retained
  obtain ⟨role,member,formed⟩ := List.mem_filterMap.mp filtered.1
  obtain ⟨value,valueFormed,rfl⟩ := Option.map_eq_some_iff.mp formed
  obtain ⟨expected,declared⟩ := Option.isSome_iff_exists.mp filtered.2
  have same := BindingContext.lookup_role_type pools clause role expected declared
  refine ⟨expected,declared,?_⟩
  rw [same]
  exact role_value_typed language pools environment chosen role value member valueFormed

def ofClause (pools : Join.Pools) (clause : Clause) (environment : SourceEnvironment) (chosen : List GroundFact) : Bindings :=
  restrict (BindingContext.context pools clause) (Bindings.ofInstance pools environment chosen)

theorem clause_pools (pools : Join.Pools) (clause : Clause) (environment : SourceEnvironment) (chosen : List GroundFact) :
    PhysicalInstances.PoolBindings pools (ofClause pools clause environment chosen) := by
  constructor
  · intro index inside
    rw [show ofClause pools clause environment chosen = restrict (BindingContext.context pools clause) (Bindings.ofInstance pools environment chosen) from rfl,
      restrict_lookup _ _ _ (by rw [BindingContext.relation_declared pools clause index inside]; rfl)]
    exact (Bindings.pools_read pools environment chosen).relations index inside
  · intro index inside
    rw [show ofClause pools clause environment chosen = restrict (BindingContext.context pools clause) (Bindings.ofInstance pools environment chosen) from rfl,
      restrict_lookup _ _ _ (by rw [BindingContext.literal_declared pools clause index inside]; rfl)]
    exact (Bindings.pools_read pools environment chosen).literals index inside

theorem clause_variables (pools : Join.Pools) (clause : Clause) (environment : SourceEnvironment) (chosen : List GroundFact)
    (values : ∀ pair ∈ environment, pair.2 ∈ pools.literals)
    (names : ∀ pair ∈ environment, pair.1 ∈ clause.providedVariables) :
    PhysicalInstances.VariablesRead pools (ofClause pools clause environment chosen) (Mettapedia.Languages.Datalog.Join.assignment environment) := by
  intro name value found
  obtain ⟨before,after,shape,_⟩ := List.lookup_eq_some_iff.mp found
  have member : (name,value) ∈ environment := by rw [shape]; simp
  obtain ⟨encoded,formed,read⟩ := Bindings.variables_read pools environment chosen values name value found
  refine ⟨encoded,formed,?_⟩
  rw [show ofClause pools clause environment chosen = restrict (BindingContext.context pools clause) (Bindings.ofInstance pools environment chosen) from rfl,
    restrict_lookup _ _ _ (by rw [BindingContext.logical_declared pools clause name (names (name,value) member)]; rfl)]
  exact read

theorem clause_anonymous (pools : Join.Pools) (clause : Clause) (environment : SourceEnvironment) (chosen : List GroundFact)
    (position index : Nat) (source : Mettapedia.Languages.Datalog.Atom) (fact : GroundFact) (value : Value)
    (atSource : (Join.orderedBody clause)[position]? = some (.atom source))
    (atArgument : source.arguments[index]? = some .anonymous)
    (atFact : chosen[position]? = some fact) (atValue : fact.values[index]? = some value)
    (available : value ∈ pools.literals) :
    ∃ encoded, PhysicalInstances.value? pools value = some encoded ∧
      (ofClause pools clause environment chosen).lookup (Join.anonymousVariable position index) = some encoded := by
  obtain ⟨encoded,formed,read⟩ := Bindings.anonymous_read pools environment chosen position index fact value atFact atValue available
  refine ⟨encoded,formed,?_⟩
  rw [show ofClause pools clause environment chosen = restrict (BindingContext.context pools clause) (Bindings.ofInstance pools environment chosen) from rfl,
    restrict_lookup _ _ _ (by rw [BindingContext.anonymous_declared pools clause position index source atSource atArgument]; rfl)]
  exact read

theorem clause_typed_extended (language : LanguageDef) (pools : Join.Pools) (clause : Clause)
    (environment : SourceEnvironment) (chosen : List GroundFact) (extra : List (String × TypeExpr)) :
    CapturesTyped language (FreeTypeContext.ofList (Executable.freeTypes pools)) []
      (BindingContext.context pools clause ++ extra) (ofClause pools clause environment chosen) := by
  intro entry member
  obtain ⟨expected,declared,typed⟩ := restricted_typed language pools clause environment chosen entry member
  exact ⟨expected,by simp only [List.lookup_append,declared,Option.some_or],typed⟩

#print axioms restrict_lookup
#print axioms restricted_typed
#print axioms clause_pools
#print axioms clause_variables
#print axioms clause_anonymous
#print axioms clause_typed_extended

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.BindingTyping
