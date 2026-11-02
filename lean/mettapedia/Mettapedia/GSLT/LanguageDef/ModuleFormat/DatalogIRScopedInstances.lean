import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRBindingTyping
import Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderScopedInstance

/-! Construct admitted scoped matches from the fixed, typed clause
substitution. Capture typing and dependency declarations follow from the
actual rule context and its admitted zero-dependency specification. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ScopedInstances

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax Match MatchSpec RuleBinding GeneralScopedMatch
open GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted

private theorem restricted_declared (pools : Join.Pools) (clause : Clause)
    (environment : BindingTyping.SourceEnvironment) (chosen : List GroundFact) (name : String) (value : Pattern)
    (found : (BindingTyping.ofClause pools clause environment chosen).lookup name = some value) :
    ∃ type, (BindingContext.context pools clause).lookup name = some type := by
  have member := raw_lookup_member found
  have filtered : (name,value) ∈ Bindings.ofInstance pools environment chosen ∧
      ((BindingContext.context pools clause).lookup name).isSome = true := List.mem_filter.mp member
  exact Option.isSome_iff_exists.mp filtered.2

theorem typed_match (language : LanguageDef) (pools : Join.Pools) (clause : Clause)
    (environment : BindingTyping.SourceEnvironment) (chosen : List GroundFact)
    (rule : RewriteRule) (spec : RuleBindingSpec) (extra : List (String × TypeExpr))
    (context : rule.typeContext = BindingContext.context pools clause ++ extra)
    (admitted : admittedFor rule spec = true) (zero : GeneralPremise.checkZeroDependencies spec = true)
    (site : RulePatternSite) (path : List Nat) (schema target : Pattern)
    (shape : VectorFirstOrder schema) (noBinders : binderFree schema = true)
    (coherent : NameCoherent rule site path schema)
    (defined : Defined (BindingTyping.ofClause pools clause environment chosen) schema.freeFvarNames)
    (instantiated : applyBindings (BindingTyping.ofClause pools clause environment chosen) schema = target)
    (type : TypeExpr) (typedTarget : OpenPatternWellSorted language (FreeTypeContext.ofList (Executable.freeTypes pools)) [] type target)
    (initial : ScopedRuleMatching.Assignment)
    (before : ScopedCompatible 0 (BindingTyping.ofClause pools clause environment chosen) initial) :
    ∃ final, Matches rule spec 0 site path 0 initial schema target final ∧
      ScopedCompatible 0 (BindingTyping.ofClause pools clause environment chosen) final ∧
      ConditionalEquationExecution.AssignmentTyped language (FreeTypeContext.ofList (Executable.freeTypes pools)) [] rule spec final ∧
      ConditionalEquationExecution.AssignmentObjects final := by
  obtain ⟨raw,matched,compatible,_,_⟩ := vector_match_instance _ shape defined
  rw [instantiated] at matched
  have declared : ∀ name ∈ schema.freeFvarNames, dependencies? spec name = some [] := by
    intro name member
    obtain ⟨value,found⟩ := defined name member
    obtain ⟨type,declared⟩ := restricted_declared pools clause environment chosen name value found
    apply dependencies_empty_of_admitted (type := type) admitted zero
    rw [context]
    simp only [List.lookup_append,declared,Option.some_or]
  obtain ⟨final,matching,compatible⟩ := binderFree_scoped_of_matchRel_admitted admitted noBinders coherent declared
    matched compatible typedTarget.2.2.2 typedTarget.2.2.1 before
  have typed : CapturesTyped language (FreeTypeContext.ofList (Executable.freeTypes pools)) [] rule.typeContext
      (BindingTyping.ofClause pools clause environment chosen) := by
    rw [context]
    exact BindingTyping.clause_typed_extended language pools clause environment chosen extra
  obtain ⟨sorted,objects⟩ := compatible.typed_admitted typed admitted zero
  exact ⟨final,matching,compatible,sorted,objects⟩

theorem input_value (pools : Join.Pools) (clause : Clause) (sourceEnvironment : BindingTyping.SourceEnvironment)
    (chosen : List GroundFact) (environment : GeneralPremise.Environment) (context : GeneralPremise.Context)
    (extra : List (String × TypeExpr))
    (ctx : context.rule.typeContext = BindingContext.context pools clause ++ extra)
    (bound : context.bound = [])
    (admitted : admittedFor context.rule context.spec = true) (zero : GeneralPremise.checkZeroDependencies context.spec = true)
    (argument : Nat) (schema target : Pattern) (shape : ∃ name, schema = .fvar name)
    (coherent : NameCoherent context.rule (context.site argument) [] schema)
    (initial : ScopedRuleMatching.Assignment)
    (before : ScopedCompatible 0 (BindingTyping.ofClause pools clause sourceEnvironment chosen) initial)
    (defined : GeneralPremise.BoundNames initial schema.freeFvarNames)
    (instantiated : applyBindings (BindingTyping.ofClause pools clause sourceEnvironment chosen) schema = target) :
    ScopedRuleMatching.instantiateAt? context.rule context.spec context.bound.length
      (context.site argument) [] 0 initial schema = some target := by
  obtain ⟨name,rfl⟩ := shape
  obtain ⟨value,found⟩ := defined name (by simp [Pattern.freeFvarNames])
  have member := ConditionalEquationExecution.lookup_assignment_member initial name value found
  have compatible := before (name,value) member
  have rawTyped : CapturesTyped environment.language (FreeTypeContext.ofList (Executable.freeTypes pools)) [] context.rule.typeContext
      (BindingTyping.ofClause pools clause sourceEnvironment chosen) := by
    rw [ctx]
    exact BindingTyping.clause_typed_extended environment.language pools clause sourceEnvironment chosen extra
  have assigned := ScopedCompatible.typed_admitted (bound := []) before rawTyped admitted zero
  obtain ⟨_,type,_,typeDeclared,_,_,_⟩ := assigned.1 name value member
  have dependency := dependencies_empty_of_admitted admitted zero typeDeclared
  have arguments := arguments_empty_of_admitted admitted dependency coherent.fvar
  have read := root_value_readout ((ScopedCompatible.rootValues (bound := []) before rawTyped) name value found)
  simp only [List.length_nil] at read
  have same : value.body = target := by
    rw [apply_variable,compatible.2.2,Option.getD_some] at instantiated
    exact instantiated
  rw [← same]
  simp only [ScopedRuleMatching.instantiateAt?,ScopedRuleMatching.instantiateWith?,bound,List.length_nil,found,arguments,
    Option.bind_eq_bind,Option.bind_some,read]

#print axioms typed_match
#print axioms input_value

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ScopedInstances
