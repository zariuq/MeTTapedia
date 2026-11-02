import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRBindings
import Mettapedia.Languages.Datalog.JoinValueDomain

/-! A finite source join supplies one physical substitution for every body
atom. Shared variables use the join environment; anonymous fields use their
own selected fact positions. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.JoinInstances

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax Match
open GeneralFirstOrderProjection

abbrev SourceEnvironment := Mettapedia.Languages.Datalog.Join.Environment
abbrev SourceRow := Mettapedia.Languages.Datalog.Join.Row

private theorem value_in_pool (pools : Join.Pools) (value : Value) (code : Pattern)
    (encoded : PhysicalInstances.value? pools value = some code) : value ∈ pools.literals := by
  obtain ⟨index,present,_⟩ := Option.map_eq_some_iff.mp encoded
  exact List.isSome_idxOf?.mp (by simp [present])

private theorem values_in_pool (pools : Join.Pools) (inputs : List Value) (outputs : List Pattern)
    (read : inputs.mapM (PhysicalInstances.value? pools) = some outputs) :
    ∀ value ∈ inputs, value ∈ pools.literals := by
  induction inputs generalizing outputs with
  | nil => simp
  | cons head rest ih =>
    cases first : PhysicalInstances.value? pools head with
    | none => simp [List.mapM_cons,first] at read
    | some code =>
      cases tail : rest.mapM (PhysicalInstances.value? pools) with
      | none => simp [List.mapM_cons,first,tail] at read
      | some remaining =>
        intro other member
        rcases List.mem_cons.mp member with rfl | member
        · exact value_in_pool pools other code first
        · exact ih remaining tail other member

theorem fact_values_in_pool (pools : Join.Pools) (fact : GroundFact) (code : Pattern)
    (encoded : Executable.fact? pools fact = some code) : ∀ value ∈ fact.values, value ∈ pools.literals := by
  change ((pools.relations.idxOf? fact.relation).bind fun relation =>
    (fact.values.mapM (PhysicalInstances.value? pools)).bind fun values =>
      some (Pattern.apply "GroundFact" [Executable.relationRef relation,.apply "GroundTuple" [Join.vector values]])) = some code at encoded
  simp only [Option.bind_eq_some_iff,Option.some.injEq] at encoded
  obtain ⟨_,_,values,read,_⟩ := encoded
  exact values_in_pool pools fact.values values read

theorem environment_values (pools : Join.Pools) (atoms : List Mettapedia.Languages.Datalog.Atom)
    (known : List GroundFact) (row : SourceRow)
    (canonical : ∀ fact ∈ known, ∃ code, Executable.fact? pools fact = some code)
    (joined : row ∈ Mettapedia.Languages.Datalog.Join.join atoms known []) :
    ∀ pair ∈ row.environment, pair.2 ∈ pools.literals := by
  apply Mettapedia.Languages.Datalog.Join.join_values (fun value => value ∈ pools.literals) atoms known [] (by intro pair member; cases member)
    (fun fact member value present => by
      obtain ⟨code,encoded⟩ := canonical fact member
      exact fact_values_in_pool pools fact code encoded value present) joined

theorem body_atom_instance (pools : Join.Pools) (atoms : List Mettapedia.Languages.Datalog.Atom)
    (known : List GroundFact) (row : SourceRow)
    (canonical : ∀ fact ∈ known, ∃ code, Executable.fact? pools fact = some code)
    (joined : row ∈ Mettapedia.Languages.Datalog.Join.join atoms known [])
    (position : Nat) (source : Mettapedia.Languages.Datalog.Atom) (fact : GroundFact) (code : Pattern)
    (atSource : atoms[position]? = some source) (atFact : row.facts[position]? = some fact)
    (compiled : Join.atom? pools position source = some code) :
    Executable.fact? pools fact = some (applyBindings (Bindings.ofInstance pools row.environment row.facts) code) := by
  have evidence := Mettapedia.Languages.Datalog.Join.join_sound atoms known [] joined
  have bounds := (List.getElem?_eq_some_iff.mp atSource).1
  have factBound := (List.getElem?_eq_some_iff.mp atFact).1
  have matched : source.Matches (Mettapedia.Languages.Datalog.Join.assignment row.environment) fact := by
    have actual := evidence.2.1.get bounds factBound
    simpa only [List.get_eq_getElem,(List.getElem?_eq_some_iff.mp atSource).2,(List.getElem?_eq_some_iff.mp atFact).2] using actual
  have member : fact ∈ known := by
    have selected := evidence.2.2.get factBound (by simpa only [← evidence.2.2.length_eq] using factBound)
    exact List.mem_of_getElem? (by simpa only [List.get_eq_getElem,(List.getElem?_eq_some_iff.mp atFact).2] using selected)
  exact PhysicalInstances.atom_instance pools _ (Bindings.pools_read pools row.environment row.facts)
    (Mettapedia.Languages.Datalog.Join.assignment row.environment)
    (Bindings.variables_read pools row.environment row.facts (environment_values pools atoms known row canonical joined))
    position source fact code compiled matched (by
      intro index value _ atValue
      obtain ⟨physical,encoded⟩ := canonical fact member
      exact Bindings.anonymous_read pools row.environment row.facts position index fact value atFact atValue
        (fact_values_in_pool pools fact physical encoded value (List.mem_of_getElem? atValue)))

theorem head_instance (pools : Join.Pools) (clause : Clause) (known : List GroundFact) (row : SourceRow)
    (canonical : ∀ fact ∈ known, ∃ code, Executable.fact? pools fact = some code)
    (joined : row ∈ Mettapedia.Languages.Datalog.Join.join clause.positiveAtoms known [])
    (restricted : clause.RangeRestricted) (fact : GroundFact) (formed : Grounding.head? row.environment clause.head = some fact)
    (code : Pattern) (compiled : Join.atom? pools clause.body.length clause.head = some code) :
    Executable.fact? pools fact = some (applyBindings (Bindings.ofInstance pools row.environment row.facts) code) := by
  exact PhysicalInstances.atom_instance pools _ (Bindings.pools_read pools row.environment row.facts)
    (Mettapedia.Languages.Datalog.Join.assignment row.environment)
    (Bindings.variables_read pools row.environment row.facts (environment_values pools clause.positiveAtoms known row canonical joined))
    clause.body.length clause.head fact code compiled (Grounding.head?_sound formed) (by
      intro index value atSource _
      exact (restricted.1 .anonymous (List.mem_append_left _ (List.mem_of_getElem? atSource)) rfl).elim)

theorem guard_instance (program : Program) (pools : Join.Pools) (clause : Clause) (known : List GroundFact) (row : SourceRow)
    (canonical : ∀ fact ∈ known, ∃ code, Executable.fact? pools fact = some code)
    (joined : row ∈ Mettapedia.Languages.Datalog.Join.join clause.positiveAtoms known [])
    (restricted : clause.RangeRestricted) (comparison : Comparison) (inClause : comparison ∈ Comparisons.guards clause)
    (used : comparison.operator ∈ Executable.operators program)
    (holds : Comparisons.Holds Executable.policy (Mettapedia.Languages.Datalog.Join.assignment row.environment) comparison)
    (position : Nat) (leftCode rightCode : Pattern)
    (leftCompiled : Join.argument? pools position 0 comparison.left = some leftCode)
    (rightCompiled : Join.argument? pools position 1 comparison.right = some rightCode) :
    ∃ left right,
      (⟨Join.comparisonName comparison.operator,[left,right]⟩ : GeneralPremise.ProviderRow) ∈ Executable.comparisonRows program pools ∧
      applyBindings (Bindings.ofInstance pools row.environment row.facts) leftCode = left ∧
      applyBindings (Bindings.ofInstance pools row.environment row.facts) rightCode = right := by
  obtain ⟨left,right,leftMatched,rightMatched,compared⟩ := holds
  have read := Bindings.variables_read pools row.environment row.facts (environment_values pools clause.positiveAtoms known row canonical joined)
  have anonymousLeft : comparison.left ≠ .anonymous := restricted.1 comparison.left
    (Comparisons.guard_arguments_required inClause (by simp [Comparison.arguments]))
  have anonymousRight : comparison.right ≠ .anonymous := restricted.1 comparison.right
    (Comparisons.guard_arguments_required inClause (by simp [Comparison.arguments]))
  obtain ⟨leftValue,leftEncoded,leftRead⟩ := PhysicalInstances.argument_instance pools _ (Bindings.pools_read pools row.environment row.facts)
    _ read position 0 comparison.left leftCode left leftCompiled leftMatched (fun same => (anonymousLeft same).elim)
  obtain ⟨rightValue,rightEncoded,rightRead⟩ := PhysicalInstances.argument_instance pools _ (Bindings.pools_read pools row.environment row.facts)
    _ read position 1 comparison.right rightCode right rightCompiled rightMatched (fun same => (anonymousRight same).elim)
  obtain ⟨leftIndex,leftAt,rfl⟩ := Option.map_eq_some_iff.mp leftEncoded
  obtain ⟨rightIndex,rightAt,rfl⟩ := Option.map_eq_some_iff.mp rightEncoded
  refine ⟨Executable.valueRef leftIndex,Executable.valueRef rightIndex,?_,leftRead,rightRead⟩
  apply (Executable.comparison_row_iff program pools comparison.operator leftIndex rightIndex).mpr
  exact ⟨used,left,right,
    by obtain ⟨bound,same,_⟩ := List.idxOf?_eq_some_iff.mp leftAt; simp [bound,same],
    by obtain ⟨bound,same,_⟩ := List.idxOf?_eq_some_iff.mp rightAt; simp [bound,same],compared⟩

#print axioms fact_values_in_pool
#print axioms environment_values
#print axioms body_atom_instance
#print axioms head_instance
#print axioms guard_instance

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.JoinInstances
