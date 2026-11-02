import Mettapedia.Languages.Datalog.ClosureSemantics

/-! Clause matching directly introduces the independent source judgment.
The witness records a finite grounding and its actual positive premises. -/

set_option autoImplicit false

namespace Mettapedia.Languages.Datalog

private theorem collect_matches (atoms : List Atom) (model : Assignment) (known : List GroundFact)
    (available : ∀ atom ∈ atoms, ∃ fact ∈ known, atom.Matches model fact) :
    ∃ facts, List.Forall₂ (Atom.Matches model) atoms facts ∧ ∀ fact ∈ facts, fact ∈ known := by
  induction atoms with
  | nil => exact ⟨[],.nil,by simp⟩
  | cons atom atoms ih =>
    obtain ⟨fact,present,matched⟩ := available atom List.mem_cons_self
    obtain ⟨facts,matchedList,members⟩ := ih (fun other member => available other (List.mem_cons_of_mem _ member))
    refine ⟨fact :: facts,.cons matched matchedList,?_⟩
    intro other member
    rcases List.mem_cons.mp member with rfl | member
    · exact present
    · exact members other member

private theorem collect_grounding (names : List String) (model : Assignment)
    (defined : ∀ name ∈ names, ∃ value, model name = some value) :
    ∃ grounding : List (String × Value), grounding.map Prod.fst = names ∧
      ∀ pair ∈ grounding, model pair.1 = some pair.2 := by
  induction names with
  | nil => exact ⟨[],rfl,by simp⟩
  | cons name names ih =>
    obtain ⟨value,read⟩ := defined name List.mem_cons_self
    obtain ⟨rest,fields,reads⟩ := ih (fun other member => defined other (List.mem_cons_of_mem _ member))
    refine ⟨(name,value) :: rest,by simp only [List.map_cons,fields],?_⟩
    intro pair member
    rcases List.mem_cons.mp member with rfl | member
    · exact read
    · exact reads pair member

private theorem argument_values_exist (arguments : List Argument) (model : Assignment)
    (named : ∀ argument ∈ arguments, argument ≠ .anonymous)
    (defined : ∀ identifier ∈ arguments.flatMap Argument.vars, ∃ value, model identifier = some value) :
    ∃ values, List.Forall₂ (Argument.Matches model) arguments values := by
  induction arguments with
  | nil => exact ⟨[],.nil⟩
  | cons argument arguments ih =>
    obtain ⟨rest,related⟩ := ih
      (fun other member => named other (List.mem_cons_of_mem _ member))
      (fun identifier member => defined identifier (List.mem_append_right _ member))
    cases argument with
    | literal value => exact ⟨value :: rest,.cons rfl related⟩
    | var identifier =>
      obtain ⟨value,read⟩ := defined identifier (by simp [Argument.vars])
      exact ⟨value :: rest,.cons read related⟩
    | anonymous => exact (named .anonymous List.mem_cons_self rfl).elim

theorem Clause.head_has_matching_fact (clause : Clause) (restricted : clause.RangeRestricted)
    (model : Assignment) (known : List GroundFact)
    (body : ∀ atom ∈ clause.positiveAtoms, ∃ fact ∈ known, atom.Matches model fact) :
    ∃ fact, clause.head.Matches model fact := by
  obtain ⟨values,related⟩ := argument_values_exist clause.head.arguments model
    (fun argument member => restricted.1 argument (List.mem_append_left _ member)) (by
      intro identifier member
      have needed : identifier ∈ clause.requiredVariables := by
        obtain ⟨argument,atHead,used⟩ := List.mem_flatMap.mp member
        exact List.mem_flatMap.mpr ⟨argument,List.mem_append_left _ atHead,used⟩
      obtain ⟨_,_,value,_,defined⟩ := Clause.required_variable_from_body restricted model
        {fact | fact ∈ known} body needed
      exact ⟨value,defined⟩)
  exact ⟨⟨clause.head.relation,values⟩,rfl,related⟩

theorem clause_instance (policy : Comparisons.Policy) (program : Program) (known : List GroundFact)
    (ordinal : Nat) (clause : Clause) (source : ProgramGrounding.ClauseAt program ordinal clause)
    (restricted : clause.RangeRestricted) (model : Assignment) (conclusion : GroundFact)
    (head : clause.head.Matches model conclusion)
    (body : ∀ atom ∈ clause.positiveAtoms, ∃ fact ∈ known, atom.Matches model fact)
    (guards : ∀ comparison ∈ Comparisons.guards clause, Comparisons.Holds policy model comparison) :
    ∃ row : GroundInstances.Instance, row.conclusion = conclusion ∧
      ProgramGrounding.SourceAuthorized policy program known row := by
  obtain ⟨premises,matchedList,members⟩ := collect_matches clause.positiveAtoms model known body
  have defined : ∀ name ∈ DerivationIdentity.clauseVariables clause, ∃ value, model name = some value := by
    intro name member
    have provided : name ∈ clause.providedVariables := List.mem_eraseDups.mp member
    obtain ⟨atom,inside,used⟩ := List.mem_flatMap.mp provided
    obtain ⟨fact,_,matched⟩ := body atom inside
    obtain ⟨value,_,read⟩ := Atom.variable_has_matching_value matched used
    exact ⟨value,read⟩
  obtain ⟨grounding,names,values⟩ := collect_grounding (DerivationIdentity.clauseVariables clause) model defined
  exact ⟨⟨⟨ordinal,grounding,premises⟩,conclusion,[]⟩,rfl,
    clause,source,restricted,rfl,model,head,matchedList,members,guards,names,values⟩

theorem Closure.Derives.of_clause (policy : Comparisons.Policy) (program : Program) (seeds known : List GroundFact)
    (ordinal : Nat) (clause : Clause) (source : ProgramGrounding.ClauseAt program ordinal clause)
    (restricted : clause.RangeRestricted) (model : Assignment) (conclusion : GroundFact)
    (head : clause.head.Matches model conclusion)
    (body : ∀ atom ∈ clause.positiveAtoms, ∃ fact ∈ known, atom.Matches model fact)
    (guards : ∀ comparison ∈ Comparisons.guards clause, Comparisons.Holds policy model comparison)
    (derived : ∀ fact ∈ known, Closure.Derives policy program seeds fact) :
    Closure.Derives policy program seeds conclusion := by
  obtain ⟨row,same,authorized⟩ := clause_instance policy program known ordinal clause source restricted model conclusion head body guards
  rw [← same]
  exact .fire row (Closure.authorized_on_premises _ _ _ _ authorized)
    (fun fact member => derived fact (Closure.source_firing_premises authorized fact member))

#print axioms Clause.head_has_matching_fact
#print axioms clause_instance
#print axioms Closure.Derives.of_clause

end Mettapedia.Languages.Datalog
