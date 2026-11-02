import Mettapedia.Languages.Datalog.Join

/-! Positive matching binds only variables authored in the matched atoms.
Starting from an empty environment yields exactly source-declared names. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace Mettapedia.Languages.Datalog.Join

def NamesWithin (domain : String → Prop) (environment : Environment) : Prop := ∀ pair ∈ environment, domain pair.1

theorem matchArgument_names {domain : String → Prop} {before after : Environment} {argument : Argument} {value : Value}
    (prior : NamesWithin domain before) (allowed : ∀ name ∈ argument.vars, domain name)
    (matched : matchArgument before argument value = some after) : NamesWithin domain after := by
  cases argument with
  | literal expected =>
    simp only [matchArgument] at matched
    split at matched
    · cases Option.some.inj matched
      exact prior
    · cases matched
  | anonymous => cases Option.some.inj matched; exact prior
  | var name =>
    simp only [matchArgument] at matched
    cases found : before.lookup name with
    | none =>
      rw [found] at matched
      cases Option.some.inj matched
      intro pair member
      rcases List.mem_cons.mp member with rfl | member
      · exact allowed name List.mem_cons_self
      · exact prior pair member
    | some previous =>
      by_cases equal : previous = value
      · simp only [found,if_pos equal] at matched
        cases Option.some.inj matched
        exact prior
      · simp only [found,if_neg equal] at matched
        cases matched

theorem matchArguments_names {domain : String → Prop} {before after : Environment}
    {arguments : List Argument} {values : List Value} (prior : NamesWithin domain before)
    (allowed : ∀ name ∈ arguments.flatMap Argument.vars, domain name)
    (matched : matchArguments before arguments values = some after) : NamesWithin domain after := by
  induction arguments generalizing before values with
  | nil =>
    cases values with
    | nil => cases Option.some.inj matched; exact prior
    | cons _ _ => cases matched
  | cons argument arguments ih =>
    cases values with
    | nil => cases matched
    | cons value values =>
      cases first : matchArgument before argument value with
      | none => simp [matchArguments,first] at matched
      | some middle =>
        have tail : matchArguments middle arguments values = some after := by simpa [matchArguments,first] using matched
        exact ih (matchArgument_names prior (fun name member => allowed name (List.mem_append_left _ member)) first)
          (fun name member => allowed name (List.mem_append_right _ member)) tail

theorem matchAtom_names {domain : String → Prop} {before after : Environment} {atom : Atom} {fact : GroundFact}
    (prior : NamesWithin domain before) (allowed : ∀ name ∈ atom.variables, domain name)
    (matched : matchAtom before atom fact = some after) : NamesWithin domain after := by
  unfold matchAtom at matched
  split at matched
  · exact matchArguments_names prior allowed matched
  · cases matched

theorem join_names (domain : String → Prop) (atoms : List Atom) (known : List GroundFact) (before : Environment)
    (prior : NamesWithin domain before) (allowed : ∀ atom ∈ atoms, ∀ name ∈ atom.variables, domain name)
    {row : Row} (joined : row ∈ join atoms known before) : NamesWithin domain row.environment := by
  induction atoms generalizing before row with
  | nil =>
    have same : row = ⟨before,[],[]⟩ := by simpa [join] using joined
    cases same
    exact prior
  | cons atom atoms ih =>
    obtain ⟨⟨fact,position⟩,_,output⟩ := List.mem_flatMap.mp joined
    cases first : matchAtom before atom fact with
    | none => simp [first] at output
    | some middle =>
      simp only [first,List.mem_map] at output
      obtain ⟨tail,included,rfl⟩ := output
      exact ih middle (row := tail) (matchAtom_names prior (allowed atom List.mem_cons_self) first)
        (fun other member => allowed other (List.mem_cons_of_mem _ member)) included

theorem clause_join_names (clause : Clause) (known : List GroundFact) (row : Row)
    (joined : row ∈ join clause.positiveAtoms known []) :
    ∀ pair ∈ row.environment, pair.1 ∈ clause.providedVariables :=
  join_names (fun name => name ∈ clause.providedVariables) clause.positiveAtoms known []
    (by intro pair member; cases member)
    (fun atom member name used => List.mem_flatMap.mpr ⟨atom,member,used⟩) joined

#print axioms join_names
#print axioms clause_join_names

end Mettapedia.Languages.Datalog.Join
