import Mettapedia.Languages.Datalog.ProgramGrounding

/-! A finite join cannot invent environment values. Ground clause witnesses
therefore use only values already present in their positive input facts. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace Mettapedia.Languages.Datalog.Join

def ValuesWithin (domain : Value → Prop) (environment : Environment) : Prop :=
  ∀ pair ∈ environment, domain pair.2

theorem matchArgument_values {domain : Value → Prop} {before after : Environment}
    {argument : Argument} {value : Value} (prior : ValuesWithin domain before) (allowed : domain value)
    (matched : matchArgument before argument value = some after) : ValuesWithin domain after := by
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
      · exact allowed
      · exact prior pair member
    | some previous =>
      by_cases equal : previous = value
      · simp only [found,if_pos equal] at matched
        cases Option.some.inj matched
        exact prior
      · simp only [found,if_neg equal] at matched
        cases matched

theorem matchArguments_values {domain : Value → Prop} {before after : Environment}
    {arguments : List Argument} {values : List Value} (prior : ValuesWithin domain before)
    (allowed : ∀ value ∈ values, domain value)
    (matched : matchArguments before arguments values = some after) : ValuesWithin domain after := by
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
        exact ih (matchArgument_values prior (allowed value List.mem_cons_self) first)
          (fun other member => allowed other (List.mem_cons_of_mem _ member)) tail

theorem matchAtom_values {domain : Value → Prop} {before after : Environment} {atom : Atom} {fact : GroundFact}
    (prior : ValuesWithin domain before) (allowed : ∀ value ∈ fact.values, domain value)
    (matched : matchAtom before atom fact = some after) : ValuesWithin domain after := by
  unfold matchAtom at matched
  split at matched
  · exact matchArguments_values prior allowed matched
  · cases matched

theorem join_values (domain : Value → Prop) (atoms : List Atom) (known : List GroundFact) (before : Environment)
    (prior : ValuesWithin domain before) (allowed : ∀ fact ∈ known, ∀ value ∈ fact.values, domain value)
    {row : Row} (joined : row ∈ join atoms known before) : ValuesWithin domain row.environment := by
  induction atoms generalizing before row with
  | nil =>
    have same : row = ⟨before,[],[]⟩ := by simpa [join] using joined
    cases same
    exact prior
  | cons atom atoms ih =>
    obtain ⟨⟨fact,position⟩,present,output⟩ := List.mem_flatMap.mp joined
    have atKnown := List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp present)
    cases first : matchAtom before atom fact with
    | none => simp [first] at output
    | some middle =>
      simp only [first,List.mem_map] at output
      obtain ⟨tail,included,rfl⟩ := output
      exact ih middle (row := tail) (matchAtom_values prior (allowed fact atKnown) first) included

end Mettapedia.Languages.Datalog.Join

namespace Mettapedia.Languages.Datalog.GroundInstances

theorem source_join_witness (policy : Comparisons.Policy) (ordinal : Nat) (clause : Clause)
    (known : List GroundFact) (wanted : Instance) (authorized : Authorized policy ordinal clause known wanted) :
    ∃ row ∈ Join.join clause.positiveAtoms known [], ∃ emitted,
      fromRow? policy ordinal clause row = some emitted ∧
      emitted.key = wanted.key ∧ emitted.conclusion = wanted.conclusion := by
  obtain ⟨emitted,member,key,conclusion⟩ := produce_complete policy ordinal clause known wanted authorized
  unfold produce at member
  rw [if_pos ((Clause.checkRangeRestriction_iff clause).mpr authorized.1)] at member
  obtain ⟨row,joined,formed⟩ := List.mem_filterMap.mp member
  exact ⟨row,joined,emitted,formed,key,conclusion⟩

#print axioms source_join_witness
#print axioms Join.join_values

end Mettapedia.Languages.Datalog.GroundInstances
