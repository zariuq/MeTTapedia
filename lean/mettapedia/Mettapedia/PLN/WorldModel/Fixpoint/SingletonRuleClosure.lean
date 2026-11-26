import Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure

namespace Mettapedia.PLN.WorldModel

open Mettapedia.PLN.Evidence.EvidenceClass

variable {State Query : Type*} [EvidenceType State] [BinaryWorldModel State Query]

/-- A strength comparison at one world licenses a rule at that world. -/
abbrev WMConsequenceRuleOn.atState (world : State) (premise conclusion : Query)
    (comparison : BinaryWorldModel.queryStrength world premise ≤
      BinaryWorldModel.queryStrength world conclusion) : WMConsequenceRuleOn State Query where
  side actual := actual = world
  premise := premise
  conclusion := conclusion
  sound := by
    intro actual same
    subst actual
    exact comparison

namespace Fixpoint.PLNWorldModelFixpointClosure

/-- One active rule reads its premise from the seed during the first iteration. -/
theorem mem_immediateIter_singleton_rule_one (rule : WMConsequenceRuleOn State Query)
    (world : State) (seed : Set Query) (query : Query) :
    query ∈ immediateIter {rule} world seed 1 ↔
      query ∈ seed ∨ (rule.side world ∧ rule.premise ∈ seed ∧ query = rule.conclusion) := by
  simp [immediateIter, immediateStep, derivedByRules]

/-- A single rule cannot make its own premise available unless the premise was
already in the seed. Its first iterate is therefore the least closure. -/
theorem leastRuleClosure_singleton_rule_eq_one (rule : WMConsequenceRuleOn State Query)
    (world : State) (seed : Set Query) :
    leastRuleClosure {rule} world seed = immediateIter {rule} world seed 1 := by
  apply Set.Subset.antisymm
  · apply leastRuleClosure_least_of_seed_and_rules
    · intro query known
      exact (mem_immediateIter_singleton_rule_one rule world seed query).mpr (.inl known)
    · intro current chosen enabled premise
      have same : current = rule := Set.mem_singleton_iff.mp chosen
      subst current
      have present : rule.premise ∈ seed :=
        ((mem_immediateIter_singleton_rule_one rule world seed rule.premise).mp premise).elim
          id (fun activated => activated.2.1)
      exact (mem_immediateIter_singleton_rule_one rule world seed rule.conclusion).mpr
        (.inr ⟨enabled, present, rfl⟩)
  · exact immediateIter_subset_leastRuleClosure {rule} world seed 1

/-- A singleton-rule endpoint exposes the seed, the first operational result,
and the membership of that result in the least rule-closed set. -/
abbrev SingletonRuleClosure (rule : WMConsequenceRuleOn State Query)
    (world : State) (premise conclusion : Query) : Prop :=
  premise ∈ immediateIter {rule} world {premise} 0 ∧
    conclusion ∈ immediateIter {rule} world {premise} 1 ∧
    conclusion ∈ leastRuleClosure {rule} world {premise}

theorem singletonRuleClosure (rule : WMConsequenceRuleOn State Query) (world : State)
    (enabled : rule.side world) : SingletonRuleClosure rule world rule.premise rule.conclusion := by
  have seeded : rule.premise ∈ ({rule.premise} : Set Query) := Set.mem_singleton _
  have reached : rule.conclusion ∈ immediateIter {rule} world {rule.premise} 1 :=
    (mem_immediateIter_singleton_rule_one rule world {rule.premise} rule.conclusion).mpr
      (.inr ⟨enabled, seeded, rfl⟩)
  exact ⟨seeded, reached,
    immediateIter_subset_leastRuleClosure {rule} world {rule.premise} 1 reached⟩

end Fixpoint.PLNWorldModelFixpointClosure
end Mettapedia.PLN.WorldModel
