import Mettapedia.Languages.Datalog.ClosureSemantics
import Mettapedia.Machines.SetOutputPublication

/-! The output interface of one completed positive Datalog run. It selects
declared output relations and adds their facts without erasing occurrences
already in the destination. Capturing and decoding native Space inputs,
native publication and source-profile admission remain separate boundaries. -/

set_option autoImplicit false

namespace Mettapedia.Languages.Datalog.SpaceOutput

open Mettapedia.Machines.SetOutputPublication

def relations (program : Program) : List QualifiedName :=
  program.statements.filterMap fun statement => match statement with
    | .output name => some name
    | _ => none

def select (program : Program) (facts : List GroundFact) : List GroundFact :=
  facts.filter fun fact => decide (fact.relation ∈ relations program)

@[simp] theorem mem_select (program : Program) (facts : List GroundFact) (fact : GroundFact) :
    fact ∈ select program facts ↔ fact ∈ facts ∧ fact.relation ∈ relations program := by
  simp [select]

/-- The destination can contain unrelated or duplicate facts. Its contents
are not assumed to be exactly this run's output. -/
theorem completed_publication_exact (policy : Comparisons.Policy) (program : Program)
    (seeds destination : List GroundFact) (ticks : Nat)
    (closed : Closure.FactsComplete policy program (Closure.run policy program ticks (Closure.initial seeds)))
    (fact : GroundFact) :
    fact ∈ publish destination (select program (Closure.run policy program ticks (Closure.initial seeds)).facts) ↔
      fact ∈ destination ∨
        (Closure.Derives policy program seeds fact ∧ fact.relation ∈ relations program) := by
  rw [mem_publish, mem_select, Closure.settled_facts_exact policy program seeds ticks closed fact]

theorem repeated_publication (program : Program) (destination facts : List GroundFact) :
    publish (publish destination (select program facts)) (select program facts) =
      publish destination (select program facts) := publish_idempotent _ _

theorem preserves_existing_occurrences (program : Program) (destination facts : List GroundFact)
    (fact : GroundFact) (present : fact ∈ destination) :
    (publish destination (select program facts)).count fact = destination.count fact :=
  publish_existing_count _ _ _ present

private def one : GroundFact := ⟨["Output"], [.symbol "a"]⟩
private def hidden : GroundFact := ⟨["Internal"], [.symbol "b"]⟩
private def program : Program := ⟨[.output ["Output"]]⟩

example : select program [one, hidden, one] = [one, one] := by decide +kernel
example : publish [hidden, hidden] (select program [one, hidden, one]) =
    [hidden, hidden, one] := by decide +kernel
example : select (⟨[]⟩ : Program) [one] = [] := rfl

#print axioms completed_publication_exact
#print axioms preserves_existing_occurrences

end Mettapedia.Languages.Datalog.SpaceOutput
