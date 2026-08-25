import Mettapedia.Enactive.Basic
import Mettapedia.Algebra.QuantaleWeakness
import Mathlib.Data.Finset.Powerset

/-!
# Finite enactive abstraction layers and Bennett weakness

This is the decidable counting specialization of `Enactive.Basic`.  It follows
Michael Timothy Bennett's finite implementable-language presentation in
*The Optimal Choice of Hypothesis Is the Weakest, Not the Shortest* (2023) and
the finite-vocabulary case of *Is Complexity an Illusion?* (2024).

The abstract theory remains primary.  Here worlds and facts are finite, the
realizable statements of a vocabulary can be enumerated, and Bennett weakness
is computed as the number of completion statements in the principal extension.
-/

set_option autoImplicit false

namespace Mettapedia.Enactive.Finite

open Mettapedia.Enactive

universe uWorld

variable {World : Type uWorld} [Fintype World] [DecidableEq World]

/-- A finite abstraction layer: a finite vocabulary of finite world sets. -/
structure Layer (World : Type uWorld) [Fintype World] [DecidableEq World] where
  vocabulary : Finset (Finset World)

/-- One world realizes a finite collection of facts when it belongs to each
fact.  The bounded quantifier has an executable decision procedure. -/
def Realizes (world : World) (facts : Finset (Finset World)) : Prop :=
  ∀ fact ∈ facts, world ∈ fact

instance (world : World) (facts : Finset (Finset World)) :
    Decidable (Realizes world facts) := by
  unfold Realizes
  infer_instance

/-- Executable realization test for one world. -/
def realizesB (world : World) (facts : Finset (Finset World)) : Bool :=
  decide (Realizes world facts)

/-- A finite set of facts is realizable when some world realizes every fact. -/
def Realizable (facts : Finset (Finset World)) : Prop :=
  ∃ world : World, Realizes world facts

instance (facts : Finset (Finset World)) : Decidable (Realizable facts) :=
  by
    unfold Realizable
    infer_instance

/-- Executable finite witness search for realizability. -/
def realizableB (facts : Finset (Finset World)) : Bool :=
  decide (Realizable facts)

omit [Fintype World] [DecidableEq World] in
theorem realizable_iff (facts : Finset (Finset World)) :
    Realizable facts ↔
      ∃ world : World, ∀ fact ∈ facts, world ∈ fact := by
  rfl

@[simp]
theorem realizableB_eq_true (facts : Finset (Finset World)) :
    realizableB facts = true ↔ Realizable facts := by
  simp [realizableB]

namespace Layer

variable (layer : Layer World)

/-- Every realizable subset of the vocabulary.  This is the finite language
`L_v`. -/
def statements : Finset (Finset (Finset World)) :=
  layer.vocabulary.powerset.filter Realizable

/-- A statement is a member of the enumerated finite language. -/
abbrev Statement := {facts // facts ∈ layer.statements}

@[simp]
theorem mem_statements {facts : Finset (Finset World)} :
    facts ∈ layer.statements ↔
      facts ⊆ layer.vocabulary ∧ Realizable facts := by
  simp [statements]

instance : DecidableEq layer.Statement := inferInstance

/-- The finite extension `E_x`: all realizable vocabulary statements that
contain `x`. -/
def extension (source : layer.Statement) : Finset layer.Statement :=
  layer.statements.attach.filter fun target => source.val ⊆ target.val

@[simp]
theorem mem_extension {source target : layer.Statement} :
    target ∈ layer.extension source ↔ source.val ⊆ target.val := by
  simp [extension]

/-- Bennett weakness is the number of completions in a statement's extension
(2023, Definition 7; 2024, Definition 5).  Maximizing this quantity among
correct policies is the formal content of Bennett's razor. -/
def weakness (source : layer.Statement) : Nat :=
  (layer.extension source).card

/-- The finite enactive definition is exactly the world/completion-count
quantity named `bennettWeakness` in the general weakness algebra. -/
theorem weakness_eq_bennettWeakness (source : layer.Statement) :
    layer.weakness source =
      Mettapedia.Algebra.QuantaleWeakness.bennettWeakness
        (layer.extension source) := by
  rfl

/-- Adding facts can only remove completions. -/
theorem weakness_antitone {left right : layer.Statement}
    (included : left.val ⊆ right.val) :
    layer.weakness right ≤ layer.weakness left := by
  apply Finset.card_le_card
  intro target member
  rw [mem_extension] at member ⊢
  exact included.trans member

/-- The corresponding abstract layer contains exactly the set-valued images
of the finite vocabulary facts. -/
def toAbstract : AbstractionLayer World where
  vocabulary :=
    {fact | ∃ finiteFact ∈ layer.vocabulary,
      (finiteFact : Set World) = fact}

/-- Embed a finite statement in the abstract 2024 aspect theory. -/
def Statement.toAbstract (source : layer.Statement) : Aspect layer.toAbstract where
  facts :=
    {fact | ∃ finiteFact ∈ source.val, (finiteFact : Set World) = fact}
  facts_subset_vocabulary := by
    rintro fact ⟨finiteFact, member, rfl⟩
    exact ⟨finiteFact,
      (layer.mem_statements.mp source.property).1 member, rfl⟩
  realized := by
    obtain ⟨world, realizes⟩ := realizable_iff source.val |>.mp
      (layer.mem_statements.mp source.property).2
    refine ⟨world, ?_⟩
    rintro fact ⟨finiteFact, member, rfl⟩
    exact realizes finiteFact member

theorem Statement.toAbstract_facts
    (source : layer.Statement) (finiteFact : Finset World) :
    (finiteFact : Set World) ∈ source.toAbstract.facts ↔
      ∃ sourceFact ∈ source.val,
        (sourceFact : Set World) = (finiteFact : Set World) :=
  Iff.rfl

/-- Finite completion implies completion after embedding in the abstract
theory. -/
theorem Statement.toAbstract_mono {left right : layer.Statement}
    (included : left.val ⊆ right.val) :
    left.toAbstract ≤ right.toAbstract := by
  rintro fact ⟨finiteFact, member, equal⟩
  exact ⟨finiteFact, included member, equal⟩

/-- Because finite facts are extensional sets, the abstract embedding also
reflects completion. -/
theorem Statement.toAbstract_reflects {left right : layer.Statement}
    (included : left.toAbstract ≤ right.toAbstract) :
    left.val ⊆ right.val := by
  intro finiteFact member
  have abstractMember : (finiteFact : Set World) ∈ left.toAbstract.facts :=
    ⟨finiteFact, member, rfl⟩
  obtain ⟨rightFact, rightMember, equal⟩ := included abstractMember
  have : rightFact = finiteFact := by
    ext world
    exact Set.ext_iff.mp equal world
  simpa [this] using rightMember

theorem Statement.toAbstract_le_iff {left right : layer.Statement} :
    left.toAbstract ≤ right.toAbstract ↔ left.val ⊆ right.val :=
  ⟨Statement.toAbstract_reflects layer,
    Statement.toAbstract_mono layer⟩

/-- Extension of a finite collection of source statements. -/
def extensionSet (sources : Finset layer.Statement) : Finset layer.Statement :=
  layer.statements.attach.filter fun target =>
    ∃ source ∈ sources, source.val ⊆ target.val

@[simp]
theorem mem_extensionSet {sources : Finset layer.Statement}
    {target : layer.Statement} :
    target ∈ layer.extensionSet sources ↔
      ∃ source ∈ sources, source.val ⊆ target.val := by
  simp [extensionSet]

end Layer

/-! ## Finite tasks and policies -/

/-- The finite specialization of a 2024 task.  Correct outputs are required to
be completions of at least one input. -/
structure Task (layer : Layer World) where
  inputs : Finset layer.Statement
  correctOutputs : Finset layer.Statement
  correctOutputs_subset :
    ∀ output ∈ correctOutputs,
      ∃ input ∈ inputs, input.val ⊆ output.val

namespace Task

variable {layer : Layer World}

/-- Outputs jointly allowed by the input situations and a policy. -/
def inferredOutputs (task : Task layer) (policy : layer.Statement) :
    Finset layer.Statement :=
  layer.extensionSet task.inputs ∩ layer.extension policy

/-- Michael Timothy Bennett's 2024 definition of a correct policy, specialized
to a decidable finite abstraction layer. -/
def IsCorrectPolicy (task : Task layer) (policy : layer.Statement) : Prop :=
  task.inferredOutputs policy = task.correctOutputs

instance (task : Task layer) (policy : layer.Statement) :
    Decidable (task.IsCorrectPolicy policy) := by
  unfold IsCorrectPolicy
  infer_instance

/-- All correct policies in the finite language. -/
def correctPolicies (task : Task layer) : Finset layer.Statement :=
  layer.statements.attach.filter task.IsCorrectPolicy

@[simp]
theorem mem_correctPolicies {task : Task layer} {policy : layer.Statement} :
    policy ∈ task.correctPolicies ↔ task.IsCorrectPolicy policy := by
  simp [correctPolicies]

/-- The finite child relation from Bennett's 2024 Definition 3: strictly
fewer inputs and no correct output unavailable to the parent. -/
def IsChild (child parent : Task layer) : Prop :=
  child.inputs ⊂ parent.inputs ∧
    child.correctOutputs ⊆ parent.correctOutputs

theorem IsChild.trans {first second third : Task layer}
    (first_second : first.IsChild second)
    (second_third : second.IsChild third) :
    first.IsChild third :=
  ⟨first_second.1.trans second_third.1,
    first_second.2.trans second_third.2⟩

theorem not_isChild_self (task : Task layer) : ¬ task.IsChild task := by
  intro child
  exact (child.1.ne rfl)

/-- Forget finiteness and embed a finite task into the abstract 2024 theory.
This direction preserves the task well-formedness law. -/
def toAbstract (task : Task layer) :
    Mettapedia.Enactive.Task layer.toAbstract where
  inputs :=
    {aspect | ∃ source ∈ task.inputs, source.toAbstract = aspect}
  correctOutputs :=
    {aspect | ∃ source ∈ task.correctOutputs, source.toAbstract = aspect}
  correctOutputs_subset := by
    rintro aspect ⟨output, outputMember, rfl⟩
    obtain ⟨input, inputMember, included⟩ :=
      task.correctOutputs_subset output outputMember
    rw [Mettapedia.Enactive.Completion.mem_extensionSet]
    exact ⟨input.toAbstract, ⟨input, inputMember, rfl⟩,
      Layer.Statement.toAbstract_mono layer included⟩

end Task

/-! ## Executable finite canaries -/

namespace Canary

def trueFact : Finset Bool := {true}

def falseFact : Finset Bool := {false}

def topFact : Finset Bool := Finset.univ

def boolLayer : Layer Bool where
  vocabulary := {trueFact, falseFact, topFact}

def emptyStatement : boolLayer.Statement :=
  ⟨∅, by decide⟩

def trueStatement : boolLayer.Statement :=
  ⟨{trueFact}, by decide⟩

def contradictoryFacts : Finset (Finset Bool) :=
  {trueFact, falseFact}

/-- Positive example: the unconstrained statement has all six realizable
statements as completions. -/
theorem emptyStatement_weakness :
    boolLayer.weakness emptyStatement = 6 := by
  decide

/-- A true-only statement has exactly two completions: itself and itself plus
the universally true fact. -/
theorem trueStatement_weakness :
    boolLayer.weakness trueStatement = 2 := by
  decide

/-- Negative example: requiring both exclusive Boolean facts is not a
statement because no world realizes it. -/
theorem contradictoryFacts_not_statement :
    contradictoryFacts ∉ boolLayer.statements := by
  decide

/-- The finite-to-abstract bridge preserves the completion order on a concrete
nontrivial pair. -/
theorem empty_completes_to_true_abstractly :
    emptyStatement.toAbstract ≤ trueStatement.toAbstract := by
  exact Layer.Statement.toAbstract_mono boolLayer (Finset.empty_subset _)

end Canary

#print axioms Layer.weakness_antitone
#print axioms Layer.Statement.toAbstract_le_iff
#print axioms Canary.emptyStatement_weakness
#print axioms Canary.contradictoryFacts_not_statement

end Mettapedia.Enactive.Finite
