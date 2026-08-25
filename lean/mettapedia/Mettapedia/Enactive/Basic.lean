import Mettapedia.Machines.ConeDuality

/-!
# Enactive aspects, completions, tasks, and policies

This module formalizes the finiteness-free core of Michael Timothy Bennett's
mature enactive framework from *Is Complexity an Illusion?* (2024),
Definitions 1--5.  The earlier presentation in *The Optimal Choice of
Hypothesis Is the Weakest, Not the Shortest* (2023) is treated downstream as a
specialization, not as the foundation.

A declarative fact is a set of worlds.  An abstraction layer selects a
vocabulary of such facts.  An aspect is a realizable collection of facts in
that vocabulary; its completions are the larger aspects containing it.
Tasks retain inputs and correct outputs, while a policy is correct exactly
when its completions select those correct outputs from the input completions.

The completion closure is an instance of the existing forward-cone machinery,
so its Galois connection is inherited rather than reconstructed.  Semantic
equivalence (same realizing worlds) is deliberately distinct from extension
equivalence (same syntactic completions).  Their difference is a load-bearing
boundary in the 2024 complexity argument.

No finiteness, decidable equality, probability, or uniform task distribution
is assumed here.
-/

set_option autoImplicit false

namespace Mettapedia.Enactive

universe uWorld

/-- A declarative fact is the set of worlds in which it is true. -/
abbrev Fact (World : Type uWorld) := Set World

/-- A vocabulary selects the declarative facts available at one abstraction
layer.  Taking the vocabulary to be all facts is Bennett's no-abstraction
case. -/
structure AbstractionLayer (World : Type uWorld) where
  vocabulary : Set (Fact World)

namespace AbstractionLayer

/-- The no-abstraction layer contains every declarative fact. -/
def full (World : Type uWorld) : AbstractionLayer World where
  vocabulary := Set.univ

end AbstractionLayer

/-- A realizable aspect in an abstraction layer.  Realizability is written as
an explicit witness rather than as a potentially ambiguous empty intersection. -/
structure Aspect {World : Type uWorld} (layer : AbstractionLayer World) where
  facts : Set (Fact World)
  facts_subset_vocabulary : facts ⊆ layer.vocabulary
  realized : ∃ world, ∀ fact ∈ facts, world ∈ fact

namespace Aspect

variable {World : Type uWorld} {layer : AbstractionLayer World}

@[ext]
theorem ext {left right : Aspect layer} (facts_eq : left.facts = right.facts) :
    left = right := by
  cases left
  cases right
  cases facts_eq
  rfl

instance : LE (Aspect layer) where
  le left right := left.facts ⊆ right.facts

instance : PartialOrder (Aspect layer) where
  le_refl aspect := Set.Subset.rfl
  le_trans _ _ _ := Set.Subset.trans
  le_antisymm left right left_le right_le :=
    Aspect.ext (Set.Subset.antisymm left_le right_le)

/-- A world realizes an aspect when every fact in the aspect holds there. -/
def Realizes (world : World) (aspect : Aspect layer) : Prop :=
  ∀ fact ∈ aspect.facts, world ∈ fact

/-- The semantic extent of an aspect: all worlds realizing it. -/
def semanticExtent (aspect : Aspect layer) : Set World :=
  {world | Realizes world aspect}

theorem semanticExtent_nonempty (aspect : Aspect layer) :
    aspect.semanticExtent.Nonempty := by
  obtain ⟨world, realizes⟩ := aspect.realized
  exact ⟨world, realizes⟩

/-- Two aspects are semantically equivalent when they are realized by exactly
the same worlds. -/
def SemanticallyEquivalent (left right : Aspect layer) : Prop :=
  left.semanticExtent = right.semanticExtent

end Aspect

/-! ## Completion as a principal forward cone -/

namespace Completion

variable {World : Type uWorld} {layer : AbstractionLayer World}

/-- A completion contains every fact of its source aspect. -/
def Rel (source target : Aspect layer) : Prop := source ≤ target

/-- Zero-or-more completion steps collapse to one inclusion. -/
theorem reaches_iff {source target : Aspect layer} :
    Mettapedia.Machines.Reaches Rel source target ↔ source ≤ target := by
  constructor
  · intro reaches
    induction reaches with
    | refl => exact le_rfl
    | tail _ step ih => exact le_trans ih step
  · exact Relation.ReflTransGen.single

/-- Extension of a set of aspects: every completion reachable from one of
them.  This is Bennett's `E_X`. -/
def extensionSet (sources : Set (Aspect layer)) : Set (Aspect layer) :=
  Mettapedia.Machines.forwardCone Rel sources

/-- Extension of one aspect: its principal upper set, Bennett's `E_x`. -/
def extension (source : Aspect layer) : Set (Aspect layer) :=
  extensionSet {source}

@[simp]
theorem mem_extensionSet {sources : Set (Aspect layer)} {target : Aspect layer} :
    target ∈ extensionSet sources ↔
      ∃ source ∈ sources, source ≤ target := by
  simp only [extensionSet, Mettapedia.Machines.mem_forwardCone]
  constructor
  · rintro ⟨source, member, reaches⟩
    exact ⟨source, member, reaches_iff.mp reaches⟩
  · rintro ⟨source, member, included⟩
    exact ⟨source, member, reaches_iff.mpr included⟩

@[simp]
theorem mem_extension {source target : Aspect layer} :
    target ∈ extension source ↔ source ≤ target := by
  simp [extension, mem_extensionSet]

/-- Extensions reverse the information order: adding constraints leaves fewer
completions. -/
theorem extension_antitone : Antitone (@extension World layer) := by
  intro left right left_le target right_member
  exact mem_extension.mpr (left_le.trans (mem_extension.mp right_member))

/-- Principal extensions reflect their source order exactly. -/
theorem extension_subset_iff {left right : Aspect layer} :
    extension right ⊆ extension left ↔ left ≤ right := by
  constructor
  · intro included
    exact mem_extension.mp (included (mem_extension.mpr le_rfl))
  · exact fun left_le => extension_antitone left_le

/-- Because aspects are extensional sets of facts, equal completion extensions
identify the source aspects. -/
theorem extension_injective : Function.Injective (@extension World layer) := by
  intro left right equal
  apply le_antisymm
  · exact extension_subset_iff.mp (by rw [equal])
  · exact extension_subset_iff.mp (by rw [← equal])

/-- Extension equality is the syntactic completion equivalence used in the
2024 paper. -/
def ExtensionEquivalent (left right : Aspect layer) : Prop :=
  extension left = extension right

theorem extensionEquivalent_iff_eq {left right : Aspect layer} :
    ExtensionEquivalent left right ↔ left = right := by
  constructor
  · exact fun equal => extension_injective equal
  · intro equal
    cases equal
    rfl

/-- The completion closure inherits the production/safety Galois connection
from the generic cone theory. -/
theorem extensionSet_galois :
    GaloisConnection (@extensionSet World layer)
      (Mettapedia.Machines.alwaysWithin (@Rel World layer)) := by
  change GaloisConnection
    (Mettapedia.Machines.forwardCone (@Rel World layer))
    (Mettapedia.Machines.alwaysWithin (@Rel World layer))
  exact Mettapedia.Machines.gc_forward (@Rel World layer)

end Completion

/-! ## Tasks, policies, and inference -/

/-- A 2024 task `⟨I,O⟩`.  Correct outputs must be completions of inputs. -/
structure Task {World : Type uWorld} (layer : AbstractionLayer World) where
  inputs : Set (Aspect layer)
  correctOutputs : Set (Aspect layer)
  correctOutputs_subset :
    correctOutputs ⊆ Completion.extensionSet inputs

namespace Task

variable {World : Type uWorld} {layer : AbstractionLayer World}

/-- A policy is an aspect constraining how inputs are completed. -/
abbrev Policy (layer : AbstractionLayer World) := Aspect layer

/-- Outputs allowed jointly by a task's inputs and a policy. -/
def inferredOutputs (task : Task layer) (policy : Policy layer) :
    Set (Aspect layer) :=
  Completion.extensionSet task.inputs ∩ Completion.extension policy

/-- Bennett's definition of a correct policy: it selects exactly the correct
outputs among all input completions. -/
def IsCorrectPolicy (task : Task layer) (policy : Policy layer) : Prop :=
  task.inferredOutputs policy = task.correctOutputs

/-- The set `Π_α` of all correct policies for a task. -/
def correctPolicies (task : Task layer) : Set (Policy layer) :=
  {policy | task.IsCorrectPolicy policy}

theorem correctPolicy_sound {task : Task layer} {policy : Policy layer}
    (correct : task.IsCorrectPolicy policy) :
    task.inferredOutputs policy ⊆ task.correctOutputs := by
  rw [correct]

theorem correctPolicy_complete {task : Task layer} {policy : Policy layer}
    (correct : task.IsCorrectPolicy policy) :
    task.correctOutputs ⊆ task.inferredOutputs policy := by
  rw [correct]

/-- A child task has strictly fewer inputs and no correct output unavailable
to its parent.  This is Bennett's generational relation `α ⊏ ω`. -/
def IsChild (child parent : Task layer) : Prop :=
  child.inputs < parent.inputs ∧
    child.correctOutputs ⊆ parent.correctOutputs

theorem IsChild.trans {first second third : Task layer}
    (first_second : first.IsChild second)
    (second_third : second.IsChild third) :
    first.IsChild third :=
  ⟨first_second.1.trans second_third.1,
    first_second.2.trans second_third.2⟩

theorem not_isChild_self (task : Task layer) : ¬ task.IsChild task := by
  intro child
  exact (lt_irrefl task.inputs) child.1

/-- A length-indexed child-to-parent chain.  A numerical task level requires
additional finiteness/well-foundedness and is therefore not imposed here. -/
inductive Generation : Nat → Task layer → Task layer → Prop where
  | refl (task : Task layer) : Generation 0 task task
  | step {n : Nat} {child parent ancestor : Task layer} :
      child.IsChild parent → Generation n parent ancestor →
      Generation (n + 1) child ancestor

theorem Generation.append {m n : Nat} {first middle last : Task layer}
    (left : Generation m first middle) (right : Generation n middle last) :
    Generation (m + n) first last := by
  induction left with
  | refl => simpa using right
  | @step m child parent middle child_parent rest ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Generation.step child_parent (ih right)

end Task

/-! ## No abstraction: semantic compression versus completion identity -/

namespace NoAbstraction

variable {World : Type uWorld}

/-- At the full vocabulary, the semantic extent of an aspect is itself an
available declarative fact. -/
def semanticSingleton
    (aspect : Aspect (AbstractionLayer.full World)) :
    Aspect (AbstractionLayer.full World) where
  facts := {aspect.semanticExtent}
  facts_subset_vocabulary := by simp [AbstractionLayer.full]
  realized := by
    obtain ⟨world, realizes⟩ := aspect.realized
    refine ⟨world, ?_⟩
    intro fact member
    rw [Set.mem_singleton_iff.mp member]
    exact realizes

/-- Every aspect has a one-fact representative with the same realizing worlds
when there is no abstraction.  This is the valid semantic core of Bennett's
2024 subjectivity argument. -/
theorem semanticSingleton_equivalent
    (aspect : Aspect (AbstractionLayer.full World)) :
    (semanticSingleton aspect).SemanticallyEquivalent aspect := by
  ext world
  constructor
  · intro realizes fact member
    exact realizes aspect.semanticExtent (by rfl)
      fact member
  · intro realizes fact member
    rw [Set.mem_singleton_iff.mp member]
    exact realizes

def trueOnly : Fact Bool := {true}

def redundantTop : Fact Bool := Set.univ

/-- A one-fact aspect realized only by `true`. -/
def trueAspect : Aspect (AbstractionLayer.full Bool) where
  facts := {trueOnly}
  facts_subset_vocabulary := by simp [AbstractionLayer.full]
  realized := by
    refine ⟨true, ?_⟩
    simp [trueOnly]

/-- Adding the universally true fact does not change realizing worlds, but it
does change the syntactic set of completions. -/
def redundantTrueAspect : Aspect (AbstractionLayer.full Bool) where
  facts := {trueOnly, redundantTop}
  facts_subset_vocabulary := by simp [AbstractionLayer.full]
  realized := by
    refine ⟨true, ?_⟩
    simp [trueOnly, redundantTop]

theorem trueAspect_semanticallyEquivalent_redundant :
    trueAspect.SemanticallyEquivalent redundantTrueAspect := by
  ext world
  simp [Aspect.semanticExtent, Aspect.Realizes, trueAspect,
    redundantTrueAspect, trueOnly, redundantTop]

/-- Negative control: semantic equivalence does not imply equality of
completion extensions.  Consequently a theorem about semantic behavior may
not silently be used as a theorem about Bennett's syntactic `E_x`. -/
theorem trueAspect_extension_ne_redundant :
    Completion.extension trueAspect ≠
      Completion.extension redundantTrueAspect := by
  intro equal
  have true_mem : trueAspect ∈ Completion.extension trueAspect :=
    Completion.mem_extension.mpr le_rfl
  have false_mem : trueAspect ∈ Completion.extension redundantTrueAspect := by
    rw [← equal]
    exact true_mem
  have included : redundantTrueAspect ≤ trueAspect :=
    Completion.mem_extension.mp false_mem
  have top_member : redundantTop ∈ trueAspect.facts :=
    included (by simp [redundantTrueAspect])
  have top_eq_true : redundantTop = trueOnly := by
    simpa [trueAspect] using top_member
  have false_in_top : false ∈ redundantTop := by simp [redundantTop]
  rw [top_eq_true] at false_in_top
  simp [trueOnly] at false_in_top

end NoAbstraction

#print axioms Completion.extensionSet_galois
#print axioms Task.Generation.append
#print axioms NoAbstraction.semanticSingleton_equivalent
#print axioms NoAbstraction.trueAspect_extension_ne_redundant

end Mettapedia.Enactive
