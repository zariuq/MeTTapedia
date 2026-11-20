import Mettapedia.Machines.SemiNaiveInsertSaturation
import Mathlib.Data.Finset.Union

/-!
# Rule shards and data shards in append-only propagation

A frozen, complete fact view can be shared by workers that inspect
different rule shards. Merging their heads is the ordinary propagation
round. Giving the workers different fact views is a different operation:
it is safe for insert-only consequences, but can miss a join.

The exact data-shard condition concerns heads, not every spelling of a
rule that can derive them. Uniform distributivity holds precisely when
each rule head can follow from zero or one of that rule's own premises.
For completed closures, the test is derivability rather than one-round
derivability; the two tests need not coincide.

This contract observes finite sets of ground facts. It does not merge
consuming firings, retain proof multiplicity, or prescribe a scheduler.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.PropagationShards

open Mettapedia.Logic

section DataShards

variable {Fact Worker : Type*} [DecidableEq Fact]

private theorem head_in_step {program : LP.PropProgram Fact} {facts : Finset Fact}
    {rule : LP.PropRule Fact} (declared : rule ∈ program) (enabled : rule.premises ⊆ facts) :
    rule.head ∈ LP.step program facts :=
  Finset.mem_union_right _ ((LP.mem_fired_iff _ _ _).mpr ⟨rule, declared, enabled, rfl⟩)

/-- Independently compute on the local inputs and merge their outputs. -/
def dataRound (program : LP.PropProgram Fact) (workers : Finset Worker)
    (views : Worker → Finset Fact) : Finset Fact :=
  workers.biUnion fun worker => LP.step program (views worker)

/-- A positive consequence computed on an older or partial view stays
safe under growth. This is not equality of the complete read transcript. -/
theorem dataRound_subset_live_step (program : LP.PropProgram Fact) (workers : Finset Worker)
    (views : Worker → Finset Fact) (live : Finset Fact)
    (subviews : ∀ worker ∈ workers, views worker ⊆ live) :
    dataRound program workers views ⊆ LP.step program live := by
  intro fact observed
  obtain ⟨worker, present, localResult⟩ := Finset.mem_biUnion.mp observed
  exact LP.step_monotone program (subviews worker present) localResult

private theorem seeds_subset_dataRound (program : LP.PropProgram Fact) (workers : Finset Worker)
    (views : Worker → Finset Fact) :
    workers.biUnion views ⊆ dataRound program workers views := by
  intro fact observed
  obtain ⟨worker, present, localFact⟩ := Finset.mem_biUnion.mp observed
  exact Finset.mem_biUnion.mpr ⟨worker, present, LP.step_inflationary program _ localFact⟩

/-- A data-sharded round is exact iff every enabled head that is not
already known has a rule wholly supported by some worker's view.
That derivation may use a different rule for the same head. -/
theorem dataRound_eq_iff (program : LP.PropProgram Fact) (workers : Finset Worker)
    (views : Worker → Finset Fact) :
    dataRound program workers views = LP.step program (workers.biUnion views) ↔
      ∀ rule ∈ program, rule.premises ⊆ workers.biUnion views →
        rule.head ∈ workers.biUnion views ∨
          ∃ worker ∈ workers, ∃ witness ∈ program,
            witness.premises ⊆ views worker ∧ witness.head = rule.head := by
  constructor
  · intro exactRound rule declared enabled
    have head : rule.head ∈ dataRound program workers views :=
      exactRound.symm ▸ head_in_step declared enabled
    obtain ⟨worker, member, localHead⟩ := Finset.mem_biUnion.mp head
    rcases Finset.mem_union.mp localHead with known | emitted
    · exact Or.inl (Finset.mem_biUnion.mpr ⟨worker, member, known⟩)
    · exact Or.inr ⟨worker, member, (LP.mem_fired_iff _ _ _).mp emitted⟩
  · intro coverage
    apply Finset.Subset.antisymm
    · apply dataRound_subset_live_step
      exact fun worker member _ present => Finset.mem_biUnion.mpr ⟨worker, member, present⟩
    · intro fact result
      have retained := seeds_subset_dataRound program workers views
      rcases Finset.mem_union.mp result with known | emitted
      · exact retained known
      · obtain ⟨rule, declared, enabled, rfl⟩ := (LP.mem_fired_iff _ _ _).mp emitted
        rcases coverage rule declared enabled with known | ⟨worker, member, witness, allowed, inputs, name⟩
        · exact retained known
        · exact Finset.mem_biUnion.mpr ⟨worker, member, name ▸ head_in_step allowed inputs⟩

/-- A check on the rules' own finite premises. Syntactically
multi-premise rules may pass if their conclusion is otherwise available. -/
def SingletonSupport (program : LP.PropProgram Fact) : Prop :=
  ∀ rule ∈ program, rule.head ∈ LP.step program ∅ ∨
    ∃ fact ∈ rule.premises, rule.head ∈ LP.step program {fact}

private theorem mem_of_one_seed (operation : Finset Fact → Finset Fact)
    (preserves : ∀ left right : Finset Fact, Disjoint left right →
      operation (left ∪ right) = operation left ∪ operation right)
    (seed : Finset Fact) {fact : Fact} (produced : fact ∈ operation seed) :
    fact ∈ operation ∅ ∨ ∃ one ∈ seed, fact ∈ operation {one} := by
  induction seed using Finset.induction_on with
  | empty => exact Or.inl produced
  | @insert one rest new ih =>
      have factor := preserves {one} rest (Finset.disjoint_singleton_left.mpr new)
      rw [Finset.singleton_union] at factor
      rcases Finset.mem_union.mp (factor ▸ produced) with mine | theirs
      · exact Or.inr ⟨one, Finset.mem_insert_self _ _, mine⟩
      · rcases ih theirs with constant | ⟨other, member, consequence⟩
        · exact Or.inl constant
        · exact Or.inr ⟨other, Finset.mem_insert_of_mem member, consequence⟩

theorem singletonSupport_of_disjoint_union (program : LP.PropProgram Fact)
    (preserves : ∀ left right : Finset Fact, Disjoint left right →
      LP.step program (left ∪ right) = LP.step program left ∪ LP.step program right) :
    SingletonSupport program := by
  intro rule declared
  exact mem_of_one_seed (LP.step program) preserves rule.premises
    (head_in_step declared (Finset.Subset.refl _))

theorem union_of_singletonSupport (program : LP.PropProgram Fact) (licensed : SingletonSupport program)
    (left right : Finset Fact) :
    LP.step program (left ∪ right) = LP.step program left ∪ LP.step program right := by
  apply Finset.Subset.antisymm
  · intro fact result
    rcases Finset.mem_union.mp result with old | emitted
    · rcases Finset.mem_union.mp old with earlier | later
      · exact Finset.mem_union_left _ (LP.step_inflationary program _ earlier)
      · exact Finset.mem_union_right _ (LP.step_inflationary program _ later)
    · obtain ⟨rule, declared, enabled, rfl⟩ := (LP.mem_fired_iff _ _ _).mp emitted
      rcases licensed rule declared with constant | ⟨one, supplied, produces⟩
      · exact Finset.mem_union_left _ (LP.step_monotone program (Finset.empty_subset _) constant)
      · rcases Finset.mem_union.mp (enabled supplied) with earlier | later
        · exact Finset.mem_union_left _ (LP.step_monotone program (Finset.singleton_subset_iff.mpr earlier)
            produces)
        · exact Finset.mem_union_right _ (LP.step_monotone program (Finset.singleton_subset_iff.mpr later)
            produces)
  · intro fact result
    rcases Finset.mem_union.mp result with earlier | later
    · exact LP.step_monotone program Finset.subset_union_left earlier
    · exact LP.step_monotone program Finset.subset_union_right later

/-- Testing all disjoint two-way splits already detects every obstruction
to distributing a round over arbitrary unions. -/
theorem step_disjoint_union_iff (program : LP.PropProgram Fact) :
    (∀ left right : Finset Fact, Disjoint left right →
      LP.step program (left ∪ right) = LP.step program left ∪ LP.step program right) ↔
    SingletonSupport program :=
  ⟨singletonSupport_of_disjoint_union program,
    fun licensed left right _ => union_of_singletonSupport program licensed left right⟩

theorem step_union_iff (program : LP.PropProgram Fact) :
    (∀ left right : Finset Fact,
      LP.step program (left ∪ right) = LP.step program left ∪ LP.step program right) ↔
    SingletonSupport program :=
  ⟨fun all => singletonSupport_of_disjoint_union program (fun left right _ => all left right),
    union_of_singletonSupport program⟩

end DataShards

section CompletedClosures

variable {Fact : Type*} [DecidableEq Fact] [Fintype Fact]

def SingletonClosureSupport (program : LP.PropProgram Fact) : Prop :=
  ∀ rule ∈ program, rule.head ∈ LP.saturate program ∅ ∨
    ∃ fact ∈ rule.premises, rule.head ∈ LP.saturate program {fact}

private theorem closure_subset_of_closed (program : LP.PropProgram Fact) (seed closed : Finset Fact)
    (contains : seed ⊆ closed)
    (stable : ∀ rule ∈ program, rule.premises ⊆ closed → rule.head ∈ closed) :
    LP.saturate program seed ⊆ closed :=
  fun fact member => LP.derivable_subset_of_closed program seed closed contains stable fact
    (LP.saturate_sound program seed fact member)

private theorem closure_into_closure (program : LP.PropProgram Fact) {seed target : Finset Fact}
    (inside : seed ⊆ LP.saturate program target) :
    LP.saturate program seed ⊆ LP.saturate program target :=
  closure_subset_of_closed program seed _ inside
    (fun _ allowed enabled => LP.rule_closed_saturate program target allowed enabled)

/-- Computing complete local closures before merging permits alternative
derivations with several rounds. That is a different licence from
distributing a single round over the input split. -/
theorem saturate_union_iff (program : LP.PropProgram Fact) :
    (∀ left right : Finset Fact,
      LP.saturate program (left ∪ right) =
        LP.saturate program left ∪ LP.saturate program right) ↔ SingletonClosureSupport program := by
  constructor
  · intro distributes rule declared
    exact mem_of_one_seed (LP.saturate program) (fun left right _ => distributes left right)
      rule.premises (LP.rule_closed_saturate program rule.premises declared
        (LP.saturate_contains_facts program _))
  · intro licensed left right
    apply Finset.Subset.antisymm
    · apply closure_subset_of_closed
      · intro fact member
        rcases Finset.mem_union.mp member with localLeft | localRight
        · exact Finset.mem_union_left _ (LP.saturate_contains_facts program _ localLeft)
        · exact Finset.mem_union_right _ (LP.saturate_contains_facts program _ localRight)
      · intro rule declared enabled
        rcases licensed rule declared with constant | ⟨one, used, produces⟩
        · exact Finset.mem_union_left _ (closure_into_closure program (Finset.empty_subset _) constant)
        · rcases Finset.mem_union.mp (enabled used) with localLeft | localRight
          · exact Finset.mem_union_left _ (closure_into_closure program
              (Finset.singleton_subset_iff.mpr localLeft) produces)
          · exact Finset.mem_union_right _ (closure_into_closure program
              (Finset.singleton_subset_iff.mpr localRight) produces)
    · intro fact member
      rcases Finset.mem_union.mp member with localLeft | localRight
      · exact closure_into_closure program
          (Finset.subset_union_left.trans (LP.saturate_contains_facts program _)) localLeft
      · exact closure_into_closure program
          (Finset.subset_union_right.trans (LP.saturate_contains_facts program _)) localRight

end CompletedClosures

section RuleShards

open Mettapedia.Machines.RecursiveInsert.SemiNaive (State heads mem_heads round Invariant round_known)

variable {Fact : Type} {Worker : Type*} [DecidableEq Fact]

/-- Rule shards share the same known facts and delta. Their union of
selected heads is exact even if assignments to workers overlap. -/
theorem heads_over_rule_shards (workers : Finset Worker) (part : Worker → LP.PropProgram Fact)
    (state : State Fact) :
    heads (workers.biUnion part) state = workers.biUnion (fun worker => heads (part worker) state) := by
  ext fact
  simp only [mem_heads, Finset.mem_biUnion]
  constructor
  · rintro ⟨rule, ⟨worker, active, declared⟩, enabled, hot, target⟩
    exact ⟨worker, active, rule, declared, enabled, hot, target⟩
  · rintro ⟨worker, active, rule, declared, enabled, hot, target⟩
    exact ⟨rule, ⟨worker, active, declared⟩, enabled, hot, target⟩

def ruleShardedRound (workers : Finset Worker) (part : Worker → LP.PropProgram Fact)
    (state : State Fact) : State Fact :=
  let fresh := (workers.biUnion fun worker => heads (part worker) state) \ state.known
  ⟨state.known ∪ fresh, fresh⟩

theorem ruleShardedRound_eq (workers : Finset Worker) (part : Worker → LP.PropProgram Fact)
    (state : State Fact) :
    ruleShardedRound workers part state = round (workers.biUnion part) state := by
  simp only [ruleShardedRound, round, heads_over_rule_shards]

/-- The partitioned computation inherits the already-proved round
licence. No execution order for its pure workers has to be chosen. -/
theorem ruleShardedRound_known (workers : Finset Worker) (part : Worker → LP.PropProgram Fact)
    (state : State Fact) (valid : Invariant (workers.biUnion part) state) :
    (ruleShardedRound workers part state).known = LP.step (workers.biUnion part) state.known :=
  (congrArg State.known (ruleShardedRound_eq workers part state)).trans
    (round_known (workers.biUnion part) state valid)

end RuleShards

namespace Controls

private def both : LP.PropRule Nat := ⟨{0, 1}, 2⟩
private def justA : LP.PropRule Nat := ⟨{0}, 2⟩
private def splitViews (worker : Bool) : Finset Nat := if worker then {0} else {1}

/-- Monotonicity and add-only writes do not distribute conjunction
over an arbitrary partition of its input data. -/
theorem split_data_misses_join :
    dataRound {both} ({false, true} : Finset Bool) splitViews = {0, 1} ∧
      LP.step {both} {0, 1} = {0, 1, 2} := by
  decide +kernel

/-- A wider rule may be redundant: the singleton rule covers the same
head, so all data splits are then safe. -/
theorem redundant_join_is_union_preserving :
    both.premises.card = 2 ∧
      ∀ left right : Finset Nat,
        LP.step {both, justA} (left ∪ right) = LP.step {both, justA} left ∪ LP.step {both, justA} right := by
  refine ⟨by decide, (step_union_iff _).mpr ?_⟩
  intro rule member
  rcases Finset.mem_insert.mp member with rfl | later
  · exact Or.inr ⟨0, by decide, by decide +kernel⟩
  · have same := Finset.mem_singleton.mp later
    subst rule
    exact Or.inr ⟨0, by decide, by decide +kernel⟩

private def wide : LP.PropRule (Fin 4) := ⟨{0, 1}, 3⟩
private def first : LP.PropRule (Fin 4) := ⟨{0}, 2⟩
private def second : LP.PropRule (Fin 4) := ⟨{2}, 3⟩
private def twoRoutes : LP.PropProgram (Fin 4) := {wide, first, second}

/-- A singleton input reaches the same head by two unary rules, but
the wide rule reaches that head sooner when both inputs are available. -/
theorem closure_merge_can_be_exact_even_when_one_round_is_not :
    LP.step twoRoutes {0, 1} ≠ LP.step twoRoutes {0} ∪ LP.step twoRoutes {1} ∧
    (∀ left right : Finset (Fin 4),
      LP.saturate twoRoutes (left ∪ right) =
        LP.saturate twoRoutes left ∪ LP.saturate twoRoutes right) := by
  refine ⟨by decide +kernel, (saturate_union_iff _).mpr ?_⟩
  intro rule member
  simp only [twoRoutes, Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with rfl | rfl | rfl
  · exact Or.inr ⟨0, by decide, by decide +kernel⟩
  · exact Or.inr ⟨0, by decide, by decide +kernel⟩
  · exact Or.inr ⟨2, by decide, by decide +kernel⟩

end Controls

#print axioms dataRound_subset_live_step
#print axioms dataRound_eq_iff
#print axioms step_disjoint_union_iff
#print axioms step_union_iff
#print axioms saturate_union_iff
#print axioms heads_over_rule_shards
#print axioms ruleShardedRound_eq
#print axioms ruleShardedRound_known
#print axioms Controls.split_data_misses_join
#print axioms Controls.redundant_join_is_union_preserving
#print axioms Controls.closure_merge_can_be_exact_even_when_one_round_is_not

end Mettapedia.GSLT.Contracts.PropagationShards
