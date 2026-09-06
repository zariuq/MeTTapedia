import Mettapedia.TypeTheory.ContextualComputationKleisli
import Mettapedia.TypeTheory.WitnessRetainingDependentSequencing

/-!
# Dependent sequencing under the isolated-world handler

The existing contextual program's sequencing operation runs each continuation
in the selected world's state and branch history. Deferred intents compose in
execution order. These statements are proved for arbitrary effectful
continuations, including further state changes and choices.

The dependent instance retains the selected index and its fibre value. Fibre
maps commute with sequencing; changing the index additionally requires the
continuation to respect that change. None of these laws asserts substitution
for an object-language typing judgment or selects a dependent CBPV calculus.
The handler remains the existing isolated-world interpretation, not a new
runtime strategy.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualDependentSequencing

open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.TypeTheory.ContextualComputationKleisli.Program (bindSigma)

universe uState uAnswer uOther uIntent u

namespace WorldResult

/-- Retain a world's history, state and intents while mapping its answer. -/
def mapAnswer {State : Type uState} {Answer : Type uAnswer}
    {Other : Type uOther} {Intent : Type uIntent}
    (function : Answer → Other) (world : WorldResult State Answer Intent) :
    WorldResult State Other Intent :=
  { branch := world.branch, answer := function world.answer,
    state := world.state, intents := world.intents }

/-- A continuation's deferred requests follow the selected prefix's requests. -/
def prependIntents {State : Type uState} {Answer : Type uAnswer}
    {Intent : Type uIntent} (earlier : List Intent)
    (world : WorldResult State Answer Intent) : WorldResult State Answer Intent :=
  { world with intents := earlier ++ world.intents }

end WorldResult

section Handler

variable {State : Type uState} {Answer : Type uAnswer}
  {Other : Type uOther} {Intent : Type uIntent}

/-- Exact sequencing semantics: each selected answer passes its own state and
branch history to the continuation, while its intents precede later intents. -/
theorem runWorldsAt_bind (program : Program State Answer Intent)
    (next : Answer → Program State Other Intent) (state : State) (branch : BranchTrace) :
    runWorldsAt (program.bind next) state branch =
      (runWorldsAt program state branch).flatMap fun prior =>
        (runWorldsAt (next prior.answer) prior.state prior.branch).map
          (WorldResult.prependIntents prior.intents) := by
  induction program generalizing state branch with
  | pure answer =>
      simp only [Program.bind, runWorldsAt, List.flatMap_cons, List.flatMap_nil,
        List.append_nil]
      exact (List.map_id _).symm
  | choose left right leftIH rightIH =>
      simp only [Program.bind, runWorldsAt, leftIH, rightIH, List.flatMap_append]
  | read continuation continuationIH =>
      exact continuationIH state state branch
  | write newState continuation continuationIH =>
      exact continuationIH newState branch
  | intent request continuation continuationIH =>
      simp only [Program.bind, runWorldsAt, continuationIH, List.map_flatMap,
        List.flatMap_map, List.map_map, Function.comp_def, WorldResult.prependIntents]
      rfl

/-- Mapping answers does not reset the selected state, erase branch identity,
or alter deferred intents. -/
theorem runWorldsAt_map (function : Answer → Other)
    (program : Program State Answer Intent) (state : State) (branch : BranchTrace) :
    runWorldsAt (Program.map function program) state branch =
      (runWorldsAt program state branch).map (WorldResult.mapAnswer function) := by
  rw [Program.map, runWorldsAt_bind]
  simp only [runWorldsAt, List.map_cons, List.map_nil,
    WorldResult.prependIntents, List.append_nil]
  exact List.map_eq_flatMap.symm

theorem runWorlds_bind (program : Program State Answer Intent)
    (next : Answer → Program State Other Intent) (state : State) :
    runWorlds (program.bind next) state =
      (runWorlds program state).flatMap fun prior =>
        (runWorldsAt (next prior.answer) prior.state prior.branch).map
          (WorldResult.prependIntents prior.intents) :=
  runWorldsAt_bind program next state []

end Handler

section Dependent

variable {State Intent Index OtherIndex : Type u}
  {Family : Index → Type u} {OtherFamily : OtherIndex → Type u}

/-- The dependent handler law retains the actual selected index, together
with the continuation's result in that index's fibre. -/
theorem runWorldsAt_bindSigma (indices : Program State Index Intent)
    (next : (index : Index) → Program State (Family index) Intent)
    (state : State) (branch : BranchTrace) :
    runWorldsAt (bindSigma indices next) state branch =
      (runWorldsAt indices state branch).flatMap fun prior =>
        (runWorldsAt (next prior.answer) prior.state prior.branch).map fun suffix =>
          WorldResult.prependIntents prior.intents
            (WorldResult.mapAnswer (Sigma.mk prior.answer) suffix) := by
  rw [bindSigma, runWorldsAt_bind]
  simp only [runWorldsAt_map, List.map_map, Function.comp_def]

/-- Membership in the dependent result list supplies an actual selected world
and an actual continuation world, with their complete origin data retained. -/
theorem mem_runWorldsAt_bindSigma_iff (indices : Program State Index Intent)
    (next : (index : Index) → Program State (Family index) Intent)
    (state : State) (branch : BranchTrace) (output : WorldResult State (Sigma Family) Intent) :
    output ∈ runWorldsAt (bindSigma indices next) state branch ↔
      ∃ prior ∈ runWorldsAt indices state branch,
        ∃ suffix ∈ runWorldsAt (next prior.answer) prior.state prior.branch,
          WorldResult.prependIntents prior.intents
            (WorldResult.mapAnswer (Sigma.mk prior.answer) suffix) = output := by
  rw [runWorldsAt_bindSigma]
  simp only [List.mem_flatMap, List.mem_map]

/-- A dependent value map retains its source index unless a new index map is
explicitly supplied. -/
def mapDependent (indexMap : Index → OtherIndex)
    (valueMap : (index : Index) → Family index → OtherFamily (indexMap index)) :
    Sigma Family → Sigma OtherFamily :=
  fun value => ⟨indexMap value.1, valueMap value.1 value.2⟩

/-- Maps of dependent outputs distribute through actual program sequencing.
No equality, invertibility or uniformity of the fibres is required. -/
theorem map_bindSigma (indexMap : Index → OtherIndex)
    (valueMap : (index : Index) → Family index → OtherFamily (indexMap index))
    (indices : Program State Index Intent)
    (next : (index : Index) → Program State (Family index) Intent) :
    Program.map (mapDependent indexMap valueMap) (bindSigma indices next) =
      indices.bind fun index =>
        Program.map (fun value => ⟨indexMap index, valueMap index value⟩)
          (next index) := by
  unfold bindSigma Program.map
  rw [ContextualComputationKleisli.Program.bind_assoc]
  congr 1
  funext index
  rw [ContextualComputationKleisli.Program.bind_assoc]
  rfl

/-- Reindexing to a new dependent continuation is valid when its action is
independently compatible at every source index. A many-to-one index map does
not supply this compatibility automatically. -/
theorem bindSigma_reindex (indexMap : Index → OtherIndex)
    (valueMap : (index : Index) → Family index → OtherFamily (indexMap index))
    (indices : Program State Index Intent)
    (next : (index : Index) → Program State (Family index) Intent)
    (otherNext : (index : OtherIndex) → Program State (OtherFamily index) Intent)
    (compatible : ∀ index, otherNext (indexMap index) =
      Program.map (valueMap index) (next index)) :
    Program.map (mapDependent indexMap valueMap) (bindSigma indices next) =
      bindSigma (Program.map indexMap indices) otherNext := by
  rw [map_bindSigma]
  unfold bindSigma Program.map
  rw [ContextualComputationKleisli.Program.bind_assoc]
  congr 1
  funext index
  simp only [Program.bind]
  rw [compatible index]
  unfold Program.map
  rw [ContextualComputationKleisli.Program.bind_assoc]
  rfl

/-- Pointwise fibre mapping is the special case that changes no index. -/
theorem bindSigma_mapFibre {TargetFamily : Index → Type u}
    (valueMap : (index : Index) → Family index → TargetFamily index)
    (indices : Program State Index Intent)
    (next : (index : Index) → Program State (Family index) Intent) :
    Program.map (mapDependent id valueMap) (bindSigma indices next) =
      bindSigma indices (fun index => Program.map (valueMap index) (next index)) := by
  have law := bindSigma_reindex id valueMap indices next
    (fun index => Program.map (valueMap index) (next index)) (fun _ => rfl)
  have identityMap : Program.map id indices = indices :=
    ContextualComputationKleisli.Program.map_id indices
  rw [identityMap] at law
  exact law

end Dependent

namespace Examples

/-- The selected Boolean genuinely changes the answer type. -/
def Fibre : Bool → Type
  | false => PUnit
  | true => Bool

/-- Each branch writes a different private state before selecting its index. -/
def indices : Program Bool Bool Nat :=
  .choose
    (.write true (.intent 10 (.read fun state => .pure state)))
    (.write false (.intent 20 (.read fun state => .pure state)))

/-- The Boolean fibre observes the selected state, then branches and emits
different intents. The singleton fibre still records its own request. -/
def next : (index : Bool) → Program Bool (Fibre index) Nat
  | false => .intent 30 (.pure PUnit.unit)
  | true => .read fun state =>
      .choose (.intent 40 (.pure state))
        (.write (!state) (.intent 50 (.pure (!state))))

def result : Program Bool (Sigma Fibre) Nat := bindSigma indices next

/-- Exact values, states, occurrence traces and ordered intent lists from
genuinely dependent, state-sensitive sequencing. -/
theorem selected_worlds :
    runWorlds result false =
      [{ branch := [false, false], answer := ⟨true, true⟩,
         state := true, intents := [10, 40] },
       { branch := [true, false], answer := ⟨true, false⟩,
         state := false, intents := [10, 50] },
       { branch := [true], answer := ⟨false, PUnit.unit⟩,
         state := false, intents := [20, 30] }] := by
  rfl

/-- Resetting every continuation to the initial state is not the handler's
sequencing operation. Even the answer observations then differ. -/
theorem initial_state_reuse_changes_answers :
    (runWorlds result false).map WorldResult.answer ≠
      ((runWorlds indices false).flatMap fun prior =>
        (runWorldsAt (Program.map (Sigma.mk prior.answer) (next prior.answer))
          false prior.branch).map
            (WorldResult.prependIntents prior.intents)).map WorldResult.answer := by
  letI (index : Bool) : DecidableEq (Fibre index) := by
    cases index with
    | false => exact inferInstanceAs (DecidableEq PUnit)
    | true => exact inferInstanceAs (DecidableEq Bool)
  decide

/-- No common carrier represents these two fibres bidirectionally. -/
theorem fibres_not_uniform :
    ¬ Nonempty
      (WitnessRetainingDependentSequencing.UniformFibreRepresentation Fibre) := by
  intro uniform
  obtain ⟨representation⟩ := uniform
  have equivalence : PUnit ≃ Bool :=
    (representation.identify false).trans (representation.identify true).symm
  have same : equivalence.symm false = equivalence.symm true := Subsingleton.elim _ _
  have impossible : (false : Bool) = true := equivalence.symm.injective same
  cases impossible

/-- An observation may still hide the index lossily. It is not an exact
dependent result representation. -/
def observe : Sigma Fibre → Bool
  | ⟨false, _⟩ => false
  | ⟨true, value⟩ => value

theorem observation_loses_index :
    observe ⟨false, PUnit.unit⟩ = observe ⟨true, false⟩ ∧
      (⟨false, PUnit.unit⟩ : Sigma Fibre) ≠ ⟨true, false⟩ := by
  constructor
  · rfl
  · intro equal
    have impossible := congrArg Sigma.fst equal
    cases impossible

/-- Collapsing indices does not manufacture a compatible continuation. -/
theorem collapsed_index_requires_compatibility :
    ¬ ∃ otherNext : PUnit → Program Bool Bool Nat,
      ∀ index : Bool, otherNext PUnit.unit = .pure index := by
  rintro ⟨otherNext, compatible⟩
  have impossible : (Program.pure false : Program Bool Bool Nat) = .pure true :=
    (compatible false).symm.trans (compatible true)
  cases impossible

end Examples

#print axioms runWorldsAt_bind
#print axioms runWorldsAt_map
#print axioms runWorldsAt_bindSigma
#print axioms mem_runWorldsAt_bindSigma_iff
#print axioms map_bindSigma
#print axioms bindSigma_reindex
#print axioms bindSigma_mapFibre
#print axioms Examples.selected_worlds
#print axioms Examples.initial_state_reuse_changes_answers
#print axioms Examples.fibres_not_uniform
#print axioms Examples.observation_loses_index
#print axioms Examples.collapsed_index_requires_compatibility

end Mettapedia.TypeTheory.ContextualDependentSequencing
