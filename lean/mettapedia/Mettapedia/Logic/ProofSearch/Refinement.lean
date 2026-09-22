import Mettapedia.Logic.ProofSearch.Planning
import Mathlib.Data.Fintype.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Finite indexed proof obligations and their reconstruction

A refinement is one authorized backward inference, not an exhaustive search
space. All of its indexed premises are required; alternative refinements are
separate choices. Reconstruction consumes actual evidence at each premise's
own query. Finite composition retains a dependent pair of occurrence indices,
so equal queries or answers do not collapse distinct obligations.

This planning capability does not add fields to the language definition or
choose a search controller. Missing premise evidence leaves that route
unresolved; it does not refute the original goal. Native checking and
compilation remain separate boundaries.
-/


set_option autoImplicit false

namespace Mettapedia.Logic.ProofSearch
namespace ProofObligations

universe u v

open scoped BigOperators

variable {Goal : Type u} {Solution : Goal → Type u}

/-- The finite premises of one inference and its executable reconstruction. -/
structure Refinement (Solution : Goal → Type u) (goal : Goal) where
  Premise : Type u
  [finite : Fintype Premise]
  query : Premise → Goal
  rebuild : (∀ index, Solution (query index)) → Solution goal

attribute [instance] Refinement.finite

namespace Refinement

variable {goal : Goal}

/-- Reconstruction is partial until every premise has actual evidence. -/
def tryRebuild (route : Refinement Solution goal)
    (candidate : ∀ index, Option (Solution (route.query index))) : Option (Solution goal) :=
  if supplied : ∀ index, (candidate index).isSome = true then
    some (route.rebuild (fun index => (candidate index).get (supplied index)))
  else none

/-- A returned proof retains the actual answers at every premise and the
exact reconstruction equation, not only their existence or semantic truth. -/
theorem tryRebuild_eq_some_iff (route : Refinement Solution goal)
    (candidate : ∀ index, Option (Solution (route.query index))) (proof : Solution goal) :
    route.tryRebuild candidate = some proof ↔
      ∃ answers, (∀ index, candidate index = some (answers index)) ∧
        route.rebuild answers = proof := by
  unfold tryRebuild
  split
  · rename_i supplied
    constructor
    · intro returned
      exact ⟨fun index => (candidate index).get (supplied index),
        fun index => (Option.some_get (supplied index)).symm, Option.some.inj returned⟩
    · rintro ⟨answers, actual, rebuilt⟩
      have same : (fun index => (candidate index).get (supplied index)) = answers := by
        funext index
        apply Option.some.inj
        exact (Option.some_get (supplied index)).trans (actual index)
      rw [same, rebuilt]
  · rename_i missing
    constructor
    · intro impossible; cases impossible
    · rintro ⟨answers, actual, _⟩
      exact False.elim (missing (fun index => by rw [actual index]; rfl))

/-- Missing evidence is not silently supplied by the reconstruction. -/
theorem tryRebuild_eq_none_iff (route : Refinement Solution goal)
    (candidate : ∀ index, Option (Solution (route.query index))) :
    route.tryRebuild candidate = none ↔ ∃ index, candidate index = none := by
  simp only [tryRebuild]
  split
  · rename_i supplied
    simp only [Option.some_ne_none, false_iff]
    rintro ⟨index, missing⟩
    simpa only [missing, Option.isSome_none, Bool.false_eq_true] using supplied index
  · rename_i missing
    constructor
    · intro _
      classical
      obtain ⟨index, absent⟩ := Classical.not_forall.mp missing
      cases answer : candidate index with
      | none => exact ⟨index, answer⟩
      | some proof => exact False.elim (absent (by simp [answer]))
    · intro _; rfl

/-- A supplied proof discharges one obligation without inventing further ones. -/
def discharged (proof : Solution goal) : Refinement Solution goal where
  Premise := ULift.{u} (Fin 0)
  query index := Fin.elim0 index.down
  rebuild _ := proof

/-- The identity refinement is a genuine outstanding obligation. -/
def awaiting (goal : Goal) : Refinement Solution goal where
  Premise := ULift.{u} (Fin 1)
  query _ := goal
  rebuild answers := answers ⟨0⟩

/-- Substitute a finite refinement for each premise, retaining the outer
and inner occurrence indices and their possibly different scoped queries. -/
def comp (outer : Refinement Solution goal)
    (inner : ∀ index, Refinement Solution (outer.query index)) :
    Refinement Solution goal where
  Premise := Sigma fun index => (inner index).Premise
  query occurrence := (inner occurrence.1).query occurrence.2
  rebuild answers := outer.rebuild (fun index =>
    (inner index).rebuild (fun occurrence => answers ⟨index, occurrence⟩))

/-- Rebracketing three actual inference layers preserves their exact proof,
not merely its conclusion. The premise correspondence is the Sigma associator. -/
theorem rebuild_assoc (outer : Refinement Solution goal)
    (middle : ∀ index, Refinement Solution (outer.query index))
    (inner : ∀ index occurrence, Refinement Solution ((middle index).query occurrence))
    (answers : ∀ index occurrence leaf,
      Solution ((inner index occurrence).query leaf)) :
    ((outer.comp middle).comp (fun occurrence => inner occurrence.1 occurrence.2)).rebuild
        (fun occurrence => answers occurrence.1.1 occurrence.1.2 occurrence.2) =
      (outer.comp (fun index => (middle index).comp (inner index))).rebuild
        (fun occurrence => answers occurrence.1 occurrence.2.1 occurrence.2.2) := rfl

@[simp] theorem rebuild_awaiting (route : Refinement Solution goal)
    (answers : ∀ index, Solution (route.query index)) :
    (route.comp (fun index => awaiting (route.query index))).rebuild
      (fun occurrence => answers occurrence.1) = route.rebuild answers := rfl

/-- Solving composed obligations and solving their inner routes first
return exactly the same proof, including failed/missing-premise behavior. -/
theorem tryRebuild_comp (outer : Refinement Solution goal)
    (inner : ∀ index, Refinement Solution (outer.query index))
    (candidate : ∀ occurrence,
      Option (Solution ((outer.comp inner).query occurrence))) :
    (outer.comp inner).tryRebuild candidate =
      outer.tryRebuild (fun index =>
        (inner index).tryRebuild (fun occurrence => candidate ⟨index, occurrence⟩)) := by
  apply Option.ext
  intro proof
  rw [tryRebuild_eq_some_iff, tryRebuild_eq_some_iff]
  constructor
  · rintro ⟨answers, actual, rebuilt⟩
    refine ⟨fun index => (inner index).rebuild (fun occurrence => answers ⟨index, occurrence⟩),
      ?_, rebuilt⟩
    intro index
    apply (tryRebuild_eq_some_iff _ _ _).2
    exact ⟨fun occurrence => answers ⟨index, occurrence⟩,
      fun occurrence => actual ⟨index, occurrence⟩, rfl⟩
  · rintro ⟨answers, actual, rebuilt⟩
    have available : ∀ index, ∃ leaves,
        (∀ occurrence, candidate ⟨index, occurrence⟩ = some (leaves occurrence)) ∧
          (inner index).rebuild leaves = answers index := fun index =>
      (tryRebuild_eq_some_iff _ _ _).1 (actual index)
    classical
    choose leaves provided reconstruct using available
    refine ⟨fun occurrence => leaves occurrence.1 occurrence.2,
      fun occurrence => provided occurrence.1 occurrence.2, ?_⟩
    change outer.rebuild (fun index => (inner index).rebuild (leaves index)) = proof
    have same : (fun index => (inner index).rebuild (leaves index)) = answers := by
      funext index; exact reconstruct index
    rw [same, rebuilt]

/-- Each alternative route needs only its own premises, not the premises of
every competing route. The chosen route identity remains in the receipt. -/
structure Choice (routes : List (Refinement Solution goal)) where
  occurrence : Fin routes.length
  answers : ∀ index, Solution ((routes.get occurrence).query index)

def Choice.proof {routes : List (Refinement Solution goal)} (choice : Choice routes) :
    Solution goal := (routes.get choice.occurrence).rebuild choice.answers

/-- Reconstruction is a stage retaining the exact supplied premise proofs. -/
def stage (route : Refinement Solution goal) :
    Stage (∀ index, Solution (route.query index)) (Solution goal) where
  Evidence answers proof := PLift (route.rebuild answers = proof)

/-- Arbitrary resource interpretation of the same reconstruction receipt.
No search priority or algebraic grade is promoted to proof authority. -/
def cost (route : Refinement Solution goal) {Grade : Type v} [AddMonoid Grade]
    (charge : (∀ index, Solution (route.query index)) → Grade) : Stage.Cost route.stage Grade where
  charge := fun {input} {_output} _ => charge input

/-- Evidence for the AND premises is a dependent family of actual solved
runs. Each run keeps its own indexed plan, initial state, and transition trace. -/
def premiseStage (route : Refinement Solution goal)
    {counter : CounterSystem Goal Solution} {Constraint : Goal → Type u}
    (plans : ∀ index, System Solution counter Constraint (route.query index)) :
    Stage Unit (∀ index, Solution (route.query index)) where
  Evidence _ answers := ∀ index, System.Run (plans index) (.solved (answers index))

/-- Unordered independent work accounting requires commutative addition.
It sums indexed run receipts without identifying equal goals or equal proofs;
this is not an ordered effect trace or a scheduling policy. -/
def premiseCost (route : Refinement Solution goal)
    {counter : CounterSystem Goal Solution} {Constraint : Goal → Type u}
    (plans : ∀ index, System Solution counter Constraint (route.query index))
    {Grade : Type v} [AddCommMonoid Grade]
    (costs : ∀ index, System.CostModel (plans index) Grade) :
    Stage.Cost (route.premiseStage plans) Grade where
  charge runs := ∑ index, (costs index).total (runs index).trace

/-- Composed evidence keeps every actual solved child run, all returned
trees, and the exact root reconstruction equation. -/
def reconstructionStage (route : Refinement Solution goal)
    {counter : CounterSystem Goal Solution} {Constraint : Goal → Type u}
    (plans : ∀ index, System Solution counter Constraint (route.query index)) :
    Stage Unit (Solution goal) := (route.premiseStage plans).comp route.stage

def reconstructionCost (route : Refinement Solution goal)
    {counter : CounterSystem Goal Solution} {Constraint : Goal → Type u}
    (plans : ∀ index, System Solution counter Constraint (route.query index))
    {Grade : Type v} [AddCommMonoid Grade]
    (costs : ∀ index, System.CostModel (plans index) Grade)
    (charge : (∀ index, Solution (route.query index)) → Grade) :
    Stage.Cost (route.reconstructionStage plans) Grade :=
  (route.premiseCost plans costs).comp (route.cost charge)

/-- Costs are read from the very runs and premise trees in the composed
receipt, not from rerunning the providers or rebuilding another proof. -/
theorem reconstruction_charge (route : Refinement Solution goal)
    {counter : CounterSystem Goal Solution} {Constraint : Goal → Type u}
    (plans : ∀ index, System Solution counter Constraint (route.query index))
    {Grade : Type v} [AddCommMonoid Grade]
    (costs : ∀ index, System.CostModel (plans index) Grade)
    (charge : (∀ index, Solution (route.query index)) → Grade)
    {proof : Solution goal} (receipt : (route.reconstructionStage plans).Evidence () proof) :
    (route.reconstructionCost plans costs charge).charge receipt =
      (∑ index, (costs index).total (receipt.2.1 index).trace) + charge receipt.1 := rfl

end Refinement

#print axioms Refinement.tryRebuild_eq_some_iff
#print axioms Refinement.tryRebuild_eq_none_iff
#print axioms Refinement.tryRebuild_comp
#print axioms Refinement.rebuild_assoc

end ProofObligations
end Mettapedia.Logic.ProofSearch
