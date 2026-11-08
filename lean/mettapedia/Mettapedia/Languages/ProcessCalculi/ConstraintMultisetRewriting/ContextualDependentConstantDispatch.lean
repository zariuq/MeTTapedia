import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentConstantDiscovery
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentConstantPruningTower

/-!
# Applying principal constant pruning to an actual equation queue

The newest declaration is inspected and checked. Candidate endpoints are
compared with the computed closed independence equation, in both orientations.
Successful recognition applies the principal rule and transports every other
equation. Unrecognized or unfinished candidates remain in the queue.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentConstantDispatch

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate

section HeadTransport

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head} (levels : LevelModel rules L)

theorem head_equivalent {Γ : Context rules} (original canonical : Equation (TotalTerm Γ))
    (rest : EquationStore (TotalTerm Γ))
    (first : (frames levels).E original.1 canonical.1) (second : (frames levels).E original.2 canonical.2) :
    (frames levels).Equivalent (original :: rest) (rest ++ [canonical]) := by
  intro Δ solution
  have firstAt := (frames levels).preserves solution first
  have secondAt := (frames levels).preserves solution second
  constructor
  · intro solved equation member
    rcases List.mem_append.mp member with earlier | last
    · exact solved equation (List.mem_cons_of_mem _ earlier)
    · obtain rfl := List.mem_singleton.mp last
      exact ((frames levels).equivalence Δ).trans (((frames levels).equivalence Δ).symm firstAt)
        (((frames levels).equivalence Δ).trans (solved original List.mem_cons_self) secondAt)
  · intro solved equation member
    rcases List.mem_cons.mp member with rfl | later
    · have compared := solved canonical (List.mem_append_right _ (List.mem_singleton_self _))
      exact ((frames levels).equivalence Δ).trans firstAt
        (((frames levels).equivalence Δ).trans compared (((frames levels).equivalence Δ).symm secondAt))
    · exact solved equation (List.mem_append_left _ later)

end HeadTransport

variable {L : Type} [UniverseLevel.LevelOrder L] (valuation : Nat → L)
variable [DecidableEq (LevelTower.Head L)] [DecidableRel (TowerModel.setting valuation).R.headEq]
  [∀ head, Decidable ((TowerModel.setting valuation).R.isUniverse head)] [DecidableRel (TowerModel.setting valuation).R.cumulative]

def forward (fuel : Nat) {Γ : Context (LevelTower.rules L)} (whole : TypeOver Γ)
    (candidate : Equation (TotalTerm (extend Γ whole))) (rest : EquationStore (TotalTerm (extend Γ whole))) :
    Option (Update (TowerModel.setting valuation).levels (candidate :: rest)) :=
  match ContextualDependentConstantDiscovery.discover (S := TowerModel.setting valuation)
      TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentUnaryConstancy.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentTowerBudget.reducer fuel whole with
  | none => none
  | some found => by
      rcases found with ⟨shape, same⟩
      cases same
      exact do
        let pruned := ContextualDependentConstantPruningTower.prune valuation shape
        match known : pruned.closed.equations with
        | [canonical] =>
            let first ← Conversion.compare (S := TowerModel.setting valuation)
              TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
              ContextualDependentTowerBudget.reducer fuel candidate.1 canonical.1
            let second ← Conversion.compare (S := TowerModel.setting valuation)
              TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
              ContextualDependentTowerBudget.reducer fuel candidate.2 canonical.2
            let singleton : Update (TowerModel.setting valuation).levels [canonical] :=
              pruned.update.rephrase (by intro Δ solution; rw [known])
            return (singleton.keepLeft rest).rephrase
              (head_equivalent (TowerModel.setting valuation).levels candidate canonical rest first.down second.down)
        | _ => none

def orient (fuel : Nat) {Γ : Context (LevelTower.rules L)} (whole : TypeOver Γ)
    (candidate : Equation (TotalTerm (extend Γ whole))) (rest : EquationStore (TotalTerm (extend Γ whole))) :
    Option (Update (TowerModel.setting valuation).levels (candidate :: rest)) :=
  match forward valuation fuel whole candidate rest with
  | some result => some result
  | none => do
      let reversed ← forward valuation fuel whole (candidate.2, candidate.1) rest
      return reversed.rephrase (ContextualDependentDispatch.swap_models (levels := (TowerModel.setting valuation).levels) candidate.1 candidate.2 rest)

def search (fuel : Nat) {Γ : Context (LevelTower.rules L)} (whole : TypeOver Γ) :
    (problem : EquationStore (TotalTerm (extend Γ whole))) → Option (Update (TowerModel.setting valuation).levels problem)
  | [] => none
  | candidate :: rest =>
      match orient valuation fuel whole candidate rest with
      | some result => some result
      | none => do
          let later ← search fuel whole rest
          return later.keepLeft [candidate]

def step (fuel : Nat) {Γ : Context (LevelTower.rules L)} (whole : TypeOver Γ)
    (problem : EquationStore (TotalTerm (extend Γ whole))) : Update (TowerModel.setting valuation).levels problem :=
  (search valuation fuel whole problem).getD (Update.pending (TowerModel.setting valuation).levels problem)

set_option backward.isDefEq.respectTransparency false in
theorem forward_zero {Γ : Context (LevelTower.rules L)} (whole : TypeOver Γ)
    (candidate : Equation (TotalTerm (extend Γ whole))) (rest : EquationStore (TotalTerm (extend Γ whole))) :
    forward valuation 0 whole candidate rest = none := by
  unfold forward
  rw [ContextualDependentConstantDiscovery.discover_zero]

theorem orient_zero {Γ : Context (LevelTower.rules L)} (whole : TypeOver Γ)
    (candidate : Equation (TotalTerm (extend Γ whole))) (rest : EquationStore (TotalTerm (extend Γ whole))) :
    orient valuation 0 whole candidate rest = none := by
  simp only [orient, forward_zero]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem search_zero {Γ : Context (LevelTower.rules L)} (whole : TypeOver Γ)
    (problem : EquationStore (TotalTerm (extend Γ whole))) : search valuation 0 whole problem = none := by
  induction problem with
  | nil => rfl
  | cons candidate rest ih =>
      simp only [search, orient_zero, ih]
      rfl

theorem step_zero {Γ : Context (LevelTower.rules L)} (whole : TypeOver Γ)
    (problem : EquationStore (TotalTerm (extend Γ whole))) :
    step valuation 0 whole problem = Update.pending (TowerModel.setting valuation).levels problem := by
  unfold step
  rw [search_zero]
  rfl

end ContextualDependentConstantDispatch
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
