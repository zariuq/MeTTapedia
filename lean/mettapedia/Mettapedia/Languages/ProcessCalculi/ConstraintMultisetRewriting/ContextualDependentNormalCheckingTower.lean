import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNormalChecking
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNormalizationTower

/-!
# Every finite typed tower store reaches the bidirectional relation

The executable normalizer reaches a fragment on which the existing
bidirectional typing relation is complete. Membership in that fragment is
derived from the original independent typing; it is not an extra restriction
on the unifier's inputs. This theorem does not yet give a successful budget
for the executable checker itself.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentNormalCheckingTower

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentNormalChecking

variable {L : Type} [UniverseLevel.LevelOrder L] (valuation : Nat → L)

theorem head_typing_unique {head first second : LevelTower.Head L}
    (one : (LevelTower.rules L).headTyping head first)
    (two : (LevelTower.rules L).headTyping head second) : first = second := by
  cases one <;> cases two <;> rfl

def Ready {Γ : Context (LevelTower.rules L)} (term : TotalTerm Γ) : Prop :=
  Bidirectional .check term.2.code ∧ Bidirectional .synth term.1.code ∧
    TypedEquality.Normalization.Check (LevelTower.rules L) (TowerModel.setting valuation).roles
      Γ.raw term.2.code term.1.code ∧
    ∃ annotationType, Synth (LevelTower.rules L) (TowerModel.setting valuation).roles
      Γ.raw term.1.code annotationType

theorem ready_of_normal {Γ : Context (LevelTower.rules L)} (term : TotalTerm Γ)
    (normal : ContextualDependentNormalizationTower.TermNormal term) : Ready valuation term := by
  have value := normal_checkable (S := TowerModel.setting valuation) TowerModel.facts
    term.2.code Γ.formed term.2.typed normal.2
  have annotation := normal_type_synthesizes (S := TowerModel.setting valuation) TowerModel.facts
    Γ.formed term.1.isType normal.1
  exact ⟨value, annotation,
    normal_checked (S := TowerModel.setting valuation) TowerModel.facts TowerModel.algebra
      head_typing_unique Γ.formed term.2.typed normal.2,
    Bidirectional.complete (S := TowerModel.setting valuation) TowerModel.facts TowerModel.algebra
      head_typing_unique annotation Γ.formed term.1.formed⟩

def StoreReady {Γ : Context (LevelTower.rules L)} (problem : EquationStore (TotalTerm Γ)) : Prop :=
  ∀ equation ∈ problem, Ready valuation equation.1 ∧ Ready valuation equation.2

/-- Original typed inputs reach the complete relational checking fragment
at one finite normalization budget and at every larger budget. Every future
solution of the original store is still preserved and reflected. -/
theorem eventually_ready_and_equivalent {Γ : Context (LevelTower.rules L)}
    (problem : EquationStore (TotalTerm Γ)) :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      StoreReady valuation (ContextualDependentNormalization.storeAt (S := TowerModel.setting valuation)
        (fun _ => none) TowerModel.facts TowerModel.roots TowerModel.heads larger problem) ∧
      (frames (TowerModel.setting valuation).levels).Equivalent problem
        (ContextualDependentNormalization.storeAt (S := TowerModel.setting valuation)
          (fun _ => none) TowerModel.facts TowerModel.roots TowerModel.heads larger problem) := by
  obtain ⟨fuel, ready⟩ := ContextualDependentNormalizationTower.all_large_normal_and_equivalent valuation problem
  refine ⟨fuel, fun larger enough => ?_⟩
  obtain ⟨normal, equivalent⟩ := ready larger enough
  exact ⟨fun equation member => ⟨ready_of_normal valuation _ (normal equation member).1,
    ready_of_normal valuation _ (normal equation member).2⟩, equivalent⟩

end ContextualDependentNormalCheckingTower
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
