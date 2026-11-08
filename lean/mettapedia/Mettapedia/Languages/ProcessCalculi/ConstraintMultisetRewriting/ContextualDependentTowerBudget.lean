import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentReductionBudget
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEta
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.Elaboration

/-!
# Executable normalization eventually succeeds on typed tower terms

The existing strong-normalization theorem discharges the termination premise
for every typed term in a formed cumulative-tower context. The conclusion is
about the actual fuelled reducer used by the dependent solver, at every
larger budget, and includes directed normality of its output. No closed
inhabitant of the context is needed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentTowerBudget

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ExecutableReduction

variable {L : Type} [UniverseLevel.LevelOrder L]

def reducer : Reducer (LevelTower.rules L) := normalize (LevelTower.rules L) (fun _ => none)

theorem typed_eventually_stable {n : Nat} {Γ : LevelTower.Ctx L n}
    {term type : LevelTower.Tm L n} (formed : CtxFormed (LevelTower.rules L) Γ)
    (typed : Typed (LevelTower.rules L) Γ term type) :
    ∃ fuel result,
      (∀ target, ¬ StrongNormalization.Reduces (LevelTower.rules L) result.val target) ∧
      ∀ larger, fuel ≤ larger → reducer larger term = some result := by
  obtain ⟨fuel, result, stopped, stable⟩ :=
    ContextualDependentReductionBudget.eventually_stable_of_sn (LevelTower.rules L) (fun _ => none)
      (TowerInterpretation.tower_sn formed typed)
  refine ⟨fuel, result, ?_, stable⟩
  exact ContextualDependentReductionBudget.normal_of_stopped (LevelTower.rules L) (fun _ => none)
    (fun _ _ _ impossible => impossible.elim) result.val stopped

theorem term_eventually_stable {Γ : Context (LevelTower.rules L)} {type : TypeOver Γ}
    (term : Term Γ type) :
    ∃ fuel result,
      (∀ target, ¬ StrongNormalization.Reduces (LevelTower.rules L) result.val target) ∧
      ∀ larger, fuel ≤ larger → reducer larger term.code = some result :=
  typed_eventually_stable Γ.formed term.typed

theorem type_eventually_stable {Γ : Context (LevelTower.rules L)} (type : TypeOver Γ) :
    ∃ fuel result,
      (∀ target, ¬ StrongNormalization.Reduces (LevelTower.rules L) result.val target) ∧
      ∀ larger, fuel ≤ larger → reducer larger type.code = some result :=
  typed_eventually_stable Γ.formed type.formed

/-- One budget suffices for both the actual term and its annotation. -/
theorem annotated_eventually_stable {Γ : Context (LevelTower.rules L)} (term : TotalTerm Γ) :
    ∃ fuel value annotation,
      (∀ target, ¬ StrongNormalization.Reduces (LevelTower.rules L) value.val target) ∧
      (∀ target, ¬ StrongNormalization.Reduces (LevelTower.rules L) annotation.val target) ∧
      ∀ larger, fuel ≤ larger →
        reducer larger term.2.code = some value ∧ reducer larger term.1.code = some annotation := by
  obtain ⟨termFuel, value, valueNormal, valueStable⟩ := term_eventually_stable term.2
  obtain ⟨typeFuel, annotation, typeNormal, typeStable⟩ := type_eventually_stable term.1
  exact ⟨max termFuel typeFuel, value, annotation, valueNormal, typeNormal,
    fun larger enough => ⟨valueStable larger ((Nat.le_max_left _ _).trans enough),
      typeStable larger ((Nat.le_max_right _ _).trans enough)⟩⟩

end ContextualDependentTowerBudget
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
