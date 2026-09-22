import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveDependentComputation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.DeclarationFormation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.SigmaConversionBoundary
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeConversionSkeleton
import Mettapedia.TypeTheory.ContextualDependentSequencing

/-! # Concrete examples of FormationSensitiveDependentComputation -/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
set_option autoImplicit false
open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.TypeTheory.ContextualComputationKleisli.Program (bindSigma)
open Mettapedia.TypeTheory.ContextualDependentSequencing

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitive.DependentComputation

namespace Examples

def ground {n : Nat} : Tower.Tm n := .head .legacyGround

def context : Tower.Ctx 2 := .snoc (.snoc .nil ground) ground

theorem context_formed : ContextFormation Tower.rules context :=
  .snoc (.snoc .nil (.headType .legacyGround) (.sort Tower.zero))
    (.headType .legacyGround) (.sort Tower.zero)

def older : TypedValue Tower.rules context ground := ⟨.var 1, context_formed, .var 1⟩
def newer : TypedValue Tower.rules context ground := ⟨.var 0, context_formed, .var 0⟩

/-- The selected term occurs in both endpoints of an actual native identity type. -/
def family : Tower.Tm 3 := .id ground (.var 0) (.var 0)

theorem sigma_formed : Judgment Tower.rules context (.sigma ground family)
    (sortTm (.max Tower.zero Tower.zero)) := by
  refine ⟨context_formed, ?_⟩
  exact .sigmaForm (.headType .legacyGround) (.sort Tower.zero)
    (.idForm (.headType .legacyGround) (.sort Tower.zero) (.var 0) (.var 0))
    (.sort Tower.zero) (.sorts Tower.zero Tower.zero)

def reflexivity (first : TypedValue Tower.rules context ground) :
    TypedValue Tower.rules context (inst0 first.val family) :=
  ⟨.refl first.val, context_formed, by
    simpa only [family, inst0, subst, ground, subst0_zero] using
      (Typing.reflIntro first.property.typing)⟩

def indices : Program Bool (TypedValue Tower.rules context ground) Nat :=
  .choose
    (.write true (.intent 10 (.pure older)))
    (.write false (.intent 20 (.pure newer)))

/-- The effect inspects the selected world's state; the value remains in
the fibre of the selected native term, independently of that effect. -/
def next (first : TypedValue Tower.rules context ground) :
    Program Bool (TypedValue Tower.rules context (inst0 first.val family)) Nat :=
  .read fun state => .intent (if state then 30 else 40) (.pure (reflexivity first))

def result : Program Bool (TypedValue Tower.rules context (.sigma ground family)) Nat :=
  sigmaProgram sigma_formed (.sort _) indices next

theorem selected_worlds :
    runWorlds result false =
      [{ branch := [false], answer := sigmaPair sigma_formed (.sort _) older (reflexivity older),
          state := true, intents := [10, 30] },
       { branch := [true], answer := sigmaPair sigma_formed (.sort _) newer (reflexivity newer),
          state := false, intents := [20, 40] }] := rfl

theorem native_pair_answers :
    (runWorlds result false).map (fun world => world.answer.val) =
      [.pair (.var 1) (.refl (.var 1)), .pair (.var 0) (.refl (.var 0))] := rfl

theorem initial_state_reset_changes_intents :
    (runWorlds result false).map WorldResult.intents ≠
      ((runWorlds indices false).flatMap fun prior =>
        (runWorldsAt (next prior.answer) false prior.branch).map fun suffix =>
          prior.intents ++ suffix.intents) := by decide

theorem selected_types_differ : inst0 older.val family ≠ inst0 newer.val family := by decide

private theorem reflGeneration {n : Nat} {Γ : Tower.Ctx n} {term type : Tower.Tm n}
    (typing : Typing Tower.rules Γ term type) :
    ∀ {value : Tower.Tm n}, term = .refl value →
      ∃ carrier, Typing Tower.rules Γ value carrier ∧
        TypeAdjustment Tower.rules (.id carrier value value) type := by
  induction typing with
  | reflIntro typed _ =>
      intro value equality
      cases equality
      exact ⟨_, typed, .refl _⟩
  | cumul _ order ih =>
      intro value equality
      obtain ⟨carrier, typed, adjustment⟩ := ih equality
      exact ⟨carrier, typed, .trans adjustment (.cumulative order)⟩
  | conv _ _ _ conversion ih _ =>
      intro value equality
      obtain ⟨carrier, typed, adjustment⟩ := ih equality
      exact ⟨carrier, typed, .trans adjustment (.conversion conversion)⟩
  | _ => intro value equality; cases equality

/-- The other branch's selected index cannot be substituted into the fibre
of this reflexivity value, even allowing the native conversion tail rules. -/
theorem wrong_selected_index_not_admitted :
    ¬ Judgment Tower.rules context (.refl older.val) (inst0 newer.val family) := by
  intro judgment
  obtain ⟨carrier, _, adjustment⟩ := reflGeneration judgment.typing rfl
  have conversion := adjustment.toConvOfSourceDisjointHeads
    (fun head => TowerConversionSkeleton.not_conv_id_head carrier older.val older.val head)
  have endpoint := (TowerConversionSkeleton.id_components_of_conv conversion).2.1
  have equality := Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.normalForms_eq_of_conv
    (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Reduction.RedStar.refl _)
    (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Reduction.RedStar.refl _)
    (TowerConversionSkeleton.erase_var_normal (1 : Fin 2))
    (TowerConversionSkeleton.erase_var_normal (0 : Fin 2)) endpoint
  cases equality

end Examples

#print axioms Examples.sigma_formed
#print axioms Examples.selected_worlds
#print axioms Examples.native_pair_answers
#print axioms Examples.initial_state_reset_changes_intents
#print axioms Examples.wrong_selected_index_not_admitted

end FormationSensitive.DependentComputation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
