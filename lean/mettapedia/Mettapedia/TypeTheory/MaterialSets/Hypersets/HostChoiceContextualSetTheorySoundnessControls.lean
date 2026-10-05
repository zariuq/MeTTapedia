import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetTheorySoundness
import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetPowersControls

/-!
# Intuitionistic controls in the actual contextual set-axiom model

An actual material set acquires a member along an infinite chain of
contexts. The same model validates the adopted set axioms while refuting
membership excluded middle and double-negation elimination. External host
Choice therefore does not supply these object-theory deduction rules.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetTheorySoundnessControls

open _root_.CategoryTheory ContextualMaterialLogic
open HostChoiceContextualSetInterpretation HostChoiceContextualSetInterpretation.Finality
open HostChoiceContextualMaterialLogic (model)
open HostChoiceContextualSetTheorySoundness
open HostChoiceContextualSetPowersControls.Infinite
open PowerClassPresheafDescent.Controls

abbrev values := sets (D := Stagesᵒᵖ)

def atom : Formula 2 := .member 0 1

def negative : Formula 2 := .imply atom .bottom

def doubleNegative : Formula 2 := .imply negative .bottom

def excludedMiddle : Formula 2 := .either atom negative

def doubleNegationElimination : Formula 2 := .imply doubleNegative atom

noncomputable def environment (point : Stagesᵒᵖ) : Environment values 2 point :=
  Fin.cases (emptySet.val point) (Fin.cases ((thresholdSet 0).val point) Fin.elim0)

theorem environment_transport {point target : Stagesᵒᵖ} (arrow : point ⟶ target) :
    ContextualMaterialLogic.transport values arrow (environment point) = environment target := by
  funext index
  refine Fin.cases ?_ (fun next => Fin.cases ?_ (fun impossible => Fin.elim0 impossible) next) index
  · exact emptySet.property arrow
  · exact (thresholdSet 0).property arrow

theorem atom_iff (point : Stagesᵒᵖ) :
    force values model atom point (environment point) ↔ 1 ≤ stageIndex point := by
  change Member point (emptySet.val point) ((thresholdSet 0).val point) ↔ _
  exact (threshold_future 0 point point (𝟙 point) _).trans (and_iff_left rfl)

theorem atom_future_true : force values model atom (world 1) (environment (world 1)) :=
  (atom_iff (world 1)).mpr (Nat.le_refl 1)

theorem atom_now_false : ¬ force values model atom (world 0) (environment (world 0)) :=
  fun proof => Nat.not_succ_le_zero 0 ((atom_iff (world 0)).mp proof)

theorem negative_now_false : ¬ force values model negative (world 0) (environment (world 0)) := by
  intro refuses
  have later := refuses (world 1) (arrival 1)
  rw [environment_transport] at later
  exact later atom_future_true

theorem excluded_middle_fails :
    ¬ force values model excludedMiddle (world 0) (environment (world 0)) :=
  fun disjunction => disjunction.elim atom_now_false negative_now_false

def advanceAfter (point : Stagesᵒᵖ) : point ⟶ world (stageIndex point + 1) :=
  (homOfLE (Nat.le_succ (stageIndex point))).op.op

theorem double_negative_valid (point : Stagesᵒᵖ) :
    force values model doubleNegative point (environment point) := by
  intro target arrow refuses
  rw [environment_transport] at refuses
  have later := refuses (world (stageIndex target + 1)) (advanceAfter target)
  rw [environment_transport] at later
  exact later ((atom_iff _).mpr (Nat.succ_le_succ (Nat.zero_le (stageIndex target))))

theorem double_negation_elimination_fails :
    ¬ force values model doubleNegationElimination (world 0) (environment (world 0)) := by
  intro elimination
  exact atom_now_false (force_modusPonens model doubleNegative atom _ _ elimination
    (double_negative_valid (world 0)))

theorem no_set_proof_excluded_middle {assumptions : List (Formula 2)}
    (adopted : ∀ formula ∈ assumptions, ContextualMaterialSetTheory.Axiom formula) :
    ¬ Nonempty (ContextualMaterialLogic.Derivation assumptions excludedMiddle) := by
  rintro ⟨derivation⟩
  exact excluded_middle_fails (set_derivation_valid derivation adopted (world 0) (environment (world 0)))

theorem no_set_proof_double_negation_elimination {assumptions : List (Formula 2)}
    (adopted : ∀ formula ∈ assumptions, ContextualMaterialSetTheory.Axiom formula) :
    ¬ Nonempty (ContextualMaterialLogic.Derivation assumptions doubleNegationElimination) := by
  rintro ⟨derivation⟩
  exact double_negation_elimination_fails
    (set_derivation_valid derivation adopted (world 0) (environment (world 0)))

end Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetTheorySoundnessControls
