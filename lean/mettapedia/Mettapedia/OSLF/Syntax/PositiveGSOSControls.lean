import Mettapedia.OSLF.Syntax.PositiveGSOSFiniteRules
import Mettapedia.OSLF.Syntax.DeterministicGSOSControls
import Mettapedia.OSLF.Syntax.DeterministicGSOSRuleQuotient
import Mettapedia.OSLF.Syntax.DeterministicGSOSImageFiniteBoundary

/-!
# Positive-format and corrected-correspondence controls

One transition at the left argument is enough to fire an active/passive
clause while the right argument is dead. The all-active domain rejects
that same input. A real variable collision preserves the complete target.
The independent infinite-action separators distinguish the two finite
observation bounds in the rule-class correspondence.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.DeterministicGSOS.PositivePremises.Controls

open CategoryTheory Mettapedia.TypeTheory
open Mettapedia.OSLF.DeterministicGSOS.Controls

def leftActive : Pattern (Actions := actions) (sort := ()) Operator.priority where
  active position := decide (position = left)
  label _ _ := 7

def leftOnly : BehaviourArguments signature actions naturals (sort := ()) Operator.priority :=
  fun position => if position = left then (10, fun action => if action = 7 then some 11 else none)
    else (20, fun _ => none)

def selected : Input leftActive naturals where
  originals position := if position = left then 10 else 20
  derivatives _ _ := 11

noncomputable def leftTarget : signature.Term (variableFamily leftActive) () :=
  priority (pure (.derivative left rfl)) (pure (.original right))

theorem leftOnly_realizes : leftActive.Realizes leftOnly selected := by
  constructor
  · intro position
    by_cases same : position = left <;> simp [selected, leftOnly, same]
  · intro position active
    have same : position = left := by simpa [leftActive] using active
    subst position
    simp [leftActive, leftOnly, selected]

/-- The inactive right argument has no selected edge and needs none. -/
theorem passive_right_is_dead : (leftOnly right).2 = fun _ => none := by
  simp [leftOnly, left, right]

theorem positive_finite_rule_fires :
    (leftActive.finiteRule leftTarget).Matches (inputGuard actions leftOnly) :=
  leftActive.realizes_matches leftTarget leftOnly selected leftOnly_realizes

/-- The independently authored conclusion retains the exact passive source. -/
theorem positive_target_readout :
    (NaturalConclusion.ofTarget leftActive leftTarget).operation naturals selected =
      priority (pure 11) (pure 20) := by
  change signature.rename selected.assignment leftTarget = _
  rw [leftTarget, rename_priority]
  rfl

/-- Requiring an edge on every child would exclude this active/passive firing. -/
theorem all_active_rejects_leftOnly :
    ¬ ∃ input : Input (Pattern.allActive (Actions := actions)
        (operator := Operator.priority) (fun _ => 7)) naturals,
      (Pattern.allActive (Actions := actions) (operator := Operator.priority) (fun _ => 7)).Realizes
        leftOnly input := by
  rintro ⟨input, realizes⟩
  have impossible := realizes.2 right rfl
  simp [Pattern.allActive, passive_right_is_dead] at impossible

/-- The positive conclusion satisfies its substitution contract at a noninjective map. -/
theorem target_collision :
    (NaturalConclusion.ofTarget leftActive leftTarget).operation units (selected.map collapse) =
      priority (pure ()) (pure ()) := by
  rw [(NaturalConclusion.ofTarget leftActive leftTarget).naturality, positive_target_readout]
  rw [rename_priority]
  rfl

/-- No finite-premise rule equivalence class denotes the all-actions-disabled law. -/
theorem no_finite_class_for_infinite_probe :
    ¬ ∃ presentation : ConsistentPresentation AllDisabled.actions,
      FinitePresentation.toLaw AllDisabled.actions presentation.val =
        toLaw AllDisabled.actions AllDisabled.rules := by
  rintro ⟨presentation, equal⟩
  have finite := (FinitePresentation.toLaw_denotes AllDisabled.actions
    presentation.val presentation.property).finiteSuccessfulObservation AllDisabled.actions
  rw [equal, fromLaw_toLaw] at finite
  exact AllDisabled.not_finitely_observed finite

/-- A successful finite-premise presentation need not have a uniform finite bound. -/
theorem finite_success_is_strictly_weaker :
    FiniteSuccessfulObservation AllDisabled.actions EnabledProbe.rules ∧
      ¬ UniformFiniteObservation AllDisabled.actions EnabledProbe.rules :=
  EnabledProbe.finitePremise_does_not_imply_imageFinite

end Mettapedia.OSLF.DeterministicGSOS.PositivePremises.Controls
