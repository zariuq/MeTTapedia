import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveRuleReadout
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.UniverseProfiles

/-!
# Distinct proofs of one actual tower judgment

A direct head rule and the same rule followed by reflexive cumulativity
have exactly the same scoped subject and type. Their proof-irrelevant typing
proofs agree, while their authored occurrence readouts differ. Consequently
this readout cannot factor through an erased typing proof.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Examples.RuleEvidenceControls

open JudgmentDerivation FormationSensitiveRuleSignature FormationSensitiveRuleReadout

def goal : Judgment Tower.Head :=
  judgment .nil (.head .legacyGround) (.head (.sort Tower.zero))

def direct : Tree Tower.rules goal :=
  .node (.headType LevelTower.HeadTyping.legacyGround) (fun position => nomatch position)

def cumulative : Tree Tower.rules goal :=
  .node (Rule.cumul (R := Tower.rules)
    (u := LevelTower.Head.sort Tower.zero) (v := LevelTower.Head.sort Tower.zero)
    (fun _ => le_refl _)) (fun _ => direct)

theorem direct_readout : readout direct = [⟨[], .headType⟩] := rfl
theorem cumulative_readout : readout cumulative = [⟨[], .cumul⟩, ⟨[0], .headType⟩] := rfl

theorem readouts_distinct : readout direct ≠ readout cumulative := by
  intro equal
  have lengths := congrArg List.length equal
  change (1 : Nat) = 2 at lengths
  exact (by decide : (1 : Nat) ≠ 2) lengths

theorem trees_distinct : direct ≠ cumulative :=
  fun same => readouts_distinct (congrArg readout same)

/-- Both trees prove the actual maintained judgment. -/
theorem both_sound :
    FormationSensitive.Typing Tower.rules goal.context goal.subject goal.type ∧
      FormationSensitive.Typing Tower.rules goal.context goal.subject goal.type :=
  ⟨sound direct, sound cumulative⟩

/-- Erasure genuinely identifies the propositions' proofs. It does not
authorize identification of their retained occurrence histories. -/
theorem erased_typing_proofs_agree : sound direct = sound cumulative :=
  Subsingleton.elim _ _

theorem readout_cannot_factor_through_typing :
    ¬ ∃ read : PLift (FormationSensitive.Typing Tower.rules goal.context goal.subject goal.type) →
        List Use,
      ∀ tree : Tree Tower.rules goal, read ⟨sound tree⟩ = readout tree := by
  rintro ⟨read, computes⟩
  apply readouts_distinct
  rw [← computes direct, ← computes cumulative]

/-- Equal rule labels at different premise paths are still different uses. -/
theorem duplicate_labels_retain_positions :
    prependPosition 0 (⟨[], .headType⟩ : Use) ≠
      prependPosition 1 (⟨[], .headType⟩ : Use) :=
  different_positions (by decide) _

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Examples.RuleEvidenceControls
