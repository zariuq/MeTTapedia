import Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.Ontology.UpperShard
import Mettapedia.Ethics.ChoicePoint

set_option autoImplicit false

/-!
# Ethical Conflict Lane

This module connects the Stage 1 structured-claim kernel to FOET's
`ChoicePoint` machinery.

The key idea is processual rather than taxonomic:

- a set of candidate ethical commitments can arise in the `activeGoal` role,
- their propositional contents induce a FOET choice point,
- and dilemma transport theorems then move conflict information across
  deontic, value, utilitarian, and virtue presentations.

This is still an adapter layer, but it puts `ChoicePoint` into the live
deliberation lane instead of leaving it disconnected from the WM bridge work.
-/

namespace Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.Ontology

open Mettapedia.Ethics

universe u

/-- Extract the underlying formula from a propositional-content claim. -/
def StructuredEthicalClaim.propositionalFormula?
    {World : Type u} {Agent : Type u}
    (claim : StructuredEthicalClaim World Agent) : Option (Formula World) :=
  match claim.content with
  | .propositional φ => some φ
  | .relational .. => none
  | .dispositional .. => none

/-- A deliberative lane of candidate commitments, all living in the
`activeGoal` role and all propositional so they induce a FOET choice point. -/
structure EthicalConflictLane (World : Type u) (Agent : Type u) where
  options : Set (StructuredEthicalClaim World Agent)
  activeGoalOnly :
    ∀ claim, claim ∈ options → claim.role = .activeGoal
  propositionalOnly :
    ∀ claim, claim ∈ options → ∃ φ, claim.content = .propositional φ

/-- Forget the richer claims and recover the FOET choice point they induce. -/
def EthicalConflictLane.choicePoint
    {World : Type u} {Agent : Type u}
    (lane : EthicalConflictLane World Agent) : ChoicePoint World :=
  fun φ => ∃ claim, claim ∈ lane.options ∧ claim.content = .propositional φ

@[simp] theorem mem_choicePoint_iff
    {World : Type u} {Agent : Type u}
    (lane : EthicalConflictLane World Agent) (φ : Formula World) :
    φ ∈ lane.choicePoint ↔
      ∃ claim, claim ∈ lane.options ∧ claim.content = .propositional φ := by
  rfl

def EthicalConflictLane.DeonticMoralDilemmaAt
    {World : Type u} {Agent : Type u}
    (lane : EthicalConflictLane World Agent)
    (semD : DeonticSemantics World) (w : World) : Prop :=
  DeonticMoralDilemma semD w lane.choicePoint

def EthicalConflictLane.ValueMoralDilemmaAt
    {World : Type u} {Agent : Type u}
    (lane : EthicalConflictLane World Agent)
    (semV : ValueSemantics World) (w : World) : Prop :=
  ValueMoralDilemma semV w lane.choicePoint

def EthicalConflictLane.UtilitarianMoralDilemmaAt
    {World : Type u} {Agent : Type u}
    (lane : EthicalConflictLane World Agent)
    (semU : UtilityAssignmentSemantics World) (w : World) : Prop :=
  UtilitarianMoralDilemma semU w lane.choicePoint

def EthicalConflictLane.VirtueTargetMoralDilemmaAt
    {World : Type u} {Agent : Type u}
    (lane : EthicalConflictLane World Agent)
    (semT : VirtueTargetSemantics World) (w : World) : Prop :=
  VirtueTargetMoralDilemma semT w lane.choicePoint

theorem EthicalConflictLane.deonticMoralDilemmaAt_iff_valueMoralDilemmaAt
    {World : Type u} {Agent : Type u}
    (lane : EthicalConflictLane World Agent)
    (semD : DeonticSemantics World) (semV : ValueSemantics World)
    (h_align : ∀ a φ w, semD.deontic a φ w ↔ semV.morally (deonticToMoralValue a) φ w)
    (w : World) :
    lane.DeonticMoralDilemmaAt semD w ↔ lane.ValueMoralDilemmaAt semV w := by
  simpa [EthicalConflictLane.DeonticMoralDilemmaAt,
    EthicalConflictLane.ValueMoralDilemmaAt] using
    deonticMoralDilemma_iff_valueMoralDilemma semD semV h_align w lane.choicePoint

theorem EthicalConflictLane.utilitarianMoralDilemmaAt_iff_valueMoralDilemmaAt
    {World : Type u} {Agent : Type u}
    (lane : EthicalConflictLane World Agent)
    (semU : UtilityAssignmentSemantics World) (w : World) :
    lane.UtilitarianMoralDilemmaAt semU w ↔
      lane.ValueMoralDilemmaAt (valueSemanticsOfUtility World semU) w := by
  simpa [EthicalConflictLane.UtilitarianMoralDilemmaAt,
    EthicalConflictLane.ValueMoralDilemmaAt] using
    utilitarianMoralDilemma_iff_valueMoralDilemma semU w lane.choicePoint

theorem EthicalConflictLane.utilitarianMoralDilemmaAt_iff_virtueTargetMoralDilemmaAt
    {World : Type u} {Agent : Type u}
    (lane : EthicalConflictLane World Agent)
    (semU : UtilityAssignmentSemantics World) (w : World) :
    lane.UtilitarianMoralDilemmaAt semU w ↔
      lane.VirtueTargetMoralDilemmaAt (virtueTargetSemanticsOfUtility World semU) w := by
  simpa [EthicalConflictLane.UtilitarianMoralDilemmaAt,
    EthicalConflictLane.VirtueTargetMoralDilemmaAt] using
    utilitarianMoralDilemma_iff_virtueTargetMoralDilemma semU w lane.choicePoint

end Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.Ontology
