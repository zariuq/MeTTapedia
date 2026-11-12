import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperPlacementCoherence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ContextualRunComposition

/-!
# Coherence of complete contextual declaration blocks

The local declaration square lifts through arbitrary finite local runs.
Both resulting source embeddings and the complete joint store are retained.
These placement laws do not identify execution histories; native trace
interchange additionally needs the corresponding event squares.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs

variable {S : Signature} {O : Type} [DecidableEq O]

theorem run_solvable_iff : ∀ {source : State S O} (run : helperStep.Run source),
    (Frames.contextual S).Solvable run.last.knowledge ↔ (Frames.contextual S).Solvable source.knowledge
  | _, .nil _ => Iff.rfl
  | _, .cons f _ rest =>
      (run_solvable_iff rest).trans ⟨knowledge_solvable f, information_solvable f⟩

namespace ContextPlacement

abbrev afterRight {left right : State S O} (place : ContextPlacement left right) (g : Firing right) :
    ContextPlacement left g.after := (place.swap.afterLeft g).swap

def advanceLeft : {left right : State S O} → ContextPlacement left right →
    (run : helperStep.Run left) → ContextPlacement run.last right
  | _, _, place, .nil _ => place
  | _, _, place, .cons f _ rest => advanceLeft (place.afterLeft f) rest

def advanceRight {left right : State S O} (place : ContextPlacement left right) (run : helperStep.Run right) :
    ContextPlacement left run.last := (place.swap.advanceLeft run).swap

theorem advanceRight_nil {left right : State S O} (place : ContextPlacement left right) :
    place.advanceRight (.nil right) = place := rfl

theorem advanceRight_cons {left right : State S O} (place : ContextPlacement left right)
    (g : Firing right) (allowed : helperStep.Admits g) (rest : helperStep.Run g.after) :
    place.advanceRight (.cons g allowed rest) = (place.afterRight g).advanceRight rest := rfl

theorem advanceLeft_append : ∀ {left right : State S O} (place : ContextPlacement left right)
    (first : helperStep.Run left) (later : helperStep.Run first.last),
    HEq (place.advanceLeft (first.append later)) ((place.advanceLeft first).advanceLeft later)
  | _, _, _, .nil _, _ => HEq.rfl
  | _, _, place, .cons f _ rest, later => advanceLeft_append (place.afterLeft f) rest later

theorem rebase_target : ∀ {left right : State S O} (place : ContextPlacement left right)
    (run : helperStep.Run left) (plan : RebasePlan S O place run),
    (RebasePlan.realize place run plan).target = place.advanceLeft run
  | _, _, _, .nil _, .nil _ => rfl
  | _, _, place, .cons f _ rest, .cons _ _ tail => rebase_target (place.afterLeft f) rest tail

theorem tensor_target {left right : State S O} (place : ContextPlacement left right)
    (first : helperStep.Run left) (second : helperStep.Run right) (plan : TensorPlan place first second) :
    (TensorPlan.realize plan).target = (place.advanceLeft first).advanceRight second := by
  change (RebasePlan.realize (RebasePlan.realize place first plan.leftPlan).target.swap second plan.rightPlan).target.swap = _
  have rightTarget := rebase_target (RebasePlan.realize place first plan.leftPlan).target.swap second plan.rightPlan
  have leftTarget := rebase_target place first plan.leftPlan
  exact (congrArg ContextPlacement.swap rightTarget).trans
    (congrArg (fun p : ContextPlacement first.last right => (p.swap.advanceLeft second).swap) leftTarget)

end ContextPlacement

namespace PlacementIso

def advanceLeft : ∀ {left right : State S O} {p q : ContextPlacement left right}
    (_mapping : PlacementIso p q) (run : helperStep.Run left),
    PlacementIso (p.advanceLeft run) (q.advanceLeft run)
  | _, _, _, _, mapping, .nil _ => mapping
  | _, _, _, _, mapping, .cons f _ rest => advanceLeft (mapping.afterLeft f) rest

def advanceRight {left right : State S O} {p q : ContextPlacement left right}
    (mapping : PlacementIso p q) (run : helperStep.Run right) :
    PlacementIso (p.advanceRight run) (q.advanceRight run) := (mapping.swap.advanceLeft run).swap

end PlacementIso

namespace ContextPlacement

def crossRightBlock : ∀ {left right : State S O} (place : ContextPlacement left right)
    (f : Firing left) (run : helperStep.Run right),
    PlacementIso ((place.afterLeft f).advanceRight run) ((place.advanceRight run).afterLeft f)
  | _, _, place, f, .nil _ => PlacementIso.refl (place.afterLeft f)
  | _, _, place, f, .cons g _ rest =>
      ((place.afterBothIso f g).advanceRight rest).trans (crossRightBlock (place.afterRight g) f rest)

def blockSwap : ∀ {left right : State S O} (place : ContextPlacement left right)
    (first : helperStep.Run left) (second : helperStep.Run right),
    PlacementIso ((place.advanceLeft first).advanceRight second) ((place.advanceRight second).advanceLeft first)
  | _, _, place, .nil _, second => PlacementIso.refl (place.advanceRight second)
  | _, _, place, .cons f _ rest, second =>
      (blockSwap (place.afterLeft f) rest second).trans ((place.crossRightBlock f second).advanceLeft rest)

/-- Four-block coherence of the complete placements, independently of a
claim about the original execution histories. -/
def fourBlockIso {left right : State S O} (place : ContextPlacement left right)
    (first : helperStep.Run left) (second : helperStep.Run right)
    (afterFirst : helperStep.Run first.last) (afterSecond : helperStep.Run second.last) :
    PlacementIso
      ((((place.advanceLeft first).advanceLeft afterFirst).advanceRight second).advanceRight afterSecond)
      ((((place.advanceLeft first).advanceRight second).advanceLeft afterFirst).advanceRight afterSecond) :=
  ((place.advanceLeft first).blockSwap afterFirst second).advanceRight afterSecond

end ContextPlacement
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers
