import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationRepresentedRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RepresentedPathsControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationComposition

/-!
# An unbounded source consumer of represented-run correspondence

Natural-number state codes use the authored configuration/index constructors.
The interpreted store grows on every event, and candidate labels remain in
the source rule data. The represented-run theorem covers all finite semantic
runs of this profile, not only a fixed sample or a bounded state table.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.RepresentedRunsControls

open Interface RepresentedPathsControls
open Mettapedia.OSLF.MeTTaIL.Syntax

def configuration (length : Nat) : Configuration Payloads.Term Nat := ⟨[], {length}⟩

def statePattern (length : Nat) : Pattern :=
  .apply "StateData" [Payloads.configurationPattern (configuration length)]

def readState : Pattern → Option Nat
  | .apply "StateData" [.apply "TcConfigurationData" [_equations, indices]] => do
      match ← Payloads.readIndices indices with
      | [length] => some length
      | _ => none
  | _ => none

def rule (label : Bool) : RuleInstance Payloads.Term :=
  ⟨[], [], [], [], [.node (.quotedRule (if label then 1 else 0)) .nil]⟩

def firingPattern (candidate : (_length : Nat) × Bool) : Pattern :=
  .apply "FiringData" [Payloads.configurationPattern (configuration candidate.1),
    Payloads.rulePattern (rule candidate.2), Payloads.selectionPattern ⟨[], [], []⟩]

def readFiring : Pattern → Option ((_length : Nat) × Bool)
  | .apply "FiringData" [state, rule, _selection] => do
      let length ← readState (.apply "StateData" [state])
      let decoded ← Payloads.readRule rule
      match decoded.produce with
      | [.node (.quotedRule 0) .nil] => some ⟨length, false⟩
      | [.node (.quotedRule 1) .nil] => some ⟨length, true⟩
      | _ => none
  | _ => none

theorem state_readback (length : Nat) : readState (statePattern length) = some length := by
  simp [readState, statePattern, configuration, Payloads.configurationPattern,
    Payloads.readIndices_pattern]

theorem firing_readback (candidate : (_length : Nat) × Bool) :
    readFiring (firingPattern candidate) = some candidate := by
  rcases candidate with ⟨length, label⟩
  have decoded : readState (.apply "StateData" [Payloads.configurationPattern (configuration length)]) =
      some length := state_readback length
  cases label <;> simp [readFiring, firingPattern, decoded, Payloads.readRule_pattern, rule]

def encoding : Encoding Nat (fun _ => Bool) where
  state := ⟨⟨"tcalc.counted-store", 1⟩, readState, statePattern, state_readback⟩
  firing := ⟨⟨"tcalc.labelled-tell", 1⟩, readFiring, firingPattern, firing_readback⟩

def decisions : Decisions representation.effect (representation.admission allow) where
  prepare {s} _ := .isTrue (Presentation.Controls.prepares (store s) ())
  permit {s} _ _ := .isTrue ⟨Presentation.Controls.prepares (store s) (), trivial⟩

theorem every_semantic_run_has_unique_source (length : Nat)
    (path : @Quiver.PathStar (EffectCore.EventObject E allow) _ (store length)) :
    ∃! source : @Quiver.PathStar (RepresentedRuns.Source representation allow encoding decisions) _
        (statePattern length),
      RepresentedRuns.interpretRun representation allow encoding decisions length source = path :=
  RepresentedRuns.unique_source_run representation allow encoding decisions coverage faithful length path

theorem actual_source_run (length : Nat) (labels : List Bool) :
    ∃ source : @Quiver.PathStar (RepresentedRuns.Source representation allow encoding decisions) _
        (statePattern length),
      RepresentedRuns.interpretRun representation allow encoding decisions length source =
        (representation.mapEvents allow).pathStar length (run length labels) := by
  exact (every_semantic_run_has_unique_source length
    ((representation.mapEvents allow).pathStar length (run length labels))).exists

theorem authored_step (length : Nat) (label : Bool) :
    atState (statePattern (length + 1)) ∈
      Mettapedia.OSLF.MeTTaIL.Engine.rewriteStepWithPremisesUsing
        (effectQueries representation.effect (representation.admission allow) encoding decisions).relations
        authoredLanguage (request (statePattern length) (firingPattern ⟨length, label⟩)) := by
  rw [authored_root_execution]
  exact (execution_iff_event representation.effect (representation.admission allow) encoding decisions
    (s := length) (t := length + 1) label).mpr ⟨event length label, rfl⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.RepresentedRunsControls
