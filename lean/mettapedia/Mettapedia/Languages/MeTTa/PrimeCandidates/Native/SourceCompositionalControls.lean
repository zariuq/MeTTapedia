import Mettapedia.Languages.MeTTa.PrimeCandidates.Native.SourceCompositionalAdequacy
import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceWitnesses
import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceCompositionControls

/-!
# Source-to-shared-return execution controls

These controls compile authored expressions through the existing argument
profile, then execute the actual shared-return machine. The divergent control
is semantic nonderivability, not exhaustion of a chosen fuel bound.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.Native.SourceCompositionalAdequacy.Controls

open Mettapedia.Machines.BranchLocalNeed
open CallTimeChoice

def rules : SProgram := [⟨0, 1, .con 8 (.cons (.var 0) (.cons (.var 0) .nil))⟩]

def choosing : Expr := .choose (.con 2 .nil) (.con 3 .nil)

def expression : Expr := .call 0 (.cons choosing .nil)

def pair (left right : Nat) : Val Nat := .app (.app (.sym 8) (.sym left)) (.sym right)

theorem source_application_shares_one_argument_occurrence :
    sourceValues .need rules 100 expression = some [pair 2 2, pair 3 3] := by
  decide +kernel

theorem resampling_is_a_different_profile :
    sourceValues .name rules 100 expression =
      some [pair 2 2, pair 2 3, pair 3 2, pair 3 3] := by
  decide +kernel

theorem target_executes_the_compiled_source :
    SharedFinished (rules.toCore .need) (expression.toCore .need id) 300 true ∧
      sharedObservations (rules.toCore .need) 300 (expression.toCore .need id) =
        some [(.value (.app (.app (.sym 8) (.sym 2)) (.sym 2)), []),
          (.value (.app (.app (.sym 8) (.sym 3)) (.sym 3)), [])] := by
  constructor
  · unfold SharedFinished
    decide +kernel
  · decide +kernel

/-- The missing finite derivation rules out every completed target run. -/
theorem eager_divergence_has_no_invented_completion (steps : Nat) :
    ¬ SharedFinished (Witnesses.programExt.toCore .value)
      (Witnesses.konstLoop.toCore .value id) steps true := by
  intro finished
  obtain ⟨results, _, source, _, _⟩ := no_invention finished
  exact Witnesses.konstLoop_value_diverges results source

/-- An unused divergent argument has a source observation and consequently
an actual recorded target execution under the need profile. -/
theorem ignored_divergence_is_realized :
    ∃ steps observations,
      SharedFinished (Witnesses.programExt.toCore .need)
        (Witnesses.konstLoop.toCore .need id) steps true ∧
      sharedObservations (Witnesses.programExt.toCore .need) steps
        (Witnesses.konstLoop.toCore .need id) = some observations := by
  obtain ⟨results, source, _⟩ := sourceValues_sound Witnesses.konstLoop_need
  obtain ⟨steps, observations, finished, exactRead, _⟩ := preservation source
  exact ⟨steps, observations, finished, exactRead⟩

/-- Active-context replacement also preserves the eventual candidate
observation under a surrounding effect and choice. -/
theorem replacement_inside_effectful_context :
    Composition.Equivalent []
      (.emit 17 (.choose Composition.Controls.discarded (.ret (.sym 4))))
      (.emit 17 (.choose (.ret (.sym 2)) (.ret (.sym 4)))) :=
  ((Composition.Controls.discard_pure_stage []).choose (.refl _ _)).emit 17

end Mettapedia.Languages.MeTTa.PrimeCandidates.Native.SourceCompositionalAdequacy.Controls
