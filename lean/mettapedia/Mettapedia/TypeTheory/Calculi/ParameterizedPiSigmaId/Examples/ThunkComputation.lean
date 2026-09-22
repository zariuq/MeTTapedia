import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveThunkComputation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveDependentComputation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.DependentComputation
import Mettapedia.TypeTheory.ContextualKleisliAdjunction
import Mettapedia.TypeTheory.ContextualThunkStrategy

/-! # Concrete examples of FormationSensitiveThunkComputation -/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
set_option autoImplicit false
open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.TypeTheory.ContextualDependentSequencing
open Mettapedia.TypeTheory.ContextualComputationKleisli.Program (bind_assoc)
open Mettapedia.TypeTheory

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitive.ThunkComputation

open FormationSensitive.DependentComputation
namespace Examples

open FormationSensitive.DependentComputation.Examples

def deferred : Program Bool (AdmittedThunk Tower.rules context ground family Bool Nat) Nat :=
  Program.map (fun first => ⟨first, next first⟩) indices

def rawDeferred : Program Bool (RawThunk Tower.Head Bool Nat 2) Nat :=
  Program.map erase deferred

/-- The body is stored as a value: only the index selection's intents occur. -/
theorem delaying_does_not_run_body :
    (runWorlds rawDeferred false).map WorldResult.intents = [[10], [20]] := rfl

/-- Forcing at the selected world runs each body there and retains its index. -/
theorem force_dependent_worlds :
    runWorlds (force rawDeferred) false =
      [{ branch := [false], answer := .pair (.var 1) (.refl (.var 1)),
          state := true, intents := [10, 30] },
       { branch := [true], answer := .pair (.var 0) (.refl (.var 0)),
          state := false, intents := [20, 40] }] := rfl

theorem every_forced_result_admitted (output : WorldResult Bool (Tower.Tm 2) Nat)
    (member : output ∈ runWorlds (force rawDeferred) false) :
    Judgment Tower.rules context output.answer (.sigma ground family) :=
  force_result_judgment sigma_formed (.sort _) rawDeferred false []
    (erased_packets_qualified deferred false []) output member

/-- Updating the consumer state before forcing is not undone by a thunk.
Its code and dependent index are captured; the mutable state is not. -/
def forceAfterWrite : Program Bool (Tower.Tm 2) Nat :=
  rawDeferred.bind fun packet => .write true (force (.pure packet))

theorem force_uses_consumer_state :
    (runWorlds forceAfterWrite false).map WorldResult.intents = [[10, 30], [20, 30]] := rfl

theorem captured_index_does_not_capture_mutable_state :
    (runWorlds forceAfterWrite false).map WorldResult.intents ≠
      (runWorlds (force rawDeferred) false).map WorldResult.intents := by decide

/-- A body returning the other branch's proof is executable, but fails the
selected native fibre's independent qualification. -/
def misindexed : RawThunk Tower.Head Bool Nat 2 :=
  ⟨newer.val, .pure (.refl older.val)⟩

theorem misindexed_executes :
    runWorlds (force (.pure misindexed)) false =
      [{ branch := [], answer := .pair newer.val (.refl older.val),
          state := false, intents := [] }] := rfl

theorem misindexed_not_qualified :
    ¬ Qualified Tower.rules context ground family misindexed := by
  intro qualified
  have typed := qualified.bodyTyping false []
    { branch := [], answer := .refl older.val, state := false, intents := [] }
    (by simp [misindexed, runWorldsAt])
  exact wrong_selected_index_not_admitted ⟨context_formed, typed⟩

end Examples

#print axioms Examples.delaying_does_not_run_body
#print axioms Examples.force_dependent_worlds
#print axioms Examples.every_forced_result_admitted
#print axioms Examples.force_uses_consumer_state
#print axioms Examples.captured_index_does_not_capture_mutable_state
#print axioms Examples.misindexed_executes
#print axioms Examples.misindexed_not_qualified

end FormationSensitive.ThunkComputation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
