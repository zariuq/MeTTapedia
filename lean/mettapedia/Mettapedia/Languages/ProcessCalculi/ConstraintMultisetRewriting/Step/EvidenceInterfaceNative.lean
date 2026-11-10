import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EvidenceInterface
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeInstance

/-!
# The native step never enters an inconsistent store

The native step settles a firing by the inclusion of its information frame into the active frame of
the solver's update (`ContextualComputedFreshFrame.includeSource`). That inclusion has no retraction
in general: the returned names may have no terms over the information frame. It is still
conservative (`native_conservative`): a solution of the information extends along the inclusion,
sending every returned name to the parameterless metavariable of its sort (`extendFirst`,
`extendFirst_includeSource`). So **every native run from solvable knowledge ends in solvable
knowledge** (`native_run_solvable`), and the evidence row's run consistency holds for the native
step too.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.EvidenceInterface.Native

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Interface (Frames)
open Interface.Frames (Frame firstOrderFrame toFirstOrder)

variable {S : Signature}

/-- **Extend an assignment along the inclusion into an active family**: the returned names go to the
parameterless metavariable of their sort. -/
def extendFirst {V W : Type} {source : V → MetaArity S} {returned : W → MetaArity S}
    (σ : Assignment source (firstOrderFrame S).arity) :
    Assignment (ContextualComputedFreshFrame.active source returned) (firstOrderFrame S).arity
  | .inl v => σ v
  | .inr w => toFirstOrder ⟨W ⊕ Empty, ContextualComputedFreshFrame.target returned⟩ w

/-- **The extension agrees with the assignment on the included names.** -/
theorem extendFirst_includeSource {V : Type} {source : V → MetaArity S}
    {problem : ContextualResidual.Problem source} (update : ContextualFrameUpdate.Update problem)
    (σ : Assignment source (firstOrderFrame S).arity) :
    Assignment.compose (extendFirst (returned := update.declaration) σ)
      (ContextualComputedFreshFrame.includeSource update) = σ := by
  funext v
  show instantiate (extendFirst (returned := update.declaration) σ)
      (instantiate (ContextualFreshFrame.includeOld source update.declaration
        ContextualComputedFreshFrame.noDeclarations)
        (generator (ContextualComputedFreshFrame.old source) (.inl v))) = σ v
  rw [instantiate_generator]
  show instantiate (extendFirst (returned := update.declaration) σ)
      (generator (ContextualComputedFreshFrame.active source update.declaration) (.inl v)) = σ v
  rw [instantiate_generator]
  rfl

variable {O : Type} [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

/-- **The native step settles conservatively.** -/
theorem native_conservative :
    SettlesConservatively (Interface.native (S := S) (O := O) (Γ := Γ) (sort := sort)).toStep := by
  intro s f realized solvable
  obtain ⟨σ, solved⟩ := (Frames.contextual_solvable_iff_firstOrder _).mp solvable
  refine ⟨firstOrderFrame S, extendFirst (returned := (f.pinned realized).firing.update.declaration) σ,
    (Frames.models_applyStore _ _ _).mpr ((Frames.models_congr (fun t => ?_) _).mpr solved)⟩
  show instantiateObservation (Assignment.compose (extendFirst σ)
      (ContextualComputedFreshFrame.includeSource (f.pinned realized).firing.update)) t =
    instantiateObservation σ t
  exact congrArg (fun a => instantiateObservation a t)
    (extendFirst_includeSource (f.pinned realized).firing.update σ)

/-- **Every native run from solvable knowledge ends in solvable knowledge.** -/
theorem native_run_solvable {s : Interface.NativeState S O Γ sort}
    (r : (Interface.native (S := S) (O := O) (Γ := Γ) (sort := sort)).Run s)
    (solvable : (Frames.contextual S).Solvable (Interface.native.knowledge s)) :
    (Frames.contextual S).Solvable (Interface.native.knowledge r.last) :=
  run_solvable native_conservative r solvable

#print axioms extendFirst_includeSource
#print axioms native_conservative
#print axioms native_run_solvable

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.EvidenceInterface.Native
