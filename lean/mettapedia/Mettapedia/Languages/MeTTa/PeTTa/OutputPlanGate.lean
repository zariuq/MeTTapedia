import Mettapedia.Languages.MeTTa.PeTTa.OutputPlan

/-!
# Literal output unification before producing goals

The gate uses the actual source unifier. Success reaches the continuation
with its bindings; refusal leaves the whole reached world unchanged and runs
no part of the continuation. The finite entry charge belongs to this reference
lowering, not to a mandatory sequence of native operations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.OutputPlan

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)

def focused (base : Streaming.State) (bindings : Subst) (expression : Atom)
    (frames : List Streaming.Frame) (older : List Streaming.Job) : Streaming.State :=
  {base with agenda := .execute ⟨.evaluate bindings expression,frames⟩ :: older}

theorem gate_success (registry : SpaceSemantics.Program) (base : Streaming.State)
    (bindings bound : Subst) (left right continuation : Atom)
    (frames : List Streaming.Frame) (older : List Streaming.Job)
    (unified : Unifying.unify bindings left (Unifying.resolve bindings right) = .ok bound) :
    Streaming.advance registry 4 (focused base bindings (equate left right continuation) frames older) =
      focused base bound continuation frames older := by
  simp [Streaming.advance,Mettapedia.Machines.BoundedDeterministicRun.run,Streaming.step,
    focused,equate,hold,call,Streaming.returnAnswer,Streaming.enqueuePhase,Streaming.laterAnswers,
    Streaming.World.configuration,Streaming.World.fromConfiguration,
    Unifying.step,Unifying.bindAnswers,Unifying.unifyBinding,unified,bind]

theorem gate_refusal (registry : SpaceSemantics.Program) (base : Streaming.State)
    (bindings : Subst) (left right continuation : Atom)
    (frames : List Streaming.Frame) (older : List Streaming.Job)
    (clashed : Unifying.unify bindings left (Unifying.resolve bindings right) = .clash) :
    Streaming.advance registry 4 (focused base bindings (equate left right continuation) frames older) =
      {base with agenda := older} := by
  simp [Streaming.advance,Mettapedia.Machines.BoundedDeterministicRun.run,Streaming.step,
    focused,equate,hold,call,Streaming.returnAnswer,Streaming.enqueuePhase,Streaming.laterAnswers,
    Streaming.World.configuration,Streaming.World.fromConfiguration,
    Unifying.step,Unifying.bindAnswers,Unifying.unifyBinding,clashed,bind]

/-- An unserved unification retains its complete waiting frame. It is not
converted to the empty producer and does not enter the producing body. -/
theorem gate_interruption (registry : SpaceSemantics.Program) (base : Streaming.State)
    (bindings : Subst) (left right continuation : Atom)
    (frames : List Streaming.Frame) (older : List Streaming.Job)
    (unserved : Unifying.unify bindings left (Unifying.resolve bindings right) = .exhausted) :
    Streaming.advance registry 4 (focused base bindings (equate left right continuation) frames older) =
      {base with
        agenda := .execute ⟨.returned [⟨Unifying.resolve bindings right,bindings⟩],
          .source (.bind (hold left) continuation) :: frames⟩ :: older} := by
  simp [Streaming.advance,Mettapedia.Machines.BoundedDeterministicRun.run,Streaming.step,
    focused,equate,hold,call,Streaming.returnAnswer,Streaming.enqueuePhase,Streaming.laterAnswers,
    Streaming.World.configuration,Streaming.World.fromConfiguration,
    Unifying.step,Unifying.bindAnswers,Unifying.unifyBinding,unserved,bind]

end Mettapedia.Languages.MeTTa.PeTTa.OutputPlan
