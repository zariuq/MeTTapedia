import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ScopedComputationCaptures
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ScopedComputationSemantics

/-!
# Captured return packets preserve the source worlds

Connect checked capture reconstruction to the independently defined source
world-list semantics. Exact agreement includes ordered branch occurrences,
native answers, state and deferred intents. Empty primitive results are
allowed. This is a law of the finite scoped computation grammar, not a claim
that a native heap, foreign resource or permission policy has been implemented.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ScopedComputation

open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers

universe uState uIntent

variable {Head Operation : Type} {State : Type uState} {Intent : Type uIntent}
  {n m k : Nat}

/-- Direct source world semantics commutes with native value substitution,
without a totality assumption on primitive effects. -/
theorem Code.worlds_substitute
    (primitive : Operation → Tm Head k → State → BranchTrace →
      List (WorldResult State (Tm Head k) Intent))
    (later : Sub Head m k) (earlier : Sub Head n m) (code : Code Head Operation n)
    (state : State) (branch : BranchTrace) :
    (code.substitute earlier).worlds primitive later state branch =
      code.worlds primitive (subComp later earlier) state branch := by
  induction code generalizing m state branch with
  | returnValue value => simp only [substitute, worlds, subst_subComp]
  | sequence first body ihFirst ihBody =>
      simp only [substitute, worlds, ihFirst]
      congr 1
      funext prior
      rw [ihBody, consSub_liftSub_comp]
  | sequenceSigma first body ihFirst ihBody =>
      simp only [substitute, worlds, ihFirst]
      congr 1
      funext prior
      rw [ihBody, consSub_liftSub_comp]
  | choose left right ihLeft ihRight => simp only [substitute, worlds, ihLeft, ihRight]
  | call operation argument => simp only [substitute, worlds, subst_subComp]

namespace Captures

/-- Observe the resumed source computation only after reconstruction succeeds. -/
def Packet.worlds? {program : Program Head Operation} (packet : Packet program m)
    (answer : Tm Head m)
    (primitive : Operation → Tm Head m → State → BranchTrace →
      List (WorldResult State (Tm Head m) Intent))
    (state : State) (branch : BranchTrace) :
    Option (List (WorldResult State (Tm Head m) Intent)) :=
  (packet.resume? answer).map fun result => result.1.worlds primitive ids state branch

/-- The packet representation has exactly the independently specified source
continuation's worlds, after binding the selected return value. -/
theorem compile_worlds (program : Program Head Operation) (label : Fin program.labels)
    (environment : Sub Head (program.entry label).arity m) (answer : Tm Head m)
    (primitive : Operation → Tm Head m → State → BranchTrace →
      List (WorldResult State (Tm Head m) Intent))
    (state : State) (branch : BranchTrace) :
    (compile program label environment).worlds? answer primitive state branch =
      some ((program.entry label).body.worlds primitive (consSub answer environment) state branch) := by
  rw [Packet.worlds?, compile_resume]
  simp only [Option.map_some, Code.worlds_substitute]
  congr 2
  funext index
  exact subst_ids _

end Captures
end ScopedComputation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
