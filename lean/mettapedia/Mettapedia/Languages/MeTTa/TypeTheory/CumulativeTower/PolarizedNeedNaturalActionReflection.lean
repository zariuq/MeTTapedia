import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedNaturalMeaning

/-!
# Source reconstruction for reference actions

When the language-local transition is absent, each actual reference-action
successor reconstructs the preceding source meaning. The reconstruction
retains allocation, selected worlds, lexical bodies and raw mismatch faults.
Matching computation-function applications are excluded by the local-transition
test, not assigned an artificial pure meaning.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace PolarizedNeedNaturalSemantics.Reflection

open PrimeNeedReference PolarizedNeedMachine
open PolarizedNeed (Value Computation)

variable {Head Operation Effect StableFault NativeFault : Type} {n m v k : Nat}

theorem bindNative_meaning
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    {first : Computation Head Operation Effect n v k}
    {body : Computation Head Operation Effect (n + 1) v k}
    {native : Sub Head n m} {values : Fin v → RuntimeValue Head Operation Effect m}
    {needs : Fin k → CellId} {kont : Kont Head Operation Effect m}
    {world allocated final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {cell : CellId} {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    (allocation : world.allocate? ⟨n, v, k, first, native, values, needs⟩ = some (allocated, cell))
    (meaning : LocalMeaning primitive
      (.demand cell (.bindNative ⟨n, v, k, body, native, values, needs⟩ kont)) allocated outcome final) :
    EvalMeaning primitive ⟨n, v, k, .bindNative first body, native, values, needs⟩ kont world outcome final := by
  rcases meaning with ⟨input, selected, ⟨forced⟩, resumed⟩
  cases input with
  | value answer =>
      cases answer with
      | returned value =>
          cases value with
          | native term =>
              rcases resumed with ⟨raw, bodyFinal, ⟨evaluated⟩, consumed⟩
              exact ⟨raw, bodyFinal, ⟨.bindNativeValue allocation forced evaluated⟩, consumed⟩
          | thunk _ _ _ _ =>
              rcases resumed with ⟨rfl, rfl⟩
              exact ⟨_, _, ⟨.bindNativeMismatch body allocation forced
                (by intro term impossible; cases impossible)⟩, ⟨.retryableFault _ _ _⟩⟩
          | packNative _ _ =>
              rcases resumed with ⟨rfl, rfl⟩
              exact ⟨_, _, ⟨.bindNativeMismatch body allocation forced
                (by intro term impossible; cases impossible)⟩, ⟨.retryableFault _ _ _⟩⟩
      | nativeFunction _ =>
          rcases resumed with ⟨rfl, rfl⟩
          exact ⟨_, _, ⟨.bindNativeMismatch body allocation forced
            (by intro term impossible; cases impossible)⟩, ⟨.retryableFault _ _ _⟩⟩
      | valueFunction _ =>
          rcases resumed with ⟨rfl, rfl⟩
          exact ⟨_, _, ⟨.bindNativeMismatch body allocation forced
            (by intro term impossible; cases impossible)⟩, ⟨.retryableFault _ _ _⟩⟩
  | stableFault fault =>
      rcases resumed with ⟨rfl, rfl⟩
      exact ⟨_, _, ⟨.bindNativeFault body allocation forced (.stableFault fault)⟩,
        ⟨.stableFault _ _ _⟩⟩
  | retryableFault reason =>
      rcases resumed with ⟨rfl, rfl⟩
      exact ⟨_, _, ⟨.bindNativeFault body allocation forced (.retryableFault reason)⟩,
        ⟨.retryableFault _ _ _⟩⟩

theorem bindValue_meaning
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    {first : Computation Head Operation Effect n v k}
    {body : Computation Head Operation Effect n (v + 1) k}
    {native : Sub Head n m} {values : Fin v → RuntimeValue Head Operation Effect m}
    {needs : Fin k → CellId} {kont : Kont Head Operation Effect m}
    {world allocated final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {cell : CellId} {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    (allocation : world.allocate? ⟨n, v, k, first, native, values, needs⟩ = some (allocated, cell))
    (meaning : LocalMeaning primitive
      (.demand cell (.bindValue ⟨n, v, k, body, native, values, needs⟩ kont)) allocated outcome final) :
    EvalMeaning primitive ⟨n, v, k, .bindValue first body, native, values, needs⟩ kont world outcome final := by
  rcases meaning with ⟨input, selected, ⟨forced⟩, resumed⟩
  cases input with
  | value answer =>
      cases answer with
      | returned value =>
          rcases resumed with ⟨raw, bodyFinal, ⟨evaluated⟩, consumed⟩
          exact ⟨raw, bodyFinal, ⟨.bindValueValue allocation forced evaluated⟩, consumed⟩
      | nativeFunction _ =>
          rcases resumed with ⟨rfl, rfl⟩
          exact ⟨_, _, ⟨.bindValueMismatch body allocation forced
            (by intro value impossible; cases impossible)⟩, ⟨.retryableFault _ _ _⟩⟩
      | valueFunction _ =>
          rcases resumed with ⟨rfl, rfl⟩
          exact ⟨_, _, ⟨.bindValueMismatch body allocation forced
            (by intro value impossible; cases impossible)⟩, ⟨.retryableFault _ _ _⟩⟩
  | stableFault fault =>
      rcases resumed with ⟨rfl, rfl⟩
      exact ⟨_, _, ⟨.bindValueFault body allocation forced (.stableFault fault)⟩,
        ⟨.stableFault _ _ _⟩⟩
  | retryableFault reason =>
      rcases resumed with ⟨rfl, rfl⟩
      exact ⟨_, _, ⟨.bindValueFault body allocation forced (.retryableFault reason)⟩,
        ⟨.retryableFault _ _ _⟩⟩

theorem sequenceSigma_meaning
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    {first : Computation Head Operation Effect n v k}
    {body : Computation Head Operation Effect (n + 1) v k}
    {native : Sub Head n m} {values : Fin v → RuntimeValue Head Operation Effect m}
    {needs : Fin k → CellId} {kont : Kont Head Operation Effect m}
    {world allocated final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {cell : CellId} {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    (allocation : world.allocate? ⟨n, v, k, first, native, values, needs⟩ = some (allocated, cell))
    (meaning : LocalMeaning primitive
      (.demand cell (.bindSigma ⟨n, v, k, body, native, values, needs⟩ kont)) allocated outcome final) :
    EvalMeaning primitive ⟨n, v, k, .sequenceSigma first body, native, values, needs⟩ kont world outcome final := by
  rcases meaning with ⟨input, selected, ⟨forced⟩, resumed⟩
  cases input with
  | value answer =>
      cases answer with
      | returned value =>
          cases value with
          | native term =>
              rcases resumed with ⟨raw, bodyFinal, ⟨evaluated⟩, consumed⟩
              exact ⟨pairOutcome term raw, bodyFinal, ⟨.sequenceSigmaValue allocation forced evaluated⟩,
                (KontEval.pair_iff term).mp consumed⟩
          | thunk _ _ _ _ =>
              rcases resumed with ⟨rfl, rfl⟩
              exact ⟨_, _, ⟨.sequenceSigmaMismatch body allocation forced
                (by intro term impossible; cases impossible)⟩, ⟨.retryableFault _ _ _⟩⟩
          | packNative _ _ =>
              rcases resumed with ⟨rfl, rfl⟩
              exact ⟨_, _, ⟨.sequenceSigmaMismatch body allocation forced
                (by intro term impossible; cases impossible)⟩, ⟨.retryableFault _ _ _⟩⟩
      | nativeFunction _ =>
          rcases resumed with ⟨rfl, rfl⟩
          exact ⟨_, _, ⟨.sequenceSigmaMismatch body allocation forced
            (by intro term impossible; cases impossible)⟩, ⟨.retryableFault _ _ _⟩⟩
      | valueFunction _ =>
          rcases resumed with ⟨rfl, rfl⟩
          exact ⟨_, _, ⟨.sequenceSigmaMismatch body allocation forced
            (by intro term impossible; cases impossible)⟩, ⟨.retryableFault _ _ _⟩⟩
  | stableFault fault =>
      rcases resumed with ⟨rfl, rfl⟩
      exact ⟨_, _, ⟨.sequenceSigmaFault body allocation forced (.stableFault fault)⟩,
        ⟨.stableFault _ _ _⟩⟩
  | retryableFault reason =>
      rcases resumed with ⟨rfl, rfl⟩
      exact ⟨_, _, ⟨.sequenceSigmaFault body allocation forced (.retryableFault reason)⟩,
        ⟨.retryableFault _ _ _⟩⟩

theorem choose_meaning
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    (left right : Computation Head Operation Effect n v k)
    {native : Sub Head n m} {values : Fin v → RuntimeValue Head Operation Effect m}
    {needs : Fin k → CellId} {kont : Kont Head Operation Effect m}
    {world allocated final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {cell : CellId} {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    (allocation : world.allocate? ⟨n, v, k, .choose left right, native, values, needs⟩ = some (allocated, cell))
    (meaning : LocalMeaning primitive (.demand cell (.finish kont)) allocated outcome final) :
    EvalMeaning primitive ⟨n, v, k, .choose left right, native, values, needs⟩ kont world outcome final := by
  rcases meaning with ⟨input, selected, ⟨forced⟩, consumed⟩
  exact ⟨input, selected, ⟨.choose left right allocation forced⟩, consumed⟩

theorem evaluate_fallback_backward
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (world : NeedWorld Head Operation Effect StableFault NativeFault m) (work : Work)
    (closure : Closure Head Operation Effect m) (kont : Kont Head Operation Effect m)
    (stack : List (Frame (Resume Head Operation Effect m)))
    {next : NeedMachine Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    {final : NeedWorld Head Operation Effect StableFault NativeFault m}
    (noLocal : localStep (StableFault := StableFault) (NativeFault := NativeFault)
      (.evaluate closure kont) = none)
    (member : next ∈ step (reference primitive) ⟨world, .run (.evaluate closure kont) stack, work⟩)
    (meaning : ControlMeaning primitive next.control next.world outcome final) :
    ControlMeaning primitive (.run (.evaluate closure kont) stack) world outcome final := by
  rcases closure with ⟨n, v, k, code, native, values, needs⟩
  cases code with
  | returnValue value =>
      simp only [step, reference, action, List.mem_singleton] at member
      subst next
      exact ⟨_, world, ⟨_, world, ⟨.returnValue value native values needs world⟩,
        ⟨KontEval.returned_input kont _ world⟩⟩, meaning⟩
  | call operation argument =>
      simp only [step, reference, action, List.mem_singleton] at member
      subst next
      refine ⟨_, world, ⟨_, world, ⟨.call operation argument native values needs world⟩, ?_⟩, meaning⟩
      cases result : primitive operation (subst native argument) with
      | value value => exact ⟨KontEval.returned_input kont _ world⟩
      | stableFault fault =>
          have same : finish (liftOutcome (.stableFault fault)) kont =
              (Produced.stableFault fault : Outcome Head Operation Effect StableFault NativeFault m) := by
            induction kont <;> rfl
          rw [same]
          exact ⟨.stableFault kont fault world⟩
      | retryableFault reason =>
          have same : finish (liftOutcome (.retryableFault reason)) kont =
              (liftOutcome (.retryableFault reason) : Outcome Head Operation Effect StableFault NativeFault m) := by
            induction kont <;> rfl
          rw [same]
          exact ⟨.retryableFault kont _ world⟩
  | emit effect body =>
      simp only [step, reference, action, List.mem_singleton] at member
      subst next
      rcases meaning with ⟨result, selected, ⟨raw, bodyFinal, ⟨evaluated⟩, consumed⟩, remaining⟩
      exact ⟨result, selected, ⟨raw, bodyFinal, ⟨.emit effect evaluated⟩, consumed⟩, remaining⟩
  | forceNeed reference =>
      simp only [step, PolarizedNeedMachine.reference, action, List.mem_singleton] at member
      subst next
      rcases meaning with ⟨input, selected, ⟨forced⟩, result, completed, resumed, remaining⟩
      exact ⟨result, completed, ⟨input, selected, ⟨.forceNeed reference forced⟩, resumed⟩, remaining⟩
  | bindNative first body =>
      cases allocation : world.allocate? ⟨n, v, k, first, native, values, needs⟩ with
      | none =>
          simp only [step, reference, action, allocation, List.mem_singleton] at member
          subst next
          exact ⟨_, _, ⟨_, _, ⟨.bindNativeAllocationFailure body allocation⟩,
            ⟨.retryableFault _ _ _⟩⟩, meaning⟩
      | some allocated =>
          rcases allocated with ⟨allocated, cell⟩
          simp only [step, reference, action, allocation, List.mem_singleton] at member
          subst next
          rcases meaning with ⟨result, selected, demanded, remaining⟩
          exact ⟨result, selected, bindNative_meaning allocation demanded, remaining⟩
  | bindValue first body =>
      cases allocation : world.allocate? ⟨n, v, k, first, native, values, needs⟩ with
      | none =>
          simp only [step, reference, action, allocation, List.mem_singleton] at member
          subst next
          exact ⟨_, _, ⟨_, _, ⟨.bindValueAllocationFailure body allocation⟩,
            ⟨.retryableFault _ _ _⟩⟩, meaning⟩
      | some allocated =>
          rcases allocated with ⟨allocated, cell⟩
          simp only [step, reference, action, allocation, List.mem_singleton] at member
          subst next
          rcases meaning with ⟨result, selected, demanded, remaining⟩
          exact ⟨result, selected, bindValue_meaning allocation demanded, remaining⟩
  | sequenceSigma first body =>
      cases allocation : world.allocate? ⟨n, v, k, first, native, values, needs⟩ with
      | none =>
          simp only [step, reference, action, allocation, List.mem_singleton] at member
          subst next
          exact ⟨_, _, ⟨_, _, ⟨.sequenceSigmaAllocationFailure body allocation⟩,
            ⟨.retryableFault _ _ _⟩⟩, meaning⟩
      | some allocated =>
          rcases allocated with ⟨allocated, cell⟩
          simp only [step, reference, action, allocation, List.mem_singleton] at member
          subst next
          rcases meaning with ⟨result, selected, demanded, remaining⟩
          exact ⟨result, selected, sequenceSigma_meaning allocation demanded, remaining⟩
  | choose left right =>
      cases allocation : world.allocate? ⟨n, v, k, .choose left right, native, values, needs⟩ with
      | none =>
          simp only [step, reference, action, allocation, List.mem_singleton] at member
          subst next
          exact ⟨_, _, ⟨_, _, ⟨.chooseAllocationFailure left right allocation⟩,
            ⟨.retryableFault _ _ _⟩⟩, meaning⟩
      | some allocated =>
          rcases allocated with ⟨allocated, cell⟩
          simp only [step, reference, action, allocation, List.mem_singleton] at member
          subst next
          rcases meaning with ⟨result, selected, demanded, remaining⟩
          exact ⟨result, selected, choose_meaning left right allocation demanded, remaining⟩
  | letNeed suspended body =>
      cases allocation : world.allocate? ⟨n, v, k, suspended, native, values, needs⟩ with
      | none =>
          simp only [step, reference, action, allocation, List.mem_singleton] at member
          subst next
          exact ⟨_, _, ⟨_, _, ⟨.letNeedAllocationFailure body allocation⟩,
            ⟨.retryableFault _ _ _⟩⟩, meaning⟩
      | some allocated =>
          rcases allocated with ⟨allocated, cell⟩
          simp only [step, reference, action, allocation, List.mem_singleton] at member
          subst next
          rcases meaning with ⟨result, selected, ⟨raw, bodyFinal, ⟨evaluated⟩, consumed⟩, remaining⟩
          exact ⟨result, selected, ⟨raw, bodyFinal, ⟨.letNeed allocation evaluated⟩, consumed⟩, remaining⟩
  | nativeLambda body =>
      simp only [step, reference, action, List.mem_singleton] at member
      subst next
      refine ⟨_, world, ⟨_, world, ⟨.nativeLambda body native values needs world⟩, ?_⟩, meaning⟩
      cases kont with
      | done => exact ⟨.done _ _⟩
      | pair first rest => exact ⟨.pairMismatch first rest _ world
          (by intro term impossible; cases impossible)⟩
      | nativeApply argument rest => cases noLocal
      | valueApply argument rest => exact ⟨.valueMismatch argument rest _ world
          (by intro function impossible; cases impossible)⟩
  | valueLambda body =>
      simp only [step, reference, action, List.mem_singleton] at member
      subst next
      refine ⟨_, world, ⟨_, world, ⟨.valueLambda body native values needs world⟩, ?_⟩, meaning⟩
      cases kont with
      | done => exact ⟨.done _ _⟩
      | pair first rest => exact ⟨.pairMismatch first rest _ world
          (by intro term impossible; cases impossible)⟩
      | nativeApply argument rest => exact ⟨.nativeMismatch argument rest _ world
          (by intro function impossible; cases impossible)⟩
      | valueApply argument rest => cases noLocal
  | nativeApply function argument => cases noLocal
  | valueApply function argument => cases noLocal
  | forceThunk value =>
      simp only [localStep] at noLocal
      split at noLocal <;> cases noLocal
  | unpackNative value body =>
      simp only [localStep] at noLocal
      split at noLocal <;> cases noLocal

#print axioms bindNative_meaning
#print axioms bindValue_meaning
#print axioms sequenceSigma_meaning
#print axioms choose_meaning
#print axioms evaluate_fallback_backward

end PolarizedNeedNaturalSemantics.Reflection
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
