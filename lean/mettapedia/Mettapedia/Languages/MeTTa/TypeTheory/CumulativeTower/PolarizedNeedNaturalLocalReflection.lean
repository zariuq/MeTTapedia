import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedNaturalMeaning

/-!
# Reconstructing source meaning through intercepted local transitions

Applications reconstruct a source function evaluation followed by its captured
body evaluation. Lambda delivery, ordinary force and packet elimination retain
the captured source environment and the current world. These proofs inspect the
actual local transition; no source derivation of its predecessor is supplied.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace PolarizedNeedNaturalSemantics
namespace Reflection

open PrimeNeedReference PolarizedNeedMachine
open PolarizedNeed (Value Computation)

variable {Head Operation Effect StableFault NativeFault : Type} {n m v k : Nat}

theorem nativeApply_meaning
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    (argument : Tm Head n) {function : Computation Head Operation Effect n v k}
    {native : Sub Head n m} {values : Fin v → RuntimeValue Head Operation Effect m}
    {needs : Fin k → CellId} {kont : Kont Head Operation Effect m}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    (meaning : EvalMeaning primitive ⟨n, v, k, function, native, values, needs⟩
      (.nativeApply (subst native argument) kont) world outcome final) :
    EvalMeaning primitive ⟨n, v, k, .nativeApply function argument, native, values, needs⟩
      kont world outcome final := by
  rcases meaning with ⟨input, selected, ⟨evaluated⟩, ⟨consumed⟩⟩
  cases consumed with
  | nativeApply _ body bodyEval remaining =>
      exact ⟨_, _, ⟨.nativeApply argument evaluated bodyEval⟩, ⟨remaining⟩⟩
  | nativeMismatch _ _ answer _ wrong =>
      exact ⟨_, _, ⟨.nativeApplyMismatch argument evaluated wrong⟩, ⟨.retryableFault kont _ _⟩⟩
  | stableFault _ fault _ =>
      exact ⟨_, _, ⟨.nativeApplyFault argument evaluated (.stableFault fault)⟩,
        ⟨.stableFault kont fault _⟩⟩
  | retryableFault _ reason _ =>
      exact ⟨_, _, ⟨.nativeApplyFault argument evaluated (.retryableFault reason)⟩,
        ⟨.retryableFault kont reason _⟩⟩

theorem valueApply_meaning
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    (argument : Value Head Operation Effect n v k) {function : Computation Head Operation Effect n v k}
    {native : Sub Head n m} {values : Fin v → RuntimeValue Head Operation Effect m}
    {needs : Fin k → CellId} {kont : Kont Head Operation Effect m}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    (meaning : EvalMeaning primitive ⟨n, v, k, function, native, values, needs⟩
      (.valueApply (captureValue native values needs argument) kont) world outcome final) :
    EvalMeaning primitive ⟨n, v, k, .valueApply function argument, native, values, needs⟩
      kont world outcome final := by
  rcases meaning with ⟨input, selected, ⟨evaluated⟩, ⟨consumed⟩⟩
  cases consumed with
  | valueApply _ body bodyEval remaining =>
      exact ⟨_, _, ⟨.valueApply argument evaluated bodyEval⟩, ⟨remaining⟩⟩
  | valueMismatch _ _ answer _ wrong =>
      exact ⟨_, _, ⟨.valueApplyMismatch argument evaluated wrong⟩, ⟨.retryableFault kont _ _⟩⟩
  | stableFault _ fault _ =>
      exact ⟨_, _, ⟨.valueApplyFault argument evaluated (.stableFault fault)⟩,
        ⟨.stableFault kont fault _⟩⟩
  | retryableFault _ reason _ =>
      exact ⟨_, _, ⟨.valueApplyFault argument evaluated (.retryableFault reason)⟩,
        ⟨.retryableFault kont reason _⟩⟩

theorem local_meaning_backward
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    {state next : Local Head Operation Effect StableFault NativeFault m}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    (transition : localStep state = some next)
    (meaning : LocalMeaning primitive next world outcome final) :
    LocalMeaning primitive state world outcome final := by
  cases state with
  | demand cell resume => simp [localStep] at transition
  | complete result => simp [localStep] at transition
  | evaluate closure kont =>
      rcases closure with ⟨n, v, k, code, native, values, needs⟩
      cases code with
      | returnValue value | bindNative first body | bindValue first body
          | sequenceSigma first body | choose first body | call first body
          | emit first body | letNeed first body | forceNeed value =>
          simp [localStep] at transition
      | nativeApply function argument =>
          simp only [localStep, Option.some.injEq] at transition
          subst next
          exact nativeApply_meaning argument meaning
      | valueApply function argument =>
          simp only [localStep, Option.some.injEq] at transition
          subst next
          exact valueApply_meaning argument meaning
      | nativeLambda body =>
          cases kont with
          | done | pair first rest | valueApply argument rest =>
              simp [localStep] at transition
          | nativeApply argument rest =>
              simp only [localStep, Option.some.injEq] at transition
              subst next
              rcases meaning with ⟨raw, selected, ⟨evaluated⟩, ⟨consumed⟩⟩
              exact ⟨_, world, ⟨.nativeLambda body native values needs world⟩,
                ⟨.nativeApply argument _ evaluated consumed⟩⟩
      | valueLambda body =>
          cases kont with
          | done | pair first rest | nativeApply argument rest =>
              simp [localStep] at transition
          | valueApply argument rest =>
              simp only [localStep, Option.some.injEq] at transition
              subst next
              rcases meaning with ⟨raw, selected, ⟨evaluated⟩, ⟨consumed⟩⟩
              exact ⟨_, world, ⟨.valueLambda body native values needs world⟩,
                ⟨.valueApply argument _ evaluated consumed⟩⟩
      | forceThunk value =>
          cases captured : captureValue native values needs value with
          | thunk code capturedNative capturedValues capturedNeeds =>
              simp only [localStep, captured, Option.some.injEq] at transition
              subst next
              rcases meaning with ⟨raw, selected, ⟨evaluated⟩, consumed⟩
              exact ⟨raw, selected, ⟨.forceThunk value captured evaluated⟩, consumed⟩
          | native term =>
              simp only [localStep, captured, Option.some.injEq] at transition
              subst next
              rcases meaning with ⟨rfl, rfl⟩
              exact ⟨_, world, ⟨.forceThunkMismatch value world (by
                intro p w l code capturedNative capturedValues capturedNeeds impossible
                rw [captured] at impossible
                cases impossible)⟩, ⟨.retryableFault kont _ world⟩⟩
          | packNative index payload =>
              simp only [localStep, captured, Option.some.injEq] at transition
              subst next
              rcases meaning with ⟨rfl, rfl⟩
              exact ⟨_, world, ⟨.forceThunkMismatch value world (by
                intro p w l code capturedNative capturedValues capturedNeeds impossible
                rw [captured] at impossible
                cases impossible)⟩, ⟨.retryableFault kont _ world⟩⟩
      | unpackNative value body =>
          cases captured : captureValue native values needs value with
          | packNative index payload =>
              simp only [localStep, captured, Option.some.injEq] at transition
              subst next
              rcases meaning with ⟨raw, selected, ⟨evaluated⟩, consumed⟩
              exact ⟨raw, selected, ⟨.unpackNative value captured evaluated⟩, consumed⟩
          | native term =>
              simp only [localStep, captured, Option.some.injEq] at transition
              subst next
              rcases meaning with ⟨rfl, rfl⟩
              exact ⟨_, world, ⟨.unpackNativeMismatch value body world (by
                intro index payload impossible
                rw [captured] at impossible
                cases impossible)⟩, ⟨.retryableFault kont _ world⟩⟩
          | thunk code capturedNative capturedValues capturedNeeds =>
              simp only [localStep, captured, Option.some.injEq] at transition
              subst next
              rcases meaning with ⟨rfl, rfl⟩
              exact ⟨_, world, ⟨.unpackNativeMismatch value body world (by
                intro index payload impossible
                rw [captured] at impossible
                cases impossible)⟩, ⟨.retryableFault kont _ world⟩⟩

#print axioms nativeApply_meaning
#print axioms valueApply_meaning
#print axioms local_meaning_backward

end Reflection
end PolarizedNeedNaturalSemantics
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
