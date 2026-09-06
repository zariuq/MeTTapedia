import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedNaturalAdequacy

/-!
# Exact active-evaluation equations for captured computations

Ordinary thunk forcing and the three principal lexical openings preserve the
literal outcome and complete final world. The right sides retain the captured
source body and extend its environments; they are not source terms obtained
by syntactic substitution. These are equations for active evaluation, not a
congruence under arbitrary source capture or allocation, and not eta or monad
laws. Their machine corollaries concern completed runs, not equal fuel or work.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace PolarizedNeedNaturalSemantics

open PrimeNeedReference PolarizedNeedMachine
open PolarizedNeed (Value Computation)

variable {Head Operation Effect StableFault NativeFault : Type} {n m v k : Nat}
  {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
  {native : Sub Head n m} {values : Fin v → RuntimeValue Head Operation Effect m}
  {needs : Fin k → CellId}
  {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
  {outcome : Outcome Head Operation Effect StableFault NativeFault m}

theorem forceThunk_thunk_iff (body : Computation Head Operation Effect n v k) :
    Nonempty (Eval primitive ⟨n, v, k, .forceThunk (.thunk body), native, values, needs⟩
      world outcome final) ↔
    Nonempty (Eval primitive ⟨n, v, k, body, native, values, needs⟩ world outcome final) := by
  constructor
  · rintro ⟨evaluation⟩
    cases evaluation with
    | forceThunk _ captured bodyEvaluation =>
        cases captured
        exact ⟨bodyEvaluation⟩
    | forceThunkMismatch _ _ mismatch =>
        exact False.elim (mismatch _ _ _ _ _ _ _ rfl)
  · rintro ⟨evaluation⟩
    exact ⟨.forceThunk (.thunk body) rfl evaluation⟩

theorem nativeApply_nativeLambda_iff
    (body : Computation Head Operation Effect (n + 1) v k) (argument : Tm Head n) :
    Nonempty (Eval primitive
      ⟨n, v, k, .nativeApply (.nativeLambda body) argument, native, values, needs⟩
      world outcome final) ↔
    Nonempty (Eval primitive
      (NativeBody.open ⟨n, v, k, body, native, values, needs⟩ (subst native argument))
      world outcome final) := by
  constructor
  · rintro ⟨evaluation⟩
    cases evaluation with
    | nativeApply _ function bodyEvaluation =>
        cases function
        exact ⟨bodyEvaluation⟩
    | nativeApplyMismatch _ function mismatch =>
        cases function
        exact False.elim (mismatch _ rfl)
    | nativeApplyFault _ function fault =>
        cases function
        cases fault
  · rintro ⟨evaluation⟩
    exact ⟨.nativeApply argument (.nativeLambda body native values needs world) evaluation⟩

theorem valueApply_valueLambda_iff
    (body : Computation Head Operation Effect n (v + 1) k)
    (argument : Value Head Operation Effect n v k) :
    Nonempty (Eval primitive
      ⟨n, v, k, .valueApply (.valueLambda body) argument, native, values, needs⟩
      world outcome final) ↔
    Nonempty (Eval primitive
      (ValueBody.open ⟨n, v, k, body, native, values, needs⟩
        (captureValue native values needs argument)) world outcome final) := by
  constructor
  · rintro ⟨evaluation⟩
    cases evaluation with
    | valueApply _ function bodyEvaluation =>
        cases function
        exact ⟨bodyEvaluation⟩
    | valueApplyMismatch _ function mismatch =>
        cases function
        exact False.elim (mismatch _ rfl)
    | valueApplyFault _ function fault =>
        cases function
        cases fault
  · rintro ⟨evaluation⟩
    exact ⟨.valueApply argument (.valueLambda body native values needs world) evaluation⟩

theorem unpackNative_packNative_iff
    (index : Tm Head n) (value : Value Head Operation Effect n v k)
    (body : Computation Head Operation Effect (n + 1) (v + 1) k) :
    Nonempty (Eval primitive
      ⟨n, v, k, .unpackNative (.packNative index value) body, native, values, needs⟩
      world outcome final) ↔
    Nonempty (Eval primitive
      (PairBody.open ⟨n, v, k, body, native, values, needs⟩
        (subst native index) (captureValue native values needs value)) world outcome final) := by
  constructor
  · rintro ⟨evaluation⟩
    cases evaluation with
    | unpackNative _ captured bodyEvaluation =>
        cases captured
        exact ⟨bodyEvaluation⟩
    | unpackNativeMismatch _ _ _ mismatch =>
        exact False.elim (mismatch _ _ rfl)
  · rintro ⟨evaluation⟩
    exact ⟨.unpackNative (.packNative index value) rfl evaluation⟩

theorem forceThunk_thunk_runSegment_iff (body : Computation Head Operation Effect n v k) :
    RunSegment primitive world
      (.run (.evaluate ⟨n, v, k, .forceThunk (.thunk body), native, values, needs⟩ .done) [])
      final (.halted outcome) ↔
    RunSegment primitive world
      (.run (.evaluate ⟨n, v, k, body, native, values, needs⟩ .done) []) final (.halted outcome) := by
  rw [← eval_iff_runSegment, ← eval_iff_runSegment]
  exact forceThunk_thunk_iff body

theorem nativeApply_nativeLambda_runSegment_iff
    (body : Computation Head Operation Effect (n + 1) v k) (argument : Tm Head n) :
    RunSegment primitive world
      (.run (.evaluate
        ⟨n, v, k, .nativeApply (.nativeLambda body) argument, native, values, needs⟩ .done) [])
      final (.halted outcome) ↔
    RunSegment primitive world
      (.run (.evaluate
        (NativeBody.open ⟨n, v, k, body, native, values, needs⟩ (subst native argument)) .done) [])
      final (.halted outcome) := by
  rw [← eval_iff_runSegment, ← eval_iff_runSegment]
  exact nativeApply_nativeLambda_iff body argument

theorem valueApply_valueLambda_runSegment_iff
    (body : Computation Head Operation Effect n (v + 1) k)
    (argument : Value Head Operation Effect n v k) :
    RunSegment primitive world
      (.run (.evaluate
        ⟨n, v, k, .valueApply (.valueLambda body) argument, native, values, needs⟩ .done) [])
      final (.halted outcome) ↔
    RunSegment primitive world
      (.run (.evaluate
        (ValueBody.open ⟨n, v, k, body, native, values, needs⟩
          (captureValue native values needs argument)) .done) []) final (.halted outcome) := by
  rw [← eval_iff_runSegment, ← eval_iff_runSegment]
  exact valueApply_valueLambda_iff body argument

theorem unpackNative_packNative_runSegment_iff
    (index : Tm Head n) (value : Value Head Operation Effect n v k)
    (body : Computation Head Operation Effect (n + 1) (v + 1) k) :
    RunSegment primitive world
      (.run (.evaluate
        ⟨n, v, k, .unpackNative (.packNative index value) body, native, values, needs⟩ .done) [])
      final (.halted outcome) ↔
    RunSegment primitive world
      (.run (.evaluate
        (PairBody.open ⟨n, v, k, body, native, values, needs⟩
          (subst native index) (captureValue native values needs value)) .done) [])
      final (.halted outcome) := by
  rw [← eval_iff_runSegment, ← eval_iff_runSegment]
  exact unpackNative_packNative_iff index value body

#print axioms forceThunk_thunk_iff
#print axioms nativeApply_nativeLambda_iff
#print axioms valueApply_valueLambda_iff
#print axioms unpackNative_packNative_iff
#print axioms forceThunk_thunk_runSegment_iff
#print axioms nativeApply_nativeLambda_runSegment_iff
#print axioms valueApply_valueLambda_runSegment_iff
#print axioms unpackNative_packNative_runSegment_iff

end PolarizedNeedNaturalSemantics
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
