import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedNaturalEquations

/-!
# Completed evaluation equivalence under active consumers

Equal finite source evaluations may be consumed by the same first-class
continuation. The intermediate answer and entire world are retained, including
the lexical environment of a function and the heap used when it is applied.
The result is an equivalence of actual completed machine runs, not merely of
an abstract sequencing operation.

The relation is deliberately on active closures. It is not a congruence under
source quotation, capture or allocation: those operations retain source data.
It does not establish divergence preservation or compare derivation
multiplicity, fuel or work. Transferring admission below requires independent
typing of one complete source consumer;
evaluation equivalence itself does not supply source formation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace PolarizedNeedNaturalSemantics

open PrimeNeedReference PolarizedNeedMachine
open PolarizedNeed (Computation CTy)

variable {Head Operation Effect StableFault NativeFault : Type} {m : Nat}
  {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}

/-- Equality of finite completed results at the literal answer/full-world
observer. In particular, function answers retain their captured source. -/
def EvaluationEquivalent
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (left right : Closure Head Operation Effect m) : Prop :=
  ∀ world outcome final, Nonempty (Eval primitive left world outcome final) ↔
    Nonempty (Eval primitive right world outcome final)

namespace EvaluationEquivalent

variable {left middle right : Closure Head Operation Effect m}

theorem refl (closure : Closure Head Operation Effect m) :
    EvaluationEquivalent primitive closure closure := fun _ _ _ => Iff.rfl

theorem symm (equal : EvaluationEquivalent primitive left right) :
    EvaluationEquivalent primitive right left := fun world outcome final =>
  (equal world outcome final).symm

theorem trans (first : EvaluationEquivalent primitive left middle)
    (second : EvaluationEquivalent primitive middle right) :
    EvaluationEquivalent primitive left right := fun world outcome final =>
  (first world outcome final).trans (second world outcome final)

theorem iff_completed_runs : EvaluationEquivalent primitive left right ↔
    ∀ world outcome final,
      RunSegment primitive world (.run (.evaluate left .done) []) final (.halted outcome) ↔
      RunSegment primitive world (.run (.evaluate right .done) []) final (.halted outcome) := by
  simp only [EvaluationEquivalent, ← eval_iff_runSegment]

/-- The same consumer receives exactly the same intermediate answer and world;
it may subsequently enter a computation function and perform further effects. -/
theorem consumer_meaning (equal : EvaluationEquivalent primitive left right)
    (kont : Kont Head Operation Effect m)
    (world : NeedWorld Head Operation Effect StableFault NativeFault m)
    (outcome : Outcome Head Operation Effect StableFault NativeFault m)
    (final : NeedWorld Head Operation Effect StableFault NativeFault m) :
    Reflection.EvalMeaning primitive left kont world outcome final ↔
      Reflection.EvalMeaning primitive right kont world outcome final := by
  constructor
  · rintro ⟨raw, selected, evaluated, consumed⟩
    exact ⟨raw, selected, (equal world raw selected).mp evaluated, consumed⟩
  · rintro ⟨raw, selected, evaluated, consumed⟩
    exact ⟨raw, selected, (equal world raw selected).mpr evaluated, consumed⟩

end EvaluationEquivalent

/-- Completed-run adequacy with an arbitrary active first-class consumer.
The empty protocol stack is at the outer boundary, not a restriction on the
allocations, cache demands or function calls performed by either derivation. -/
theorem evalMeaning_iff_runSegment {closure : Closure Head Operation Effect m}
    {kont : Kont Head Operation Effect m}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head Operation Effect StableFault NativeFault m} :
    Reflection.EvalMeaning primitive closure kont world outcome final ↔
      RunSegment primitive world (.run (.evaluate closure kont) []) final (.halted outcome) := by
  constructor
  · rintro ⟨raw, selected, ⟨evaluation⟩, ⟨consumer⟩⟩
    exact (evaluation.sound consumer []).trans (RunSegment.halt primitive final outcome)
  · intro execution
    obtain ⟨length, finalWork, steps⟩ := execution {}
    have meaning := Reflection.steps_backward steps
      (show Reflection.ControlMeaning primitive (.halted outcome) final outcome final from
        ⟨rfl, rfl⟩)
    obtain ⟨raw, selected, evaluated, rest⟩ := meaning
    obtain ⟨rfl, rfl⟩ := rest
    exact evaluated

namespace EvaluationEquivalent

variable {left right : Closure Head Operation Effect m}

theorem consumer_runs (equal : EvaluationEquivalent primitive left right)
    (kont : Kont Head Operation Effect m)
    (world : NeedWorld Head Operation Effect StableFault NativeFault m)
    (outcome : Outcome Head Operation Effect StableFault NativeFault m)
    (final : NeedWorld Head Operation Effect StableFault NativeFault m) :
    RunSegment primitive world (.run (.evaluate left kont) []) final (.halted outcome) ↔
      RunSegment primitive world (.run (.evaluate right kont) []) final (.halted outcome) := by
  rw [← evalMeaning_iff_runSegment, ← evalMeaning_iff_runSegment]
  exact equal.consumer_meaning kont world outcome final

variable {R : Rules Head} {signature : ScopedComputation.OperationSignature Head Operation}
  {Δ : Ctx Head m}

/-- A run of the replacement has the same typed final heap and answer as a
run of the independently typed reference consumer. No typing of the replacement
is inferred solely from its completed-evaluation relation. -/
theorem consumer_final_world_typing (equal : EvaluationEquivalent primitive left right)
    {kont : Kont Head Operation Effect m}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    (execution : RunSegment primitive world (.run (.evaluate right kont) []) final (.halted outcome))
    (sound : PrimitiveSoundness R signature Δ primitive)
    {types : CellTypes Head m} {A : CTy Head m} {work : Work}
    (typed : MachineTyping R signature Δ types
      ⟨world, .run (.evaluate left kont) [], work⟩ A) :
    ∃ finalTypes, StoreExtends types finalTypes ∧ HeapTyping R signature Δ finalTypes final.heap ∧
      OutcomeTyping R signature Δ finalTypes A outcome := by
  obtain ⟨length, finalWork, steps⟩ :=
    ((equal.consumer_runs kont world outcome final).mpr execution) work
  obtain ⟨finalTypes, grows, finalTyped⟩ := machine_steps_typing sound steps typed
  exact ⟨finalTypes, grows, finalTyped.heap, finalTyped.haltedOutcome rfl⟩

theorem consumer_native_judgment (equal : EvaluationEquivalent primitive left right)
    {kont : Kont Head Operation Effect m}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {value A : Tm Head m}
    (execution : RunSegment primitive world (.run (.evaluate right kont) [])
      final (.halted (.value (.returned (.native value)))))
    (sound : PrimitiveSoundness R signature Δ primitive)
    (context : FormationSensitive.ContextFormation R Δ)
    {types : CellTypes Head m} {work : Work}
    (typed : MachineTyping R signature Δ types
      ⟨world, .run (.evaluate left kont) [], work⟩ (.returns (.native A))) :
    FormationSensitive.Judgment R Δ value A := by
  obtain ⟨_, _, _, admitted⟩ := equal.consumer_final_world_typing execution sound typed
  cases admitted with
  | value answer =>
      cases answer with
      | returned valueTyped => exact ⟨context, valueTyped.native_admitted⟩

end EvaluationEquivalent

section Equations

variable {n v k : Nat} {native : Sub Head n m}
  {values : Fin v → RuntimeValue Head Operation Effect m} {needs : Fin k → CellId}

theorem forceThunk_thunk_equivalent (body : Computation Head Operation Effect n v k) :
    EvaluationEquivalent primitive
      ⟨n, v, k, .forceThunk (.thunk body), native, values, needs⟩
      ⟨n, v, k, body, native, values, needs⟩ := fun _ _ _ => forceThunk_thunk_iff body

theorem nativeApply_nativeLambda_equivalent
    (body : Computation Head Operation Effect (n + 1) v k) (argument : Tm Head n) :
    EvaluationEquivalent primitive
      ⟨n, v, k, .nativeApply (.nativeLambda body) argument, native, values, needs⟩
      (NativeBody.open ⟨n, v, k, body, native, values, needs⟩ (subst native argument)) :=
  fun _ _ _ => nativeApply_nativeLambda_iff body argument

theorem valueApply_valueLambda_equivalent
    (body : Computation Head Operation Effect n (v + 1) k)
    (argument : PolarizedNeed.Value Head Operation Effect n v k) :
    EvaluationEquivalent primitive
      ⟨n, v, k, .valueApply (.valueLambda body) argument, native, values, needs⟩
      (ValueBody.open ⟨n, v, k, body, native, values, needs⟩
        (captureValue native values needs argument)) :=
  fun _ _ _ => valueApply_valueLambda_iff body argument

theorem unpackNative_packNative_equivalent
    (index : Tm Head n) (value : PolarizedNeed.Value Head Operation Effect n v k)
    (body : Computation Head Operation Effect (n + 1) (v + 1) k) :
    EvaluationEquivalent primitive
      ⟨n, v, k, .unpackNative (.packNative index value) body, native, values, needs⟩
      (PairBody.open ⟨n, v, k, body, native, values, needs⟩
        (subst native index) (captureValue native values needs value)) :=
  fun _ _ _ => unpackNative_packNative_iff index value body

end Equations

/-- A nonempty higher-order use: the consumer applies a forced computation
function, which records an effect before returning its native argument. -/
theorem forced_function_consumer_run (effect : Effect) (argument : Tm Head m)
    (world : NeedWorld Head Operation Effect StableFault NativeFault m) :
    RunSegment primitive world
      (.run (.evaluate
        ⟨0, 0, 0, .forceThunk (.thunk
          (.nativeLambda (.emit effect (.returnValue (.native (.var 0)))))),
          Fin.elim0, Fin.elim0, Fin.elim0⟩
        (.nativeApply argument .done)) [])
      (world.record (.effect effect)).1 (.halted (.value (.returned (.native argument)))) := by
  apply ((forceThunk_thunk_equivalent
    (.nativeLambda (.emit effect (.returnValue (.native (.var 0)))))).consumer_runs
    (.nativeApply argument .done) world _ _).mpr
  apply evalMeaning_iff_runSegment.mp
  refine ⟨_, world, ⟨.nativeLambda _ Fin.elim0 Fin.elim0 Fin.elim0 world⟩, ?_⟩
  exact ⟨.nativeApply argument _
    (.emit effect (.returnValue (.native (.var 0)) (Fin.cases argument Fin.elim0)
      Fin.elim0 Fin.elim0 _)) (.done _ _)⟩

#print axioms EvaluationEquivalent.refl
#print axioms EvaluationEquivalent.symm
#print axioms EvaluationEquivalent.trans
#print axioms EvaluationEquivalent.iff_completed_runs
#print axioms EvaluationEquivalent.consumer_meaning
#print axioms evalMeaning_iff_runSegment
#print axioms EvaluationEquivalent.consumer_runs
#print axioms EvaluationEquivalent.consumer_final_world_typing
#print axioms EvaluationEquivalent.consumer_native_judgment
#print axioms forceThunk_thunk_equivalent
#print axioms nativeApply_nativeLambda_equivalent
#print axioms valueApply_valueLambda_equivalent
#print axioms unpackNative_packNative_equivalent
#print axioms forced_function_consumer_run

end PolarizedNeedNaturalSemantics
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
