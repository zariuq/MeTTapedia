import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedNaturalSoundness
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedNaturalReflection
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedMachinePreservation

/-!
# Exact-world finite adequacy and admission for first-class owned computations

Independent source evaluation is equivalent to a completed finite run of the
actual local-step extension. Both directions preserve the full final world,
not only its native answer or effect projection. Source evaluation includes
raw faults; source formation is not an assumption of the adequacy theorem.

Admission is a separate consequence of independent source/environment typing
and primitive qualification. Its conclusion keeps the exact final heap, so
cached function bodies remain supported when cells were allocated during the
run. Neither finite adequacy nor admission is a termination, multiplicity or
runtime-cost theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace PolarizedNeedNaturalSemantics

open PrimeNeedReference PolarizedNeedMachine
open PolarizedNeed (CTy Computation)
open ScopedComputation (OperationSignature)

variable {Head Operation Effect StableFault NativeFault : Type} {m : Nat}
  {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}

theorem eval_iff_runSegment {closure : Closure Head Operation Effect m}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head Operation Effect StableFault NativeFault m} :
    Nonempty (Eval primitive closure world outcome final) ↔
      RunSegment primitive world (.run (.evaluate closure .done) []) final (.halted outcome) :=
  ⟨fun ⟨evaluation⟩ => evaluation.halts, Reflection.eval_of_runSegment⟩

theorem force_iff_runSegment {cell : CellId}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head Operation Effect StableFault NativeFault m} :
    Nonempty (Force primitive cell world outcome final) ↔
      RunSegment primitive world (.force cell []) final (.halted outcome) :=
  ⟨fun ⟨forcing⟩ => forcing.halts, Reflection.force_of_runSegment⟩

/-- The exact observed frontier state supplies its own source final world.
Other branches and other states returning the same answer are not substituted
for that state. -/
theorem frontier_halt_has_natural_derivation
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    {closure : Closure Head Operation Effect m}
    {world : NeedWorld Head Operation Effect StableFault NativeFault m}
    {work : Work} {fuel : Nat} {final : NeedMachine Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    (member : final ∈ PrimeNeedLocalSteps.runFrontier (extension primitive) fuel
      [⟨world, .run (.evaluate closure .done) [], work⟩])
    (observed : haltedOutcome final = some outcome) :
    Nonempty (Eval primitive closure world outcome final.world) := by
  obtain ⟨initial, membership, length, _, execution⟩ :=
    PrimeNeedLocalSteps.runFrontier_reachable (extension primitive) member
  cases List.mem_singleton.mp membership
  rcases final with ⟨finalWorld, control, finalWork⟩
  cases control with
  | run _ _ | force _ _ | returned _ _ => cases observed
  | halted result =>
      have same : result = outcome := Option.some.inj observed
      cases same
      exact Reflection.eval_of_steps execution

theorem answers_have_natural_derivations {closure : Closure Head Operation Effect m}
    {world : NeedWorld Head Operation Effect StableFault NativeFault m} {work : Work}
    {fuel : Nat} {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    (member : outcome ∈ PrimeNeedLocalSteps.answers (extension primitive) fuel
      ⟨world, .run (.evaluate closure .done) [], work⟩) :
    ∃ final, Nonempty (Eval primitive closure world outcome final) := by
  obtain ⟨final, member, observed⟩ := List.mem_filterMap.mp member
  exact ⟨final.world, frontier_halt_has_natural_derivation primitive member observed⟩

theorem answers_iff_natural {closure : Closure Head Operation Effect m}
    {world : NeedWorld Head Operation Effect StableFault NativeFault m} (work : Work)
    {outcome : Outcome Head Operation Effect StableFault NativeFault m} :
    (∃ fuel, outcome ∈ PrimeNeedLocalSteps.answers (extension primitive) fuel
      ⟨world, .run (.evaluate closure .done) [], work⟩) ↔
      ∃ final, Nonempty (Eval primitive closure world outcome final) := by
  constructor
  · rintro ⟨fuel, member⟩
    exact answers_have_natural_derivations member
  · rintro ⟨final, ⟨evaluation⟩⟩
    obtain ⟨length, finalWork, execution⟩ := evaluation.halts work
    exact ⟨length, (PrimeNeedLocalSteps.answers_iff_steps (extension primitive) length _ _).mpr
      ⟨length, Nat.le_refl _, final, finalWork, execution⟩⟩

theorem force_answers_iff_natural {cell : CellId}
    {world : NeedWorld Head Operation Effect StableFault NativeFault m} (work : Work)
    {outcome : Outcome Head Operation Effect StableFault NativeFault m} :
    (∃ fuel, outcome ∈ PrimeNeedLocalSteps.answers (extension primitive) fuel
      ⟨world, .force cell [], work⟩) ↔
      ∃ final, Nonempty (Force primitive cell world outcome final) := by
  constructor
  · rintro ⟨fuel, member⟩
    obtain ⟨length, _, final, finalWork, execution⟩ :=
      (PrimeNeedLocalSteps.answers_iff_steps (extension primitive) fuel _ _).mp member
    exact ⟨final, Reflection.force_of_steps execution⟩
  · rintro ⟨final, ⟨forcing⟩⟩
    obtain ⟨length, finalWork, execution⟩ := forcing.halts work
    exact ⟨length, (PrimeNeedLocalSteps.answers_iff_steps (extension primitive) length _ _).mpr
      ⟨length, Nat.le_refl _, final, finalWork, execution⟩⟩

variable {R : Rules Head} {signature : OperationSignature Head Operation} {Δ : Ctx Head m}

/-- Source-world adequacy uses the actual path endpoint, so preservation must
retain that endpoint rather than choose any state with the same answer. -/
theorem machine_steps_typing
    (sound : PrimitiveSoundness R signature Δ primitive)
    {types : CellTypes Head m} {A : CTy Head m} {length : Nat}
    {initial final : NeedMachine Head Operation Effect StableFault NativeFault m}
    (execution : PrimeNeedLocalSteps.Steps (extension primitive) length initial final)
    (typed : MachineTyping R signature Δ types initial A) :
    ∃ finalTypes, StoreExtends types finalTypes ∧ MachineTyping R signature Δ finalTypes final A := by
  induction execution generalizing types with
  | refl => exact ⟨types, StoreExtends.refl types, typed⟩
  | cons occurrence rest ih =>
      obtain ⟨nextTypes, grows, nextTyped⟩ :=
        step_preservation sound typed (occurrence.mem (extension primitive))
      obtain ⟨finalTypes, later, finalTyped⟩ := ih nextTyped
      exact ⟨finalTypes, grows.trans later, finalTyped⟩

theorem Eval.final_world_typing
    {closure : Closure Head Operation Effect m}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    (evaluation : Eval primitive closure world outcome final)
    (sound : PrimitiveSoundness R signature Δ primitive)
    {types : CellTypes Head m} {A : CTy Head m} {work : Work}
    (typed : MachineTyping R signature Δ types
      ⟨world, .run (.evaluate closure .done) [], work⟩ A) :
    ∃ finalTypes, StoreExtends types finalTypes ∧ HeapTyping R signature Δ finalTypes final.heap ∧
      OutcomeTyping R signature Δ finalTypes A outcome := by
  obtain ⟨length, finalWork, execution⟩ := evaluation.halts work
  obtain ⟨finalTypes, grows, finalTyped⟩ := machine_steps_typing sound execution typed
  exact ⟨finalTypes, grows, finalTyped.heap, finalTyped.haltedOutcome rfl⟩

theorem Force.final_world_typing
    {cell : CellId} {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    (forcing : Force primitive cell world outcome final)
    (sound : PrimitiveSoundness R signature Δ primitive)
    {types : CellTypes Head m} {A : CTy Head m} {work : Work}
    (typed : MachineTyping R signature Δ types ⟨world, .force cell [], work⟩ A) :
    ∃ finalTypes, StoreExtends types finalTypes ∧ HeapTyping R signature Δ finalTypes final.heap ∧
      OutcomeTyping R signature Δ finalTypes A outcome := by
  obtain ⟨length, finalWork, execution⟩ := forcing.halts work
  obtain ⟨finalTypes, grows, finalTyped⟩ := machine_steps_typing sound execution typed
  exact ⟨finalTypes, grows, finalTyped.heap, finalTyped.haltedOutcome rfl⟩

/-- Logical admission requires a formed target context and independently
qualified source execution. Natural evaluation alone supplies neither. -/
theorem Eval.native_judgment
    {closure : Closure Head Operation Effect m}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m} {value A : Tm Head m}
    (evaluation : Eval primitive closure world (.value (.returned (.native value))) final)
    (sound : PrimitiveSoundness R signature Δ primitive)
    (context : FormationSensitive.ContextFormation R Δ)
    {types : CellTypes Head m} {work : Work}
    (typed : MachineTyping R signature Δ types
      ⟨world, .run (.evaluate closure .done) [], work⟩ (.returns (.native A))) :
    FormationSensitive.Judgment R Δ value A := by
  obtain ⟨_, _, _, admitted⟩ := evaluation.final_world_typing sound typed
  cases admitted with
  | value answer =>
      cases answer with
      | returned valueTyped => exact ⟨context, valueTyped.native_admitted⟩

theorem Eval.source_value_judgment {n : Nat} {Γ : Ctx Head n}
    {code : Computation Head Operation Effect n 0 0} {A : Tm Head n}
    {native : Sub Head n m} {value : Tm Head m}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    (evaluation : Eval primitive ⟨n, 0, 0, code, native, Fin.elim0, Fin.elim0⟩ world
      (.value (.returned (.native value))) final)
    (sound : PrimitiveSoundness R signature Δ primitive)
    (context : FormationSensitive.ContextFormation R Δ)
    (source : PolarizedNeed.ComputationTyping R signature Γ Fin.elim0 Fin.elim0 code (.returns (.native A)))
    (environment : FormationSensitive.CtxMor R Γ Δ native)
    (empty : world.heap = Heap.empty) :
    FormationSensitive.Judgment R Δ value (subst native A) := by
  exact evaluation.native_judgment sound context
    (source_closed_initial_typing source environment world empty)

#print axioms eval_iff_runSegment
#print axioms force_iff_runSegment
#print axioms frontier_halt_has_natural_derivation
#print axioms answers_have_natural_derivations
#print axioms answers_iff_natural
#print axioms force_answers_iff_natural
#print axioms machine_steps_typing
#print axioms Eval.final_world_typing
#print axioms Force.final_world_typing
#print axioms Eval.native_judgment
#print axioms Eval.source_value_judgment

end PolarizedNeedNaturalSemantics
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
