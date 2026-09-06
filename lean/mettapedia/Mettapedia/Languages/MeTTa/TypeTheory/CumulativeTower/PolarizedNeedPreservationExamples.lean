import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedMachinePreservation
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedTypingExamples
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedMachineExamples

/-!
# Preserved shared computation functions with dependent native results

One Need cell caches a native-argument computation function, not a returned
native value. Its construction emits once; two calls emit separately and
return identity evidence at their distinct supplied native arguments.

Source admission is proved independently. General whole-machine preservation
then qualifies every bounded answer and excludes administrative polarity
faults at every fuel. Separate exact executions inspect the real completed
function cache and effect receipts. No general termination or source-adequacy
claim follows from these specimens.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace PolarizedNeedPreservationExamples

open PrimeNeedReference PolarizedNeed PolarizedNeedMachine

abbrev ground {n : Nat} : Tower.Tm n := .head .legacyGround

def signature : ScopedComputation.OperationSignature Tower.Head Unit where
  input _ := ground
  output _ := ground

def primitive {m : Nat} (_ : Unit) (argument : Tower.Tm m) : Produced (Tower.Tm m) Unit Unit :=
  .value argument

theorem primitive_sound {m : Nat} {Γ : Tower.Ctx m} :
    PrimitiveSoundness Tower.rules signature Γ primitive := by
  intro operation argument value _ admitted success
  cases success
  exact admitted

/-- The body is the admitted dependent reflexivity function, with a visible
per-call effect. Construction has its own separate effect. -/
def functionProducer {n v k : Nat} : Computation Tower.Head Unit Nat n v k :=
  .emit 3 (.nativeLambda (.emit 4 (.returnValue (.native (.refl (.var 0))))))

def sharedFunction {n : Nat} (left right : Tower.Tm n) : Computation Tower.Head Unit Nat n 0 0 :=
  .letNeed functionProducer
    (.sequenceSigma (.nativeApply (.forceNeed 0) left)
      (.nativeApply (.forceNeed 0) (rename wk right)))

def resultType {n : Nat} (left right : Tower.Tm n) : Tower.Tm n :=
  .sigma (.id ground left left) (.id ground (rename wk right) (rename wk right))

theorem function_producer_typed {n v k : Nat} {Γ : Tower.Ctx n}
    {sv : Fin v → VTy Tower.Head n} {sn : Fin k → CTy Tower.Head n} :
    ComputationTyping Tower.rules signature Γ sv sn functionProducer Examples.reflexiveType :=
  .emit (.nativeLambda Examples.ground_formed
    (.returns (.native ⟨.sort Tower.zero, .sort Tower.zero,
      .idForm (.headType .legacyGround) (.sort Tower.zero) (.var 0) (.var 0)⟩))
    (.emit (.returnValue (.native (.reflIntro (.var 0))))))

theorem result_type_formed {n : Nat} {Γ : Tower.Ctx n} {left right : Tower.Tm n}
    (leftTyped : FormationSensitive.Typing Tower.rules Γ left ground)
    (rightTyped : FormationSensitive.Typing Tower.rules Γ right ground) :
    NativeFormation Tower.rules Γ (resultType left right) :=
  ⟨.sort (.max Tower.zero Tower.zero), .sort _,
    .sigmaForm (.idForm (.headType .legacyGround) (.sort Tower.zero) leftTyped leftTyped)
      (.sort Tower.zero)
      (.idForm (.headType .legacyGround) (.sort Tower.zero) rightTyped.weaken rightTyped.weaken)
      (.sort Tower.zero) (.sorts Tower.zero Tower.zero)⟩

theorem shared_function_typed {n : Nat} {Γ : Tower.Ctx n} {left right : Tower.Tm n}
    (leftTyped : FormationSensitive.Typing Tower.rules Γ left ground)
    (rightTyped : FormationSensitive.Typing Tower.rules Γ right ground) :
    ComputationTyping Tower.rules signature Γ Fin.elim0 Fin.elim0 (sharedFunction left right)
      (.returns (.native (resultType left right))) := by
  apply ComputationTyping.letNeed Examples.reflexive_type_formed
    (.returns (.native (result_type_formed leftTyped rightTyped))) function_producer_typed
  apply ComputationTyping.sequenceSigma (result_type_formed leftTyped rightTyped)
  · have function : ComputationTyping (Effect := Nat) Tower.rules signature Γ Fin.elim0
        (extendNeedTypes Examples.reflexiveType Fin.elim0) (.forceNeed 0) Examples.reflexiveType :=
      .forceNeed 0
    exact .nativeApply function leftTyped
  · have function : ComputationTyping (Effect := Nat) Tower.rules signature
        (.snoc Γ (.id ground left left)) (weakenValueTypes (Fin.elim0 : Fin 0 → VTy Tower.Head n))
        (weakenNeedTypes (extendNeedTypes (Examples.reflexiveType : CTy Tower.Head n) Fin.elim0))
        (.forceNeed 0) Examples.reflexiveType := .forceNeed 0
    exact .nativeApply function rightTyped.weaken

def initial {n : Nat} (source : Computation Tower.Head Unit Nat n 0 0) :
    NeedMachine Tower.Head Unit Nat Unit Unit n where
  world := ⟨0, [], .empty, .empty, 0, 0⟩
  control := .run (.evaluate ⟨n, 0, 0, source, ids, Fin.elim0, Fin.elim0⟩ .done) []

theorem shared_initial_typed {n : Nat} {Γ : Tower.Ctx n} {left right : Tower.Tm n}
    (leftTyped : FormationSensitive.Typing Tower.rules Γ left ground)
    (rightTyped : FormationSensitive.Typing Tower.rules Γ right ground) :
    MachineTyping Tower.rules signature Γ (fun _ => none) (initial (sharedFunction left right))
      (.returns (.native (resultType left right))) := by
  have native : FormationSensitive.CtxMor Tower.rules Γ Γ ids := by
    intro i
    simpa only [subst_ids, ids] using (FormationSensitive.Typing.var (R := Tower.rules) (Γ := Γ) i)
  simpa only [initial, CTy.substitute_ids] using
    source_closed_initial_typing (shared_function_typed leftTyped rightTyped) native
      (⟨0, [], .empty, .empty, 0, 0⟩ : NeedWorld Tower.Head Unit Nat Unit Unit n) rfl

/-- Every completed answer comes from the general preservation invariant,
including the enlarged cell assignment introduced during the run. -/
theorem shared_answers_typed {n : Nat} {Γ : Tower.Ctx n} {left right : Tower.Tm n}
    (leftTyped : FormationSensitive.Typing Tower.rules Γ left ground)
    (rightTyped : FormationSensitive.Typing Tower.rules Γ right ground)
    {fuel : Nat} {outcome : Outcome Tower.Head Unit Nat Unit Unit n}
    (returned : outcome ∈ PrimeNeedLocalSteps.answers (extension primitive) fuel
      (initial (sharedFunction left right))) :
    ∃ types, StoreExtends (fun _ => none) types ∧
      OutcomeTyping Tower.rules signature Γ types (.returns (.native (resultType left right))) outcome :=
  answers_typing primitive_sound (shared_initial_typed leftTyped rightTyped) returned

theorem shared_native_result_judgment {n : Nat} {Γ : Tower.Ctx n} {left right value : Tower.Tm n}
    (context : FormationSensitive.ContextFormation Tower.rules Γ)
    (leftTyped : FormationSensitive.Typing Tower.rules Γ left ground)
    (rightTyped : FormationSensitive.Typing Tower.rules Γ right ground)
    {fuel : Nat} (returned : .value (.returned (.native value)) ∈
      PrimeNeedLocalSteps.answers (extension primitive) fuel (initial (sharedFunction left right))) :
    FormationSensitive.Judgment Tower.rules Γ value (resultType left right) :=
  answers_value_judgment primitive_sound context (shared_initial_typed leftTyped rightTyped) returned

/-- This excludes every administrative domain fault for all fuel bounds, not
only the particular successful execution displayed below. -/
theorem shared_no_administrative_fault {n : Nat} {Γ : Tower.Ctx n} {left right : Tower.Tm n}
    (leftTyped : FormationSensitive.Typing Tower.rules Γ left ground)
    (rightTyped : FormationSensitive.Typing Tower.rules Γ right ground)
    (fuel : Nat) (fault : Fault Unit) (administrative : ∀ native, fault ≠ .native native) :
    .retryableFault (.domain fault) ∉
      PrimeNeedLocalSteps.answers (extension primitive) fuel (initial (sharedFunction left right)) := by
  intro returned
  obtain ⟨native, equal⟩ := answers_domain_fault_native primitive_sound
    (shared_initial_typed leftTyped rightTyped) returned
  exact administrative native equal

def sample : Computation Tower.Head Unit Nat 2 0 0 := sharedFunction Examples.older Examples.newer

def sampleFrontier (fuel : Nat) :=
  PrimeNeedLocalSteps.runFrontier (extension primitive) fuel [initial sample]

def effects {n : Nat} (machine : NeedMachine Tower.Head Unit Nat Unit Unit n) : List Nat :=
  machine.world.receipts.nodes.reverse.filterMap fun node =>
    match node.payload with
    | .effect effect => some effect
    | _ => none

def functionCell : CellId := ⟨0, [], 0, 0⟩

def cachedFunction {n : Nat} (machine : NeedMachine Tower.Head Unit Nat Unit Unit n) :
    Option (Answer Tower.Head Unit Nat n) :=
  (machine.world.heap.lookup functionCell).bind fun record =>
    match record.cache with
    | .value answer => some answer
    | _ => none

theorem sample_answers :
    PrimeNeedLocalSteps.answers (extension primitive) 96 (initial sample) =
      [.value (.returned (.native (.pair (.refl Examples.older) (.refl Examples.newer))))] := by
  rfl

theorem construction_once_calls_twice :
    (sampleFrontier 96).map effects = [[3, 4, 4]] := by
  rfl

/-- The actual persistent heap retains the full computation-function answer,
including its source body and lexical environments, after both calls. -/
theorem function_cache_retained :
    (sampleFrontier 96).map cachedFunction =
      [some (.nativeFunction
        ⟨2, 0, 0, .emit 4 (.returnValue (.native (.refl (.var 0)))), ids, Fin.elim0, Fin.elim0⟩)] := by
  rfl

theorem sample_result_judgment :
    FormationSensitive.Judgment Tower.rules Examples.context
      (.pair (.refl Examples.older) (.refl Examples.newer))
      (resultType Examples.older Examples.newer) := by
  apply shared_native_result_judgment ScopedComputation.NativeExamples.context_formed
    (.var 1) (.var 0) (fuel := 96)
  change _ ∈ PrimeNeedLocalSteps.answers (extension primitive) 96 (initial sample)
  rw [sample_answers]
  exact List.mem_singleton_self _

theorem shared_function_never_faults_on_function_polarity (fuel : Nat) :
    .retryableFault (.domain .expectedNativeFunction) ∉
      PrimeNeedLocalSteps.answers (extension primitive) fuel (initial sample) :=
  shared_no_administrative_fault (Γ := Examples.context) (.var 1) (.var 0) fuel
    .expectedNativeFunction (by intro native; cases native; intro impossible; cases impossible)

def sampleFunctionBody : NativeBody Tower.Head Unit Nat 2 :=
  ⟨2, 0, 0, .emit 4 (.returnValue (.native (.refl (.var 0)))), ids, Fin.elim0, Fin.elim0⟩

/-- A reusable cached function comes with its actual final machine and heap,
not only a detached answer and an existential store. Its source-backed body
typing is extracted from the preserved heap invariant. -/
theorem sample_function_cache_with_state :
    ∃ (types : CellTypes Tower.Head 2) (final : NeedMachine Tower.Head Unit Nat Unit Unit 2)
      (A : Tower.Tm 2) (B : CTy Tower.Head 3),
      final ∈ sampleFrontier 96 ∧
      MachineTyping Tower.rules signature Examples.context types final
        (.returns (.native (resultType Examples.older Examples.newer))) ∧
      types functionCell = some (.nativePi A B) ∧
      NativeBodyTyping Tower.rules signature Examples.context types sampleFunctionBody A B ∧
      cachedFunction final = some (.nativeFunction sampleFunctionBody) := by
  have returned : .value (.returned (.native (.pair (.refl Examples.older) (.refl Examples.newer)))) ∈
      PrimeNeedLocalSteps.answers (extension primitive) 96 (initial sample) := by
    rw [sample_answers]
    exact List.mem_singleton_self _
  obtain ⟨types, final, inFrontier, _, _, machineTyped⟩ :=
    answers_with_state primitive_sound
      (shared_initial_typed (Γ := Examples.context) (.var 1) (.var 0)) returned
  have cached : cachedFunction final ∈ (sampleFrontier 96).map cachedFunction :=
    List.mem_map.mpr ⟨final, inFrontier, rfl⟩
  rw [function_cache_retained, List.mem_singleton] at cached
  change cachedFunction final = some (.nativeFunction sampleFunctionBody) at cached
  have retained := cached
  unfold cachedFunction at cached
  cases present : final.world.heap.lookup functionCell with
  | none =>
      simp only [present, Option.bind_none] at cached
      cases cached
  | some record =>
      simp only [present, Option.bind_some] at cached
      obtain ⟨C, declared, _, cacheTyped⟩ := machineTyped.heap.entries functionCell record present
      cases cacheState : record.cache with
      | suspended => simp only [cacheState] at cached; cases cached
      | evaluating _ => simp only [cacheState] at cached; cases cached
      | stableFault _ => simp only [cacheState] at cached; cases cached
      | value answer =>
          simp only [cacheState] at cached
          have equal : answer = .nativeFunction sampleFunctionBody := Option.some.inj cached
          rw [cacheState, equal] at cacheTyped
          cases cacheTyped with
          | value answerTyped =>
              cases answerTyped with
              | nativeFunction _ _ bodyTyped =>
                  exact ⟨types, final, _, _, inFrontier, machineTyped, declared, bodyTyped, retained⟩

#print axioms primitive_sound
#print axioms shared_function_typed
#print axioms shared_initial_typed
#print axioms shared_answers_typed
#print axioms shared_native_result_judgment
#print axioms shared_no_administrative_fault
#print axioms sample_answers
#print axioms construction_once_calls_twice
#print axioms function_cache_retained
#print axioms sample_result_judgment
#print axioms shared_function_never_faults_on_function_polarity
#print axioms sample_function_cache_with_state

end PolarizedNeedPreservationExamples
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
