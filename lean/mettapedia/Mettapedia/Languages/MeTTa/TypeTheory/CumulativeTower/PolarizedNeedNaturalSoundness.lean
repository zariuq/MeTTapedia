import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedNaturalContinuation
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedNaturalMachineLaws

/-!
# Contextual forward adequacy for first-class owned suspensions

Independent finite source and consumer derivations produce an actual extended
machine path with the same full final world and outcome. Computation functions
may run source bodies inside their consumers, so the proof decreases the sum
of source and consumer derivation weights. This is not program normalization,
a uniform fuel bound, or a quotient of effects and branch occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace PolarizedNeedNaturalSemantics

open PrimeNeedReference PolarizedNeedMachine
open PolarizedNeed (Value Computation)

variable {Head Operation Effect StableFault NativeFault : Type} {m : Nat}
  {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}

private theorem finish_stable (kont : Kont Head Operation Effect m) (fault : StableFault) :
    finish (NativeFault := NativeFault) (.stableFault fault) kont = .stableFault fault := by
  cases kont <;> rfl

private theorem finish_retry (kont : Kont Head Operation Effect m) (reason : RetryReason (Fault NativeFault)) :
    finish (StableFault := StableFault) (.retryableFault reason) kont = .retryableFault reason := by
  cases kont <;> rfl

private theorem deliver_stable (kont : Kont Head Operation Effect m) (fault : StableFault) :
    deliver (NativeFault := NativeFault) (.stableFault fault) kont = .complete (.stableFault fault) := by
  cases kont <;> rfl

private theorem deliver_retry (kont : Kont Head Operation Effect m) (reason : RetryReason (Fault NativeFault)) :
    deliver (StableFault := StableFault) (.retryableFault reason) kont = .complete (.retryableFault reason) := by
  cases kont <;> rfl

private theorem allocation_failure
    (world : NeedWorld Head Operation Effect StableFault NativeFault m)
    (stack : List (Frame (Resume Head Operation Effect m)))
    (state : Local Head Operation Effect StableFault NativeFault m)
    (origin : Closure Head Operation Effect m) (token : Resume Head Operation Effect m)
    (unhandled : localStep state = none) (selected : action primitive state = .allocate origin token)
    (absent : world.allocate? origin = none) :
    RunSegment primitive world (.run state stack) (allocationFailure world).2
      (.returned (allocationFailure world).1 stack) := by
  apply RunSegment.fallback primitive world stack state unhandled
    (lookups := 1) (updates := 0) (receipts := 1) (allocations := 0)
  intro work
  simp only [PrimeNeedReference.step, reference, selected, absent,
    allocationFailure, retryResult, retryMachine, finished, recorded]

private theorem native_mismatch (body : NativeBody Head Operation Effect m)
    (kont : Kont Head Operation Effect m) (answer : Answer Head Operation Effect m)
    (wrong : ∀ value, answer ≠ .returned (.native value)) :
    afterDemand (StableFault := StableFault) (NativeFault := NativeFault)
      (.bindNative body kont) (.value answer) = .complete (.retryableFault (.domain .expectedNativeValue)) := by
  cases answer with
  | returned value =>
      cases value with
      | native term => exact False.elim (wrong term rfl)
      | thunk _ _ _ _ => rfl
      | packNative _ _ => rfl
  | nativeFunction _ => rfl
  | valueFunction _ => rfl

private theorem value_mismatch (body : ValueBody Head Operation Effect m)
    (kont : Kont Head Operation Effect m) (answer : Answer Head Operation Effect m)
    (wrong : ∀ value, answer ≠ .returned value) :
    afterDemand (StableFault := StableFault) (NativeFault := NativeFault)
      (.bindValue body kont) (.value answer) = .complete (.retryableFault (.domain .expectedReturnedValue)) := by
  cases answer with
  | returned value => exact False.elim (wrong value rfl)
  | nativeFunction _ => rfl
  | valueFunction _ => rfl

private theorem sigma_mismatch (body : NativeBody Head Operation Effect m)
    (kont : Kont Head Operation Effect m) (answer : Answer Head Operation Effect m)
    (wrong : ∀ value, answer ≠ .returned (.native value)) :
    afterDemand (StableFault := StableFault) (NativeFault := NativeFault)
      (.bindSigma body kont) (.value answer) = .complete (.retryableFault (.domain .expectedNativeValue)) := by
  cases answer with
  | returned value =>
      cases value with
      | native term => exact False.elim (wrong term rfl)
      | thunk _ _ _ _ => rfl
      | packNative _ _ => rfl
  | nativeFunction _ => rfl
  | valueFunction _ => rfl

private structure SoundBelow
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (limit : Nat) : Prop where
  evaluation : ∀ {closure : Closure Head Operation Effect m}
    {world middle final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {raw outcome : Outcome Head Operation Effect StableFault NativeFault m}
    {kont : Kont Head Operation Effect m}
    (evaluation : Eval primitive closure world raw middle)
    (consumer : KontEval primitive kont raw middle outcome final),
    evaluation.weight + consumer.weight < limit →
    ∀ stack, RunSegment primitive world (.run (.evaluate closure kont) stack) final (.returned outcome stack)
  forcing : ∀ {cell : CellId}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    (forcing : Force primitive cell world outcome final), forcing.weight < limit →
    ∀ stack, RunSegment primitive world (.force cell stack) final (.returned outcome stack)
  continuation : ∀ {kont : Kont Head Operation Effect m}
    {input outcome : Outcome Head Operation Effect StableFault NativeFault m}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    (consumer : KontEval primitive kont input world outcome final), consumer.weight < limit →
    ∀ stack, RunSegment primitive world (.run (deliver input kont) stack) final (.returned outcome stack)

private theorem SoundBelow.eval {limit : Nat} (ih : SoundBelow (Effect := Effect) primitive limit)
    {closure : Closure Head Operation Effect m}
    {world middle final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {raw outcome : Outcome Head Operation Effect StableFault NativeFault m}
    {kont : Kont Head Operation Effect m}
    (evaluation : Eval primitive closure world raw middle)
    (consumer : KontEval primitive kont raw middle outcome final)
    (stack : List (Frame (Resume Head Operation Effect m)))
    (smaller : evaluation.weight + consumer.weight < limit := by
      dsimp only [Eval.weight, Force.weight, KontEval.weight] at bounded ⊢; omega) :
    RunSegment primitive world (.run (.evaluate closure kont) stack) final (.returned outcome stack) :=
  ih.evaluation evaluation consumer smaller stack

private theorem SoundBelow.force {limit : Nat} (ih : SoundBelow (Effect := Effect) primitive limit)
    {cell : CellId} {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    (forcing : Force primitive cell world outcome final)
    (stack : List (Frame (Resume Head Operation Effect m)))
    (smaller : forcing.weight < limit := by
      dsimp only [Eval.weight, Force.weight, KontEval.weight] at bounded ⊢; omega) :
    RunSegment primitive world (.force cell stack) final (.returned outcome stack) :=
  ih.forcing forcing smaller stack

private theorem SoundBelow.kont {limit : Nat} (ih : SoundBelow (Effect := Effect) primitive limit)
    {kont : Kont Head Operation Effect m}
    {input outcome : Outcome Head Operation Effect StableFault NativeFault m}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    (consumer : KontEval primitive kont input world outcome final)
    (stack : List (Frame (Resume Head Operation Effect m)))
    (smaller : consumer.weight < limit := by
      dsimp only [Eval.weight, Force.weight, KontEval.weight] at bounded ⊢; omega) :
    RunSegment primitive world (.run (deliver input kont) stack) final (.returned outcome stack) :=
  ih.continuation consumer smaller stack

private theorem eval_sound_step {limit : Nat} (ih : SoundBelow (Effect := Effect) primitive limit)
    {closure : Closure Head Operation Effect m}
    {world middle final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {raw outcome : Outcome Head Operation Effect StableFault NativeFault m}
    {kont : Kont Head Operation Effect m}
    (evaluation : Eval primitive closure world raw middle)
    (consumer : KontEval primitive kont raw middle outcome final)
    (bounded : evaluation.weight + consumer.weight ≤ limit)
    (stack : List (Frame (Resume Head Operation Effect m))) :
    RunSegment primitive world (.run (.evaluate closure kont) stack) final (.returned outcome stack) := by
  match evaluation with
  | .returnValue value native values needs world =>
      obtain ⟨rfl, rfl⟩ := consumer.returned_exact
      exact RunSegment.returnValue primitive _ stack value native values needs kont
  | .nativeLambda body native values needs world =>
      match consumer with
      | .done _ _ => exact RunSegment.action_done primitive world stack _ _ rfl rfl
      | .pairMismatch _ _ _ _ _ => exact RunSegment.action_done primitive world stack _ _ rfl rfl
      | .nativeApply argument _ bodyEval rest =>
          exact (RunSegment.local_step primitive world stack _ _ rfl).trans
            (ih.eval bodyEval rest stack)
      | .nativeMismatch _ _ _ _ wrong => exact False.elim (wrong _ rfl)
      | .valueMismatch _ _ _ _ _ => exact RunSegment.action_done primitive world stack _ _ rfl rfl
  | .valueLambda body native values needs world =>
      match consumer with
      | .done _ _ => exact RunSegment.action_done primitive world stack _ _ rfl rfl
      | .pairMismatch _ _ _ _ _ => exact RunSegment.action_done primitive world stack _ _ rfl rfl
      | .valueApply argument _ bodyEval rest =>
          exact (RunSegment.local_step primitive world stack _ _ rfl).trans
            (ih.eval bodyEval rest stack)
      | .valueMismatch _ _ _ _ wrong => exact False.elim (wrong _ rfl)
      | .nativeMismatch _ _ _ _ _ => exact RunSegment.action_done primitive world stack _ _ rfl rfl
  | .call operation argument native values needs world =>
      cases produced : primitive operation (subst native argument) with
      | value value =>
          simp only [produced, liftOutcome] at consumer
          obtain ⟨rfl, rfl⟩ := consumer.returned_exact
          simpa only [produced, liftOutcome] using
            RunSegment.call primitive _ stack operation argument native values needs kont
      | stableFault fault =>
          simp only [produced, liftOutcome] at consumer
          obtain ⟨rfl, rfl⟩ := consumer.stable_exact
          simpa only [produced, liftOutcome, finish_stable] using
            RunSegment.call primitive _ stack operation argument native values needs kont
      | retryableFault reason =>
          simp only [produced, liftOutcome] at consumer
          obtain ⟨rfl, rfl⟩ := consumer.retry_exact
          simpa only [produced, liftOutcome, finish_retry] using
            RunSegment.call primitive _ stack operation argument native values needs kont
  | .emit effect bodyEval =>
      exact (RunSegment.emit primitive world stack effect _ _ _ _ kont).trans
        (ih.eval bodyEval consumer stack)
  | .forceNeed index forced =>
      exact (RunSegment.forceNeed primitive world stack index _ _ _ kont).trans
        ((ih.force forced (.resume (.finish kont) :: stack)).trans
          ((RunSegment.finish_resume primitive _ stack _ kont).trans (ih.kont consumer stack)))
  | .nativeApply argument function bodyEval =>
      exact (RunSegment.local_step primitive world stack _ _ rfl).trans
        (ih.eval function (.nativeApply _ _ bodyEval consumer) stack)
  | .nativeApplyMismatch argument function wrong =>
      obtain ⟨rfl, rfl⟩ := consumer.retry_exact
      exact (RunSegment.local_step primitive world stack _ _ rfl).trans
        (ih.eval function (.nativeMismatch _ kont _ _ wrong) stack)
  | .nativeApplyFault argument function fault =>
      obtain ⟨rfl, rfl⟩ := consumer.fault_exact fault
      cases fault with
      | stableFault fault =>
          exact (RunSegment.local_step primitive world stack _ _ rfl).trans
            (ih.eval function (.stableFault _ fault _) stack)
      | retryableFault reason =>
          exact (RunSegment.local_step primitive world stack _ _ rfl).trans
            (ih.eval function (.retryableFault _ reason _) stack)
  | .valueApply argument function bodyEval =>
      exact (RunSegment.local_step primitive world stack _ _ rfl).trans
        (ih.eval function (.valueApply _ _ bodyEval consumer) stack)
  | .valueApplyMismatch argument function wrong =>
      obtain ⟨rfl, rfl⟩ := consumer.retry_exact
      exact (RunSegment.local_step primitive world stack _ _ rfl).trans
        (ih.eval function (.valueMismatch _ kont _ _ wrong) stack)
  | .valueApplyFault argument function fault =>
      obtain ⟨rfl, rfl⟩ := consumer.fault_exact fault
      cases fault with
      | stableFault fault =>
          exact (RunSegment.local_step primitive world stack _ _ rfl).trans
            (ih.eval function (.stableFault _ fault _) stack)
      | retryableFault reason =>
          exact (RunSegment.local_step primitive world stack _ _ rfl).trans
            (ih.eval function (.retryableFault _ reason _) stack)
  | .forceThunk value captured bodyEval =>
      exact (RunSegment.local_step primitive world stack _ _
        (by simp only [localStep, captured])).trans (ih.eval bodyEval consumer stack)
  | .forceThunkMismatch value world wrong =>
      obtain ⟨rfl, rfl⟩ := consumer.retry_exact
      apply (RunSegment.local_step primitive _ stack _ _ ?_).trans
        (RunSegment.complete primitive _ stack (.retryableFault (.domain .expectedThunk)))
      simp only [localStep]
  | .unpackNative value captured bodyEval =>
      exact (RunSegment.local_step primitive world stack _ _
        (by simp only [localStep, captured])).trans (ih.eval bodyEval consumer stack)
  | .unpackNativeMismatch value body world wrong =>
      obtain ⟨rfl, rfl⟩ := consumer.retry_exact
      apply (RunSegment.local_step primitive _ stack _ _ ?_).trans
        (RunSegment.complete primitive _ stack (.retryableFault (.domain .expectedNativePair)))
      simp only [localStep]
  | .bindNativeValue allocated forced bodyEval =>
      exact (RunSegment.action_allocate primitive world stack _ _ (.bindNative _ kont) rfl rfl allocated).trans
        ((RunSegment.demand primitive _ stack _ _).trans
          ((ih.force forced (.resume (.bindNative _ kont) :: stack)).trans
            ((RunSegment.bindNative_resume primitive _ stack _ _ kont).trans
              (ih.eval bodyEval consumer stack))))
  | .bindNativeMismatch body allocated forced wrong =>
      obtain ⟨rfl, rfl⟩ := consumer.retry_exact
      refine (RunSegment.action_allocate primitive world stack _ _ (.bindNative _ kont) rfl rfl allocated).trans
        ((RunSegment.demand primitive _ stack _ _).trans
          ((ih.force forced (.resume (.bindNative _ kont) :: stack)).trans ?_))
      refine (RunSegment.resume primitive _ stack (.bindNative _ kont) (.value _)).trans ?_
      rw [native_mismatch _ kont _ wrong]
      exact RunSegment.complete primitive _ stack _
  | .bindNativeFault body allocated forced fault =>
      obtain ⟨rfl, rfl⟩ := consumer.fault_exact fault
      refine (RunSegment.action_allocate primitive world stack _ _ (.bindNative _ kont) rfl rfl allocated).trans
        ((RunSegment.demand primitive _ stack _ _).trans
          ((ih.force forced (.resume (.bindNative _ kont) :: stack)).trans ?_))
      cases fault <;>
        exact (RunSegment.resume primitive _ stack (.bindNative _ kont) _).trans
          (RunSegment.complete primitive _ stack _)
  | .bindNativeAllocationFailure body absent =>
      obtain ⟨rfl, rfl⟩ := consumer.retry_exact
      exact allocation_failure world stack _ _ _ rfl rfl absent
  | .bindValueValue allocated forced bodyEval =>
      exact (RunSegment.action_allocate primitive world stack _ _ (.bindValue _ kont) rfl rfl allocated).trans
        ((RunSegment.demand primitive _ stack _ _).trans
          ((ih.force forced (.resume (.bindValue _ kont) :: stack)).trans
            ((RunSegment.bindValue_resume primitive _ stack _ _ kont).trans
              (ih.eval bodyEval consumer stack))))
  | .bindValueMismatch body allocated forced wrong =>
      obtain ⟨rfl, rfl⟩ := consumer.retry_exact
      refine (RunSegment.action_allocate primitive world stack _ _ (.bindValue _ kont) rfl rfl allocated).trans
        ((RunSegment.demand primitive _ stack _ _).trans
          ((ih.force forced (.resume (.bindValue _ kont) :: stack)).trans ?_))
      refine (RunSegment.resume primitive _ stack (.bindValue _ kont) (.value _)).trans ?_
      rw [value_mismatch _ kont _ wrong]
      exact RunSegment.complete primitive _ stack _
  | .bindValueFault body allocated forced fault =>
      obtain ⟨rfl, rfl⟩ := consumer.fault_exact fault
      refine (RunSegment.action_allocate primitive world stack _ _ (.bindValue _ kont) rfl rfl allocated).trans
        ((RunSegment.demand primitive _ stack _ _).trans
          ((ih.force forced (.resume (.bindValue _ kont) :: stack)).trans ?_))
      cases fault <;>
        exact (RunSegment.resume primitive _ stack (.bindValue _ kont) _).trans
          (RunSegment.complete primitive _ stack _)
  | .bindValueAllocationFailure body absent =>
      obtain ⟨rfl, rfl⟩ := consumer.retry_exact
      exact allocation_failure world stack _ _ _ rfl rfl absent
  | .sequenceSigmaValue allocated forced bodyEval =>
      let paired := KontEval.pair_input _ consumer
      have pairedBound := paired.property
      exact (RunSegment.action_allocate primitive world stack _ _ (.bindSigma _ kont) rfl rfl allocated).trans
        ((RunSegment.demand primitive _ stack _ _).trans
          ((ih.force forced (.resume (.bindSigma _ kont) :: stack)).trans
            ((RunSegment.bindSigma_resume primitive _ stack _ _ kont).trans
              (ih.eval bodyEval paired.val stack))))
  | .sequenceSigmaMismatch body allocated forced wrong =>
      obtain ⟨rfl, rfl⟩ := consumer.retry_exact
      refine (RunSegment.action_allocate primitive world stack _ _ (.bindSigma _ kont) rfl rfl allocated).trans
        ((RunSegment.demand primitive _ stack _ _).trans
          ((ih.force forced (.resume (.bindSigma _ kont) :: stack)).trans ?_))
      refine (RunSegment.resume primitive _ stack (.bindSigma _ kont) (.value _)).trans ?_
      rw [sigma_mismatch _ kont _ wrong]
      exact RunSegment.complete primitive _ stack _
  | .sequenceSigmaFault body allocated forced fault =>
      obtain ⟨rfl, rfl⟩ := consumer.fault_exact fault
      refine (RunSegment.action_allocate primitive world stack _ _ (.bindSigma _ kont) rfl rfl allocated).trans
        ((RunSegment.demand primitive _ stack _ _).trans
          ((ih.force forced (.resume (.bindSigma _ kont) :: stack)).trans ?_))
      cases fault <;>
        exact (RunSegment.resume primitive _ stack (.bindSigma _ kont) _).trans
          (RunSegment.complete primitive _ stack _)
  | .sequenceSigmaAllocationFailure body absent =>
      obtain ⟨rfl, rfl⟩ := consumer.retry_exact
      exact allocation_failure world stack _ _ _ rfl rfl absent
  | .choose left right allocated forced =>
      exact (RunSegment.action_allocate primitive world stack _ _ (.finish kont) rfl rfl allocated).trans
        ((RunSegment.demand primitive _ stack _ _).trans
          ((ih.force forced (.resume (.finish kont) :: stack)).trans
            ((RunSegment.finish_resume primitive _ stack _ kont).trans (ih.kont consumer stack))))
  | .chooseAllocationFailure left right absent =>
      obtain ⟨rfl, rfl⟩ := consumer.retry_exact
      exact allocation_failure world stack _ _ _ rfl rfl absent
  | .letNeed allocated bodyEval =>
      exact (RunSegment.action_allocate primitive world stack _ _ (.bindNeed _ kont) rfl rfl allocated).trans
        (ih.eval bodyEval consumer stack)
  | .letNeedAllocationFailure body absent =>
      obtain ⟨rfl, rfl⟩ := consumer.retry_exact
      exact allocation_failure world stack _ _ _ rfl rfl absent

private theorem force_sound_step {limit : Nat} (ih : SoundBelow (Effect := Effect) primitive limit)
    {cell : CellId}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    (forcing : Force primitive cell world outcome final)
    (bounded : forcing.weight ≤ limit)
    (stack : List (Frame (Resume Head Operation Effect m))) :
    RunSegment primitive world (.force cell stack) final (.returned outcome stack) := by
  match forcing with
  | .cachedValue cached => exact RunSegment.cached_answer primitive world stack cell _ _ cached
  | .cachedStable cached =>
      apply RunSegment.of_singleton (lookups := 1) (updates := 0) (receipts := 1) (allocations := 0)
      intro work
      simp only [PrimeNeedLocalSteps.step, PrimeNeedReference.step, cached, finished, recorded]
  | .missing absent =>
      apply RunSegment.of_singleton (lookups := 1) (updates := 0) (receipts := 1) (allocations := 0)
      intro work
      simp only [PrimeNeedLocalSteps.step, PrimeNeedReference.step, absent, retryResult, retryMachine, finished, recorded]
  | .evaluating cached =>
      apply RunSegment.of_singleton (lookups := 1) (updates := 0) (receipts := 1) (allocations := 0)
      intro work
      simp only [PrimeNeedLocalSteps.step, PrimeNeedReference.step, cached, retryResult, retryMachine, finished, recorded]
  | .suspended cached selected bodyEval =>
      exact (selected.force_entry primitive world stack cached).trans
        ((ih.eval bodyEval (.done _ _) (.commit cell world.nextEvaluator :: stack)).trans
          (finalize_commit primitive _ stack cell world.nextEvaluator _))

private theorem kont_sound_step {limit : Nat} (ih : SoundBelow (Effect := Effect) primitive limit)
    {kont : Kont Head Operation Effect m}
    {input outcome : Outcome Head Operation Effect StableFault NativeFault m}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    (consumer : KontEval primitive kont input world outcome final)
    (bounded : consumer.weight ≤ limit)
    (stack : List (Frame (Resume Head Operation Effect m))) :
    RunSegment primitive world (.run (deliver input kont) stack) final (.returned outcome stack) := by
  match consumer with
  | .done input world => exact RunSegment.complete primitive world stack input
  | .pairNative first second rest => exact ih.kont rest stack
  | .pairMismatch first rest answer world wrong =>
      cases answer with
      | returned value =>
          cases value with
          | native term => exact False.elim (wrong term rfl)
          | thunk _ _ _ _ => exact RunSegment.complete primitive world stack _
          | packNative _ _ => exact RunSegment.complete primitive world stack _
      | nativeFunction _ => exact RunSegment.complete primitive world stack _
      | valueFunction _ => exact RunSegment.complete primitive world stack _
  | .nativeApply argument body evaluation rest => exact ih.eval evaluation rest stack
  | .nativeMismatch argument rest answer world wrong =>
      cases answer with
      | returned _ => exact RunSegment.complete primitive world stack _
      | nativeFunction body => exact False.elim (wrong body rfl)
      | valueFunction _ => exact RunSegment.complete primitive world stack _
  | .valueApply argument body evaluation rest => exact ih.eval evaluation rest stack
  | .valueMismatch argument rest answer world wrong =>
      cases answer with
      | returned _ => exact RunSegment.complete primitive world stack _
      | nativeFunction _ => exact RunSegment.complete primitive world stack _
      | valueFunction body => exact False.elim (wrong body rfl)
  | .stableFault kont fault world =>
      rw [deliver_stable]
      exact RunSegment.complete primitive world stack _
  | .retryableFault kont reason world =>
      rw [deliver_retry]
      exact RunSegment.complete primitive world stack _

private theorem sound_below (limit : Nat) : SoundBelow (Effect := Effect) primitive limit := by
  induction limit using Nat.strong_induction_on with
  | h limit ih =>
      constructor
      · intro closure world middle final raw outcome kont evaluation consumer bounded stack
        exact eval_sound_step (ih (evaluation.weight + consumer.weight) bounded)
          evaluation consumer (Nat.le_refl _) stack
      · intro cell world final outcome forcing bounded stack
        exact force_sound_step (ih forcing.weight bounded) forcing (Nat.le_refl _) stack
      · intro kont input outcome world final consumer bounded stack
        exact kont_sound_step (ih consumer.weight bounded) consumer (Nat.le_refl _) stack

theorem Eval.sound {closure : Closure Head Operation Effect m}
    {world middle final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {raw outcome : Outcome Head Operation Effect StableFault NativeFault m}
    {kont : Kont Head Operation Effect m}
    (evaluation : Eval primitive closure world raw middle)
    (consumer : KontEval primitive kont raw middle outcome final)
    (stack : List (Frame (Resume Head Operation Effect m))) :
    RunSegment primitive world (.run (.evaluate closure kont) stack) final (.returned outcome stack) :=
  (sound_below (evaluation.weight + consumer.weight + 1)).evaluation
    evaluation consumer (Nat.lt_succ_self _) stack

theorem Force.sound {cell : CellId}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    (forcing : Force primitive cell world outcome final)
    (stack : List (Frame (Resume Head Operation Effect m))) :
    RunSegment primitive world (.force cell stack) final (.returned outcome stack) :=
  (sound_below (forcing.weight + 1)).forcing forcing (Nat.lt_succ_self _) stack

theorem KontEval.sound {kont : Kont Head Operation Effect m}
    {input outcome : Outcome Head Operation Effect StableFault NativeFault m}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    (consumer : KontEval primitive kont input world outcome final)
    (stack : List (Frame (Resume Head Operation Effect m))) :
    RunSegment primitive world (.run (deliver input kont) stack) final (.returned outcome stack) :=
  (sound_below (consumer.weight + 1)).continuation consumer (Nat.lt_succ_self _) stack

theorem Eval.halts {closure : Closure Head Operation Effect m}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    (evaluation : Eval primitive closure world outcome final) :
    RunSegment primitive world (.run (.evaluate closure .done) []) final (.halted outcome) :=
  (evaluation.sound (.done _ _) []).trans (RunSegment.halt primitive final outcome)

theorem Force.halts {cell : CellId}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    (forcing : Force primitive cell world outcome final) :
    RunSegment primitive world (.force cell []) final (.halted outcome) :=
  (forcing.sound []).trans (RunSegment.halt primitive final outcome)

#print axioms Eval.sound
#print axioms Force.sound
#print axioms KontEval.sound
#print axioms Eval.halts
#print axioms Force.halts

end PolarizedNeedNaturalSemantics
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
