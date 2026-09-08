import Mettapedia.Languages.MeTTa.PrimeNeedAllocationBound
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedEvaluationEquivalence
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedSubstitution

/-!
# Raw closure boundaries of active-evaluation equations

Forcing an ordinary freshly constructed thunk has the same completed active
evaluation as its body. Capturing either source as an unused Need producer
nevertheless stores different origins in the final heap. Likewise, lexical
beta opening and syntactic substitution can return distinct raw thunk records:
the former retains its extended environment, while the latter changes source
syntax. A subsequent source force observes the same native result in the
examples below. These probes do not prove contextual equivalence or authorize
quotienting heaps, closures, receipts, effects, or native terms.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace PolarizedNeedEquationBoundaries

open PrimeNeedReference PrimeNeedAllocationBound PolarizedNeedMachine
open PolarizedNeedNaturalSemantics
open PolarizedNeed (Value Computation)

variable {Head Operation Effect StableFault NativeFault : Type} {m : Nat}
  {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
  {world : NeedWorld Head Operation Effect StableFault NativeFault m}

/-- A source closure with its native variables interpreted identically. -/
def close (code : Computation Head Operation Effect m 0 0) :
    Closure Head Operation Effect m :=
  ⟨m, 0, 0, code, ids, Fin.elim0, Fin.elim0⟩

def returnNative (term : Tm Head m) : Computation Head Operation Effect m 0 0 :=
  .returnValue (.native term)

def forceWrapped (code : Computation Head Operation Effect m 0 0) :
    Computation Head Operation Effect m 0 0 := .forceThunk (.thunk code)

def unusedNeed (producer : Computation Head Operation Effect m 0 0) (term : Tm Head m) :
    Computation Head Operation Effect m 0 0 :=
  .letNeed producer (.returnValue (.native term))

/-- This is a diagnostic on retained raw syntax, not an adopted language observer. -/
def originReturns (origin : Closure Head Operation Effect m) : Bool :=
  match origin.code with
  | .returnValue _ => true
  | _ => false

theorem forceWrapped_active_iff (code : Computation Head Operation Effect m 0 0)
    (outcome : Outcome Head Operation Effect StableFault NativeFault m)
    (final : NeedWorld Head Operation Effect StableFault NativeFault m) :
    Nonempty (Eval primitive (close (forceWrapped code)) world outcome final) ↔
      Nonempty (Eval primitive (close code) world outcome final) :=
  forceThunk_thunk_iff code

theorem returnNative_eval (term : Tm Head m) :
    Nonempty (Eval primitive (close (returnNative term)) world
      (.value (.returned (.native term))) world) := by
  simpa only [close, returnNative, captureValue, subst_ids] using
    (Nonempty.intro (Eval.returnValue (.native term) ids Fin.elim0 Fin.elim0 world)
      : Nonempty (Eval primitive _ _ _ _))

theorem forceWrapped_returnNative_eval (term : Tm Head m) :
    Nonempty (Eval primitive (close (forceWrapped (returnNative term))) world
      (.value (.returned (.native term))) world) :=
  (forceWrapped_active_iff _ _ _).mpr (returnNative_eval term)

theorem unusedNeed_eval (producer : Computation Head Operation Effect m 0 0)
    (term : Tm Head m) {allocated : NeedWorld Head Operation Effect StableFault NativeFault m}
    {cell : CellId}
    (allocation : world.allocate? (close producer) = some (allocated, cell)) :
    Nonempty (Eval primitive (close (unusedNeed producer term)) world
      (.value (.returned (.native term))) allocated) := by
  apply Nonempty.intro
  apply Eval.letNeed allocation
  simpa only [NeedBody.open, captureValue, subst_ids] using
    (Eval.returnValue (.native term) ids Fin.elim0 (Fin.cases cell Fin.elim0) allocated
      : Eval primitive _ _ _ _)

theorem unusedNeed_eval_exact (producer : Computation Head Operation Effect m 0 0)
    (term : Tm Head m) {allocated final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {cell : CellId} {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    (allocation : world.allocate? (close producer) = some (allocated, cell))
    (evaluation : Eval primitive (close (unusedNeed producer term)) world outcome final) :
    final = allocated ∧ outcome = .value (.returned (.native term)) := by
  cases evaluation with
  | letNeed actual body =>
      have same := Option.some.inj (actual.symm.trans allocation)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
      cases body
      exact ⟨rfl, by simp only [captureValue, subst_ids]⟩
  | letNeedAllocationFailure _ failed =>
      change world.allocate? (close producer) = none at failed
      rw [allocation] at failed
      cases failed

/-- Two active-equivalent producers leave different raw stored origins even
when the allocated cell is never demanded. No empty-heap reset is required. -/
theorem unusedNeed_distinct_heaps (bounded : SlotBound world) (term : Tm Head m) :
    ∃ plainFinal wrappedFinal,
      Nonempty (Eval primitive (close (unusedNeed (returnNative term) term)) world
        (.value (.returned (.native term))) plainFinal) ∧
      Nonempty (Eval primitive (close (unusedNeed (forceWrapped (returnNative term)) term)) world
        (.value (.returned (.native term))) wrappedFinal) ∧
      plainFinal.heap.lookup (world.freshCell 0) =
        some ⟨close (returnNative term), .suspended⟩ ∧
      wrappedFinal.heap.lookup (world.freshCell 0) =
        some ⟨close (forceWrapped (returnNative term)), .suspended⟩ ∧
      plainFinal.heap ≠ wrappedFinal.heap := by
  obtain ⟨plainFinal, plainAllocation⟩ := bounded.allocate_succeeds (close (returnNative term)) 0
  obtain ⟨wrappedFinal, wrappedAllocation⟩ :=
    bounded.allocate_succeeds (close (forceWrapped (returnNative term))) 0
  have plainLookup := World.allocate?_lookup_same plainAllocation
  have wrappedLookup := World.allocate?_lookup_same wrappedAllocation
  refine ⟨plainFinal, wrappedFinal, unusedNeed_eval _ term plainAllocation,
    unusedNeed_eval _ term wrappedAllocation, plainLookup, wrappedLookup, ?_⟩
  intro sameHeap
  have sameLookup := congrArg (fun heap => heap.lookup (world.freshCell 0)) sameHeap
  rw [plainLookup, wrappedLookup] at sameLookup
  have sameOrigin := congrArg CellRecord.origin (Option.some.inj sameLookup)
  have impossible := congrArg originReturns sameOrigin
  cases impossible

theorem unusedNeed_distinct_machine_heaps (bounded : SlotBound world) (term : Tm Head m) :
    ∃ plainFinal wrappedFinal,
      RunSegment primitive world
        (.run (.evaluate (close (unusedNeed (returnNative term) term)) .done) [])
        plainFinal (.halted (.value (.returned (.native term)))) ∧
      RunSegment primitive world
        (.run (.evaluate (close (unusedNeed (forceWrapped (returnNative term)) term)) .done) [])
        wrappedFinal (.halted (.value (.returned (.native term)))) ∧
      plainFinal.heap ≠ wrappedFinal.heap := by
  obtain ⟨plainFinal, wrappedFinal, ⟨plain⟩, ⟨wrapped⟩, _, _, distinct⟩ :=
    unusedNeed_distinct_heaps (primitive := primitive) bounded term
  exact ⟨plainFinal, wrappedFinal, plain.halts, wrapped.halts, distinct⟩

/-- Exact active equivalence is not a congruence for an unused producer
capture when literal retained heaps belong to the observation. -/
theorem unusedNeed_not_equivalent (bounded : SlotBound world) (term : Tm Head m) :
    ¬ EvaluationEquivalent (Effect := Effect) primitive
      (close (unusedNeed (returnNative term) term))
      (close (unusedNeed (forceWrapped (returnNative term)) term)) := by
  intro equivalent
  obtain ⟨plainFinal, plainAllocation⟩ := bounded.allocate_succeeds (close (returnNative term)) 0
  obtain ⟨wrappedFinal, wrappedAllocation⟩ :=
    bounded.allocate_succeeds (close (forceWrapped (returnNative term))) 0
  obtain ⟨evaluation⟩ := (equivalent world _ plainFinal).mp
    (unusedNeed_eval _ term plainAllocation)
  have sameFinal := (unusedNeed_eval_exact _ term wrappedAllocation evaluation).1
  have plainLookup := World.allocate?_lookup_same plainAllocation
  have wrappedLookup := World.allocate?_lookup_same wrappedAllocation
  have sameLookup := congrArg (fun final => final.heap.lookup (world.freshCell 0)) sameFinal
  rw [plainLookup, wrappedLookup] at sameLookup
  have sameOrigin := congrArg CellRecord.origin (Option.some.inj sameLookup)
  have impossible := congrArg originReturns sameOrigin
  cases impossible

/-- Returning a thunk of the newly bound native argument. -/
def nativeThunkBody : Computation Head Operation Effect (m + 1) 0 0 :=
  .returnValue (.thunk (.returnValue (.native (.var 0))))

/-- Returning a thunk of the newly bound value argument. -/
def valueThunkBody : Computation Head Operation Effect m 1 0 :=
  .returnValue (.thunk (.returnValue (.variable 0)))

def nativeBeta (term : Tm Head m) : Computation Head Operation Effect m 0 0 :=
  .nativeApply (.nativeLambda nativeThunkBody) term

def valueBeta (term : Tm Head m) : Computation Head Operation Effect m 0 0 :=
  .valueApply (.valueLambda valueThunkBody) (.native term)

def substitutedThunk (term : Tm Head m) : Computation Head Operation Effect m 0 0 :=
  .returnValue (.thunk (returnNative term))

theorem nativeBeta_substituted_code (term : Tm Head m) :
    Computation.instantiateNative term
      (nativeThunkBody : Computation Head Operation Effect (m + 1) 0 0) =
        substitutedThunk term := rfl

theorem valueBeta_substituted_code (term : Tm Head m) :
    Computation.instantiateValue (.native term)
      (valueThunkBody : Computation Head Operation Effect m 1 0) =
        substitutedThunk term := rfl

def nativeOpenedThunk (term : Tm Head m) : RuntimeValue Head Operation Effect m :=
  .thunk (.returnValue (.native (.var 0)) : Computation Head Operation Effect (m + 1) 0 0)
    (Fin.cases term ids) Fin.elim0 Fin.elim0

def valueOpenedThunk (term : Tm Head m) : RuntimeValue Head Operation Effect m :=
  .thunk (.returnValue (.variable 0) : Computation Head Operation Effect m 1 0)
    ids (Fin.cases (.native term) Fin.elim0) Fin.elim0

def substitutedRuntimeThunk (term : Tm Head m) : RuntimeValue Head Operation Effect m :=
  .thunk (returnNative term) ids Fin.elim0 Fin.elim0

theorem nativeBeta_eval (term : Tm Head m) :
    Nonempty (Eval primitive (close (nativeBeta term)) world
      (.value (.returned (nativeOpenedThunk term))) world) := by
  apply (nativeApply_nativeLambda_iff nativeThunkBody term).mpr
  simpa only [NativeBody.open, subst_ids, nativeThunkBody, nativeOpenedThunk, captureValue] using
    (Nonempty.intro
      (Eval.returnValue (.thunk (.returnValue (.native (.var 0))))
        (Fin.cases term ids) Fin.elim0 Fin.elim0 world)
      : Nonempty (Eval primitive _ _ _ _))

theorem valueBeta_eval (term : Tm Head m) :
    Nonempty (Eval primitive (close (valueBeta term)) world
      (.value (.returned (valueOpenedThunk term))) world) := by
  apply (valueApply_valueLambda_iff valueThunkBody (.native term)).mpr
  simpa only [ValueBody.open, subst_ids, valueThunkBody, valueOpenedThunk, captureValue] using
    (Nonempty.intro
      (Eval.returnValue (.thunk (.returnValue (.variable 0)))
        ids (Fin.cases (.native term) Fin.elim0) Fin.elim0 world)
      : Nonempty (Eval primitive _ _ _ _))

theorem substitutedThunk_eval (term : Tm Head m) :
    Nonempty (Eval primitive (close (substitutedThunk term)) world
      (.value (.returned (substitutedRuntimeThunk term))) world) :=
  ⟨Eval.returnValue (.thunk (returnNative term)) ids Fin.elim0 Fin.elim0 world⟩

theorem substitutedThunk_eval_exact (term : Tm Head m)
    {final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    (evaluation : Eval primitive (close (substitutedThunk term)) world outcome final) :
    outcome = .value (.returned (substitutedRuntimeThunk term)) ∧ final = world := by
  cases evaluation
  exact ⟨rfl, rfl⟩

/-- Stored scope lengths distinguish raw closure records without requiring
decidable equality on function-valued environments. -/
def thunkScopes : RuntimeValue Head Operation Effect m → Option (Nat × Nat × Nat)
  | .thunk (n := n) (v := v) (k := k) _ _ _ _ => some (n, v, k)
  | _ => none

theorem nativeOpenedThunk_ne_substituted (term : Tm Head m) :
    nativeOpenedThunk (Operation := Operation) (Effect := Effect) term ≠
      substitutedRuntimeThunk term := by
  intro same
  have scope := congrArg thunkScopes same
  have impossible : m + 1 = m := congrArg (fun value => value.map (fun x => x.1)) scope |>
    Option.some.inj
  omega

theorem valueOpenedThunk_ne_substituted (term : Tm Head m) :
    valueOpenedThunk (Operation := Operation) (Effect := Effect) term ≠
      substitutedRuntimeThunk term := by
  intro same
  have impossible := congrArg thunkScopes same
  cases impossible

theorem nativeBeta_not_substitution_equivalent
    (initial : NeedWorld Head Operation Effect StableFault NativeFault m) (term : Tm Head m) :
    ¬ EvaluationEquivalent (Effect := Effect) primitive (close (nativeBeta term))
      (close (Computation.instantiateNative term nativeThunkBody)) := by
  rw [nativeBeta_substituted_code]
  intro equivalent
  obtain ⟨evaluation⟩ := (equivalent initial _ initial).mp (nativeBeta_eval term)
  have equal := (substitutedThunk_eval_exact term evaluation).1
  exact nativeOpenedThunk_ne_substituted term (Answer.returned.inj (Produced.value.inj equal))

theorem valueBeta_not_substitution_equivalent
    (initial : NeedWorld Head Operation Effect StableFault NativeFault m) (term : Tm Head m) :
    ¬ EvaluationEquivalent (Effect := Effect) primitive (close (valueBeta term))
      (close (Computation.instantiateValue (.native term) valueThunkBody)) := by
  rw [valueBeta_substituted_code]
  intro equivalent
  obtain ⟨evaluation⟩ := (equivalent initial _ initial).mp (valueBeta_eval term)
  have equal := (substitutedThunk_eval_exact term evaluation).1
  exact valueOpenedThunk_ne_substituted term (Answer.returned.inj (Produced.value.inj equal))

/-- A source force of a supplied runtime value; its current world is arbitrary. -/
def forceProbe (value : RuntimeValue Head Operation Effect m) : Closure Head Operation Effect m :=
  ⟨0, 1, 0, .forceThunk (.variable 0), Fin.elim0, Fin.cases value Fin.elim0, Fin.elim0⟩

theorem forceProbe_nativeOpenedThunk (term : Tm Head m) :
    Nonempty (Eval primitive (forceProbe (nativeOpenedThunk term)) world
      (.value (.returned (.native term))) world) := by
  refine ⟨Eval.forceThunk (.variable 0) rfl ?_⟩
  exact Eval.returnValue (.native (.var 0)) (Fin.cases term ids) Fin.elim0 Fin.elim0 world

theorem forceProbe_valueOpenedThunk (term : Tm Head m) :
    Nonempty (Eval primitive (forceProbe (valueOpenedThunk term)) world
      (.value (.returned (.native term))) world) := by
  refine ⟨Eval.forceThunk (.variable 0) rfl ?_⟩
  exact Eval.returnValue (.variable 0) ids (Fin.cases (.native term) Fin.elim0) Fin.elim0 world

theorem forceProbe_substitutedThunk (term : Tm Head m) :
    Nonempty (Eval primitive (forceProbe (substitutedRuntimeThunk term)) world
      (.value (.returned (.native term))) world) := by
  refine ⟨Eval.forceThunk (.variable 0) rfl ?_⟩
  simpa only [returnNative, captureValue, subst_ids] using
    (Eval.returnValue (.native term) ids Fin.elim0 Fin.elim0 world : Eval primitive _ _ _ _)

/-- Each distinct raw thunk has an actual completed source-force run with the
same native answer and the same current world. This is one probe, not a
contextual-equivalence characterization. -/
theorem forceProbes_same_native_run (term : Tm Head m) :
    RunSegment primitive world
      (.run (.evaluate (forceProbe (nativeOpenedThunk term)) .done) [])
      world (.halted (.value (.returned (.native term)))) ∧
    RunSegment primitive world
      (.run (.evaluate (forceProbe (valueOpenedThunk term)) .done) [])
      world (.halted (.value (.returned (.native term)))) ∧
    RunSegment primitive world
      (.run (.evaluate (forceProbe (substitutedRuntimeThunk term)) .done) [])
      world (.halted (.value (.returned (.native term)))) := by
  obtain ⟨native⟩ := forceProbe_nativeOpenedThunk (primitive := primitive) (world := world) term
  obtain ⟨value⟩ := forceProbe_valueOpenedThunk (primitive := primitive) (world := world) term
  obtain ⟨substituted⟩ := forceProbe_substitutedThunk (primitive := primitive) (world := world) term
  exact ⟨native.halts, value.halts, substituted.halts⟩

section SourceTyping

open PolarizedNeed

variable {R : Rules Head} {signature : ScopedComputation.OperationSignature Head Operation}
  {Γ : Ctx Head m} {term A : Tm Head m}

theorem returnNative_typed (typed : FormationSensitive.Typing R Γ term A) :
    ComputationTyping R signature Γ Fin.elim0 Fin.elim0
      (returnNative (Effect := Effect) term) (.returns (.native A)) :=
  .returnValue (.native typed)

theorem forceWrapped_typed {code : Computation Head Operation Effect m 0 0} {B : CTy Head m}
    (typed : ComputationTyping R signature Γ Fin.elim0 Fin.elim0 code B) :
    ComputationTyping R signature Γ Fin.elim0 Fin.elim0 (forceWrapped code) B :=
  .forceThunk (.thunk typed)

theorem unusedNeed_typed {producer : Computation Head Operation Effect m 0 0} {B : CTy Head m}
    (formedProducer : ComputationFormation R Γ B) (formedA : NativeFormation R Γ A)
    (producerTyped : ComputationTyping R signature Γ Fin.elim0 Fin.elim0 producer B)
    (termTyped : FormationSensitive.Typing R Γ term A) :
    ComputationTyping R signature Γ Fin.elim0 Fin.elim0 (unusedNeed producer term)
      (.returns (.native A)) :=
  .letNeed formedProducer (.returns (.native formedA)) producerTyped (.returnValue (.native termTyped))

theorem substitutedThunk_typed (typed : FormationSensitive.Typing R Γ term A) :
    ComputationTyping R signature Γ Fin.elim0 Fin.elim0
      (substitutedThunk (Effect := Effect) term) (.returns (.thunk (.returns (.native A)))) :=
  .returnValue (.thunk (.returnValue (.native typed)))

theorem nativeBeta_typed (formedA : NativeFormation R Γ A)
    (typed : FormationSensitive.Typing R Γ term A) :
    ComputationTyping R signature Γ Fin.elim0 Fin.elim0
      (nativeBeta (Effect := Effect) term) (.returns (.thunk (.returns (.native A)))) := by
  have formedWeak : NativeFormation R (.snoc Γ A) (rename wk A) := by
    obtain ⟨u, isUniverse, formation⟩ := formedA
    exact ⟨u, isUniverse, formation.weaken⟩
  have function : ComputationTyping R signature Γ Fin.elim0 Fin.elim0
      (.nativeLambda (nativeThunkBody : Computation Head Operation Effect (m + 1) 0 0))
      (.nativePi A ((.returns (.thunk (.returns (.native A))) : CTy Head m).rename wk)) :=
    .nativeLambda formedA (.returns (.thunk (.returns (.native formedWeak))))
      (.returnValue (.thunk (.returnValue (.native (.var 0)))))
  simpa only [nativeBeta, CTy.instantiate_weaken] using ComputationTyping.nativeApply function typed

theorem valueBeta_typed (formedA : NativeFormation R Γ A)
    (typed : FormationSensitive.Typing R Γ term A) :
    ComputationTyping R signature Γ Fin.elim0 Fin.elim0
      (valueBeta (Effect := Effect) term) (.returns (.thunk (.returns (.native A)))) :=
  .valueApply
    (.valueLambda (.native formedA) (.returns (.thunk (.returns (.native formedA))))
      (.returnValue (.thunk (.returnValue (.variable 0)))))
    (.native typed)

end SourceTyping

#print axioms forceWrapped_active_iff
#print axioms returnNative_eval
#print axioms forceWrapped_returnNative_eval
#print axioms unusedNeed_eval
#print axioms unusedNeed_eval_exact
#print axioms unusedNeed_distinct_heaps
#print axioms unusedNeed_distinct_machine_heaps
#print axioms unusedNeed_not_equivalent
#print axioms nativeBeta_substituted_code
#print axioms valueBeta_substituted_code
#print axioms nativeBeta_eval
#print axioms valueBeta_eval
#print axioms substitutedThunk_eval
#print axioms substitutedThunk_eval_exact
#print axioms nativeOpenedThunk_ne_substituted
#print axioms valueOpenedThunk_ne_substituted
#print axioms nativeBeta_not_substitution_equivalent
#print axioms valueBeta_not_substitution_equivalent
#print axioms forceProbe_nativeOpenedThunk
#print axioms forceProbe_valueOpenedThunk
#print axioms forceProbe_substitutedThunk
#print axioms forceProbes_same_native_run
#print axioms returnNative_typed
#print axioms forceWrapped_typed
#print axioms unusedNeed_typed
#print axioms substitutedThunk_typed
#print axioms nativeBeta_typed
#print axioms valueBeta_typed

end PolarizedNeedEquationBoundaries
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
