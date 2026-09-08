import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ScopedNeedMachineTyping
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveDependentComputation

/-!
# Native admission of actual cached Need results

A captured force obtains its displayed native result type from independent
source typing, a typed captured environment, and the actual heap invariant.
Successful lookup alone provides no native admission. Source conversion tails
are replayed with their formation premises after typed substitution.

The cached-step theorem concerns the existing machine's actual successor, and
the continuation theorem concerns its actual resume operation. The dependent
sharing example executes the machine with a genuine native Sigma result. These
are local admission results and a concrete execution, not preservation for every
control stack. The malformed-cache control makes that boundary explicit.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace ScopedNeedMachine

open PrimeNeedReference
open ScopedComputation (OperationSignature)

variable {Head Operation Effect StableFault NativeFault : Type} {n m k : Nat}
  {R : Rules Head} {signature : OperationSignature Head Operation} {Δ : Ctx Head m}

/-- Recover the captured force's complete displayed type, including conversion
tails. Its selected cache is independently admitted through the actual heap. -/
theorem ClosureTyping.cached_force_judgment
    {types : CellTypes Head m} {values : Sub Head n m} {needs : Fin k → CellId}
    {index : Fin k} {A value : Tm Head m}
    {origin : Closure Head Operation Effect m}
    {heap : Heap (Closure Head Operation Effect m) (Tm Head m) StableFault}
    (source : ClosureTyping (Effect := Effect) R signature Δ types
      ⟨n, k, .force index, values, needs⟩ A)
    (context : FormationSensitive.ContextFormation R Δ)
    (heapTyped : HeapTyping R signature Δ types heap)
    (cached : heap.lookup (needs index) = some ⟨origin, .value value⟩) :
    FormationSensitive.Judgment R Δ value A := by
  cases source with
  | captured source environment references =>
      refine ⟨context, ?_⟩
      exact (source.substitute environment).force_replay rfl
        (heapTyped.cached_value (references index) cached)

/-- Every returned value of the actual cached-force step has the source
closure's displayed native judgment. Recording an observation does not change
the selected cached value, and cannot create its typing evidence. -/
theorem cached_force_result_judgment
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    {types : CellTypes Head m} {values : Sub Head n m} {needs : Fin k → CellId}
    {index : Fin k} {A value result : Tm Head m}
    {origin : Closure Head Operation Effect m}
    {machine next : NeedMachine Head Operation Effect StableFault NativeFault m}
    {stack : List (Frame (Resume Head Operation Effect m))}
    (source : ClosureTyping (Effect := Effect) R signature Δ types
      ⟨n, k, .force index, values, needs⟩ A)
    (context : FormationSensitive.ContextFormation R Δ)
    (heapTyped : HeapTyping R signature Δ types machine.world.heap)
    (control : machine.control = .force (needs index) stack)
    (cached : machine.world.heap.lookup (needs index) = some ⟨origin, .value value⟩)
    (successor : next ∈ step (spec primitive) machine)
    (returned : next.control = .returned (.value result) stack) :
    FormationSensitive.Judgment R Δ result A := by
  rw [cached_force_step primitive machine control cached, List.mem_singleton] at successor
  subst next
  have equal : value = result := by cases returned; rfl
  subst result
  exact source.cached_force_judgment context heapTyped cached

/-- Resume a typed native pair continuation with the actual cached result.
Only value outcomes yield native judgments; stable and retryable faults do not. -/
theorem cached_force_consumer_judgment
    {types : CellTypes Head m} {values : Sub Head n m} {needs : Fin k → CellId}
    {index : Fin k} {A B value result : Tm Head m}
    {origin : Closure Head Operation Effect m} {kont : Kont Head m}
    {heap : Heap (Closure Head Operation Effect m) (Tm Head m) StableFault}
    (source : ClosureTyping (Effect := Effect) R signature Δ types
      ⟨n, k, .force index, values, needs⟩ A)
    (context : FormationSensitive.ContextFormation R Δ)
    (heapTyped : HeapTyping R signature Δ types heap)
    (cached : heap.lookup (needs index) = some ⟨origin, .value value⟩)
    (continuation : KontTyping R Δ kont A B)
    (resumed : afterDemand (.finish kont) (.value value) =
      (.complete (.value result) : Local Head Operation Effect StableFault NativeFault m)) :
    FormationSensitive.Judgment R Δ result B := by
  have input := source.cached_force_judgment context heapTyped cached
  have output : OutcomeTyping R Δ B
      (finish (.value value : Outcome Head StableFault NativeFault m) kont) :=
    continuation.finish_preserves (.value input.typing)
  have equal := Local.complete.inj resumed
  rw [equal] at output
  cases output with
  | value admitted => exact ⟨context, admitted⟩

namespace AdmissionExamples

open ScopedNeedComputation.Examples

abbrev ExampleMachine := NeedMachine Tower.Head Empty Bool Empty Empty 1

def primitive : Empty → Tower.Tm 1 → Produced (Tower.Tm 1) Empty Empty :=
  fun operation => nomatch operation

def machineSpec : NeedSpec Tower.Head Empty Bool Empty Empty 1 := spec primitive

def initial : ExampleMachine where
  world :=
    { lineage := 0, path := [], heap := .empty, receipts := .empty,
      nextCell := 0, nextEvaluator := 0 }
  control := .run (.evaluate ⟨1, 0, source, ids, Fin.elim0⟩ .done) []

/-- The source is admitted before execution; its result type depends on the
first selected native value through both endpoints of an identity type. -/
theorem initial_source_typed :
    ClosureTyping Tower.rules operationSignature context (fun _ => none)
      (⟨1, 0, source, ids, Fin.elim0⟩ : Closure Tower.Head Empty Bool 1)
      (.sigma ground identityFamily) := by
  have typed : ClosureTyping Tower.rules operationSignature context (fun _ => none)
      (⟨1, 0, source, ids, Fin.elim0⟩ : Closure Tower.Head Empty Bool 1)
      (subst ids (.sigma ground identityFamily)) :=
    .captured source_typing (fun index => by simpa only [subst_ids, ids] using
      (FormationSensitive.Typing.var (R := Tower.rules) (Γ := context) index))
      (fun index => Fin.elim0 index)
  simpa only [subst_ids] using typed

def effects (machine : ExampleMachine) : List Bool :=
  machine.world.receipts.nodes.reverse.filterMap fun node =>
    match node.payload with
    | .effect effect => some effect
    | _ => none

def observe (machine : ExampleMachine) : Option (Outcome Tower.Head Empty Empty 1) × List Bool :=
  (haltedOutcome machine, effects machine)

/-- Two force sites share the one effectful producer, including the force
below a native binder. The retained result is a native dependent pair. -/
theorem shared_dependent_run :
    (runFrontier machineSpec 64 [initial]).map observe =
      [(some (.value (.pair (.var 0) (.refl (.var 0)))), [true])] := by
  rfl

theorem dependent_result_admitted :
    FormationSensitive.Judgment Tower.rules context
      (.pair (.var 0) (.refl (.var 0))) (.sigma ground identityFamily) :=
  ⟨source_judgment.context,
    .pairIntro sigma_formed (.sort _) (.var 0) (.reflIntro (.var 0))⟩

/-- This bounded execution's actual value results have native judgments.
The proof uses its computed frontier and independent native pair admission,
not a claim of preservation for arbitrary machine stacks. -/
theorem shared_returned_judgment {machine : ExampleMachine} {value : Tower.Tm 1}
    (member : machine ∈ runFrontier machineSpec 64 [initial])
    (returned : haltedOutcome machine = some (.value value)) :
    FormationSensitive.Judgment Tower.rules context value (.sigma ground identityFamily) := by
  have observed : observe machine ∈ (runFrontier machineSpec 64 [initial]).map observe :=
    List.mem_map.mpr ⟨machine, member, rfl⟩
  rw [shared_dependent_run, List.mem_singleton] at observed
  have equal := congrArg Prod.fst observed
  change haltedOutcome machine = _ at equal
  rw [returned] at equal
  cases equal
  exact dependent_result_admitted

end AdmissionExamples

namespace CacheExamples

open FormationSensitive.DependentComputation.Examples
open ScopedNeedComputation.Examples (operationSignature)

abbrev ExampleMachine := NeedMachine Tower.Head Empty Bool Empty Empty 2

def primitive : Empty → Tower.Tm 2 → Produced (Tower.Tm 2) Empty Empty :=
  fun operation => nomatch operation

def cell : CellId := ⟨0, [], 0, 0⟩

def producer : Closure Tower.Head Empty Bool 2 :=
  ⟨2, 0, .returnValue (.refl older.val), ids, Fin.elim0⟩

def suspendedHeap : Heap (Closure Tower.Head Empty Bool 2) (Tower.Tm 2) Empty where
  current := Function.update (fun _ => none) cell (some ⟨producer, .suspended⟩)
  spine := [.allocate cell producer]

/-- The fixture's allocation is an actual successful heap operation. -/
theorem suspendedHeap_allocated :
    Heap.empty.allocate? cell producer = some suspendedHeap := rfl

def completedHeap : Heap (Closure Tower.Head Empty Bool 2) (Tower.Tm 2) Empty :=
  suspendedHeap.setKnownCache cell ⟨producer, .suspended⟩ (.value (.refl older.val))

def cellTypes : CellTypes Tower.Head 2 :=
  Function.update (fun _ => none) cell (some (inst0 older.val family))

private theorem environment : FormationSensitive.CtxMor Tower.rules context context ids := by
  intro index
  simpa only [subst_ids, ids] using
    (FormationSensitive.Typing.var (R := Tower.rules) (Γ := context) index)

theorem producer_typed :
    ClosureTyping Tower.rules operationSignature context cellTypes producer
      (inst0 older.val family) := by
  have typed : ClosureTyping Tower.rules operationSignature context cellTypes producer
      (subst ids (inst0 older.val family)) :=
    .captured (needTypes := Fin.elim0)
      (.returnValue (reflexivity older).property.typing) environment
      (fun index => Fin.elim0 index)
  simpa only [subst_ids] using typed

theorem suspendedHeap_typed :
    HeapTyping Tower.rules operationSignature context cellTypes suspendedHeap := by
  constructor
  · intro key record lookup
    by_cases equal : key = cell
    · subst key
      have same : record = ⟨producer, .suspended⟩ := by
        simpa [Heap.lookup, suspendedHeap] using lookup.symm
      subst record
      exact ⟨inst0 older.val family, by simp [cellTypes], producer_typed, .suspended⟩
    · simp only [Heap.lookup, suspendedHeap, Function.update_of_ne equal] at lookup
      cases lookup
  · intro key A declared
    by_cases equal : key = cell
    · subst key
      exact ⟨⟨producer, .suspended⟩, by simp [Heap.lookup, suspendedHeap]⟩
    · simp only [cellTypes, Function.update_of_ne equal] at declared
      cases declared

/-- The cache write is qualified by independent native reflexivity typing. -/
theorem completedHeap_typed :
    HeapTyping Tower.rules operationSignature context cellTypes completedHeap :=
  suspendedHeap_typed.setKnownCache (by simp [Heap.lookup, suspendedHeap])
    (by simp [cellTypes]) (.value (reflexivity older).property.typing)

def forceClosure : Closure Tower.Head Empty Bool 2 :=
  ⟨2, 1, .force 0, ids, fun _ => cell⟩

theorem force_typed :
    ClosureTyping Tower.rules operationSignature context cellTypes forceClosure
      (inst0 older.val family) := by
  have typed : ClosureTyping Tower.rules operationSignature context cellTypes forceClosure
      (subst ids (inst0 older.val family)) := by
    apply ClosureTyping.captured
      (needTypes := fun _ => inst0 older.val family) (.force 0) environment
    intro index
    simp [cellTypes]
  simpa only [subst_ids] using typed

def pairKont : Kont Tower.Head 2 := .pair older.val .done

theorem pairKont_typed : KontTyping Tower.rules context pairKont
    (inst0 older.val family) (.sigma ground family) :=
  .pair sigma_formed.typing (.sort _) older.property.typing (.done _)

/-- This actual cache consumer returns the dependent pair at the selected
older value; its second component is admitted in that exact identity fibre. -/
theorem actual_cached_pair_judgment :
    FormationSensitive.Judgment Tower.rules context
      (.pair older.val (.refl older.val)) (.sigma ground family) :=
  cached_force_consumer_judgment (NativeFault := Empty) (origin := producer)
    force_typed context_formed
    completedHeap_typed (by simp [completedHeap, Heap.setKnownCache_lookup_same])
    pairKont_typed rfl

def cachedMachine : ExampleMachine where
  world :=
    { lineage := 0, path := [], heap := completedHeap, receipts := .empty,
      nextCell := 1, nextEvaluator := 0 }
  control := .force cell [.resume (.finish pairKont)]

theorem actual_cached_pair_run :
    answers (spec primitive) 8 cachedMachine =
      [.value (.pair older.val (.refl older.val))] := rfl

def wrongCellTypes : CellTypes Tower.Head 2 :=
  Function.update (fun _ => none) cell (some (inst0 newer.val family))

/-- The same raw cached term cannot acquire the other selected value's fibre.
This refutes the independently stated heap invariant, not machine execution. -/
theorem wrong_fibre_cache_not_typed :
    ¬ HeapTyping Tower.rules operationSignature context wrongCellTypes completedHeap := by
  intro typed
  exact wrong_selected_index_not_admitted
    (typed.cached_judgment (cell := cell) (origin := producer)
      context_formed (by simp [wrongCellTypes])
      (by simp [completedHeap, Heap.setKnownCache_lookup_same]))

/-- With no proof-side cell-type assignment consulted, the raw machine still
returns an injected value even when it violates the declared native fibre. -/
def wrongMachine : ExampleMachine :=
  { cachedMachine with control := .force cell [] }

theorem wrong_fibre_still_returned :
    answers (spec primitive) 4 wrongMachine = [.value (.refl older.val)] := rfl

theorem wrong_return_has_no_requested_judgment :
    ¬ FormationSensitive.Judgment Tower.rules context
      (.refl older.val) (inst0 newer.val family) := wrong_selected_index_not_admitted

end CacheExamples

#print axioms ClosureTyping.cached_force_judgment
#print axioms cached_force_result_judgment
#print axioms cached_force_consumer_judgment
#print axioms AdmissionExamples.initial_source_typed
#print axioms AdmissionExamples.shared_dependent_run
#print axioms AdmissionExamples.shared_returned_judgment
#print axioms CacheExamples.suspendedHeap_allocated
#print axioms CacheExamples.completedHeap_typed
#print axioms CacheExamples.actual_cached_pair_judgment
#print axioms CacheExamples.actual_cached_pair_run
#print axioms CacheExamples.wrong_fibre_cache_not_typed
#print axioms CacheExamples.wrong_fibre_still_returned
#print axioms CacheExamples.wrong_return_has_no_requested_judgment

end ScopedNeedMachine
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
