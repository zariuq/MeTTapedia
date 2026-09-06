import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedRuntimeTyping
import Mettapedia.Languages.MeTTa.PrimeNeedCacheLaws

/-!
# Source-backed heap typing for first-class Need answers

Every allocated cell retains an independently typed source closure. A completed
value cache additionally retains typing of its actual answer, including captured
function and thunk environments. Both obligations transport when allocation
extends the store. The declaration domain agrees exactly with the actual heap.
The invariant concerns current cells, not admission of arbitrary historical
heap updates or receipts supplied in an initial world.

These lemmas qualify the existing allocation and cache operations. Cache typing
does not authorize an overwrite, establish evaluator ownership, or identify an
arbitrary replacement with the result of its producer. Those obligations belong
to the control and protocol preservation proofs. Retry reset retains the actual
world's receipts; no heap operation below removes or rolls back an effect.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace PolarizedNeedMachine

open PrimeNeedReference
open PolarizedNeed (CTy)
open ScopedComputation (OperationSignature)

variable {Head Operation Effect StableFault NativeFault : Type} {m : Nat}
  {R : Rules Head} {signature : OperationSignature Head Operation} {Δ : Ctx Head m}

inductive CacheTyping (R : Rules Head) (signature : OperationSignature Head Operation)
    (Δ : Ctx Head m) (types : CellTypes Head m) (B : CTy Head m) :
    Cache (Answer Head Operation Effect m) StableFault → Prop where
  | suspended : CacheTyping R signature Δ types B .suspended
  | evaluating (owner : EvaluatorId) : CacheTyping R signature Δ types B (.evaluating owner)
  | value {answer : Answer Head Operation Effect m} :
      AnswerTyping R signature Δ types answer B →
      CacheTyping R signature Δ types B (.value answer)
  | stableFault (fault : StableFault) : CacheTyping R signature Δ types B (.stableFault fault)

/-- Captured references inside completed answers also survive store extension. -/
theorem CacheTyping.extend {before after : CellTypes Head m} {B : CTy Head m}
    {cache : Cache (Answer Head Operation Effect m) StableFault}
    (typed : CacheTyping R signature Δ before B cache) (extension : StoreExtends before after) :
    CacheTyping R signature Δ after B cache := by
  cases typed with
  | suspended => exact .suspended
  | evaluating owner => exact .evaluating owner
  | value answerTyped => exact .value (answerTyped.extend extension)
  | stableFault fault => exact .stableFault fault

theorem CacheTyping.value_iff {types : CellTypes Head m} {B : CTy Head m}
    {answer : Answer Head Operation Effect m} :
    CacheTyping (StableFault := StableFault) R signature Δ types B (.value answer) ↔
      AnswerTyping R signature Δ types answer B := by
  constructor
  · intro typed
    cases typed with
    | value answerTyped => exact answerTyped
  · exact .value

/-- The metadata describes exactly the allocated domain, with independent
origin and cache obligations at each selected computation type. -/
structure HeapTyping (R : Rules Head) (signature : OperationSignature Head Operation)
    (Δ : Ctx Head m) (types : CellTypes Head m)
    (heap : Heap (Closure Head Operation Effect m) (Answer Head Operation Effect m) StableFault) :
    Prop where
  entries : ∀ cell record, heap.lookup cell = some record →
    ∃ B, types cell = some B ∧ ClosureTyping R signature Δ types record.origin B ∧
      CacheTyping R signature Δ types B record.cache
  domain : ∀ cell B, types cell = some B → ∃ record, heap.lookup cell = some record

theorem HeapTyping.empty :
    HeapTyping R signature Δ (fun _ => none)
      (Heap.empty : Heap (Closure Head Operation Effect m) (Answer Head Operation Effect m)
        StableFault) := by
  constructor
  · intro cell record impossible
    cases impossible
  · intro cell B impossible
    cases impossible

theorem HeapTyping.of_heap_eq {types : CellTypes Head m}
    {before after : Heap (Closure Head Operation Effect m) (Answer Head Operation Effect m)
      StableFault}
    (typed : HeapTyping R signature Δ types before) (same : after = before) :
    HeapTyping R signature Δ types after := by
  simpa only [same] using typed

theorem HeapTyping.recorded {types : CellTypes Head m}
    {world : NeedWorld Head Operation Effect StableFault NativeFault m}
    (typed : HeapTyping R signature Δ types world.heap)
    (payload : ReceiptPayload (Closure Head Operation Effect m) Rule (Answer Head Operation Effect m)
      StableFault (Fault NativeFault) Effect) :
    HeapTyping R signature Δ types (recorded world payload).heap :=
  typed.of_heap_eq (PrimeNeedCacheLaws.recorded_heap world payload)

theorem HeapTyping.fork {types : CellTypes Head m}
    {world : NeedWorld Head Operation Effect StableFault NativeFault m}
    (typed : HeapTyping R signature Δ types world.heap) (branch : Nat) :
    HeapTyping R signature Δ types (world.fork branch).heap :=
  typed.of_heap_eq (World.fork_preserves_heap world branch)

/-- Selecting a declared cell recovers both the source and cached answer's
typing. A successful raw lookup by itself does not provide either. -/
theorem HeapTyping.lookup_typed {types : CellTypes Head m}
    {heap : Heap (Closure Head Operation Effect m) (Answer Head Operation Effect m) StableFault}
    (typed : HeapTyping R signature Δ types heap) {cell : CellId}
    {record : CellRecord (Closure Head Operation Effect m) (Answer Head Operation Effect m)
      StableFault} {B : CTy Head m}
    (declared : types cell = some B) (present : heap.lookup cell = some record) :
    ClosureTyping R signature Δ types record.origin B ∧
      CacheTyping R signature Δ types B record.cache := by
  obtain ⟨A, key, originTyped, cacheTyped⟩ := typed.entries cell record present
  have same : A = B := Option.some.inj (key.symm.trans declared)
  subst A
  exact ⟨originTyped, cacheTyped⟩

theorem HeapTyping.cached_answer {types : CellTypes Head m}
    {heap : Heap (Closure Head Operation Effect m) (Answer Head Operation Effect m) StableFault}
    (typed : HeapTyping R signature Δ types heap) {cell : CellId}
    {origin : Closure Head Operation Effect m} {answer : Answer Head Operation Effect m}
    {B : CTy Head m} (declared : types cell = some B)
    (cached : heap.lookup cell = some ⟨origin, .value answer⟩) :
    AnswerTyping R signature Δ types answer B :=
  CacheTyping.value_iff.mp (typed.lookup_typed declared cached).2

/-- At a native return type, actual cached payloads recover the original
formation-sensitive judgment, including any admitted conversion tail. -/
theorem HeapTyping.cached_native_judgment {types : CellTypes Head m}
    {heap : Heap (Closure Head Operation Effect m) (Answer Head Operation Effect m) StableFault}
    (typed : HeapTyping R signature Δ types heap)
    (context : FormationSensitive.ContextFormation R Δ) {cell : CellId}
    {origin : Closure Head Operation Effect m} {term A : Tm Head m}
    (declared : types cell = some (.returns (.native A)))
    (cached : heap.lookup cell = some ⟨origin, .value (.returned (.native term))⟩) :
    FormationSensitive.Judgment R Δ term A := by
  have answerTyped := typed.cached_answer declared cached
  cases answerTyped with
  | returned valueTyped =>
      obtain ⟨other, equal, admitted⟩ := valueTyped.native_payload
      cases equal
      exact ⟨context, admitted⟩

theorem HeapTyping.absent_type {types : CellTypes Head m}
    {heap : Heap (Closure Head Operation Effect m) (Answer Head Operation Effect m) StableFault}
    (typed : HeapTyping R signature Δ types heap) {cell : CellId}
    (absent : heap.lookup cell = none) : types cell = none := by
  cases declared : types cell with
  | none => rfl
  | some B =>
      obtain ⟨record, present⟩ := typed.domain cell B declared
      rw [absent] at present
      cases present

theorem HeapTyping.absent_iff {types : CellTypes Head m}
    {heap : Heap (Closure Head Operation Effect m) (Answer Head Operation Effect m) StableFault}
    (typed : HeapTyping R signature Δ types heap) (cell : CellId) :
    heap.lookup cell = none ↔ types cell = none := by
  constructor
  · exact typed.absent_type
  · intro absent
    cases present : heap.lookup cell with
    | none => rfl
    | some record =>
        obtain ⟨B, declared, _, _⟩ := typed.entries cell record present
        rw [absent] at declared
        cases declared

/-- This declaration update is proof-side metadata, not a runtime oracle. -/
def extendStore (types : CellTypes Head m) (cell : CellId) (B : CTy Head m) : CellTypes Head m :=
  Function.update types cell (some B)

@[simp] theorem extendStore_same (types : CellTypes Head m) (cell : CellId) (B : CTy Head m) :
    extendStore types cell B cell = some B := by
  simp [extendStore]

theorem extendStore_other (types : CellTypes Head m) {cell other : CellId}
    (different : other ≠ cell) (B : CTy Head m) : extendStore types cell B other = types other := by
  simp only [extendStore, Function.update_of_ne different]

theorem extendStore_extends {types : CellTypes Head m} {cell : CellId}
    (fresh : types cell = none) (B : CTy Head m) : StoreExtends types (extendStore types cell B) := by
  intro other A declared
  by_cases equal : other = cell
  · subst other
    rw [fresh] at declared
    cases declared
  · simpa only [extendStore, Function.update_of_ne equal] using declared

theorem HeapTyping.allocation_extends {types : CellTypes Head m}
    {world next : NeedWorld Head Operation Effect StableFault NativeFault m}
    {origin : Closure Head Operation Effect m} {cell : CellId} {generation : Nat}
    (typed : HeapTyping R signature Δ types world.heap)
    (allocated : world.allocate? origin generation = some (next, cell)) (B : CTy Head m) :
    StoreExtends types (extendStore types cell B) :=
  extendStore_extends (typed.absent_type (PrimeNeedCacheLaws.allocate_fresh_absent allocated)) B

theorem HeapTyping.allocation_declared {types : CellTypes Head m}
    {world next : NeedWorld Head Operation Effect StableFault NativeFault m}
    {origin : Closure Head Operation Effect m} {cell : CellId} {generation : Nat}
    (typed : HeapTyping R signature Δ types world.heap)
    (allocated : world.allocate? origin generation = some (next, cell)) (B : CTy Head m) :
    types cell = none ∧ extendStore types cell B cell = some B :=
  ⟨typed.absent_type (PrimeNeedCacheLaws.allocate_fresh_absent allocated),
    extendStore_same types cell B⟩

/-- Successful allocation preserves typing inside all older cached closures,
not merely their retained source origins. The generation is unrestricted. -/
theorem HeapTyping.allocate {types : CellTypes Head m}
    {world next : NeedWorld Head Operation Effect StableFault NativeFault m}
    {origin : Closure Head Operation Effect m} {cell : CellId} {B : CTy Head m} {generation : Nat}
    (typed : HeapTyping R signature Δ types world.heap)
    (source : ClosureTyping R signature Δ types origin B)
    (allocated : world.allocate? origin generation = some (next, cell)) :
    HeapTyping R signature Δ (extendStore types cell B) next.heap := by
  have extension := typed.allocation_extends allocated B
  constructor
  · intro other record lookup
    by_cases equal : other = cell
    · subst other
      rw [World.allocate?_lookup_same allocated] at lookup
      cases Option.some.inj lookup
      exact ⟨B, extendStore_same types cell B, source.extend extension, .suspended⟩
    · rw [World.allocate?_preserves_other allocated equal] at lookup
      obtain ⟨A, declared, originTyped, cacheTyped⟩ := typed.entries other record lookup
      exact ⟨A, extension other A declared, originTyped.extend extension, cacheTyped.extend extension⟩
  · intro other A declared
    by_cases equal : other = cell
    · subst other
      exact ⟨⟨origin, .suspended⟩, World.allocate?_lookup_same allocated⟩
    · have prior : types other = some A := by
        simpa only [extendStore, Function.update_of_ne equal] using declared
      obtain ⟨record, lookup⟩ := typed.domain other A prior
      exact ⟨record, (World.allocate?_preserves_other allocated equal).trans lookup⟩

theorem HeapTyping.allocate_package {types : CellTypes Head m}
    {world next : NeedWorld Head Operation Effect StableFault NativeFault m}
    {origin : Closure Head Operation Effect m} {cell : CellId} {B : CTy Head m} {generation : Nat}
    (typed : HeapTyping R signature Δ types world.heap)
    (source : ClosureTyping R signature Δ types origin B)
    (allocated : world.allocate? origin generation = some (next, cell)) :
    StoreExtends types (extendStore types cell B) ∧
      extendStore types cell B cell = some B ∧
      HeapTyping R signature Δ (extendStore types cell B) next.heap :=
  ⟨typed.allocation_extends allocated B, extendStore_same types cell B,
    typed.allocate source allocated⟩

/-- This preserves admission of a supplied cache replacement, not permission
to perform it. Ownership and production are checked by the actual protocol. -/
theorem HeapTyping.setKnownCache {types : CellTypes Head m}
    {heap : Heap (Closure Head Operation Effect m) (Answer Head Operation Effect m) StableFault}
    (typed : HeapTyping R signature Δ types heap) {cell : CellId}
    {record : CellRecord (Closure Head Operation Effect m) (Answer Head Operation Effect m)
      StableFault} {B : CTy Head m} {cache : Cache (Answer Head Operation Effect m) StableFault}
    (lookup : heap.lookup cell = some record) (declared : types cell = some B)
    (replacement : CacheTyping R signature Δ types B cache) :
    HeapTyping R signature Δ types (heap.setKnownCache cell record cache) := by
  constructor
  · intro other found present
    by_cases equal : other = cell
    · subst other
      rw [Heap.setKnownCache_lookup_same] at present
      cases Option.some.inj present
      exact ⟨B, declared, (typed.lookup_typed declared lookup).1, replacement⟩
    · rw [Heap.setKnownCache_preserves_other heap record cache equal] at present
      exact typed.entries other found present
  · intro other A key
    by_cases equal : other = cell
    · subst other
      exact ⟨{ record with cache := cache }, Heap.setKnownCache_lookup_same _ _ _ _⟩
    · obtain ⟨found, present⟩ := typed.domain other A key
      exact ⟨found, (Heap.setKnownCache_preserves_other heap record cache equal).trans present⟩

/-- Beginning an evaluation changes only the cache's ownership state. -/
theorem HeapTyping.claim {types : CellTypes Head m}
    {world : NeedWorld Head Operation Effect StableFault NativeFault m}
    (typed : HeapTyping R signature Δ types world.heap) {cell : CellId}
    {record : CellRecord (Closure Head Operation Effect m) (Answer Head Operation Effect m)
      StableFault} {B : CTy Head m} (lookup : world.heap.lookup cell = some record)
    (declared : types cell = some B) (owner : EvaluatorId) :
    HeapTyping R signature Δ types (world.setKnownCache cell record (.evaluating owner)).heap :=
  typed.setKnownCache lookup declared (.evaluating owner)

/-- Value completion requires the independently admitted rich answer. -/
theorem HeapTyping.complete {types : CellTypes Head m}
    {world : NeedWorld Head Operation Effect StableFault NativeFault m}
    (typed : HeapTyping R signature Δ types world.heap) {cell : CellId}
    {record : CellRecord (Closure Head Operation Effect m) (Answer Head Operation Effect m)
      StableFault} {B : CTy Head m} {answer : Answer Head Operation Effect m}
    (lookup : world.heap.lookup cell = some record) (declared : types cell = some B)
    (admitted : AnswerTyping R signature Δ types answer B) :
    HeapTyping R signature Δ types
      (PrimeNeedReference.recorded (world.setKnownCache cell record (.value answer))
        (.observe cell (.value answer))).heap :=
  (typed.setKnownCache lookup declared (.value admitted)).recorded _

theorem HeapTyping.completeFault {types : CellTypes Head m}
    {world : NeedWorld Head Operation Effect StableFault NativeFault m}
    (typed : HeapTyping R signature Δ types world.heap) {cell : CellId}
    {record : CellRecord (Closure Head Operation Effect m) (Answer Head Operation Effect m)
      StableFault} {B : CTy Head m} (lookup : world.heap.lookup cell = some record)
    (declared : types cell = some B) (fault : StableFault) :
    HeapTyping R signature Δ types
      (PrimeNeedReference.recorded (world.setKnownCache cell record (.stableFault fault))
        (.observe cell (.stableFault fault))).heap :=
  (typed.setKnownCache lookup declared (.stableFault fault)).recorded _

/-- Reset does not erase earlier receipts or reinterpret a retry as a value. -/
theorem HeapTyping.reset {types : CellTypes Head m}
    {world : NeedWorld Head Operation Effect StableFault NativeFault m}
    (typed : HeapTyping R signature Δ types world.heap) {cell : CellId}
    {record : CellRecord (Closure Head Operation Effect m) (Answer Head Operation Effect m)
      StableFault} {B : CTy Head m} (lookup : world.heap.lookup cell = some record)
    (declared : types cell = some B) (reason : RetryReason (Fault NativeFault)) :
    HeapTyping R signature Δ types
      (PrimeNeedReference.recorded (world.setKnownCache cell record .suspended) (.retry cell reason)).heap :=
  (typed.setKnownCache lookup declared .suspended).recorded _

/-- Resampling retains the old source and allocates a fresh generation; its
new receipt and cell are not erased by the typing argument. -/
theorem HeapTyping.resample_package {types : CellTypes Head m}
    {world next : NeedWorld Head Operation Effect StableFault NativeFault m}
    (typed : HeapTyping R signature Δ types world.heap) {source fresh : CellId}
    {record : CellRecord (Closure Head Operation Effect m) (Answer Head Operation Effect m)
      StableFault} {B : CTy Head m} (lookup : world.heap.lookup source = some record)
    (declared : types source = some B)
    (allocated : world.allocate? record.origin (source.generation + 1) = some (next, fresh)) :
    StoreExtends types (extendStore types fresh B) ∧
      extendStore types fresh B fresh = some B ∧
      HeapTyping R signature Δ (extendStore types fresh B)
        (PrimeNeedReference.recorded next (.resample source fresh)).heap :=
  ⟨typed.allocation_extends allocated B, extendStore_same types fresh B,
    (typed.allocate (typed.lookup_typed declared lookup).1 allocated).recorded _⟩

/-- Every selected rule occurrence starts from the claimed heap. Path and
receipt differences remain in the worlds; this equation projects only heaps. -/
theorem branchAlternatives_heap
    (machine : NeedMachine Head Operation Effect StableFault NativeFault m)
    (base : NeedWorld Head Operation Effect StableFault NativeFault m)
    (cell : CellId)
    (record : CellRecord (Closure Head Operation Effect m) (Answer Head Operation Effect m)
      StableFault) (owner : EvaluatorId) (stack : List (Frame (Resume Head Operation Effect m)))
    (index : Nat) (choices : List (Rule × Local Head Operation Effect StableFault NativeFault m))
    {candidate : NeedMachine Head Operation Effect StableFault NativeFault m}
    (selected : candidate ∈ branchAlternatives machine base cell record owner stack index choices) :
    candidate.world.heap = base.heap.setKnownCache cell record (.evaluating owner) := by
  induction choices generalizing index candidate with
  | nil => simp only [branchAlternatives, List.not_mem_nil] at selected
  | cons head tail ih =>
      simp only [branchAlternatives, List.mem_cons] at selected
      rcases selected with rfl | selected
      · rfl
      · exact ih (index := index + 1) selected

theorem HeapTyping.branchAlternative {types : CellTypes Head m}
    (machine : NeedMachine Head Operation Effect StableFault NativeFault m)
    {base : NeedWorld Head Operation Effect StableFault NativeFault m}
    (typed : HeapTyping R signature Δ types base.heap) {cell : CellId}
    {record : CellRecord (Closure Head Operation Effect m) (Answer Head Operation Effect m)
      StableFault} {B : CTy Head m} (lookup : base.heap.lookup cell = some record)
    (declared : types cell = some B) (owner : EvaluatorId)
    (stack : List (Frame (Resume Head Operation Effect m))) (index : Nat)
    (choices : List (Rule × Local Head Operation Effect StableFault NativeFault m))
    {candidate : NeedMachine Head Operation Effect StableFault NativeFault m}
    (selected : candidate ∈ branchAlternatives machine base cell record owner stack index choices) :
    HeapTyping R signature Δ types candidate.world.heap :=
  (typed.setKnownCache lookup declared (.evaluating owner)).of_heap_eq
    (branchAlternatives_heap machine base cell record owner stack index choices selected)

/-- A native answer is cacheable from native admission without running a
producer or attaching a proof to the raw answer representation. -/
theorem native_cache_admitted {types : CellTypes Head m} {term A : Tm Head m}
    (admitted : FormationSensitive.Typing R Δ term A) :
    CacheTyping (StableFault := StableFault) (Effect := Effect) R signature Δ types
      (.returns (.native A)) (.value (.returned (.native term))) :=
  .value (.returned (.native admitted))

/-- Caching a function as a returned value cannot be justified by relabelling
the declared cell. The two computation types remain distinct. -/
theorem not_function_cache_at_return {types : CellTypes Head m}
    (body : NativeBody Head Operation Effect m) (A : PolarizedNeed.VTy Head m) :
    ¬ CacheTyping (StableFault := StableFault) R signature Δ types
      (.returns A) (.value (.nativeFunction body)) := by
  intro typed
  have answerTyped := CacheTyping.value_iff.mp typed
  cases answerTyped

/-- A raw heap can contain this mismatched cache, but it cannot satisfy the
independent declaration-sensitive heap invariant. -/
theorem not_heapTyping_function_at_return {types : CellTypes Head m}
    {heap : Heap (Closure Head Operation Effect m) (Answer Head Operation Effect m) StableFault}
    {cell : CellId} {origin : Closure Head Operation Effect m}
    {body : NativeBody Head Operation Effect m} {A : PolarizedNeed.VTy Head m}
    (declared : types cell = some (.returns A))
    (cached : heap.lookup cell = some ⟨origin, .value (.nativeFunction body)⟩) :
    ¬ HeapTyping R signature Δ types heap := by
  intro typed
  exact not_function_cache_at_return body A (typed.lookup_typed declared cached).2

/-- Extending metadata without actual allocation cannot preserve exact domains. -/
theorem not_heapTyping_extended_empty (cell : CellId) (B : CTy Head m) :
    ¬ HeapTyping R signature Δ (extendStore (fun _ => none) cell B)
      (Heap.empty : Heap (Closure Head Operation Effect m) (Answer Head Operation Effect m)
        StableFault) := by
  intro typed
  obtain ⟨record, present⟩ := typed.domain cell B (extendStore_same _ cell B)
  cases present

#print axioms CacheTyping.extend
#print axioms HeapTyping.lookup_typed
#print axioms HeapTyping.cached_answer
#print axioms HeapTyping.cached_native_judgment
#print axioms HeapTyping.absent_iff
#print axioms HeapTyping.allocate_package
#print axioms HeapTyping.setKnownCache
#print axioms HeapTyping.complete
#print axioms HeapTyping.reset
#print axioms HeapTyping.resample_package
#print axioms HeapTyping.branchAlternative
#print axioms native_cache_admitted
#print axioms not_function_cache_at_return
#print axioms not_heapTyping_function_at_return
#print axioms not_heapTyping_extended_empty

end PolarizedNeedMachine
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
