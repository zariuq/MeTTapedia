import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ScopedNeedMachineTyping

/-!
# Store and world laws for native Need typing

Cell declarations extend monotonically, but a heap typing invariant also
requires its declared domain to agree with the actual heap. Recording receipts
and forking worlds preserve that heap. Successful allocation supplies both the
new declaration and the enlarged heap; adding a declaration without allocating
its cell does not preserve heap typing.

Lookup recovers the retained origin and cache at the independently selected
cell type. Conversion of an outcome or cache still requires the existing
formation-sensitive target-formation and conversion premises. None of these
laws infer typing from runtime success or prove whole-machine preservation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace ScopedNeedMachine

open PrimeNeedReference
open ScopedComputation (OperationSignature)

variable {Head Operation Effect StableFault NativeFault : Type} {m : Nat}
  {R : Rules Head} {signature : OperationSignature Head Operation} {Δ : Ctx Head m}

theorem StoreExtends.refl (types : CellTypes Head m) : StoreExtends types types :=
  fun _ _ declared => declared

theorem StoreExtends.trans {first middle last : CellTypes Head m}
    (earlier : StoreExtends first middle) (later : StoreExtends middle last) :
    StoreExtends first last :=
  fun cell A declared => later cell A (earlier cell A declared)

theorem HeapTyping.of_heap_eq {types : CellTypes Head m}
    {before after : Heap (Closure Head Operation Effect m) (Tm Head m) StableFault}
    (typed : HeapTyping R signature Δ types before) (same : after = before) :
    HeapTyping R signature Δ types after := by
  simpa only [same] using typed

theorem HeapTyping.recorded {types : CellTypes Head m}
    {world : NeedWorld Head Operation Effect StableFault NativeFault m}
    (typed : HeapTyping R signature Δ types world.heap)
    (payload : ReceiptPayload (Closure Head Operation Effect m) Rule (Tm Head m)
      StableFault (Fault NativeFault) Effect) :
    HeapTyping R signature Δ types (recorded world payload).heap :=
  typed.of_heap_eq (PrimeNeedCacheLaws.recorded_heap world payload)

theorem HeapTyping.fork {types : CellTypes Head m}
    {world : NeedWorld Head Operation Effect StableFault NativeFault m}
    (typed : HeapTyping R signature Δ types world.heap) (branch : Nat) :
    HeapTyping R signature Δ types (world.fork branch).heap :=
  typed.of_heap_eq (World.fork_preserves_heap world branch)

/-- The externally selected declaration determines both source and cache type. -/
theorem HeapTyping.lookup_typed {types : CellTypes Head m}
    {heap : Heap (Closure Head Operation Effect m) (Tm Head m) StableFault}
    (typed : HeapTyping R signature Δ types heap) {cell : CellId}
    {record : CellRecord (Closure Head Operation Effect m) (Tm Head m) StableFault}
    {A : Tm Head m} (declared : types cell = some A)
    (present : heap.lookup cell = some record) :
    ClosureTyping R signature Δ types record.origin A ∧ CacheTyping R Δ A record.cache := by
  obtain ⟨B, key, originTyped, cacheTyped⟩ := typed.entries cell record present
  have same : B = A := Option.some.inj (key.symm.trans declared)
  subst B
  exact ⟨originTyped, cacheTyped⟩

theorem HeapTyping.absent_type {types : CellTypes Head m}
    {heap : Heap (Closure Head Operation Effect m) (Tm Head m) StableFault}
    (typed : HeapTyping R signature Δ types heap) {cell : CellId}
    (absent : heap.lookup cell = none) : types cell = none := by
  cases declared : types cell with
  | none => rfl
  | some A =>
      obtain ⟨record, present⟩ := typed.domain cell A declared
      rw [absent] at present
      cases present

/-- Heap and declaration absence agree, not just successful lookup. -/
theorem HeapTyping.absent_iff {types : CellTypes Head m}
    {heap : Heap (Closure Head Operation Effect m) (Tm Head m) StableFault}
    (typed : HeapTyping R signature Δ types heap) (cell : CellId) :
    heap.lookup cell = none ↔ types cell = none := by
  constructor
  · exact typed.absent_type
  · intro absent
    cases present : heap.lookup cell with
    | none => rfl
    | some record =>
        obtain ⟨A, declared, _, _⟩ := typed.entries cell record present
        rw [absent] at declared
        cases declared

@[simp] theorem extendStore_same (types : CellTypes Head m) (cell : CellId) (A : Tm Head m) :
    extendStore types cell A cell = some A := by
  simp [extendStore]

theorem extendStore_other (types : CellTypes Head m) {cell other : CellId}
    (different : other ≠ cell) (A : Tm Head m) :
    extendStore types cell A other = types other := by
  simp only [extendStore, Function.update_of_ne different]

theorem HeapTyping.allocation_extends {types : CellTypes Head m}
    {world next : NeedWorld Head Operation Effect StableFault NativeFault m}
    {origin : Closure Head Operation Effect m} {cell : CellId} {generation : Nat}
    (typed : HeapTyping R signature Δ types world.heap)
    (allocated : world.allocate? origin generation = some (next, cell)) (A : Tm Head m) :
    StoreExtends types (extendStore types cell A) :=
  extendStore_extends (typed.absent_type (PrimeNeedCacheLaws.allocate_fresh_absent allocated)) A

/-- Successful allocation supplies a genuinely new, exactly typed key. -/
theorem HeapTyping.allocation_declared {types : CellTypes Head m}
    {world next : NeedWorld Head Operation Effect StableFault NativeFault m}
    {origin : Closure Head Operation Effect m} {cell : CellId} {generation : Nat}
    (typed : HeapTyping R signature Δ types world.heap)
    (allocated : world.allocate? origin generation = some (next, cell)) (A : Tm Head m) :
    types cell = none ∧ extendStore types cell A cell = some A :=
  ⟨typed.absent_type (PrimeNeedCacheLaws.allocate_fresh_absent allocated),
    extendStore_same types cell A⟩

theorem HeapTyping.allocate_package {types : CellTypes Head m}
    {world next : NeedWorld Head Operation Effect StableFault NativeFault m}
    {origin : Closure Head Operation Effect m} {cell : CellId} {A : Tm Head m}
    (typed : HeapTyping R signature Δ types world.heap)
    (source : ClosureTyping R signature Δ types origin A)
    (allocated : world.allocate? origin = some (next, cell)) :
    StoreExtends types (extendStore types cell A) ∧
      extendStore types cell A cell = some A ∧
      HeapTyping R signature Δ (extendStore types cell A) next.heap :=
  ⟨typed.allocation_extends allocated A, extendStore_same types cell A,
    typed.allocate source allocated⟩

theorem CacheTyping.value_iff {A value : Tm Head m} :
    CacheTyping (StableFault := StableFault) R Δ A (.value value) ↔
      FormationSensitive.Typing R Δ value A := by
  constructor
  · intro typed
    cases typed with
    | value admitted => exact admitted
  · exact .value

theorem CacheTyping.value_outcome {A value : Tm Head m}
    (typed : CacheTyping (StableFault := StableFault) R Δ A (.value value)) :
    OutcomeTyping (StableFault := StableFault) (NativeFault := NativeFault) R Δ A (.value value) :=
  .value (CacheTyping.value_iff.mp typed)

/-- A native type conversion cannot be obtained merely by changing the label. -/
theorem CacheTyping.convert {A B : Tm Head m} {u : Head}
    {cache : Cache (Tm Head m) StableFault} (typed : CacheTyping R Δ A cache)
    (formed : FormationSensitive.Typing R Δ B (.head u)) (universeWitness : R.isUniverse u)
    (conversion : Conv R.headEq A B R.computation) : CacheTyping R Δ B cache := by
  cases typed with
  | suspended => exact .suspended
  | evaluating owner => exact .evaluating owner
  | value admitted => exact .value (.conv admitted formed universeWitness conversion)
  | stableFault fault => exact .stableFault fault

/-- A monotone proof-side store extension alone cannot create a runtime cell. -/
theorem not_heapTyping_extended_empty (cell : CellId) (A : Tm Head m) :
    ¬ HeapTyping R signature Δ (extendStore (fun _ => none) cell A)
      (Heap.empty : Heap (Closure Head Operation Effect m) (Tm Head m) StableFault) := by
  intro typed
  obtain ⟨record, present⟩ := typed.domain cell A (extendStore_same _ cell A)
  cases present

#print axioms StoreExtends.trans
#print axioms HeapTyping.lookup_typed
#print axioms HeapTyping.absent_iff
#print axioms HeapTyping.recorded
#print axioms HeapTyping.fork
#print axioms HeapTyping.allocate_package
#print axioms CacheTyping.value_outcome
#print axioms CacheTyping.convert
#print axioms not_heapTyping_extended_empty

end ScopedNeedMachine
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
