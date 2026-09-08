import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ScopedNeedMachine
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ScopedNeedComputationTyping
import Mettapedia.Languages.MeTTa.PrimeNeedAllocationBound

/-!
# Native typing at scoped Need closure and heap boundaries

The runtime stores raw native terms. A separate cell-type assignment relates
captured source typing, native environments, suspension references and cached
values. Allocation extends that assignment at a fresh cell; cache replacement
requires an independently typed value. The proofs do not manufacture native
typing from successful lookup or from an answer subtype.

Opening a value body substitutes the actual returned term and preserves all
older handle-type coordinates. Opening a need body extends only the handle
environment. Native Sigma continuations preserve their dependent pair type,
and faults remain faults. These are local preservation and heap-extension
lemmas; an all-control-stack machine preservation theorem is separate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace ScopedNeedMachine

open PrimeNeedReference
open ScopedComputation (OperationSignature)
open ScopedNeedComputation (extendNeedTypes weakenNeedTypes)

variable {Head Operation Effect StableFault NativeFault : Type} {n m k : Nat}
  {R : Rules Head} {signature : OperationSignature Head Operation} {Δ : Ctx Head m}

abbrev CellTypes (Head : Type) (m : Nat) := CellId → Option (Tm Head m)

def StoreExtends (before after : CellTypes Head m) : Prop :=
  ∀ cell A, before cell = some A → after cell = some A

/-- The captured code and value environment are independently typed. Each
handle is resolved at its complete cell identity and substituted result type. -/
inductive ClosureTyping (R : Rules Head) (signature : OperationSignature Head Operation)
    (Δ : Ctx Head m) (types : CellTypes Head m) :
    Closure Head Operation Effect m → Tm Head m → Prop where
  | captured {n k : Nat} {Γ : Ctx Head n} {needTypes : Fin k → Tm Head n}
      {code : ScopedNeedComputation.Code Head Operation Effect n k} {A : Tm Head n}
      {values : Sub Head n m} {needs : Fin k → CellId} :
      ScopedNeedComputation.Typing R signature Γ needTypes code A →
      FormationSensitive.CtxMor R Γ Δ values →
      (∀ index, types (needs index) = some (subst values (needTypes index))) →
      ClosureTyping R signature Δ types ⟨n, k, code, values, needs⟩ (subst values A)

theorem ClosureTyping.extend {before after : CellTypes Head m}
    {closure : Closure Head Operation Effect m} {A : Tm Head m}
    (typed : ClosureTyping R signature Δ before closure A)
    (extension : StoreExtends before after) : ClosureTyping R signature Δ after closure A := by
  cases typed with
  | captured source environment references =>
      exact .captured source environment (fun index => extension _ _ (references index))

/-- Opening a native binder checks the actual returned term. Older suspension
references keep their types despite native weakening in the source body. -/
theorem value_body_open {Γ : Ctx Head n} {needTypes : Fin k → Tm Head n}
    {body : ScopedNeedComputation.Code Head Operation Effect (n + 1) k}
    {A : Tm Head n} {B : Tm Head (n + 1)} {values : Sub Head n m}
    {needs : Fin k → CellId} {types : CellTypes Head m} {value : Tm Head m}
    (source : ScopedNeedComputation.Typing R signature (.snoc Γ A)
      (weakenNeedTypes needTypes) body B)
    (environment : FormationSensitive.CtxMor R Γ Δ values)
    (references : ∀ index, types (needs index) = some (subst values (needTypes index)))
    (admitted : FormationSensitive.Typing R Δ value (subst values A)) :
    ClosureTyping R signature Δ types
      ((⟨n, k, body, values, needs⟩ : ValueBody Head Operation Effect m).open value)
      (inst0 value (subst (liftSub values) B)) := by
  have opened : ClosureTyping R signature Δ types
      ⟨n + 1, k, body, consSub value values, needs⟩ (subst (consSub value values) B) := by
    apply ClosureTyping.captured source (ScopedComputation.extendEnvironment environment admitted)
    intro index
    simpa only [weakenNeedTypes, subst_consSub_rename_wk] using references index
  have same : consSub value values = Fin.cases value values := by
    funext index
    exact Fin.cases rfl (fun _ => rfl) index
  rw [subst_consSub] at opened
  simpa only [ValueBody.open, same] using opened

/-- Allocation supplies a new handle coordinate, never a native variable. -/
theorem need_body_open {Γ : Ctx Head n} {needTypes : Fin k → Tm Head n}
    {body : ScopedNeedComputation.Code Head Operation Effect n (k + 1)}
    {A B : Tm Head n} {values : Sub Head n m} {needs : Fin k → CellId}
    {types : CellTypes Head m} {cell : CellId}
    (source : ScopedNeedComputation.Typing R signature Γ (extendNeedTypes A needTypes) body B)
    (environment : FormationSensitive.CtxMor R Γ Δ values)
    (references : ∀ index, types (needs index) = some (subst values (needTypes index)))
    (allocated : types cell = some (subst values A)) :
    ClosureTyping R signature Δ types
      ((⟨n, k, body, values, needs⟩ : NeedBody Head Operation Effect m).open cell)
      (subst values B) := by
  apply ClosureTyping.captured source environment
  intro index
  exact Fin.cases allocated (fun prior => references prior) index

/-- Classify outcomes without treating a fault as a native proof. -/
inductive OutcomeTyping (R : Rules Head) (Δ : Ctx Head m) (A : Tm Head m) :
    Outcome Head StableFault NativeFault m → Prop where
  | value {value : Tm Head m} : FormationSensitive.Typing R Δ value A →
      OutcomeTyping R Δ A (.value value)
  | stableFault (fault : StableFault) : OutcomeTyping R Δ A (.stableFault fault)
  | retryableFault (reason : RetryReason (Fault NativeFault)) :
      OutcomeTyping R Δ A (.retryableFault reason)

/-- A pair continuation consumes the selected first value's actual fibre. -/
inductive KontTyping (R : Rules Head) (Δ : Ctx Head m) :
    Kont Head m → Tm Head m → Tm Head m → Prop where
  | done (A : Tm Head m) : KontTyping R Δ .done A A
  | pair {A : Tm Head m} {B : Tm Head (m + 1)} {u : Head}
      {first : Tm Head m} {kont : Kont Head m} {result : Tm Head m} :
      FormationSensitive.Typing R Δ (.sigma A B) (.head u) → R.isUniverse u →
      FormationSensitive.Typing R Δ first A →
      KontTyping R Δ kont (.sigma A B) result →
      KontTyping R Δ (.pair first kont) (inst0 first B) result

theorem KontTyping.finish_preserves {kont : Kont Head m} {A B : Tm Head m}
    (typed : KontTyping R Δ kont A B)
    {outcome : Outcome Head StableFault NativeFault m} (admitted : OutcomeTyping R Δ A outcome) :
    OutcomeTyping R Δ B (finish outcome kont) := by
  induction typed generalizing outcome with
  | done _ => exact admitted
  | pair formed universeWitness firstTyped _ ih =>
      cases admitted with
      | value secondTyped =>
          exact ih (.value (.pairIntro formed universeWitness firstTyped secondTyped))
      | stableFault fault => exact .stableFault fault
      | retryableFault reason => exact .retryableFault reason

inductive CacheTyping (R : Rules Head) (Δ : Ctx Head m) (A : Tm Head m) :
    Cache (Tm Head m) StableFault → Prop where
  | suspended : CacheTyping R Δ A .suspended
  | evaluating (owner : EvaluatorId) : CacheTyping R Δ A (.evaluating owner)
  | value {value : Tm Head m} : FormationSensitive.Typing R Δ value A →
      CacheTyping R Δ A (.value value)
  | stableFault (fault : StableFault) : CacheTyping R Δ A (.stableFault fault)

/-- Typed cell domains agree with the actual heap. The retained origin and
the completed cache satisfy independent conditions at the same native type. -/
structure HeapTyping (R : Rules Head) (signature : OperationSignature Head Operation)
    (Δ : Ctx Head m) (types : CellTypes Head m)
    (heap : Heap (Closure Head Operation Effect m) (Tm Head m) StableFault) : Prop where
  entries : ∀ cell record, heap.lookup cell = some record →
    ∃ A, types cell = some A ∧ ClosureTyping R signature Δ types record.origin A ∧
      CacheTyping R Δ A record.cache
  domain : ∀ cell A, types cell = some A → ∃ record, heap.lookup cell = some record

theorem HeapTyping.empty :
    HeapTyping R signature Δ (fun _ => none)
      (Heap.empty : Heap (Closure Head Operation Effect m) (Tm Head m) StableFault) := by
  constructor
  · intro cell record impossible
    cases impossible
  · intro cell A impossible
    cases impossible

/-- A cached term's native type is recovered from the heap invariant, not
from the fact that the machine returned it. -/
theorem HeapTyping.cached_value
    {types : CellTypes Head m}
    {heap : Heap (Closure Head Operation Effect m) (Tm Head m) StableFault}
    (typed : HeapTyping R signature Δ types heap) {cell : CellId}
    {origin : Closure Head Operation Effect m} {value A : Tm Head m}
    (declared : types cell = some A) (cached : heap.lookup cell = some ⟨origin, .value value⟩) :
    FormationSensitive.Typing R Δ value A := by
  obtain ⟨B, key, _, valueTyped⟩ := typed.entries cell _ cached
  have equal : B = A := Option.some.inj (key.symm.trans declared)
  subst B
  cases valueTyped with
  | value admitted => exact admitted

theorem HeapTyping.cached_judgment
    {types : CellTypes Head m}
    {heap : Heap (Closure Head Operation Effect m) (Tm Head m) StableFault}
    (typed : HeapTyping R signature Δ types heap) (context : FormationSensitive.ContextFormation R Δ)
    {cell : CellId} {origin : Closure Head Operation Effect m} {value A : Tm Head m}
    (declared : types cell = some A) (cached : heap.lookup cell = some ⟨origin, .value value⟩) :
    FormationSensitive.Judgment R Δ value A := ⟨context, typed.cached_value declared cached⟩

/-- The type assignment is proof-side metadata. It is not stored in values
or used as a successful-answer oracle by the runtime. -/
def extendStore (types : CellTypes Head m) (cell : CellId) (A : Tm Head m) :
    CellTypes Head m := Function.update types cell (some A)

theorem extendStore_extends {types : CellTypes Head m} {cell : CellId}
    (fresh : types cell = none) (A : Tm Head m) : StoreExtends types (extendStore types cell A) := by
  intro other B declared
  by_cases equal : other = cell
  · subst other
    rw [fresh] at declared
    cases declared
  · simpa only [extendStore, Function.update_of_ne equal] using declared

/-- Actual successful world allocation extends typing at the fresh cell and
preserves the origin and cache obligations of every older cell. -/
theorem HeapTyping.allocate {types : CellTypes Head m}
    {world next : NeedWorld Head Operation Effect StableFault NativeFault m}
    {origin : Closure Head Operation Effect m} {cell : CellId} {A : Tm Head m}
    (typed : HeapTyping R signature Δ types world.heap)
    (source : ClosureTyping R signature Δ types origin A)
    (allocated : world.allocate? origin = some (next, cell)) :
    HeapTyping R signature Δ (extendStore types cell A) next.heap := by
  have absent := PrimeNeedCacheLaws.allocate_fresh_absent allocated
  have fresh : types cell = none := by
    cases declared : types cell with
    | none => rfl
    | some B =>
        obtain ⟨record, lookup⟩ := typed.domain cell B declared
        rw [absent] at lookup
        cases lookup
  have extension := extendStore_extends fresh A
  constructor
  · intro other record lookup
    by_cases equal : other = cell
    · subst other
      rw [World.allocate?_lookup_same allocated] at lookup
      cases Option.some.inj lookup
      exact ⟨A, by simp [extendStore], source.extend extension, .suspended⟩
    · rw [World.allocate?_preserves_other allocated equal] at lookup
      obtain ⟨B, declared, originTyped, cacheTyped⟩ := typed.entries other record lookup
      exact ⟨B, extension other B declared, originTyped.extend extension, cacheTyped⟩
  · intro other B declared
    by_cases equal : other = cell
    · subst other
      exact ⟨⟨origin, .suspended⟩, World.allocate?_lookup_same allocated⟩
    · have prior : types other = some B := by
        simpa only [extendStore, Function.update_of_ne equal] using declared
      obtain ⟨record, lookup⟩ := typed.domain other B prior
      exact ⟨record, (World.allocate?_preserves_other allocated equal).trans lookup⟩

/-- Cache replacement retains the source origin and requires actual native
typing whenever the replacement is a value. This is not permission to overwrite
a completed cell, nor a proof that the replacement is its producer's result. -/
theorem HeapTyping.setKnownCache {types : CellTypes Head m}
    {heap : Heap (Closure Head Operation Effect m) (Tm Head m) StableFault}
    (typed : HeapTyping R signature Δ types heap) {cell : CellId}
    {record : CellRecord (Closure Head Operation Effect m) (Tm Head m) StableFault}
    {A : Tm Head m} {state : Cache (Tm Head m) StableFault}
    (lookup : heap.lookup cell = some record) (declared : types cell = some A)
    (replacement : CacheTyping R Δ A state) :
    HeapTyping R signature Δ types (heap.setKnownCache cell record state) := by
  constructor
  · intro other found present
    by_cases equal : other = cell
    · subst other
      rw [Heap.setKnownCache_lookup_same] at present
      cases Option.some.inj present
      obtain ⟨B, key, originTyped, _⟩ := typed.entries cell record lookup
      have equal : B = A := Option.some.inj (key.symm.trans declared)
      subst B
      exact ⟨A, declared, originTyped, replacement⟩
    · rw [Heap.setKnownCache_preserves_other heap record state equal] at present
      exact typed.entries other found present
  · intro other B key
    by_cases equal : other = cell
    · subst other
      exact ⟨{ record with cache := state }, Heap.setKnownCache_lookup_same _ _ _ _⟩
    · obtain ⟨found, present⟩ := typed.domain other B key
      exact ⟨found, (Heap.setKnownCache_preserves_other heap record state equal).trans present⟩

/-- Reachability from an empty heap supplies allocation success; the separate
logical heap and source conditions then qualify its actual resulting heap. -/
theorem HeapTyping.allocate_reachable
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    {length : Nat} {initial current : NeedMachine Head Operation Effect StableFault NativeFault m}
    {types : CellTypes Head m} {origin : Closure Head Operation Effect m} {A : Tm Head m}
    (execution : Steps (spec primitive) length initial current)
    (empty : initial.world.heap = Heap.empty)
    (typed : HeapTyping R signature Δ types current.world.heap)
    (source : ClosureTyping R signature Δ types origin A) :
    ∃ next, current.world.allocate? origin = some (next, current.world.freshCell 0) ∧
      HeapTyping R signature Δ (extendStore types (current.world.freshCell 0) A) next.heap := by
  obtain ⟨next, allocated⟩ := PrimeNeedAllocationBound.reachable_allocate_succeeds
    (spec primitive) execution empty origin 0
  exact ⟨next, allocated, typed.allocate source allocated⟩

#print axioms ClosureTyping.extend
#print axioms value_body_open
#print axioms need_body_open
#print axioms KontTyping.finish_preserves
#print axioms HeapTyping.cached_value
#print axioms HeapTyping.cached_judgment
#print axioms HeapTyping.allocate
#print axioms HeapTyping.setKnownCache
#print axioms HeapTyping.allocate_reachable

end ScopedNeedMachine
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
