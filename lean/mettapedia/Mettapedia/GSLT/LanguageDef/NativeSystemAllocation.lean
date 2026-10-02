import Mettapedia.GSLT.LanguageDef.NativeExecutionFreeStorage

/-!
Live logical storage effects of system allocation. An unsuccessful allocation
returns null without publishing storage. A successful allocation selects fresh
storage and installs its extent and initial cells. Freshness is an allocator
guarantee, not a guest runtime test. Initial cells describe the declared typed
storage profile; physical sizes, alignment and pointer realization are separate
ABI obligations. The source and target allocation relations are independent.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeSystemAllocation

open NativeOps (Address SourceValue TargetValue SourceMemory TargetMemory MemoryRelated encodeValue)
open NativeWord64 (Word encode)

def sourceFresh (memory : SourceMemory) (storage : Nat) : Prop :=
  memory.owned storage = none ∧ ∀ element, memory.cells storage element = none

def targetFresh (memory : TargetMemory) (storage : Nat) : Prop :=
  (∀ element, memory.cells storage element = none) ∧ memory.owned storage = none

theorem fresh_correspondence (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (storage : Nat) :
    targetFresh target storage ↔ sourceFresh source storage := by
  have owned : target.owned storage = none ↔ source.owned storage = none := by
    rw [related.2]
    cases source.owned storage <;> simp
  have cells : (∀ element, target.cells storage element = none) ↔
      ∀ element, source.cells storage element = none := by
    constructor <;> intro empty element
    · have cell := empty element
      rw [related.1] at cell
      cases value : source.cells storage element with
      | none => rfl
      | some _ => simp only [value, Option.map_some] at cell; cases cell
    · rw [related.1, empty element]
      rfl
  simp only [targetFresh, sourceFresh, cells, owned, and_comm]

def sourceInstall (memory : SourceMemory) (storage : Nat) (extent : Word)
    (initial : Nat → Option SourceValue) : SourceMemory :=
  ⟨fun candidate element => if candidate = storage then
      if element < extent.val then initial element else none
    else memory.cells candidate element,
    fun candidate => if candidate = storage then some extent else memory.owned candidate⟩

def targetInstall (memory : TargetMemory) (storage : Nat) (extent : BitVec 64)
    (initial : Nat → Option TargetValue) : TargetMemory :=
  { cells := fun candidate element =>
      if candidate ≠ storage then memory.cells candidate element
      else if element ≥ extent.toNat then none else initial element
    owned := fun candidate => if storage = candidate then some extent else memory.owned candidate }

theorem install_correspondence (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (storage : Nat) (extent : Word)
    (initial : Nat → Option SourceValue) :
    MemoryRelated (sourceInstall source storage extent initial)
      (targetInstall target storage (encode extent) (fun element => (initial element).map encodeValue)) := by
  constructor
  · intro candidate element
    by_cases same : candidate = storage <;> by_cases inside : element < extent.val <;>
      simp only [sourceInstall, targetInstall, NativeWord64.encode_toNat,
        same, ne_eq, not_true_eq_false, not_false_eq_true, if_true, if_false,
        show (extent.val ≤ element) ↔ ¬element < extent.val from Nat.not_lt.symm,
        inside, not_true_eq_false, not_false_eq_true, Option.map_none, related.1]
  · intro candidate
    by_cases same : candidate = storage
    · subst candidate
      simp only [sourceInstall, targetInstall, if_true, Option.map_some]
    · have reversed : storage ≠ candidate := Ne.symm same
      simp only [sourceInstall, targetInstall, if_neg same, if_neg reversed, related.2]

inductive SourceMalloc (extent : Word) (initial : Nat → Option SourceValue) :
    SourceMemory → Option Address → SourceMemory → Prop where
  | failure (memory : SourceMemory) : SourceMalloc extent initial memory none memory
  | success {memory : SourceMemory} {storage : Nat}
      (fresh : sourceFresh memory storage) :
      SourceMalloc extent initial memory (some ⟨storage, 0, []⟩)
        (sourceInstall memory storage extent initial)

inductive TargetMalloc (extent : BitVec 64) (initial : Nat → Option TargetValue) :
    TargetMemory → Option Address → TargetMemory → Prop where
  | failure (memory : TargetMemory) : TargetMalloc extent initial memory none memory
  | success {memory : TargetMemory} {storage : Nat}
      (fresh : targetFresh memory storage) :
      TargetMalloc extent initial memory (some ⟨storage, 0, []⟩)
        (targetInstall memory storage extent initial)

theorem malloc_forward (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (extent : Word) (initial : Nat → Option SourceValue)
    (pointer : Option Address) (post : SourceMemory)
    (allocated : SourceMalloc extent initial source pointer post) :
    ∃ native, TargetMalloc (encode extent) (fun element => (initial element).map encodeValue)
      target pointer native ∧ MemoryRelated post native := by
  cases allocated with
  | failure => exact ⟨target, .failure target, related⟩
  | @success storage fresh =>
    exact ⟨_, .success ((fresh_correspondence source target related storage).mpr fresh),
      install_correspondence source target related storage extent initial⟩

theorem malloc_backward (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (extent : Word) (initial : Nat → Option SourceValue)
    (pointer : Option Address) (native : TargetMemory)
    (allocated : TargetMalloc (encode extent) (fun element => (initial element).map encodeValue)
      target pointer native) :
    ∃ post, SourceMalloc extent initial source pointer post ∧ MemoryRelated post native := by
  cases allocated with
  | failure => exact ⟨source, .failure source, related⟩
  | @success storage fresh =>
    exact ⟨_, .success ((fresh_correspondence source target related storage).mp fresh),
      install_correspondence source target related storage extent initial⟩

theorem source_install_read_cell (memory : SourceMemory) (storage : Nat) (extent : Word)
    (initial : Nat → Option SourceValue) (element : Nat) (inside : element < extent.val) :
    (sourceInstall memory storage extent initial).cells storage element = initial element := by
  simp only [sourceInstall, if_true, inside]

theorem source_install_owned (memory : SourceMemory) (storage : Nat) (extent : Word)
    (initial : Nat → Option SourceValue) :
    (sourceInstall memory storage extent initial).owned storage = some extent := by
  simp only [sourceInstall, if_true]

theorem source_install_frame (memory : SourceMemory) (storage other : Nat) (extent : Word)
    (initial : Nat → Option SourceValue) (different : other ≠ storage) :
    (∀ element, (sourceInstall memory storage extent initial).cells other element =
      memory.cells other element) ∧
    (sourceInstall memory storage extent initial).owned other = memory.owned other := by
  exact ⟨fun _ => by simp only [sourceInstall, if_neg different],
    by simp only [sourceInstall, if_neg different]⟩

theorem source_success_base_live (extent : Word) (initial : Nat → Option SourceValue)
    (memory post : SourceMemory) (pointer : Address)
    (allocated : SourceMalloc extent initial memory (some pointer) post) :
    pointer.element = 0 ∧ pointer.fields = [] ∧ post.owned pointer.storage = some extent := by
  cases allocated
  exact ⟨rfl, rfl, source_install_owned _ _ _ _⟩

theorem source_success_free (extent : Word) (initial : Nat → Option SourceValue)
    (memory post : SourceMemory) (pointer : Address)
    (allocated : SourceMalloc extent initial memory (some pointer) post) :
    NativeExecutionFreeStorage.sourceFree post (some pointer) =
      some (NativeOps.sourceRelease post pointer.storage) := by
  obtain ⟨element, fields, owned⟩ := source_success_base_live extent initial memory post pointer allocated
  simp only [NativeExecutionFreeStorage.sourceFree, element, fields, and_self, if_true,
    owned, bind, Option.bind_some]

theorem source_success_avoids_live_read (extent : Word) (initial : Nat → Option SourceValue)
    (memory post : SourceMemory) (pointer used : Address) (value : SourceValue)
    (allocated : SourceMalloc extent initial memory (some pointer) post)
    (read : NativeOps.sourceRead memory used = some value) : used.storage ≠ pointer.storage := by
  cases allocated with
  | success fresh =>
    intro same
    have absent : memory.cells used.storage used.element = none := by
      rw [same]
      exact fresh.2 used.element
    simp only [NativeOps.sourceRead, absent, Option.bind_none] at read
    cases read

theorem allocation_failure_retains_all_cells (extent : Word) (initial : Nat → Option SourceValue)
    (memory post : SourceMemory) (allocated : SourceMalloc extent initial memory none post) :
    post = memory := by cases allocated; rfl

theorem allocation_cannot_replace_live_storage (memory : SourceMemory) (storage : Nat)
    (extent : Word) (owned : memory.owned storage = some extent) : ¬sourceFresh memory storage := by
  intro fresh
  have missing := fresh.1
  rw [owned] at missing
  cases missing

end Mettapedia.GSLT.LanguageDef.NativeSystemAllocation
