import Mathlib.Data.List.Basic
import Mathlib.Logic.Function.Basic

/-!
# Checked bulk publication of privately built binding environments

The reference performs checked logical updates to a function-valued binding
environment. The target separately implements lookup and writes in a private
slot buffer. Inventory reserves variable identities without binding them;
unused capacity contains spare slots. A failed checked attempt may have already
changed the private buffer. Publication discards that whole candidate on error.

The operation order is retained. Unification, context qualification, name-key
checks, cycle admission and per-operation constraint normalization belong to
the checked-attempt producer. It may return several writes and updated metadata.
Its correctness as a native binding algorithm is not assumed or established
here: the theorem preserves whichever checked operations are supplied.

The slot representation is a finite mathematical model of resizable private
storage, not a C memory or allocation-cost proof. Sparse inventories and spare
capacity cannot affect logical lookup. Allocation errors may be reported by an
attempt, but the model does not predict allocator failure from physical bytes.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BindingPublication

universe u v w x y

/-- Metadata includes any state which the publication contract must retain,
such as constraints or per-occurrence state; it is not silently erased. -/
structure Environment (Key : Type u) (Value : Type v) (Metadata : Type w) where
  get : Key → Option Value
  metadata : Metadata

structure Patch (Key : Type u) (Value : Type v) (Metadata : Type w) where
  writes : List (Key × Value)
  metadata : Metadata

/-- A checker can discover failure after tentative writes or normalization.
Only success authorizes publication of those changes. -/
structure Attempt (Key : Type u) (Value : Type v) (Metadata : Type w) (Error : Type x) where
  patch : Patch Key Value Metadata
  verdict : Except Error Unit

section General

variable {Key : Type u} {Value : Type v} {Metadata : Type w}
variable {Error : Type x} {Operation : Type y}

abbrev Checker (Key : Type u) (Value : Type v) (Metadata : Type w)
    (Error : Type x) (Operation : Type y) :=
  Environment Key Value Metadata → Operation → Attempt Key Value Metadata Error

variable [DecidableEq Key]

/-- Independent logical specification: newer checked writes update the map. -/
def applyWrites (lookup : Key → Option Value) : List (Key × Value) → Key → Option Value
  | [] => lookup
  | (key, value) :: rest => applyWrites (Function.update lookup key (some value)) rest

/-- A retained batch followed by another batch is one ordered write list. -/
theorem applyWrites_append (lookup : Key → Option Value)
    (first second : List (Key × Value)) :
    applyWrites lookup (first ++ second) =
      applyWrites (applyWrites lookup first) second := by
  induction first generalizing lookup with
  | nil => rfl
  | cons row rest ih =>
      simpa only [List.cons_append, applyWrites] using
        ih (Function.update lookup row.1 (some row.2))

/-- Writes cannot change a lookup outside their actual key support. -/
theorem applyWrites_lookup_of_not_mem (lookup : Key → Option Value)
    (writes : List (Key × Value)) (key : Key)
    (outside : key ∉ writes.map Prod.fst) :
    applyWrites lookup writes key = lookup key := by
  induction writes generalizing lookup with
  | nil => rfl
  | cons row rest ih =>
      have different : key ≠ row.1 := by
        intro same
        exact outside (by simp [same])
      have tailOutside : key ∉ rest.map Prod.fst := by
        intro member
        exact outside (by simp [member])
      simpa only [applyWrites, Function.update_of_ne different] using
        ih (Function.update lookup row.1 (some row.2)) tailOutside

/-- An independent single write commutes with a complete retained batch,
including repeated writes within that batch. -/
theorem applyWrites_update_of_not_mem (lookup : Key → Option Value)
    (writes : List (Key × Value)) (key : Key) (value : Value)
    (outside : key ∉ writes.map Prod.fst) :
    applyWrites (Function.update lookup key (some value)) writes =
      Function.update (applyWrites lookup writes) key (some value) := by
  induction writes generalizing lookup with
  | nil => rfl
  | cons row rest ih =>
      have different : key ≠ row.1 := by
        intro same
        exact outside (by simp [same])
      have tailOutside : key ∉ rest.map Prod.fst := by
        intro member
        exact outside (by simp [member])
      simp only [applyWrites]
      rw [Function.update_comm different]
      exact ih (Function.update lookup row.1 (some row.2)) tailOutside

/-- Disjoint binding writes commute as maps. Read dependencies and retained
metadata have separate obligations; this law alone does not join worlds. -/
theorem applyWrites_commute (lookup : Key → Option Value)
    (first second : List (Key × Value))
    (disjoint : List.Disjoint (first.map Prod.fst) (second.map Prod.fst)) :
    applyWrites (applyWrites lookup first) second =
      applyWrites (applyWrites lookup second) first := by
  induction first generalizing lookup with
  | nil => rfl
  | cons row rest ih =>
      have outside : row.1 ∉ second.map Prod.fst :=
        List.disjoint_left.mp disjoint (by simp)
      have tailDisjoint : List.Disjoint (rest.map Prod.fst) (second.map Prod.fst) := by
        apply List.disjoint_left.mpr
        intro key member
        exact List.disjoint_left.mp disjoint (by simp [member])
      change applyWrites (applyWrites (Function.update lookup row.1 (some row.2)) rest)
          second = applyWrites (Function.update (applyWrites lookup second) row.1
          (some row.2)) rest
      rw [ih _ tailDisjoint, applyWrites_update_of_not_mem lookup second
        row.1 row.2 outside]

def applyPatch (environment : Environment Key Value Metadata)
    (patch : Patch Key Value Metadata) : Environment Key Value Metadata :=
  ⟨applyWrites environment.get patch.writes, patch.metadata⟩

/-- Full patches commute when their map supports are disjoint and their
resulting metadata agrees. Different metadata cannot be silently discarded. -/
theorem applyPatch_commute_of_common_metadata
    (environment : Environment Key Value Metadata) (first second : Patch Key Value Metadata)
    (disjoint : List.Disjoint (first.writes.map Prod.fst) (second.writes.map Prod.fst))
    (sameMetadata : first.metadata = second.metadata) :
    applyPatch (applyPatch environment first) second =
      applyPatch (applyPatch environment second) first := by
  unfold applyPatch
  rw [applyWrites_commute environment.get first.writes second.writes disjoint,
    sameMetadata]

/-- Each reference insertion is checked before exposing its updated state.
The caller decides whether to publish a successfully completed whole batch. -/
def sequential (check : Checker Key Value Metadata Error Operation) :
    Environment Key Value Metadata → List Operation → Except Error (Environment Key Value Metadata)
  | environment, [] => .ok environment
  | environment, operation :: rest =>
      let attempt := check environment operation
      match attempt.verdict with
      | .error reason => .error reason
      | .ok _ => sequential check (applyPatch environment attempt.patch) rest

/-- Reserved variable identity is distinct from a present binding. -/
inductive Slot (Key : Type u) (Value : Type v) where
  | spare
  | reserved (key : Key)
  | bound (key : Key) (value : Value)
  deriving DecidableEq, Repr

def lookupSlots (key : Key) : List (Slot Key Value) → Option Value
  | [] => none
  | .spare :: rest => lookupSlots key rest
  | .reserved _ :: rest => lookupSlots key rest
  | .bound found value :: rest => if key = found then some value else lookupSlots key rest

/-- Reuse a spare or matching slot; grow the buffer when necessary. The
reference map specification does not call this implementation. -/
def putSlot (key : Key) (value : Value) : List (Slot Key Value) → List (Slot Key Value)
  | [] => [.bound key value]
  | .spare :: rest => .bound key value :: rest
  | .reserved found :: rest =>
      if key = found then .bound key value :: rest
      else .reserved found :: putSlot key value rest
  | .bound found old :: rest =>
      if key = found then .bound key value :: rest
      else .bound found old :: putSlot key value rest

/-- An actual slot write implements exactly one functional binding update. -/
theorem lookup_putSlot (key query : Key) (value : Value) (slots : List (Slot Key Value)) :
    lookupSlots query (putSlot key value slots) =
      if query = key then some value else lookupSlots query slots := by
  induction slots with
  | nil => simp [putSlot, lookupSlots]
  | cons slot slots ih =>
      cases slot with
      | spare => simp [putSlot, lookupSlots]
      | reserved found =>
          by_cases same : key = found
          · subst found; simp [putSlot, lookupSlots]
          · simp [putSlot, same, lookupSlots, ih]
      | bound found old =>
          by_cases same : key = found
          · subst found
            by_cases queryKey : query = key <;> simp [putSlot, lookupSlots, queryKey]
          · by_cases queryKey : query = key
            · subst query; simp [putSlot, same, lookupSlots, ih]
            · by_cases queryFound : query = found
              · subst query; simp [putSlot, same, lookupSlots, Ne.symm same]
              · simp [putSlot, same, lookupSlots, ih, queryKey, queryFound]

structure Builder (Key : Type u) (Value : Type v) (Metadata : Type w) where
  base : Environment Key Value Metadata
  slots : List (Slot Key Value)
  metadata : Metadata

/-- The base is immutable and may remain visible through independently held
aliases. All candidate writes belong to the separate private slot buffer. -/
def Builder.denote (builder : Builder Key Value Metadata) : Environment Key Value Metadata :=
  ⟨fun key => (lookupSlots key builder.slots).orElse (fun _ => builder.base.get key),
    builder.metadata⟩

def Builder.write (builder : Builder Key Value Metadata) (row : Key × Value) :
    Builder Key Value Metadata :=
  { builder with slots := putSlot row.1 row.2 builder.slots }

theorem Builder.write_lookup (builder : Builder Key Value Metadata) (row : Key × Value) :
    (builder.write row).denote.get =
      Function.update builder.denote.get row.1 (some row.2) := by
  funext key
  by_cases same : key = row.1
  · simp [Builder.write, Builder.denote, lookup_putSlot, same]
  · simp [Builder.write, Builder.denote, lookup_putSlot, same]

def Builder.writeMany : Builder Key Value Metadata → List (Key × Value) →
    Builder Key Value Metadata
  | builder, [] => builder
  | builder, row :: rest => writeMany (builder.write row) rest

theorem Builder.writeMany_lookup (builder : Builder Key Value Metadata)
    (rows : List (Key × Value)) :
    (builder.writeMany rows).denote.get = applyWrites builder.denote.get rows := by
  induction rows generalizing builder with
  | nil => rfl
  | cons row rows ih =>
      simp only [Builder.writeMany, applyWrites, ih, Builder.write_lookup]

theorem Builder.writeMany_base (builder : Builder Key Value Metadata)
    (rows : List (Key × Value)) : (builder.writeMany rows).base = builder.base := by
  induction rows generalizing builder with
  | nil => rfl
  | cons row rows ih => exact ih (builder.write row)

def Builder.stage (builder : Builder Key Value Metadata) (patch : Patch Key Value Metadata) :
    Builder Key Value Metadata :=
  { builder.writeMany patch.writes with metadata := patch.metadata }

theorem Builder.stage_exact (builder : Builder Key Value Metadata)
    (patch : Patch Key Value Metadata) :
    (builder.stage patch).denote = applyPatch builder.denote patch := by
  exact congrArg (fun lookup => Environment.mk lookup patch.metadata)
    (builder.writeMany_lookup patch.writes)

theorem Builder.stage_preserves_base (builder : Builder Key Value Metadata)
    (patch : Patch Key Value Metadata) : (builder.stage patch).base = builder.base :=
  builder.writeMany_base patch.writes

/-- All inventory entries are initially unbound, including duplicates. Spare
capacity is likewise storage rather than a semantic binding. -/
def prepare (base : Environment Key Value Metadata) (inventory : List Key) (spare : Nat) :
    Builder Key Value Metadata :=
  ⟨base, inventory.map Slot.reserved ++ List.replicate spare Slot.spare, base.metadata⟩

theorem lookup_inventory (key : Key) (inventory : List Key) (spare : Nat) :
    lookupSlots (Value := Value) key
      (inventory.map Slot.reserved ++ List.replicate spare Slot.spare) = none := by
  induction inventory with
  | nil =>
      induction spare with
      | zero => rfl
      | succ spare ih => simpa [List.replicate_succ, lookupSlots] using ih
  | cons item inventory ih => simpa [lookupSlots] using ih

theorem prepare_exact (base : Environment Key Value Metadata)
    (inventory : List Key) (spare : Nat) : (prepare base inventory spare).denote = base := by
  cases base with
  | mk lookup metadata =>
      simp [prepare, Builder.denote, lookup_inventory]

/-- A rejected internal result deliberately carries dirty private state.
That state may be inspected by the proof, but must not be published. -/
inductive PrivateResult (Key : Type u) (Value : Type v) (Metadata : Type w) (Error : Type x) where
  | accepted (builder : Builder Key Value Metadata)
  | rejected (reason : Error) (discard : Builder Key Value Metadata)

/-- The target stages the entire attempt before testing its final verdict.
It therefore models errors found after a private write or normalization. -/
def privatelyBuild (check : Checker Key Value Metadata Error Operation) :
    Builder Key Value Metadata → List Operation → PrivateResult Key Value Metadata Error
  | builder, [] => .accepted builder
  | builder, operation :: rest =>
      let attempt := check builder.denote operation
      let changed := builder.stage attempt.patch
      match attempt.verdict with
      | .error reason => .rejected reason changed
      | .ok _ => privatelyBuild check changed rest

def PrivateResult.observe : PrivateResult Key Value Metadata Error →
    Except Error (Environment Key Value Metadata)
  | .accepted builder => .ok builder.denote
  | .rejected reason _ => .error reason

/-- Independently implemented private storage and logical checked execution
agree on both successful environments and every reported failure. -/
theorem privatelyBuild_correct (check : Checker Key Value Metadata Error Operation)
    (operations : List Operation) (builder : Builder Key Value Metadata) :
    (privatelyBuild check builder operations).observe =
      sequential check builder.denote operations := by
  induction operations generalizing builder with
  | nil => rfl
  | cons operation operations ih =>
      simp only [privatelyBuild, sequential]
      split
      · rfl
      · rw [ih, Builder.stage_exact]

def bulk (check : Checker Key Value Metadata Error Operation)
    (base : Environment Key Value Metadata) (inventory : List Key) (spare : Nat)
    (operations : List Operation) : Except Error (Environment Key Value Metadata) :=
  (privatelyBuild check (prepare base inventory spare) operations).observe

theorem bulk_matches_sequential (check : Checker Key Value Metadata Error Operation)
    (base : Environment Key Value Metadata) (inventory : List Key) (spare : Nat)
    (operations : List Operation) :
    bulk check base inventory spare operations = sequential check base operations := by
  rw [bulk, privatelyBuild_correct, prepare_exact]

/-- Inventory order, extra reservations and initial spare capacity have no
semantic effect. The order of the checked binding operations is unchanged. -/
theorem inventory_capacity_irrelevant (check : Checker Key Value Metadata Error Operation)
    (base : Environment Key Value Metadata) (first second : List Key)
    (spareFirst spareSecond : Nat) (operations : List Operation) :
    bulk check base first spareFirst operations =
      bulk check base second spareSecond operations := by
  rw [bulk_matches_sequential, bulk_matches_sequential]

structure Publication (Key : Type u) (Value : Type v) (Metadata : Type w) (Error : Type x) where
  environment : Environment Key Value Metadata
  status : Except Error Unit

def publish (base : Environment Key Value Metadata) :
    PrivateResult Key Value Metadata Error → Publication Key Value Metadata Error
  | .accepted builder => ⟨builder.denote, .ok ()⟩
  | .rejected reason _ => ⟨base, .error reason⟩

def sequentialPublication (check : Checker Key Value Metadata Error Operation)
    (base : Environment Key Value Metadata) (operations : List Operation) :
    Publication Key Value Metadata Error :=
  match sequential check base operations with
  | .ok environment => ⟨environment, .ok ()⟩
  | .error reason => ⟨base, .error reason⟩

theorem publication_matches_sequential (check : Checker Key Value Metadata Error Operation)
    (base : Environment Key Value Metadata) (inventory : List Key) (spare : Nat)
    (operations : List Operation) :
    publish base (privatelyBuild check (prepare base inventory spare) operations) =
      sequentialPublication check base operations := by
  have exactResult := bulk_matches_sequential check base inventory spare operations
  unfold bulk at exactResult
  unfold sequentialPublication
  rw [← exactResult]
  cases privatelyBuild check (prepare base inventory spare) operations <;> rfl

theorem failed_publication_preserves_input
    (base : Environment Key Value Metadata) (reason : Error)
    (dirty : Builder Key Value Metadata) :
    (publish base (.rejected reason dirty)).environment = base ∧
      (publish base (.rejected reason dirty)).status = .error reason := by
  exact ⟨rfl, rfl⟩

/-- The complete executable batch inherits failure atomicity from the checked
reference, even when a target failure occurs after private mutation. -/
theorem checked_failure_preserves_input
    (check : Checker Key Value Metadata Error Operation)
    (base : Environment Key Value Metadata) (inventory : List Key) (spare : Nat)
    (operations : List Operation) (reason : Error)
    (failure : sequential check base operations = .error reason) :
    let result := publish base
      (privatelyBuild check (prepare base inventory spare) operations)
    result.environment = base ∧ result.status = .error reason := by
  dsimp only
  rw [publication_matches_sequential]
  simp [sequentialPublication, failure]

def PrivateResult.original : PrivateResult Key Value Metadata Error →
    Environment Key Value Metadata
  | .accepted builder => builder.base
  | .rejected _ builder => builder.base

/-- Every path leaves the original environment available unchanged, including
paths rejected after several tentative writes. -/
theorem privatelyBuild_preserves_original
    (check : Checker Key Value Metadata Error Operation)
    (operations : List Operation) (builder : Builder Key Value Metadata) :
    (privatelyBuild check builder operations).original = builder.base := by
  induction operations generalizing builder with
  | nil => rfl
  | cons operation operations ih =>
      simp only [privatelyBuild]
      split
      · exact builder.stage_preserves_base _
      · rw [ih, Builder.stage_preserves_base]

/-! ## Consuming an unpublished binding image

An exclusive caller can discard the entire candidate after a failed insertion.
It need not keep the previous candidate as a rollback snapshot. The result below
retains no builder on failure. The immutable base still represents an independently
held sibling; owning the candidate does not establish ownership of Atom payloads.

The trace records checked operations, including the first failed operation. This
lets the correspondence state that consuming storage neither replays a check nor
evaluates the abandoned suffix. The slot bound concerns this finite representation,
not allocator capacity, shared syntax, or total process memory.
-/

structure OwnedExecution (Key : Type u) (Value : Type v) (Metadata : Type w)
    (Error : Type x) (Operation : Type y) where
  result : Except Error (Builder Key Value Metadata)
  checked : List Operation

def executeOwned (check : Checker Key Value Metadata Error Operation) :
    Builder Key Value Metadata → List Operation →
      OwnedExecution Key Value Metadata Error Operation
  | builder, [] => ⟨.ok builder, []⟩
  | builder, operation :: rest =>
      let attempt := check builder.denote operation
      let changed := builder.stage attempt.patch
      match attempt.verdict with
      | .error reason => ⟨.error reason, [operation]⟩
      | .ok _ =>
          let tail := executeOwned check changed rest
          ⟨tail.result, operation :: tail.checked⟩

/-- Independent logical execution records the attempted prefix, not the whole
requested batch. In particular the first rejection prevents later checks. -/
def checkedPrefix (check : Checker Key Value Metadata Error Operation) :
    Environment Key Value Metadata → List Operation → List Operation
  | _, [] => []
  | environment, operation :: rest =>
      let attempt := check environment operation
      operation :: match attempt.verdict with
      | .error _ => []
      | .ok _ => checkedPrefix check (applyPatch environment attempt.patch) rest

theorem executeOwned_matches_sequential
    (check : Checker Key Value Metadata Error Operation)
    (operations : List Operation) (builder : Builder Key Value Metadata) :
    (executeOwned check builder operations).result.map Builder.denote =
      sequential check builder.denote operations := by
  induction operations generalizing builder with
  | nil => rfl
  | cons operation operations ih =>
      simp only [executeOwned, sequential]
      split
      · rfl
      · rw [ih, Builder.stage_exact]

theorem executeOwned_preserves_checked_prefix
    (check : Checker Key Value Metadata Error Operation)
    (operations : List Operation) (builder : Builder Key Value Metadata) :
    (executeOwned check builder operations).checked =
      checkedPrefix check builder.denote operations := by
  induction operations generalizing builder with
  | nil => rfl
  | cons operation operations ih =>
      simp only [executeOwned, checkedPrefix]
      split
      · rfl
      · rw [ih, Builder.stage_exact]

theorem executeOwned_preserves_sibling
    (check : Checker Key Value Metadata Error Operation)
    (operations : List Operation) (builder result : Builder Key Value Metadata)
    (accepted : (executeOwned check builder operations).result = .ok result) :
    result.base = builder.base := by
  induction operations generalizing builder with
  | nil => cases accepted; rfl
  | cons operation operations ih =>
      simp only [executeOwned] at accepted
      split at accepted
      · cases accepted
      · rw [ih _ accepted, Builder.stage_preserves_base]

def OwnedExecution.retainedSlots
    (execution : OwnedExecution Key Value Metadata Error Operation) : Nat :=
  match execution.result with
  | .ok builder => builder.slots.length
  | .error _ => 0

theorem executeOwned_failure_releases_image
    (check : Checker Key Value Metadata Error Operation)
    (operations : List Operation) (builder : Builder Key Value Metadata) (reason : Error)
    (failure : sequential check builder.denote operations = .error reason) :
    (executeOwned check builder operations).result = .error reason ∧
      (executeOwned check builder operations).retainedSlots = 0 := by
  have observes := executeOwned_matches_sequential check operations builder
  rw [failure] at observes
  cases result : (executeOwned check builder operations).result with
  | error actual =>
      rw [result] at observes
      change Except.error actual = Except.error reason at observes
      cases observes
      exact ⟨rfl, by simp [OwnedExecution.retainedSlots, result]⟩
  | ok final =>
      rw [result] at observes
      change Except.ok final.denote = Except.error reason at observes
      cases observes

theorem putSlot_length_le (key : Key) (value : Value) (slots : List (Slot Key Value)) :
    (putSlot key value slots).length ≤ slots.length + 1 := by
  induction slots with
  | nil => simp [putSlot]
  | cons slot slots ih =>
      cases slot with
      | spare => simp [putSlot]
      | reserved found =>
          by_cases same : key = found
          · simp [putSlot, same]
          · simpa [putSlot, same] using ih
      | bound found old =>
          by_cases same : key = found
          · simp [putSlot, same]
          · simpa [putSlot, same] using ih

theorem Builder.writeMany_slots_bound (builder : Builder Key Value Metadata)
    (writes : List (Key × Value)) :
    (builder.writeMany writes).slots.length ≤ builder.slots.length + writes.length := by
  induction writes generalizing builder with
  | nil => simp [Builder.writeMany]
  | cons row rest ih =>
      have next := ih (builder.write row)
      have grows := putSlot_length_le row.1 row.2 builder.slots
      simp only [Builder.writeMany, Builder.write, List.length_cons] at *
      omega

/-- Count actual writes of attempts reached before the first failure. This
includes a failing attempt's tentative writes, but excludes the unvisited tail. -/
def checkedWrites (check : Checker Key Value Metadata Error Operation) :
    Environment Key Value Metadata → List Operation → Nat
  | _, [] => 0
  | environment, operation :: rest =>
      let attempt := check environment operation
      attempt.patch.writes.length + match attempt.verdict with
      | .error _ => 0
      | .ok _ => checkedWrites check (applyPatch environment attempt.patch) rest

/-- No rollback snapshots accumulate in the consumed image: its retained slots
are bounded by initial slots plus actual attempted writes, even after failures. -/
theorem executeOwned_retained_slots_bound
    (check : Checker Key Value Metadata Error Operation)
    (operations : List Operation) (builder : Builder Key Value Metadata) :
    (executeOwned check builder operations).retainedSlots ≤
      builder.slots.length + checkedWrites check builder.denote operations := by
  induction operations generalizing builder with
  | nil => simp [executeOwned, OwnedExecution.retainedSlots, checkedWrites]
  | cons operation operations ih =>
      simp only [executeOwned, checkedWrites]
      split
      · simp [OwnedExecution.retainedSlots]
      · have tail := ih (builder.stage (check builder.denote operation).patch)
        have grows := builder.writeMany_slots_bound
          (check builder.denote operation).patch.writes
        rw [Builder.stage_exact] at tail
        change (executeOwned check (builder.stage (check builder.denote operation).patch)
          operations).retainedSlots ≤ _
        change (builder.stage (check builder.denote operation).patch).slots.length ≤ _ at grows
        have sum := Nat.add_le_add_right grows
          (checkedWrites check (applyPatch builder.denote
            (check builder.denote operation).patch) operations)
        rw [Nat.add_assoc] at sum
        exact Nat.le_trans tail sum

end General

/-! ## Executable checked-binding controls

The following checker is an acyclic finite-term insertion fragment. It admits
aliases, rejects a cyclic insertion, and checks name-key compatibility and
retained disequalities. Existing bindings can be repeated with the same resolved
value; general structural unification is deliberately outside this fragment.
The fuel parameter reports exhaustion explicitly rather than treating an
unexplored variable as absent. These controls instantiate the storage theorem;
they do not verify the native unifier or its resource bounds.
-/

namespace Examples

/-- Independent child deltas retain their final local writes. Repeated writes
within one child do not require deduplication or reordering. -/
theorem independent_patch_orders_agree :
    let base : Environment Nat Nat Nat := ⟨fun _ => none, 23⟩
    let first : Patch Nat Nat Nat := ⟨[(0, 7), (0, 8)], 23⟩
    let second : Patch Nat Nat Nat := ⟨[(1, 9)], 23⟩
    applyPatch (applyPatch base first) second = applyPatch (applyPatch base second) first ∧
      (applyPatch (applyPatch base first) second).get 0 = some 8 ∧
      (applyPatch (applyPatch base first) second).get 1 = some 9 := by
  refine ⟨applyPatch_commute_of_common_metadata _ _ _ (by simp) rfl, ?_, ?_⟩ <;> rfl

/-- Even disjoint map writes cannot authorize a full-world join when each
child carries different resulting authority metadata. -/
theorem disjoint_writes_do_not_join_different_metadata :
    let base : Environment Nat Nat Nat := ⟨fun _ => none, 0⟩
    let first : Patch Nat Nat Nat := ⟨[(0, 7)], 7⟩
    let second : Patch Nat Nat Nat := ⟨[(1, 9)], 9⟩
    List.Disjoint (first.writes.map Prod.fst) (second.writes.map Prod.fst) ∧
      (applyPatch (applyPatch base first) second).get =
        (applyPatch (applyPatch base second) first).get ∧
      applyPatch (applyPatch base first) second ≠ applyPatch (applyPatch base second) first := by
  refine ⟨by simp, applyWrites_commute _ _ _ (by simp), ?_⟩
  intro same
  have metadata := congrArg Environment.metadata same
  exact (by decide : (9 : Nat) ≠ 7) metadata

inductive Term where
  | atom (name : Nat)
  | var (key : Nat)
  | pair (left right : Term)
  deriving DecidableEq, Repr

structure Cell where
  nameKey : Option Nat
  value : Term
  deriving DecidableEq, Repr

structure Metadata where
  disequalities : List (Nat × Nat)
  checks : Nat
  occurrenceTag : Nat
  deriving DecidableEq, Repr

inductive Error where
  | fuelExhausted
  | nameConflict
  | valueConflict
  | occursCheck
  | constraintViolation
  deriving DecidableEq, Repr

structure Bind where
  key : Nat
  nameKey : Option Nat
  value : Term
  deriving DecidableEq, Repr

abbrev Env := Environment Nat Cell Metadata

/-- Follow a variable's aliases. Constructors remain terms rather than being
evaluated. A bound that is too small is an error, never an absence result. -/
def resolve : Nat → Env → Term → Except Error Term
  | _, _, .atom name => .ok (.atom name)
  | _, _, .pair left right => .ok (.pair left right)
  | fuel, environment, .var key =>
      match environment.get key with
      | none => .ok (.var key)
      | some cell =>
          match fuel with
          | 0 => .error .fuelExhausted
          | remaining + 1 => resolve remaining environment cell.value

/-- Traverse both term structure and existing aliases when deciding whether
the new edge would close a cycle. -/
def occurs : Nat → Env → Nat → Term → Except Error Bool
  | 0, _, _, _ => .error .fuelExhausted
  | _ + 1, _, _, .atom _ => .ok false
  | remaining + 1, environment, key, .var found =>
      if found = key then .ok true
      else
        match environment.get found with
        | none => .ok false
        | some cell => occurs remaining environment key cell.value
  | remaining + 1, environment, key, .pair left right => do
      let inLeft ← occurs remaining environment key left
      if inLeft then return true
      occurs remaining environment key right

/-- Compute an insertion patch, independently of any slot layout. -/
def insertion (fuel : Nat) (environment : Env) (operation : Bind) :
    Except Error (List (Nat × Cell)) := do
  if operation.value = .var operation.key then return []
  let value ← resolve fuel environment operation.value
  if value = .var operation.key then return []
  match environment.get operation.key with
  | some previous =>
      if previous.nameKey ≠ operation.nameKey then throw .nameConflict
      let old ← resolve fuel environment previous.value
      if old = value then return [] else throw .valueConflict
  | none =>
      if ← occurs fuel environment operation.key value then throw .occursCheck
      return [(operation.key, ⟨operation.nameKey, operation.value⟩)]

def checkDisequalities (fuel : Nat) (environment : Env) :
    List (Nat × Nat) → Except Error Unit
  | [] => .ok ()
  | (left, right) :: rest => do
      let first ← resolve fuel environment (.var left)
      let second ← resolve fuel environment (.var right)
      if first = second then throw .constraintViolation
      checkDisequalities fuel environment rest

/-- On insertion failure the dirty tentative row demonstrates why the
private candidate must be discarded. On success constraints are checked
against the updated logical environment at this operation, not just at end. -/
def checkedInsert (fuel : Nat) : Checker Nat Cell Metadata Error Bind :=
  fun environment operation =>
    let metadata := { environment.metadata with checks := environment.metadata.checks + 1 }
    match insertion fuel environment operation with
    | .error reason =>
        ⟨⟨[(operation.key, ⟨operation.nameKey, operation.value⟩)], metadata⟩, .error reason⟩
    | .ok writes =>
        let patch := Patch.mk writes metadata
        let next := applyPatch environment patch
        ⟨patch, checkDisequalities fuel next metadata.disequalities⟩

def empty : Env := ⟨fun _ => none, ⟨[], 0, 17⟩⟩

def aliasOperations : List Bind :=
  [⟨0, some 10, .var 1⟩, ⟨1, some 11, .atom 7⟩]

def aliasPublication : Publication Nat Cell Metadata Error :=
  publish empty (privatelyBuild (checkedInsert 8) (prepare empty [1, 0, 1] 2) aliasOperations)

/-- An alias inserted before its target resolves after the target is bound;
publication retains metadata and runs both checked operations. -/
theorem aliases_resolve_after_publication :
    aliasPublication.status = .ok () ∧
    resolve 8 aliasPublication.environment (.var 0) = .ok (.atom 7) ∧
    aliasPublication.environment.metadata = ⟨[], 2, 17⟩ := by decide

def reverseAliasOperations : List Bind :=
  [⟨0, some 10, .var 1⟩, ⟨1, some 11, .var 0⟩]

/-- The reverse alias is a successful no-op, not a new cyclic edge. -/
theorem reverse_alias_does_not_introduce_cycle :
    let result := publish empty
      (privatelyBuild (checkedInsert 8) (prepare empty [] 0) reverseAliasOperations)
    result.status = .ok () ∧
    result.environment.get 0 = some ⟨some 10, .var 1⟩ ∧
    result.environment.get 1 = none ∧
    resolve 8 result.environment (.var 0) = .ok (.var 1) := by decide

def cycleOperations : List Bind :=
  [⟨0, none, .pair (.var 1) (.atom 0)⟩, ⟨1, none, .var 0⟩]

/-- Inspect only a rejected private candidate, for a negative control.
Actual publication does not expose this environment. -/
def rejectedCandidate : PrivateResult Nat Cell Metadata Error → Option Env
  | .accepted _ => none
  | .rejected _ candidate => some candidate.denote

theorem cycle_is_rejected_after_tentative_writes :
    let candidate := privatelyBuild (checkedInsert 8) (prepare empty [0, 1] 0) cycleOperations
    (publish empty candidate).status = .error .occursCheck ∧
    ((rejectedCandidate candidate).bind (fun environment => environment.get 1)) =
      some ⟨none, .var 0⟩ ∧
    (publish empty candidate).environment.get 0 = none ∧
    (publish empty candidate).environment.get 1 = none ∧
    (publish empty candidate).environment.metadata = empty.metadata := by decide

theorem repeated_binding_cannot_change_name_key :
    let operations : List Bind := [⟨0, some 10, .atom 7⟩, ⟨0, some 11, .atom 7⟩]
    let result := publish empty
      (privatelyBuild (checkedInsert 8) (prepare empty [0] 1) operations)
    result.status = .error .nameConflict ∧ result.environment.get 0 = none := by decide

/-- Variable identity is not the presentation key: distinct variables may
carry equal name keys and still keep different values. -/
theorem equal_name_keys_do_not_merge_variable_identities :
    let operations : List Bind := [⟨0, some 10, .atom 7⟩, ⟨1, some 10, .atom 8⟩]
    let result := publish empty
      (privatelyBuild (checkedInsert 8) (prepare empty [1, 0] 0) operations)
    result.status = .ok () ∧
    result.environment.get 0 = some ⟨some 10, .atom 7⟩ ∧
    result.environment.get 1 = some ⟨some 10, .atom 8⟩ := by decide

theorem incompatible_rebinding_discards_earlier_insertions :
    let operations : List Bind := [⟨0, none, .atom 7⟩, ⟨0, none, .atom 8⟩]
    let result := publish empty
      (privatelyBuild (checkedInsert 8) (prepare empty [] 0) operations)
    result.status = .error .valueConflict ∧ result.environment.get 0 = none := by decide

/-- Reservation order can change freely; checked operation order cannot.
Changing it changes which of two concrete failures is reported first. -/
theorem operation_order_can_change_the_reported_failure :
    let conflict : List Bind := [⟨0, none, .atom 7⟩, ⟨0, none, .atom 8⟩]
    let cyclic : Bind := ⟨1, none, .pair (.var 1) (.atom 0)⟩
    (publish empty (privatelyBuild (checkedInsert 8) (prepare empty [] 0)
      (conflict ++ [cyclic]))).status = .error .valueConflict ∧
    (publish empty (privatelyBuild (checkedInsert 8) (prepare empty [] 0)
      (cyclic :: conflict))).status = .error .occursCheck := by decide

def constrained : Env := ⟨fun _ => none, ⟨[(0, 1)], 0, 23⟩⟩

/-- Per-operation constraint checking rejects a later equality and restores
the earlier constraint store as well as the binding map. -/
theorem constraint_failure_discards_whole_batch :
    let operations : List Bind := [⟨0, none, .atom 7⟩, ⟨1, none, .atom 7⟩]
    let result := publish constrained
      (privatelyBuild (checkedInsert 8) (prepare constrained [0, 1] 0) operations)
    result.status = .error .constraintViolation ∧
    result.environment.get 0 = none ∧
    result.environment.get 1 = none ∧
    result.environment.metadata = ⟨[(0, 1)], 0, 23⟩ := by decide

theorem fuel_exhaustion_is_reported_not_absence :
    let result := publish empty
      (privatelyBuild (checkedInsert 0) (prepare empty [] 3) aliasOperations)
    result.status = .error .fuelExhausted ∧ result.environment.get 0 = none := by decide

/-- Inventory identity is not a binding and does not make an alias resolve. -/
theorem reserved_variable_is_still_unbound :
    resolve 8 (prepare empty [0, 1, 2] 100).denote (.var 1) = .ok (.var 1) := by decide

theorem spare_capacity_and_inventory_order_preserve_aliases :
    bulk (checkedInsert 8) empty [0, 1] 0 aliasOperations =
      bulk (checkedInsert 8) empty [1, 0, 1, 99] 7 aliasOperations :=
  inventory_capacity_irrelevant _ _ _ _ _ _ _

/-- Aliases survive the consumed-image route with their occurrence metadata;
each checked operation occurs once and two writes occupy two slots. -/
theorem consumed_aliases_preserve_value_and_checks :
    let run := executeOwned (checkedInsert 8) (prepare empty [] 0) aliasOperations
    run.result.map (fun builder =>
      (resolve 8 builder.denote (.var 0), builder.metadata)) =
        .ok (.ok (.atom 7), ⟨[], 2, 17⟩) ∧
      run.checked = aliasOperations ∧ run.retainedSlots = 2 := by
  exact ⟨rfl, rfl, rfl⟩

/-- A rejected privately mutated row cannot escape, and an invalid suffix is
not checked. Keeping the dirty buffer would expose the conflicting value 8. -/
theorem consumed_failure_discards_storage_and_suffix :
    let first : Bind := ⟨0, none, .atom 7⟩
    let conflict : Bind := ⟨0, none, .atom 8⟩
    let cyclic : Bind := ⟨1, none, .pair (.var 1) (.atom 0)⟩
    let run := executeOwned (checkedInsert 8) (prepare empty [] 0)
      [first, conflict, cyclic]
    run.result = .error .valueConflict ∧
      run.checked = [first, conflict] ∧ run.retainedSlots = 0 := by
  exact ⟨rfl, rfl, rfl⟩

end Examples

end Mettapedia.Machines.BindingPublication
