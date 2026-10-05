import Mathlib.Data.List.Basic
import Mathlib.Data.List.Forall2

/-!
# Copying the suffixes of one immutable storage once

A list value may be a view of a longer list's storage: the storage's last
`len` elements.  Views of one storage share its end.  A collector that meets
several views of one storage need not trace or copy each: every element a view
reaches lies in the longest view (`mem_view_of_le`), and the copy of each view
is the corresponding suffix of the longest view's copy (`view_copy`).  Tracing
the longest view once and copying it once therefore serves them all.

A view is a suffix: two views of one storage of different lengths differ
(`view_length`), and the copy of a view is not a copy of the whole storage
unless the view is the whole storage (`Controls.view_not_whole`).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.SuffixViewCopy

variable {α β : Type*}

/-- The view of `storage` holding its last `len` elements. -/
def view (storage : List α) (len : ℕ) : List α :=
  storage.drop (storage.length - len)

theorem view_length (storage : List α) (len : ℕ) :
    (view storage len).length = min len storage.length := by
  unfold view
  rw [List.length_drop]
  omega

/-- A shorter view is a suffix of a longer one. -/
theorem view_view {storage : List α} {len long : ℕ} (le : len ≤ long) :
    view (view storage long) len = view storage len := by
  unfold view
  rw [List.length_drop, List.drop_drop]
  congr 1
  omega

/-- Every element a view reaches lies in any longer view. -/
theorem mem_view_of_le {storage : List α} {len long : ℕ} (le : len ≤ long) {x : α}
    (mem : x ∈ view storage len) : x ∈ view storage long := by
  rw [← view_view le] at mem
  unfold view at mem
  exact List.mem_of_mem_drop mem

/-- Copying commutes with taking a view. -/
theorem view_map (f : α → β) (storage : List α) (len : ℕ) :
    view (storage.map f) len = (view storage len).map f := by
  unfold view
  rw [List.length_map, List.map_drop]

/-- A view's copy is the matching suffix of the longest view's copy. -/
theorem view_copy (f : α → β) {storage : List α} {len long : ℕ} (le : len ≤ long) :
    view ((view storage long).map f) len = (view storage len).map f := by
  rw [view_map, view_view le]

namespace EndKeys

variable {Header SourceEnd TargetEnd OtherEnd Payload Copied : Type*}

/-- Observations of the source and copied buffer end of every known header.
Different headers may contribute the same pair. -/
def observations (headers : List Header) (source : Header → SourceEnd)
    (copied : Header → TargetEnd) : List (SourceEnd × TargetEnd) :=
  headers.map fun header => (source header, copied header)

/-- A finite check of both shared-end preservation and distinct-end reflection.
Header-address injectivity alone does not establish either condition. -/
def check [DecidableEq SourceEnd] [DecidableEq TargetEnd]
    (rows : List (SourceEnd × TargetEnd)) : Bool :=
  rows.all fun one => rows.all fun two =>
    decide (one.1 = two.1 ↔ one.2 = two.2)

/-- Every observed source end has one image; different observed ends have
different images. This property does not quantify over unobserved headers. -/
def Coherent (rows : List (SourceEnd × TargetEnd)) : Prop :=
  ∀ one ∈ rows, ∀ two ∈ rows, one.1 = two.1 ↔ one.2 = two.2

theorem check_iff [DecidableEq SourceEnd] [DecidableEq TargetEnd]
    (rows : List (SourceEnd × TargetEnd)) : check rows = true ↔ Coherent rows := by
  simp only [check, List.all_eq_true, decide_eq_true_eq, Coherent]

theorem observations_check_iff [DecidableEq SourceEnd] [DecidableEq TargetEnd]
    (headers : List Header) (source : Header → SourceEnd) (copied : Header → TargetEnd) :
    check (observations headers source copied) = true ↔
      ∀ one ∈ headers, ∀ two ∈ headers, source one = source two ↔ copied one = copied two := by
  simp only [check_iff, Coherent, observations, List.forall_mem_map]

/-- The first-match lookup denotes every observed end, even when several
different headers reported the same end. -/
theorem lookup_of_mem [DecidableEq SourceEnd]
    {rows : List (SourceEnd × TargetEnd)} (coherent : Coherent rows)
    {key : SourceEnd} {value : TargetEnd} (member : (key, value) ∈ rows) :
    rows.lookup key = some value := by
  induction rows with
  | nil => simp only [List.not_mem_nil] at member
  | cons first rest ih =>
    rcases first with ⟨firstKey, firstValue⟩
    by_cases same : key = firstKey
    · have equal := (coherent (key, value) member (firstKey, firstValue) (by simp)).mp same
      simp only [List.lookup_cons, same, beq_self_eq_true]
      exact congrArg some equal.symm
    · have tail : (key, value) ∈ rest := by
        rcases List.mem_cons.mp member with head | tail
        · exact (same (congrArg Prod.fst head)).elim
        · exact tail
      have coherentTail : Coherent rest :=
        fun one oneIn two twoIn => coherent one (List.mem_cons_of_mem _ oneIn)
          two (List.mem_cons_of_mem _ twoIn)
      simpa only [List.lookup_cons, beq_eq_false_iff_ne.mpr same] using
        ih coherentTail tail

theorem lookup_sound [DecidableEq SourceEnd]
    {rows : List (SourceEnd × TargetEnd)} {key : SourceEnd} {value : TargetEnd}
    (found : rows.lookup key = some value) : (key, value) ∈ rows := by
  obtain ⟨before, after, rfl, _⟩ := List.lookup_eq_some_iff.mp found
  exact List.mem_append_right _ (List.mem_cons_self)

/-- Successful lookups reflect exactly the same observed end classes. -/
theorem lookup_end_classes [DecidableEq SourceEnd]
    {rows : List (SourceEnd × TargetEnd)} (coherent : Coherent rows)
    {one two : SourceEnd} {first second : TargetEnd}
    (left : rows.lookup one = some first) (right : rows.lookup two = some second) :
    one = two ↔ first = second :=
  coherent (one, first) (lookup_sound left) (two, second) (lookup_sound right)

/-- Renaming both end domains preserves the finite check when both renamings
are injective. No header or payload is identified by this operation. -/
theorem check_map [DecidableEq SourceEnd] [DecidableEq TargetEnd]
    [DecidableEq OtherEnd] {CopiedEnd : Type*} [DecidableEq CopiedEnd]
    (source : SourceEnd → OtherEnd) (target : TargetEnd → CopiedEnd)
    (sourceInjective : Function.Injective source) (targetInjective : Function.Injective target)
    (rows : List (SourceEnd × TargetEnd)) :
    check (rows.map fun row => (source row.1, target row.2)) = check rows := by
  apply Bool.eq_iff_iff.mpr
  simp only [check_iff, Coherent, List.forall_mem_map,
    sourceInjective.eq_iff, targetInjective.eq_iff]

/-- End-key lookup commutes with an injective key renaming and any value map.
The coherence check is separately needed to interpret all observations. -/
theorem lookup_map [DecidableEq SourceEnd] [DecidableEq OtherEnd]
    (source : SourceEnd → OtherEnd) (target : TargetEnd → Copied)
    (injective : Function.Injective source) (key : SourceEnd)
    (rows : List (SourceEnd × TargetEnd)) :
    (rows.map fun row => (source row.1, target row.2)).lookup (source key) =
      (rows.lookup key).map target := by
  induction rows with
  | nil => rfl
  | cons first rest ih =>
    rcases first with ⟨firstKey, firstValue⟩
    simp only [List.map_cons, List.lookup_cons]
    by_cases same : key = firstKey
    · simp only [same, beq_self_eq_true, Option.map_some]
    · simp only [beq_eq_false_iff_ne.mpr same,
        beq_eq_false_iff_ne.mpr (fun equal => same (injective equal)), ih]

/-- Prepare a complete end-key table without publishing any prefix on refusal.
The payload map is the independently supplied graph relocation. -/
def prepare [DecidableEq SourceEnd] (ends : List (SourceEnd × TargetEnd))
    (payload : Payload → Copied) : List (SourceEnd × Payload) →
      Option (List (TargetEnd × Copied))
  | [] => some []
  | (key, value) :: rest =>
    match ends.lookup key, prepare ends payload rest with
    | some copied, some tail => some ((copied, payload value) :: tail)
    | _, _ => none

/-- Every old entry occurs once in the same position, with its checked end
image and relocated payload. Equal payloads do not collapse entries. -/
def TableImage (ends : List (SourceEnd × TargetEnd)) (payload : Payload → Copied)
    (before : List (SourceEnd × Payload)) (after : List (TargetEnd × Copied)) : Prop :=
  List.Forall₂ (fun one two => (one.1, two.1) ∈ ends ∧ two.2 = payload one.2) before after

/-- The executable preparation cannot omit, reorder or invent a table entry. -/
theorem prepare_sound [DecidableEq SourceEnd]
    (ends : List (SourceEnd × TargetEnd)) (payload : Payload → Copied)
    (before : List (SourceEnd × Payload)) {after : List (TargetEnd × Copied)}
    (success : prepare ends payload before = some after) :
    TableImage ends payload before after := by
  induction before generalizing after with
  | nil =>
    simp only [prepare, Option.some.injEq] at success
    subst after
    exact .nil
  | cons first rest ih =>
    rcases first with ⟨key, value⟩
    cases found : ends.lookup key with
    | none =>
      simp only [prepare, found] at success
      cases success
    | some copied =>
      cases remaining : prepare ends payload rest with
      | none =>
        simp only [prepare, found, remaining] at success
        cases success
      | some tail =>
        simp only [prepare, found, remaining, Option.some.injEq] at success
        subst after
        exact .cons ⟨lookup_sound found, rfl⟩ (ih remaining)

/-- A coherent set of observed ends realizes every full positional table image. -/
theorem prepare_complete [DecidableEq SourceEnd]
    {ends : List (SourceEnd × TargetEnd)} (coherent : Coherent ends)
    (payload : Payload → Copied)
    {before : List (SourceEnd × Payload)} {after : List (TargetEnd × Copied)}
    (image : TableImage ends payload before after) :
    prepare ends payload before = some after := by
  induction before generalizing after with
  | nil =>
    cases image
    rfl
  | cons first rest ih =>
    rcases first with ⟨key, value⟩
    cases after with
    | nil => cases image
    | cons copied after =>
      rcases copied with ⟨destination, result⟩
      cases image with
      | cons head tail =>
        have found := lookup_of_mem coherent head.1
        simp only [prepare, found, ih tail]
        rw [← head.2]

theorem prepare_iff [DecidableEq SourceEnd]
    {ends : List (SourceEnd × TargetEnd)} (coherent : Coherent ends)
    (payload : Payload → Copied)
    (before : List (SourceEnd × Payload)) (after : List (TargetEnd × Copied)) :
    prepare ends payload before = some after ↔ TableImage ends payload before after :=
  ⟨prepare_sound ends payload before, prepare_complete coherent payload⟩

theorem prepare_length [DecidableEq SourceEnd]
    (ends : List (SourceEnd × TargetEnd)) (payload : Payload → Copied)
    (before : List (SourceEnd × Payload)) {after : List (TargetEnd × Copied)}
    (success : prepare ends payload before = some after) : after.length = before.length :=
  (prepare_sound ends payload before success).length_eq.symm

/-- The complete payload sequence remains in its original order. -/
theorem prepare_payloads [DecidableEq SourceEnd]
    (ends : List (SourceEnd × TargetEnd)) (payload : Payload → Copied)
    (before : List (SourceEnd × Payload)) {after : List (TargetEnd × Copied)}
    (success : prepare ends payload before = some after) :
    after.map Prod.snd = before.map (fun row => payload row.2) := by
  have image := prepare_sound ends payload before success
  clear success
  induction image with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.map_cons]
    rw [head.2, ih]

/-- Complete preparation commutes with renaming the source keys and mapping
the copied ends and payloads. Failure is transported as failure, rather than
as an incomplete table. Coherence of end classes is checked separately. -/
theorem prepare_map [DecidableEq SourceEnd] [DecidableEq OtherEnd]
    {CopiedEnd OtherPayload : Type*}
    (source : SourceEnd → OtherEnd) (target : TargetEnd → CopiedEnd)
    (copied : Copied → OtherPayload) (injective : Function.Injective source)
    (ends : List (SourceEnd × TargetEnd)) (payload : Payload → Copied)
    (before : List (SourceEnd × Payload)) :
    prepare (ends.map fun row => (source row.1, target row.2)) (copied ∘ payload)
        (before.map fun row => (source row.1, row.2)) =
      (prepare ends payload before).map
        (List.map fun row => (target row.1, copied row.2)) := by
  induction before with
  | nil => rfl
  | cons first rest ih =>
    rcases first with ⟨key, value⟩
    simp only [List.map_cons, prepare, lookup_map source target injective key ends, ih]
    cases ends.lookup key <;> cases prepare ends payload rest <;> rfl

/-- Class coherence is checked before a complete table image is returned.
Refusal exposes no prepared prefix. Physical allocation rollback is separate. -/
def checkedPrepare [DecidableEq SourceEnd] [DecidableEq TargetEnd]
    (ends : List (SourceEnd × TargetEnd)) (payload : Payload → Copied)
    (before : List (SourceEnd × Payload)) : Option (List (TargetEnd × Copied)) :=
  if check ends then prepare ends payload before else none

theorem checkedPrepare_iff [DecidableEq SourceEnd] [DecidableEq TargetEnd]
    (ends : List (SourceEnd × TargetEnd)) (payload : Payload → Copied)
    (before : List (SourceEnd × Payload)) (after : List (TargetEnd × Copied)) :
    checkedPrepare ends payload before = some after ↔
      Coherent ends ∧ TableImage ends payload before after := by
  by_cases good : check ends = true
  · simp only [checkedPrepare, good, if_true,
      prepare_iff ((check_iff ends).mp good) payload, (check_iff ends).mp good, true_and]
  · have bad : ¬Coherent ends := fun coherent => good ((check_iff ends).mpr coherent)
    simp [checkedPrepare, good, bad]

end EndKeys

namespace Controls

/-- The views of `[a, b, c]` of lengths one and two. -/
theorem views_of_three : view [1, 2, 3] 1 = [3] ∧ view [1, 2, 3] 2 = [2, 3] := by
  decide

/-- A view shorter than its storage is not the storage. -/
theorem view_not_whole : view [1, 2, 3] 2 ≠ [1, 2, 3] := by
  decide

/-- The longest view's copy serves the shorter one. -/
theorem copy_served :
    view ((view [1, 2, 3] 2).map (· * 10)) 1 = (view [1, 2, 3] 1).map (· * 10) :=
  view_copy _ (by decide)

namespace EndTransport

/-- Header identity, buffer start and view length are different coordinates. -/
structure Header where
  address : Nat
  start : Nat
  length : Nat
  deriving DecidableEq

def Header.bufferEnd (header : Header) : Nat := header.start + header.length

def headers : List (Fin 3) := [0, 1, 2]

def source (index : Fin 3) : Header :=
  if index = 0 then ⟨10, 100, 3⟩
  else if index = 1 then ⟨11, 101, 2⟩
  else ⟨12, 200, 3⟩

def copied (index : Fin 3) : Header :=
  if index = 0 then ⟨30, 1000, 3⟩
  else if index = 1 then ⟨31, 1001, 2⟩
  else ⟨32, 2000, 3⟩

def ends : List (Nat × Nat) :=
  EndKeys.observations headers (fun index => (source index).bufferEnd)
    (fun index => (copied index).bufferEnd)

/-- Two distinct headers share an end; a third end stays distinct. -/
theorem shared_and_distinct_ends_preserved :
    (headers.map fun index => (source index).address).Nodup ∧
    (headers.map fun index => (copied index).address).Nodup ∧
    EndKeys.check ends = true ∧ ends.lookup 103 = some 1003 ∧
    ends.lookup 203 = some 2003 := by decide

/-- Shorter views still read the corresponding suffix of the longest copy. -/
theorem same_end_and_suffix_contents :
    (copied 0).bufferEnd = (copied 1).bufferEnd ∧
    view ([1, 2, 3].map (· * 10)) (copied 1).length = [20, 30] := by decide

/-- Equal payloads at different table entries retain their positions. -/
theorem complete_table_keeps_duplicate_payloads :
    EndKeys.checkedPrepare ends (· + 10) [(103, 7), (203, 7), (103, 9)] =
      some [(1003, 17), (2003, 17), (1003, 19)] := by decide

def fractured (index : Fin 3) : Header :=
  if index = 1 then ⟨31, 3000, 2⟩ else copied index

/-- Copying the short header first can fix a different backing end. Distinct
header images alone cannot authorize the resulting memo transport. -/
theorem distinct_headers_do_not_preserve_buffer_classes :
    (headers.map fun index => (fractured index).address).Nodup ∧
    EndKeys.check (EndKeys.observations headers (fun index => (source index).bufferEnd)
      (fun index => (fractured index).bufferEnd)) = false := by decide

theorem fractured_end_refuses_complete_preparation :
    EndKeys.checkedPrepare
      (EndKeys.observations headers (fun index => (source index).bufferEnd)
        (fun index => (fractured index).bufferEnd))
      (· + 10) [(103, 7), (203, 7)] = none := by decide

def coalesced (index : Fin 3) : Header :=
  if index = 2 then ⟨32, 1000, 3⟩ else copied index

/-- Preserving each individual header's length does not prevent different
source buffers from being identified. -/
theorem lengths_do_not_prevent_end_coalescence :
    (∀ index : Fin 3, (coalesced index).length = (source index).length) ∧
    EndKeys.check (EndKeys.observations headers (fun index => (source index).bufferEnd)
      (fun index => (coalesced index).bufferEnd)) = false := by decide

theorem missing_end_refuses_without_partial_table :
    EndKeys.check ends = true ∧
    EndKeys.checkedPrepare ends (· + 10) [(103, 7), (999, 8), (203, 9)] = none := by decide

/-- Observing only one of the shared headers misses the inconsistent image.
The complete observation domain is therefore a separate obligation. -/
theorem omitted_header_hides_fracture :
    EndKeys.check (EndKeys.observations [0, 2] (fun index => (source index).bufferEnd)
      (fun index => (fractured index).bufferEnd)) = true ∧
    EndKeys.check (EndKeys.observations headers (fun index => (source index).bufferEnd)
      (fun index => (fractured index).bufferEnd)) = false := by decide

end EndTransport

end Controls

end Mettapedia.Machines.SuffixViewCopy
