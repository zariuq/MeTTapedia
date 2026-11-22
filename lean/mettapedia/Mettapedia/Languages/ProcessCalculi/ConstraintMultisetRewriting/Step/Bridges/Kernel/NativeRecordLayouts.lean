import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeRecordRunsSyntax

/-!
# Finite replacement and fresh identities for live native-record layouts

An occurrence's constructor spelling does not determine its role. Replacement
uses the actual ordered made list, retains unwritten field identities, and
proves the exact resulting live support. Fresh allocation bounds only the
current eleven live identities; it imposes no global never-reuse policy.
There is no source-step, semantic guard, or native implementation premise.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeRecordLayouts

open NativeFieldSchema NativeRecordRuns

def taken (old : Layout) (writes : List Field) : Finset Occurrence :=
  (old.request :: writes.map old.field).toFinset

theorem field_mem_support (old : Layout) (field : Field) : old.field field ∈ old.support := by
  apply Finset.mem_insert_of_mem
  exact Finset.mem_image.mpr ⟨field,
    List.mem_toFinset.mpr (NativeFieldExecution.field_member field), rfl⟩

theorem support_cases (old : Layout) (occurrence : Occurrence) :
    occurrence ∈ old.support ↔ occurrence = old.request ∨ ∃ field, occurrence = old.field field := by
  constructor
  · intro present
    rcases Finset.mem_insert.mp present with same | present
    · exact Or.inl same
    · obtain ⟨field, _, same⟩ := Finset.mem_image.mp present
      exact Or.inr ⟨field, same.symm⟩
  · rintro (rfl | ⟨field, rfl⟩)
    · exact Finset.mem_insert_self _ _
    · exact field_mem_support old field

theorem taken_cases (old : Layout) (writes : List Field) (occurrence : Occurrence) :
    occurrence ∈ taken old writes ↔
      occurrence = old.request ∨ ∃ field ∈ writes, occurrence = old.field field := by
  simp [taken, eq_comm]

theorem field_taken_iff (old : Layout) (writes : List Field) (field : Field) :
    old.field field ∈ taken old writes ↔ field ∈ writes := by
  constructor
  · intro present
    rcases (taken_cases old writes _).mp present with same | ⟨other, member, same⟩
    · exact False.elim (old.request_not_field field same.symm)
    · have equal := old.field_injective same
      simpa only [equal] using member
  · intro member
    exact (taken_cases old writes _).mpr (Or.inr ⟨field, member, rfl⟩)

theorem position_lt (writes : List Field) (made : List Occurrence)
    (length : made.length = 1 + writes.length) (field : Field) (member : field ∈ writes) :
    1 + writes.idxOf field < made.length := by
  have := List.idxOf_lt_length_of_mem member
  omega

def replacementField (old : Layout) (writes : List Field) (made : List Occurrence)
    (length : made.length = 1 + writes.length) (field : Field) : Occurrence :=
  if member : field ∈ writes then made[1 + writes.idxOf field]'(position_lt writes made length field member)
  else old.field field

theorem replacementField_written (old : Layout) (writes : List Field) (made : List Occurrence)
    (length : made.length = 1 + writes.length) (field : Field) (member : field ∈ writes) :
    replacementField old writes made length field =
      made[1 + writes.idxOf field]'(position_lt writes made length field member) := by
  simp only [replacementField, dif_pos member]

theorem replacementField_unwritten (old : Layout) (writes : List Field) (made : List Occurrence)
    (length : made.length = 1 + writes.length) (field : Field) (absent : field ∉ writes) :
    replacementField old writes made length field = old.field field := by
  simp only [replacementField, dif_neg absent]

theorem replacementField_injective (old : Layout) (writes : List Field) (made : List Occurrence)
    (length : made.length = 1 + writes.length) (distinct : made.Nodup)
    (fresh : Disjoint made.toFinset old.support) :
    Function.Injective (replacementField old writes made length) := by
  intro left right same
  by_cases leftWritten : left ∈ writes
  · rw [replacementField_written old writes made length left leftWritten] at same
    by_cases rightWritten : right ∈ writes
    · rw [replacementField_written old writes made length right rightWritten] at same
      have positions := distinct.getElem_inj_iff.mp same
      exact (List.idxOf_inj leftWritten).mp (by omega)
    · rw [replacementField_unwritten old writes made length right rightWritten] at same
      have member : made[1 + writes.idxOf left]'(position_lt writes made length left leftWritten) ∈ made.toFinset :=
        List.mem_toFinset.mpr (List.getElem_mem _)
      exact False.elim ((Finset.disjoint_left.mp fresh) member
        (by rw [same]; exact field_mem_support old right))
  · rw [replacementField_unwritten old writes made length left leftWritten] at same
    by_cases rightWritten : right ∈ writes
    · rw [replacementField_written old writes made length right rightWritten] at same
      have member : made[1 + writes.idxOf right]'(position_lt writes made length right rightWritten) ∈ made.toFinset :=
        List.mem_toFinset.mpr (List.getElem_mem _)
      exact False.elim ((Finset.disjoint_left.mp fresh) member
        (by rw [← same]; exact field_mem_support old left))
    · rw [replacementField_unwritten old writes made length right rightWritten] at same
      exact old.field_injective same

theorem replacement_request_disjoint (old : Layout) (writes : List Field) (made : List Occurrence)
    (length : made.length = 1 + writes.length) (distinct : made.Nodup)
    (fresh : Disjoint made.toFinset old.support) (field : Field) :
    made[0]'(by omega) ≠ replacementField old writes made length field := by
  intro same
  by_cases written : field ∈ writes
  · rw [replacementField_written old writes made length field written] at same
    have impossible := distinct.getElem_inj_iff.mp same
    omega
  · rw [replacementField_unwritten old writes made length field written] at same
    have member : made[0]'(by omega) ∈ made.toFinset :=
      List.mem_toFinset.mpr (List.getElem_mem _)
    exact (Finset.disjoint_left.mp fresh) member (by rw [same]; exact field_mem_support old field)

def replacementLayout (old : Layout) (writes : List Field) (made : List Occurrence)
    (length : made.length = 1 + writes.length) (distinct : made.Nodup)
    (fresh : Disjoint made.toFinset old.support) : Layout where
  request := made[0]'(by omega)
  field := replacementField old writes made length
  field_injective := replacementField_injective old writes made length distinct fresh
  request_not_field := replacement_request_disjoint old writes made length distinct fresh

theorem made_eq (old : Layout) (writes : List Field) (made : List Occurrence)
    (length : made.length = 1 + writes.length) (distinct : made.Nodup)
    (fresh : Disjoint made.toFinset old.support) (writesDistinct : writes.Nodup) :
    made = (replacementLayout old writes made length distinct fresh).request ::
      writes.map (replacementLayout old writes made length distinct fresh).field := by
  apply List.ext_getElem
  · simpa only [List.length_cons, List.length_map, Nat.add_comm] using length
  · intro index within inside
    cases index with
    | zero => rfl
    | succ index =>
        have bounded : index < writes.length := by simpa only [List.length_cons, List.length_map, Nat.succ_lt_succ_iff] using inside
        simp only [List.getElem_cons_succ, List.getElem_map]
        change made[index+1] = replacementField old writes made length writes[index]
        rw [replacementField_written old writes made length _ (List.getElem_mem bounded)]
        simp only [writesDistinct.idxOf_getElem index bounded, Nat.add_comm]

theorem exact_support (old : Layout) (writes : List Field) (made : List Occurrence)
    (length : made.length = 1 + writes.length) (distinct : made.Nodup)
    (fresh : Disjoint made.toFinset old.support) (writesDistinct : writes.Nodup) :
    (replacementLayout old writes made length distinct fresh).support =
      (old.support \ taken old writes) ∪ made.toFinset := by
  let next := replacementLayout old writes made length distinct fresh
  have ordered := made_eq old writes made length distinct fresh writesDistinct
  apply Finset.ext
  intro occurrence
  constructor
  · intro present
    rcases (support_cases next occurrence).mp present with same | ⟨field, same⟩
    · apply Finset.mem_union_right
      apply List.mem_toFinset.mpr
      rw [ordered, same]
      exact List.mem_cons_self
    · by_cases written : field ∈ writes
      · apply Finset.mem_union_right
        apply List.mem_toFinset.mpr
        rw [ordered, same]
        exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨field, written, rfl⟩)
      · apply Finset.mem_union_left
        have retained : next.field field = old.field field :=
          replacementField_unwritten old writes made length field written
        rw [same, retained]
        exact Finset.mem_sdiff.mpr ⟨field_mem_support old field,
          fun absent => written ((field_taken_iff old writes field).mp absent)⟩
  · intro present
    rcases Finset.mem_union.mp present with retained | madePresent
    · obtain ⟨oldPresent, notTaken⟩ := Finset.mem_sdiff.mp retained
      rcases (support_cases old occurrence).mp oldPresent with same | ⟨field, same⟩
      · exact False.elim (notTaken ((taken_cases old writes occurrence).mpr (Or.inl same)))
      · have unwritten : field ∉ writes := fun written =>
          notTaken ((taken_cases old writes occurrence).mpr (Or.inr ⟨field, written, same⟩))
        have retained : next.field field = old.field field :=
          replacementField_unwritten old writes made length field unwritten
        exact (support_cases next occurrence).mpr (Or.inr ⟨field, same.trans retained.symm⟩)
    · have member := List.mem_toFinset.mp madePresent
      rw [ordered] at member
      rcases List.mem_cons.mp member with same | member
      · exact (support_cases next occurrence).mpr (Or.inl same)
      · obtain ⟨field, _written, same⟩ := List.mem_map.mp member
        exact (support_cases next occurrence).mpr (Or.inr ⟨field, same.symm⟩)

structure Replacement (old : Layout) (writes : List Field) (made : List Occurrence) where
  next : Layout
  made_eq : made = next.request :: writes.map next.field
  unwritten : ∀ field, field ∉ writes → next.field field = old.field field
  exact_support : next.support = (old.support \ taken old writes) ∪ made.toFinset

def replace (old : Layout) (writes : List Field) (made : List Occurrence)
    (length : made.length = 1 + writes.length) (distinct : made.Nodup)
    (fresh : Disjoint made.toFinset old.support) (writesDistinct : writes.Nodup) :
    Replacement old writes made where
  next := replacementLayout old writes made length distinct fresh
  made_eq := made_eq old writes made length distinct fresh writesDistinct
  unwritten := replacementField_unwritten old writes made length
  exact_support := exact_support old writes made length distinct fresh writesDistinct

def replace? (old : Layout) (writes : List Field) (made : List Occurrence) :
    Option (Replacement old writes made) :=
  if length : made.length = 1 + writes.length then
    if distinct : made.Nodup then
      if fresh : Disjoint made.toFinset old.support then
        if writesDistinct : writes.Nodup then some (replace old writes made length distinct fresh writesDistinct)
        else none
      else none
    else none
  else none

def rank : Occurrence → Nat
  | .field _ serial => serial
  | .request serial => serial

def bound (old : Layout) : Nat := old.support.sup rank

def allocate (old : Layout) (writes : List Field) : List Occurrence :=
  (List.range (1 + writes.length)).map (fun offset => .request (bound old + 1 + offset))

theorem allocate_length (old : Layout) (writes : List Field) :
    (allocate old writes).length = 1 + writes.length := by simp [allocate]

theorem allocate_nodup (old : Layout) (writes : List Field) : (allocate old writes).Nodup := by
  apply (List.nodup_range (n := 1 + writes.length)).map
  intro left right same
  have equal := Occurrence.request.inj same
  omega

theorem allocate_fresh (old : Layout) (writes : List Field) :
    Disjoint (allocate old writes).toFinset old.support := by
  apply Finset.disjoint_left.mpr
  intro occurrence madePresent oldPresent
  obtain ⟨offset, _within, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp madePresent)
  have bounded : rank (Occurrence.request (bound old + 1 + offset)) ≤ old.support.sup rank :=
    Finset.le_sup oldPresent
  change bound old + 1 + offset ≤ bound old at bounded
  omega

def allocateReplacement (old : Layout) (writes : List Field) (distinct : writes.Nodup) :
    Replacement old writes (allocate old writes) :=
  replace old writes (allocate old writes) (allocate_length old writes)
    (allocate_nodup old writes) (allocate_fresh old writes) distinct

namespace Controls

private def fieldNumber : Field → Nat
  | .context => 0 | .names => 1 | .typeRows => 2 | .termRows => 3 | .dbRows => 4
  | .theoremRows => 5 | .nameMap => 6 | .typeMap => 7 | .drops => 8 | .policy => 9

private theorem fieldNumber_injective : Function.Injective fieldNumber := by
  intro left right same
  cases left <;> cases right <;> simp_all [fieldNumber]

private def old : Layout where
  request := .field .policy 40
  field := fun field => .request (fieldNumber field)
  field_injective := fun _ _ same => fieldNumber_injective (Occurrence.request.inj same)
  request_not_field := by intro field same; cases same

private def two : List Field := [.context, .names]
private def made : List Occurrence := [.field .context 41, .request 42, .field .policy 43]

theorem arbitrary_constructor_roles : old.request = .field .policy 40 ∧ old.field .context = .request 0 :=
  ⟨rfl, rfl⟩

theorem empty_writes_accepted : (replace? old [] [.field .context 41]).isSome = true := by decide +kernel

theorem two_writes_accepted : (replace? old two made).isSome = true := by decide +kernel

theorem duplicate_made_refused :
    (replace? old two [.field .context 41, .request 42, .request 42]).isNone = true := by decide +kernel

theorem old_id_refused :
    (replace? old two [.field .context 41, .request 0, .field .policy 43]).isNone = true := by decide +kernel

theorem fresh_below_bound_accepted :
    (replace? old [] [.field .policy 39]).isSome = true := by decide +kernel

theorem fresh_same_rank_different_constructor_accepted :
    (replace? old [] [.request 40]).isSome = true := by decide +kernel

theorem allocation_valid :
    (allocate old two).length = 3 ∧ (allocate old two).Nodup ∧
      Disjoint (allocate old two).toFinset old.support :=
  ⟨allocate_length old two, allocate_nodup old two, allocate_fresh old two⟩

end Controls

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeRecordLayouts
