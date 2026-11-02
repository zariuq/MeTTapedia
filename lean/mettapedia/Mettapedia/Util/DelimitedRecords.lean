import Mathlib.Data.List.Basic

/-! Delimiter-framed records with optional final termination. Empty records
and repeated records are data; an empty stream contains no records. -/

set_option autoImplicit false

namespace Mettapedia.Util.DelimitedRecords

variable {α : Type} [BEq α] [LawfulBEq α]

def prepend (separator value : α) (records : List (List α)) : List (List α) :=
  if value == separator then [] :: records else
    match records with
    | [] => [[value]]
    | first :: rest => (value :: first) :: rest

def decode (separator : α) (input : List α) : List (List α) :=
  input.foldr (prepend separator) []

inductive Framed (separator : α) : List α → List (List α) → Prop where
  | empty : Framed separator [] []
  | terminated (record suffix : List α) (records : List (List α))
      (plain : separator ∉ record) (rest : Framed separator suffix records) :
      Framed separator (record ++ separator :: suffix) (record :: records)
  | unterminated (record : List α) (nonempty : record ≠ []) (plain : separator ∉ record) :
      Framed separator record [record]

theorem decode_terminated (separator : α) (record suffix : List α) (plain : separator ∉ record) :
    decode separator (record ++ separator :: suffix) = record :: decode separator suffix := by
  induction record with
  | nil => simp [decode, prepend]
  | cons first rest ih =>
    have different : first ≠ separator := by intro same; exact plain (by simp [same])
    have tail : separator ∉ rest := fun member => plain (List.mem_cons_of_mem first member)
    change prepend separator first (decode separator (rest ++ separator :: suffix)) = _
    rw [ih tail]
    simp [prepend, different]

theorem decode_unterminated (separator : α) (record : List α) (nonempty : record ≠ [])
    (plain : separator ∉ record) : decode separator record = [record] := by
  induction record with
  | nil => exact False.elim (nonempty rfl)
  | cons first rest ih =>
    have different : first ≠ separator := by intro same; exact plain (by simp [same])
    have tail : separator ∉ rest := fun member => plain (List.mem_cons_of_mem first member)
    cases rest with
    | nil => simp [decode, prepend, different]
    | cons second rest =>
      change prepend separator first (decode separator (second :: rest)) = _
      rw [ih (by simp) tail]
      simp [prepend, different]

theorem decode_complete {separator : α} {input : List α} {records : List (List α)}
    (framed : Framed separator input records) : decode separator input = records := by
  induction framed with
  | empty => rfl
  | terminated record suffix records plain _ ih => rw [decode_terminated _ _ _ plain, ih]
  | unterminated record nonempty plain => exact decode_unterminated _ _ nonempty plain

theorem Framed.prepend_plain {separator first : α} {input : List α} {records : List (List α)}
    (different : first ≠ separator) (framed : Framed separator input records) :
    Framed separator (first :: input) (prepend separator first records) := by
  cases framed with
  | empty =>
    simpa [prepend, different] using
      Framed.unterminated (separator := separator) [first] (by simp) (by simp [Ne.symm different])
  | terminated record suffix records plain later =>
    simpa [prepend, different] using Framed.terminated (separator := separator) (first :: record) suffix records
      (by simp [plain, Ne.symm different]) later
  | unterminated record nonempty plain =>
    simpa [prepend, different] using Framed.unterminated (separator := separator) (first :: input)
      (by simp) (by simp [plain, Ne.symm different])

theorem decode_sound (separator : α) (input : List α) : Framed separator input (decode separator input) := by
  induction input with
  | nil => exact .empty
  | cons first rest ih =>
    change Framed separator (first :: rest) (prepend separator first (decode separator rest))
    by_cases same : first = separator
    · subst first
      simpa [prepend] using Framed.terminated (separator := separator) [] rest (decode separator rest) (by simp) ih
    · exact ih.prepend_plain same

theorem decode_exact (separator : α) (input : List α) (records : List (List α)) :
    decode separator input = records ↔ Framed separator input records :=
  ⟨fun same => same ▸ decode_sound separator input, decode_complete⟩

def encode (separator : α) (records : List (List α)) : List α :=
  records.flatMap (· ++ [separator])

theorem roundtrip (separator : α) (records : List (List α))
    (plain : ∀ record ∈ records, separator ∉ record) : decode separator (encode separator records) = records := by
  induction records with
  | nil => rfl
  | cons first rest ih =>
    change decode separator ((first ++ [separator]) ++ encode separator rest) = _
    rw [List.append_assoc]
    change decode separator (first ++ separator :: encode separator rest) = _
    rw [decode_terminated _ _ _ (plain first List.mem_cons_self)]
    rw [ih (fun record member => plain record (List.mem_cons_of_mem first member))]

theorem empty_records_preserved : decode '\n' ['\n', '\n'] = [[], []] := by decide
theorem empty_stream_distinct : decode '\n' [] ≠ decode '\n' ['\n'] := by decide

end Mettapedia.Util.DelimitedRecords
