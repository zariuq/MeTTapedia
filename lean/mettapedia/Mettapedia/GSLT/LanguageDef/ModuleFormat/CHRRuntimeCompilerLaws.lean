import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRRuntimeCompiler
import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRProgramCodecLaws

/-! Boundary laws of the CHR package provider: the program payload is
transported exactly, and the occurrence transformation it asks for leaves
the declared constraints of the Space equal, as a multiset, to the final
CHR store. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRRuntimeCompiler

open Mettapedia.Languages

theorem groundArguments : ∀ values : List CHR.Value,
    values.mapM (groundArgument? ∘ CHR.Term.value) = some values
  | [] => rfl
  | first :: rest => by
    simp only [List.mapM_cons, Function.comp_apply, groundArgument?, groundArguments rest]
    rfl

theorem groundConstraint_asHead (constraint : CHR.Constraint) :
    groundConstraint? constraint.asHead = some constraint := by
  cases constraint with
  | mk name arguments =>
    simp only [groundConstraint?, CHR.Constraint.asHead, List.mapM_map, groundArguments]
    rfl

theorem inputHeads : ∀ inputs : List CHR.Constraint,
    inputs.mapM (CHRProgramCodec.head? ∘ fun constraint => CHRProgramCodec.head constraint.asHead) =
      some (inputs.map CHR.Constraint.asHead)
  | [] => rfl
  | first :: rest => by
    simp only [List.mapM_cons, Function.comp_apply, CHRProgramCodec.head_roundtrip, inputHeads rest,
      List.map_cons]
    rfl

theorem asHeadsGround : ∀ inputs : List CHR.Constraint,
    inputs.mapM (groundConstraint? ∘ CHR.Constraint.asHead) = some inputs
  | [] => rfl
  | first :: rest => by
    simp only [List.mapM_cons, Function.comp_apply, groundConstraint_asHead, asHeadsGround rest]
    rfl

/-- The program payload carries the lowered program and its query exactly. -/
theorem programValue_roundtrip (lowered : CHRPrologLowering.Program) :
    programOfValue? (programValue lowered) = some lowered := by
  cases lowered with
  | mk program inputs =>
    simp [programOfValue?, programValue, CHRProgramCodec.node, CHRProgramCodec.node?,
      CHRProgramCodec.program_roundtrip, inputHeads, asHeadsGround]

/-! ## The occurrence transformation -/

/-- A captured occurrence is consumed exactly when its identifier is absent
from the final store. Ordinals name distinct captured occurrences. -/
theorem mem_consumed {rows : List (Nat × Nat)} (ordinals : (rows.map Prod.fst).Nodup)
    {final : List (Nat × CHR.Constraint)} {ordinal id : Nat} (member : (ordinal, id) ∈ rows) :
    ordinal ∈ consumed rows final ↔ id ∉ final.map Prod.fst := by
  unfold consumed
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨⟨ordinal', id'⟩, member', picked⟩
    by_cases present : id' ∈ final.map Prod.fst
    · have contained : (final.map Prod.fst).contains id' = true := List.contains_iff_mem.mpr present
      simp only [contained, if_true] at picked
      cases picked
    · have absent : (final.map Prod.fst).contains id' = false := by
        cases found : (final.map Prod.fst).contains id'
        · rfl
        · exact absurd (List.contains_iff_mem.mp found) present
      simp only [absent, Bool.false_eq_true, if_false, Option.some.injEq] at picked
      have same := List.inj_on_of_nodup_map ordinals member' member picked
      simp only [Prod.mk.injEq] at same
      rw [← same.2]
      exact present
  · intro absent
    refine ⟨(ordinal, id), member, ?_⟩
    have notContained : (final.map Prod.fst).contains id = false := by
      cases found : (final.map Prod.fst).contains id
      · rfl
      · exact absurd (List.contains_iff_mem.mp found) absent
    simp only [notContained, Bool.false_eq_true, if_false]

/-- The survivors and the additions together are the final store. -/
theorem publication_perm (rows : List (Nat × Nat × CHR.Constraint)) (final : List (Nat × CHR.Constraint))
    (ordinals : (rows.map Prod.fst).Nodup) (rowIds : (rows.map fun row => row.2.1).Nodup)
    (finalIds : (final.map Prod.fst).Nodup)
    (consistent : ∀ row ∈ rows, ∀ entry ∈ final, row.2.1 = entry.1 → row.2.2 = entry.2) :
    ((rows.filter fun row => row.1 ∉ consumed (rows.map fun row => (row.1, row.2.1)) final).map (·.2.2) ++
      (additions (rows.map fun row => (row.1, row.2.1)) final).map Prod.snd).Perm (final.map Prod.snd) := by
  let captured := rows.map fun row => (row.1, row.2.1)
  have capturedOrdinals : (captured.map Prod.fst).Nodup := by
    simpa [captured, List.map_map, Function.comp_def] using ordinals
  -- Survivors are the rows whose identifiers remain.
  have survivors : (rows.filter fun row => row.1 ∉ consumed captured final) =
      rows.filter fun row => row.2.1 ∈ final.map Prod.fst := by
    apply List.filter_congr
    intro row member
    have inCaptured : (row.1, row.2.1) ∈ captured := List.mem_map.mpr ⟨row, member, rfl⟩
    have equivalence := mem_consumed (final := final) capturedOrdinals inCaptured
    by_cases present : row.2.1 ∈ final.map Prod.fst
    · simp only [present, not_true_eq_false, iff_false] at equivalence
      simp [equivalence, present]
    · simp only [present, not_false_eq_true, iff_true] at equivalence
      simp [equivalence, present]
  let capturedIds := captured.map Prod.snd
  let present := final.filter fun entry => capturedIds.contains entry.1
  let rest := final.filter fun entry => !capturedIds.contains entry.1
  have split : (present ++ rest).Perm final :=
    List.filter_append_perm (fun entry : Nat × CHR.Constraint => capturedIds.contains entry.1) final
  have additionsEq : additions captured final = rest := rfl
  -- Kept rows and captured final entries carry the same pairs.
  let kept := (rows.filter fun row => row.2.1 ∈ final.map Prod.fst).map fun row => (row.2.1, row.2.2)
  have keptNodup : kept.Nodup := by
    have ids : (kept.map Prod.fst).Nodup := by
      have sub := (List.filter_sublist (p := fun row : Nat × Nat × CHR.Constraint =>
        decide (row.2.1 ∈ final.map Prod.fst)) (l := rows)).map (fun row => row.2.1)
      simpa [kept, List.map_map, Function.comp_def] using sub.nodup rowIds
    exact List.Nodup.of_map Prod.fst ids
  have presentNodup : present.Nodup := by
    have sub := (List.filter_sublist (p := fun entry : Nat × CHR.Constraint =>
      capturedIds.contains entry.1) (l := final)).map Prod.fst
    exact List.Nodup.of_map Prod.fst (sub.nodup finalIds)
  have capturedMember : ∀ id, capturedIds.contains id = true ↔ ∃ row ∈ rows, row.2.1 = id := by
    intro id
    rw [List.contains_iff_mem]
    simp [capturedIds, captured, List.map_map, Function.comp_def]
  have pairs : kept.Perm present := by
    rw [List.perm_ext_iff_of_nodup keptNodup presentNodup]
    intro pair
    constructor
    · intro member
      obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp member
      obtain ⟨inRows, inFinal⟩ := List.mem_filter.mp rowMember
      have found : row.2.1 ∈ final.map Prod.fst := of_decide_eq_true inFinal
      obtain ⟨entry, entryMember, entryId⟩ := List.mem_map.mp found
      have sameConstraint := consistent row inRows entry entryMember entryId.symm
      have same : (row.2.1, row.2.2) = entry := Prod.ext entryId.symm sameConstraint
      refine List.mem_filter.mpr ⟨same ▸ entryMember, ?_⟩
      exact (capturedMember _).mpr ⟨row, inRows, rfl⟩
    · intro member
      obtain ⟨entryMember, wasCaptured⟩ := List.mem_filter.mp member
      obtain ⟨row, inRows, rowId⟩ := (capturedMember _).mp wasCaptured
      have sameConstraint := consistent row inRows pair entryMember rowId
      refine List.mem_map.mpr ⟨row, List.mem_filter.mpr ⟨inRows, ?_⟩, Prod.ext rowId sameConstraint⟩
      exact decide_eq_true (List.mem_map.mpr ⟨pair, entryMember, rowId.symm⟩)
  have survivorsValues : (rows.filter fun row => row.2.1 ∈ final.map Prod.fst).map (·.2.2) =
      kept.map Prod.snd := by
    simp [kept, List.map_map, Function.comp_def]
  show ((rows.filter fun row => row.1 ∉ consumed captured final).map (·.2.2) ++
      (additions captured final).map Prod.snd).Perm (final.map Prod.snd)
  rw [survivors, survivorsValues, additionsEq]
  have joined : (present.map Prod.snd ++ rest.map Prod.snd) = (present ++ rest).map Prod.snd := by
    simp [List.map_append]
  exact ((pairs.map Prod.snd).append_right _).trans (joined ▸ split.map Prod.snd)

#print axioms programValue_roundtrip
#print axioms publication_perm

/-! Host spelling controls: the names a host symbol carries unchanged. The
other names travel as host strings. -/

example : ["word", "true", "7", "a b"].all hostSymbolSupported = true := by decide_cbv
example : hostSymbolSupported "True" = false := by decide_cbv
example : hostSymbolSupported "False" = false := by decide_cbv
example : hostSymbolSupported "" = false := by decide_cbv
example : hostSymbolSupported "a\u0000b" = false := by decide_cbv

end Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRRuntimeCompiler
