import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeScopeClosure

/-!
# Known-row projection and typing-scope publication

The native known-row mutation classifier advances the declaration revision
for literal three-field `:` and `:<` rows. A variable-headed row is classified
as data, even though the full subtype query can match it. Therefore that
revision does not yet determine the subtype dependency packet.

This module states the source-level correction precisely. A potential typing
row is a root variable, or a three-field expression whose head is `:`, `:<`
or a variable. This classification is derived from ordinary atom matching;
it is not an all-row resource restriction. Irrelevant rows are proved unable
to contribute to either the actual annotation reader or the whole-row
subtype query. Corrected publication therefore preserves the captured packet
whenever its revision stays equal.

The native stored-header/atom correspondence, nonordinary representations,
custom grounded matching and opaque-row classification remain representation
obligations. This module does not claim that the currently implemented known
row classifier already has the corrected law.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypingScopeCapture

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open TypeDependencyAdmission TypeScopeClosure

/-- The declaration bit in the live known-row classifier. Unknown stored
rows take a separate opaque branch and are not represented by this input. -/
def nativeDeclarationRow : Atom → Bool
  | .expression [.symbol head, _, _] => head == ":" || head == ":<"
  | _ => false

/-- Exact outer-shape possibility for ordinary annotation/subtype rows.
Root and head variables must be included even when no literal `:<` occurs. -/
def potentialTypingRow : Atom → Bool
  | .var _ => true
  | .expression [.var _, _, _] => true
  | .expression [.symbol head, _, _] => head == ":" || head == ":<"
  | _ => false

def capture (rows : List Atom) : List Atom := rows.filter potentialTypingRow

/-- The represented ordinary-atom branch of the native open-row flag.
Native list/rational/header-failure branches additionally force decline. -/
def openRow : Atom → Bool
  | .var _ => true
  | .expression (.symbol _ :: _) => false
  | .expression (_ :: _) => true
  | _ => false

def freshScan (rows : List Atom) : Bool :=
  !(rows.any fun row => nativeDeclarationRow row && !resourceFree row) &&
    !(rows.any openRow)

theorem potential_with_closed_head_is_literal (row : Atom)
    (potential : potentialTypingRow row = true) (closedHead : openRow row = false) :
    nativeDeclarationRow row = true := by
  unfold potentialTypingRow at potential
  split at potential
  · simp [openRow] at closedHead
  · simp [openRow] at closedHead
  · exact potential
  · contradiction

/-- A freshly checked native-shaped identity/open-row gate justifies the
selected packet. The raw space may contain unrelated resource-valued data. -/
theorem freshScan_capture_resourceFree (rows : List Atom) (accepted : freshScan rows = true) :
    resourceFreeList (capture rows) = true := by
  simp only [freshScan, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false] at accepted
  apply (resourceFreeList_iff _).mpr
  intro row member
  obtain ⟨present, potential⟩ := List.mem_filter.mp member
  have closedHead : openRow row = false := by simpa using accepted.2 row present
  have literal := potential_with_closed_head_is_literal row potential closedHead
  have tested := accepted.1 row present
  simpa [literal] using tested

theorem freshScan_packet_passes (rows intrinsicRows : List Atom) (input : Atom)
    (accepted : freshScan rows = true)
    (intrinsicSafe : resourceFreeList intrinsicRows = true) (inputSafe : resourceFree input = true) :
    TypeDependencyAdmission.check ⟨capture rows, intrinsicRows, input⟩ = true := by
  simp [TypeDependencyAdmission.check, freshScan_capture_resourceFree rows accepted,
    intrinsicSafe, inputSafe]

theorem native_declaration_is_potential (row : Atom) (known : nativeDeclarationRow row = true) :
    potentialTypingRow row = true := by
  unfold nativeDeclarationRow at known
  split at known
  · exact known
  · contradiction

private def arity : Atom → Nat
  | .expression children => children.length
  | _ => 0

theorem irrelevant_cannot_match_subtype (row : Atom) (irrelevant : potentialTypingRow row = false)
    (input : Atom) (fresh : String) (theta : Mettapedia.Logic.LP.Subst UnifyAtoms.sig) :
    UnifyAtoms.unify (subtypePattern input fresh) row ≠ some theta := by
  intro matched
  have same := UnifyAtoms.unify_instance matched
  cases row with
  | var _ => simp [potentialTypingRow] at irrelevant
  | symbol _ => simp [subtypePattern, substA, substL] at same
  | grounded _ => simp [subtypePattern, substA, substL] at same
  | expression children =>
      have sizeEq := congrArg arity same
      simp only [subtypePattern, substA, substL, arity, List.length_cons, List.length_nil,
        UnifyAtoms.substL_eq_map, List.length_map] at sizeEq
      obtain ⟨head, lower, upper, rfl⟩ := List.length_eq_three.mp sizeEq.symm
      cases head with
      | var _ => simp [potentialTypingRow] at irrelevant
      | symbol name =>
          have headEq : ":<" = name := by
            have parts := Atom.expression.inj same
            have heads := (List.cons.inj parts).1
            exact Atom.symbol.inj heads
          subst name
          simp [potentialTypingRow] at irrelevant
      | grounded _ => simp [subtypePattern, substA, substL] at same
      | expression _ => simp [subtypePattern, substA, substL] at same

def rawWorld : RetainedTypePayloads.ExternalView := fun kind key => .grounded (.custom kind key)

mutual
theorem observe_raw : ∀ atom, RetainedTypePayloads.observe rawWorld atom = atom
  | .symbol _ => rfl
  | .var _ => rfl
  | .grounded value => by cases value <;> rfl
  | .expression children => by
      rw [RetainedTypePayloads.observe, observeList_raw]
theorem observeList_raw : ∀ atoms, RetainedTypePayloads.observeList rawWorld atoms = atoms
  | [] => rfl
  | atom :: atoms => by rw [RetainedTypePayloads.observeList, observe_raw, observeList_raw]
end

theorem irrelevant_subtypeRow (row : Atom) (irrelevant : potentialTypingRow row = false)
    (input : Atom) (fresh : String) : subtypeRow rawWorld input fresh row = none := by
  have rejected : UnifyAtoms.unify (subtypePattern input fresh) row = none := by
    cases answer : UnifyAtoms.unify (subtypePattern input fresh) row with
    | none => rfl
    | some theta => exact False.elim (irrelevant_cannot_match_subtype row irrelevant input fresh theta answer)
  simp [subtypeRow, observe_raw, rejected]

theorem filterMap_capture {Result : Type} (read : Atom → Option Result)
    (skip : ∀ row, potentialTypingRow row = false → read row = none) (rows : List Atom) :
    (capture rows).filterMap read = rows.filterMap read := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      cases relevant : potentialTypingRow row with
      | false => simpa only [capture, List.filter_cons, relevant, Bool.false_eq_true,
          ↓reduceIte, List.filterMap_cons, skip row relevant, Option.elim_none] using ih
      | true =>
          simp only [capture, List.filter_cons, relevant, ↓reduceIte, List.filterMap_cons] at ih ⊢
          rw [ih]

theorem subtypeQuery_capture (input : Atom) (fresh : String) (rows : List Atom) :
    subtypeQuery rawWorld input fresh (capture rows) = subtypeQuery rawWorld input fresh rows :=
  filterMap_capture (subtypeRow rawWorld input fresh)
    (fun row irrelevant => irrelevant_subtypeRow row irrelevant input fresh) rows

theorem annotations_capture (subject : Atom) (rows : List Atom) :
    getAnnotatedTypes ⟨capture rows⟩ subject = getAnnotatedTypes ⟨rows⟩ subject := by
  unfold getAnnotatedTypes
  apply filterMap_capture
  intro row irrelevant
  split
  · simp [potentialTypingRow] at irrelevant
  · rfl

structure Published where
  rows : List Atom
  declarationRevision : Nat

def appendNative (before : Published) (row : Atom) : Published :=
  ⟨before.rows ++ [row], before.declarationRevision + if nativeDeclarationRow row then 1 else 0⟩

def appendCorrected (before : Published) (row : Atom) : Published :=
  ⟨before.rows ++ [row], before.declarationRevision + if potentialTypingRow row then 1 else 0⟩

theorem corrected_same_revision_capture (before : Published) (row : Atom)
    (sameRevision : (appendCorrected before row).declarationRevision = before.declarationRevision) :
    capture (appendCorrected before row).rows = capture before.rows := by
  cases relevant : potentialTypingRow row with
  | true => simp [appendCorrected, relevant] at sameRevision
  | false => simp [appendCorrected, capture, List.filter_append, relevant]

/-- A real source-query preservation law, derived from the corrected
projection and the matching-based packet factorization. -/
theorem corrected_same_revision_queries (before : Published) (row : Atom)
    (sameRevision : (appendCorrected before row).declarationRevision = before.declarationRevision)
    (subject input : Atom) (fresh : String) :
    getAnnotatedTypes ⟨(appendCorrected before row).rows⟩ subject =
      getAnnotatedTypes ⟨before.rows⟩ subject ∧
    subtypeQuery rawWorld input fresh (appendCorrected before row).rows =
      subtypeQuery rawWorld input fresh before.rows := by
  have same := corrected_same_revision_capture before row sameRevision
  constructor
  · rw [← annotations_capture, same, annotations_capture]
  · rw [← subtypeQuery_capture, same, subtypeQuery_capture]

def appendHistory (before : Published) (edits : List Atom) : Published :=
  edits.foldl appendCorrected before

theorem history_rows (edits : List Atom) : ∀ before,
    (appendHistory before edits).rows = before.rows ++ edits := by
  induction edits with
  | nil => intro before; simp [appendHistory]
  | cons row edits ih =>
      intro before
      simpa [appendHistory, appendCorrected, List.append_assoc] using ih (appendCorrected before row)

theorem history_revision (edits : List Atom) : ∀ before,
    (appendHistory before edits).declarationRevision =
      before.declarationRevision + (capture edits).length := by
  induction edits with
  | nil => intro before; simp [appendHistory, capture]
  | cons row edits ih =>
      intro before
      have tail := ih (appendCorrected before row)
      cases relevant : potentialTypingRow row <;>
        simpa [appendHistory, appendCorrected, capture, relevant, Nat.add_assoc, Nat.add_left_comm,
          Nat.add_comm] using tail

theorem history_same_revision_capture (before : Published) (edits : List Atom)
    (sameRevision : (appendHistory before edits).declarationRevision = before.declarationRevision) :
    capture (appendHistory before edits).rows = capture before.rows := by
  rw [history_revision] at sameRevision
  have noEdits : capture edits = [] := by
    have zero : (capture edits).length = 0 := by omega
    exact List.length_eq_zero_iff.mp zero
  rw [history_rows]
  simpa only [capture, List.filter_append, noEdits, List.append_nil] using
    congrArg (capture before.rows ++ ·) noEdits

theorem history_same_revision_queries (before : Published) (edits : List Atom)
    (sameRevision : (appendHistory before edits).declarationRevision = before.declarationRevision)
    (subject input : Atom) (fresh : String) :
    getAnnotatedTypes ⟨(appendHistory before edits).rows⟩ subject = getAnnotatedTypes ⟨before.rows⟩ subject ∧
      subtypeQuery rawWorld input fresh (appendHistory before edits).rows =
        subtypeQuery rawWorld input fresh before.rows := by
  have same := history_same_revision_capture before edits sameRevision
  constructor
  · rw [← annotations_capture, same, annotations_capture]
  · rw [← subtypeQuery_capture, same, subtypeQuery_capture]

namespace Controls

def initial : Published :=
  ⟨[.expression [.symbol ":<", .symbol "Unrelated", .symbol "Top"]], 7⟩

def tupleN : Atom := .expression [.symbol "H", .symbol "N"]
def tupleS : Atom := .expression [.symbol "H", .symbol "S"]
def headless : Atom := .expression [.var "row-head", tupleN, tupleS]

theorem live_projection_misses_headless_dependency :
    (appendNative initial headless).declarationRevision = initial.declarationRevision ∧
    subtypeQuery rawWorld tupleN "fresh" initial.rows = [] ∧
    subtypeQuery rawWorld tupleN "fresh" (appendNative initial headless).rows = [tupleS] := by
  cbv

theorem corrected_projection_invalidates_headless_dependency :
    (appendCorrected initial headless).declarationRevision ≠ initial.declarationRevision := by decide

theorem literal_subtype_already_invalidates :
    (appendNative initial (.expression [.symbol ":<", tupleN, tupleS])).declarationRevision =
      initial.declarationRevision + 1 := by decide

theorem unrelated_fact_keeps_packet :
    (appendCorrected initial (.expression [.symbol "note", tupleN, tupleS])).declarationRevision =
      initial.declarationRevision ∧
    capture (appendCorrected initial (.expression [.symbol "note", tupleN, tupleS])).rows =
      capture initial.rows := by decide

theorem fresh_gate_rejects_headless_row : freshScan (appendNative initial headless).rows = false := by decide

theorem unrelated_mutable_fact_is_allowed :
    freshScan [Atom.expression [.symbol "ordinary-data", RetainedTypePayloads.Controls.state "A"]] = true ∧
    capture [Atom.expression [.symbol "ordinary-data", RetainedTypePayloads.Controls.state "A"]] = [] := by decide

theorem mutable_declaration_is_rejected :
    freshScan [Atom.expression [.symbol ":", .symbol "a", RetainedTypePayloads.Controls.state "A"]] = false := by decide

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypingScopeCapture
