import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogInputProjection

/-! Successful capture establishes input typing. Groundness, column types and
integer widths follow from the actual host decoder, rather than being extra
premises imposed on an already accepted captured input. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogRuntimeCompiler

open Mettapedia.Languages.Datalog
private abbrev HostAtom := Mettapedia.Languages.MeTTa.OSLFCore.Atom

theorem hostValues_typed (types : List AttributeType) (rows : List HostAtom)
    (values : List Mettapedia.Languages.Datalog.Value)
    (arity : types.length = rows.length)
    (read : (types.zip rows).mapM (fun (type, row) => hostValue type row) = some values) :
    List.Forall₂ StaticTyping.ValueTyped values types := by
  induction types generalizing rows values with
  | nil =>
    cases rows with
    | nil => cases Option.some.inj read; exact .nil
    | cons row rest => simp at arity
  | cons type types ih =>
    cases rows with
    | nil => simp at arity
    | cons row rows =>
      have tailArity : types.length = rows.length := Nat.succ.inj arity
      cases first : hostValue type row with
      | none => simp [List.zip_cons_cons, List.mapM_cons, first] at read
      | some value =>
        cases tail : (types.zip rows).mapM (fun (type,row) => hostValue type row) with
        | none => simp [List.zip_cons_cons, List.mapM_cons, first, tail] at read
        | some rest =>
          have same : value :: rest = values := by
            simpa [List.zip_cons_cons, List.mapM_cons, first, tail] using read
          subst values
          exact .cons (hostValue_typed type row value first) (ih rows rest tailArity tail)

theorem captureRow_typed (separator : String) (program : Program) (row : HostAtom)
    (facts : List GroundFact) (read : captureRow separator program row = .ok facts) :
    ∀ fact ∈ facts, StaticTyping.FactTyped (ProgramStatic.signature program) fact := by
  cases row with
  | grounded _ => cases Except.ok.inj read; simp
  | var _ => cases Except.ok.inj read; simp
  | symbol head =>
    cases selected : (inputRelations program).any (fun name => String.intercalate separator name == head)
    · simp [captureRow, selected] at read
      cases Except.ok.inj read
      simp
    · simp [captureRow, selected] at read
  | expression children =>
    cases children with
    | nil => cases Except.ok.inj read; simp
    | cons first rows =>
      cases first with
      | grounded _ => cases Except.ok.inj read; simp
      | var _ => cases Except.ok.inj read; simp
      | expression _ => cases Except.ok.inj read; simp
      | symbol head =>
        cases selected : (inputRelations program).find? (fun name => String.intercalate separator name == head) with
        | none =>
          simp [captureRow, selected] at read
          cases Except.ok.inj read
          simp
        | some name =>
          cases declared : ProgramStatic.signature program name with
          | none => simp [captureRow, selected, declared] at read
          | some types =>
            cases arity : types.length == rows.length with
            | false =>
              simp [captureRow, selected, declared, arity] at read
              cases read
            | true =>
              cases decoded : (types.zip rows).mapM (fun (type,row) => hostValue type row) with
              | none => simp [captureRow, selected, declared, arity, decoded] at read
              | some values =>
                have same : [GroundFact.mk name values] = facts := by
                  simp [captureRow, selected, declared, arity, decoded] at read
                  exact Except.ok.inj read
                subst facts
                intro fact member
                have sameFact := List.mem_singleton.mp member
                subst fact
                exact ⟨types, declared, hostValues_typed types rows values (by simpa using arity) decoded⟩

theorem capture_typed (separator : String) (program : Program) (rows : List HostAtom)
    (facts : List GroundFact) (read : capture separator program rows = .ok facts) :
    ∀ fact ∈ facts, StaticTyping.FactTyped (ProgramStatic.signature program) fact := by
  induction rows generalizing facts with
  | nil => cases Except.ok.inj read; simp
  | cons row rows ih =>
    change Mettapedia.Machines.SelectiveRowCapture.collect (captureRow separator program) (row :: rows) = .ok facts at read
    rw [Mettapedia.Machines.SelectiveRowCapture.collect_cons] at read
    change (do
      let head ← captureRow separator program row
      let tail ← capture separator program rows
      pure (head ++ tail)) = .ok facts at read
    cases first : captureRow separator program row with
    | error reason =>
      rw [first] at read
      cases read
    | ok firstFacts =>
      cases tail : capture separator program rows with
      | error reason =>
        rw [first, tail] at read
        cases read
      | ok rest =>
        rw [first, tail] at read
        have same : firstFacts ++ rest = facts := Except.ok.inj read
        subst facts
        intro fact member
        exact (List.mem_append.mp member).elim
          (captureRow_typed separator program row firstFacts first fact)
          (ih rest tail fact)

#print axioms hostValues_typed
#print axioms captureRow_typed
#print axioms capture_typed

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogRuntimeCompiler
