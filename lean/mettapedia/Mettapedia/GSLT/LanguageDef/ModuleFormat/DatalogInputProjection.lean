import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogRuntimeCompilerLaws

/-! Selecting declared input heads from a retained occurrence view agrees
with the complete input reader, including malformed rows and first errors. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogRuntimeCompiler

open Mettapedia.Languages.Datalog
private abbrev HostAtom := Mettapedia.Languages.MeTTa.OSLFCore.Atom

def rowHead? : HostAtom → Option String
  | .symbol head => some head
  | .expression (.symbol head :: _) => some head
  | _ => none

def inputRelevant (separator : String) (program : Program) (row : HostAtom) : Bool :=
  match rowHead? row with
  | none => false
  | some head => (inputRelations program).any (fun name => String.intercalate separator name == head)

theorem captureRow_irrelevant (separator : String) (program : Program) (row : HostAtom)
    (irrelevant : inputRelevant separator program row = false) :
    captureRow separator program row = .ok [] := by
  cases row with
  | grounded _ => rfl
  | var _ => rfl
  | symbol head =>
    change (inputRelations program).any (fun name => String.intercalate separator name == head) = false at irrelevant
    simp [captureRow, irrelevant]
    rfl
  | expression children =>
    cases children with
    | nil => rfl
    | cons first rest =>
      cases first with
      | symbol head =>
        change (inputRelations program).any (fun name => String.intercalate separator name == head) = false at irrelevant
        have absent : (inputRelations program).find?
            (fun name => String.intercalate separator name == head) = none := by
          apply List.find?_eq_none.mpr
          intro name member
          have noHead := List.any_eq_false.mp irrelevant name member
          simpa using noHead
        simp [captureRow, absent]
        rfl
      | grounded _ => rfl
      | var _ => rfl
      | expression _ => rfl

theorem capture_declared_heads (separator : String) (program : Program) (rows : List HostAtom) :
    capture separator program (rows.filter (inputRelevant separator program)) =
      capture separator program rows :=
  Mettapedia.Machines.SelectiveRowCapture.collect_filter (captureRow separator program)
    (inputRelevant separator program) (captureRow_irrelevant separator program) rows

theorem capture_index_candidates (separator : String) (program : Program)
    (possible : HostAtom → Bool)
    (complete : ∀ row, inputRelevant separator program row = true → possible row = true)
    (rows : List HostAtom) :
    capture separator program ((rows.filter possible).filter (inputRelevant separator program)) =
      capture separator program rows :=
  Mettapedia.Machines.SelectiveRowCapture.collect_candidates (captureRow separator program)
    possible (inputRelevant separator program) complete (captureRow_irrelevant separator program) rows

private def controlProgram : Program := ⟨[.declaration ⟨["Input"],[⟨"x",.symbol⟩]⟩,.input ["Input"]]⟩

example : inputRelevant ":" controlProgram (.symbol "Input") = true := by decide +kernel
example : inputRelevant ":" controlProgram (.expression [.symbol "Input"]) = true := by decide +kernel
example : inputRelevant ":" controlProgram (.expression [.symbol "Other",.var "open"]) = false := by decide +kernel
example : capture ":" controlProgram [.symbol "Input"] ≠ .ok [] := by decide +kernel

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogRuntimeCompiler
