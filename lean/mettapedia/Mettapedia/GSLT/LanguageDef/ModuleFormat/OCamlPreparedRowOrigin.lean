import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedRows
import Mettapedia.Data.List.ExceptMapM

/-! Every compiled rewrite has an actual authored kernel, source
instruction, function or pattern origin. This is the inverse of row
coverage and applies to arbitrary successfully prepared programs.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem prepared_row_origin (program : OCaml.Program) (prepared : Prepared) (row : RewriteRule)
    (built : prepare program = .ok prepared) (member : row ∈ prepared.compiled.rewrites) :
    row ∈ baseLanguage.rewrites ∨
      (∃ reference instruction, program.instruction? reference = some instruction ∧
        compileInstruction? (patterns program) reference instruction = some row) ∨
      (∃ reference instruction rows, program.instruction? reference = some instruction ∧
        functionRules? program (patterns program) reference instruction = some rows ∧ row ∈ rows) ∨
      (∃ index parameter, (patterns program)[index]? = some parameter ∧ row ∈ patternRules index parameter) := by
  obtain ⟨_, _, _, _, dispatch, functions, dispatchRead, functionsRead, allRows⟩ := prepare_readback program prepared built
  rw [allRows] at member
  rcases List.mem_append.mp member with before | pattern
  · rcases List.mem_append.mp before with before | function
    · rcases List.mem_append.mp before with kernel | instruction
      · exact Or.inl kernel
      · obtain ⟨⟨source, reference⟩, indexed, emitted⟩ := Mettapedia.Data.List.mapM_success_origin _ _ _ dispatchRead row instruction
        have declared : program.instruction? reference = some source := by
          simpa only [OCaml.Program.instruction?, Array.getElem?_toList] using List.mk_mem_zipIdx_iff_getElem?.mp indexed
        apply Or.inr ∘ Or.inl
        refine ⟨reference, source, declared, ?_⟩
        cases found : compileInstruction? (patterns program) reference source with
        | none => simp [found] at emitted
        | some actual =>
          have same : actual = row := by simpa only [found, pure, Except.pure, Except.ok.injEq] using emitted
          exact congrArg some same
    · obtain ⟨rows, listed, present⟩ := List.mem_flatten.mp function
      obtain ⟨⟨source, reference⟩, indexed, emitted⟩ := Mettapedia.Data.List.mapM_success_origin _ _ _ functionsRead rows listed
      have declared : program.instruction? reference = some source := by
        simpa only [OCaml.Program.instruction?, Array.getElem?_toList] using List.mk_mem_zipIdx_iff_getElem?.mp indexed
      apply Or.inr ∘ Or.inr ∘ Or.inl
      refine ⟨reference, source, rows, declared, ?_, present⟩
      cases found : functionRules? program (patterns program) reference source with
      | none => simp [found] at emitted
      | some actual =>
        have same : actual = rows := by simpa only [found, pure, Except.pure, Except.ok.injEq] using emitted
        exact congrArg some same
  · obtain ⟨⟨parameter, index⟩, indexed, present⟩ := List.mem_flatMap.mp pattern
    exact Or.inr (Or.inr (Or.inr ⟨index, parameter, List.mk_mem_zipIdx_iff_getElem?.mp indexed, present⟩))

#print axioms prepared_row_origin

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
