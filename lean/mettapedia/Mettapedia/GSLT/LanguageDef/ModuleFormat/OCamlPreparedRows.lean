import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparationReadback

/-! Every source instruction and resolved pattern has its actual generated
row in a successful prepared compiler result. Row positions remain source
compiler evidence; execution-plan admission is the next boundary.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem except_mapM_member_image {α β : Type} (inputs : List α) (emit : α → Except String β) (outputs : List β)
    (read : inputs.mapM emit = .ok outputs) (input : α) (present : input ∈ inputs) :
    ∃ output ∈ outputs, emit input = .ok output := by
  induction inputs generalizing outputs with
  | nil => cases present
  | cons first rest ih =>
      cases firstRead : emit first with
      | error error => simp only [List.mapM_cons, firstRead, bind, Except.bind] at read; cases read
      | ok head =>
          cases restRead : rest.mapM emit with
          | error error => simp only [List.mapM_cons, firstRead, restRead, bind, Except.bind] at read; cases read
          | ok tail =>
              have same : head :: tail = outputs := by
                simpa only [List.mapM_cons, firstRead, restRead, bind, Except.bind, pure, Except.pure, Except.ok.injEq] using read
              subst outputs
              rcases List.mem_cons.mp present with rfl | later
              · exact ⟨head, List.mem_cons_self, firstRead⟩
              · obtain ⟨output, member, found⟩ := ih tail restRead later
                exact ⟨output, List.mem_cons_of_mem head member, found⟩

theorem prepared_instruction_row (program : OCaml.Program) (prepared : Prepared) (reference : OCaml.Code)
    (instruction : OCaml.Instruction) (built : prepare program = .ok prepared)
    (declared : program.instruction? reference = some instruction) :
    ∃ row ∈ prepared.compiled.rewrites,
      compileInstruction? (patterns program) reference instruction = some row := by
  obtain ⟨_, _, _, _, dispatch, functions, dispatchRead, _, rows⟩ := prepare_readback program prepared built
  have indexed : (instruction, reference) ∈ program.code.toList.zipIdx := by
    apply List.mk_mem_zipIdx_iff_getElem?.mpr
    simpa only [OCaml.Program.instruction?, Array.getElem?_toList] using declared
  obtain ⟨row, member, emitted⟩ := except_mapM_member_image _ _ dispatch dispatchRead (instruction, reference) indexed
  have formed : compileInstruction? (patterns program) reference instruction = some row := by
    cases actual : compileInstruction? (patterns program) reference instruction with
    | none => simp [actual] at emitted
    | some candidate =>
        have same : candidate = row := by simpa only [actual, pure, Except.pure, Except.ok.injEq] using emitted
        exact congrArg some same
  refine ⟨row, ?_, formed⟩
  rw [rows]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ member))

theorem prepared_pattern_rows (program : OCaml.Program) (prepared : Prepared) (index : Nat) (parameter : OCaml.MatchPattern)
    (built : prepare program = .ok prepared) (indexed : (patterns program)[index]? = some parameter) :
    ∀ row ∈ patternRules index parameter, row ∈ prepared.compiled.rewrites := by
  obtain ⟨_, _, _, _, dispatch, functions, _, _, rows⟩ := prepare_readback program prepared built
  intro row member
  rw [rows]
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  exact ⟨(parameter, index), List.mk_mem_zipIdx_iff_getElem?.mpr indexed, member⟩

theorem prepared_function_rows (program : OCaml.Program) (prepared : Prepared) (reference : OCaml.Code)
    (instruction : OCaml.Instruction) (built : prepare program = .ok prepared)
    (declared : program.instruction? reference = some instruction) :
    ∃ rows, functionRules? program (patterns program) reference instruction = some rows ∧
      ∀ row ∈ rows, row ∈ prepared.compiled.rewrites := by
  obtain ⟨_, _, _, _, dispatch, functions, _, functionsRead, allRows⟩ := prepare_readback program prepared built
  have indexed : (instruction, reference) ∈ program.code.toList.zipIdx := by
    apply List.mk_mem_zipIdx_iff_getElem?.mpr
    simpa only [OCaml.Program.instruction?, Array.getElem?_toList] using declared
  obtain ⟨rows, member, emitted⟩ := except_mapM_member_image _ _ functions functionsRead (instruction, reference) indexed
  have formed : functionRules? program (patterns program) reference instruction = some rows := by
    cases actual : functionRules? program (patterns program) reference instruction with
    | none => simp [actual] at emitted
    | some candidate =>
        have same : candidate = rows := by simpa only [actual, pure, Except.pure, Except.ok.injEq] using emitted
        exact congrArg some same
  refine ⟨rows, formed, ?_⟩
  intro row present
  rw [allRows]
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_flatten.mpr ⟨rows, member, present⟩))

#print axioms prepared_instruction_row
#print axioms prepared_pattern_rows
#print axioms prepared_function_rows

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
