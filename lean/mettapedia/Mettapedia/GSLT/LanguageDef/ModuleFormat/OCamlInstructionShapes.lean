import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlEncodedShapes
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlFreeNames

/-! Indexed instruction compilation produces premise-free ordinary
constructor/vector rules. This covers every instruction form, including
environment lookup prefixes and ordered argument-gathering requests.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match
open Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

theorem startArguments_vector (kind : Pattern) (references : List OCaml.Code) (captured rest : Pattern)
    (kindShape : VectorFirstOrder kind) (capturedShape : VectorFirstOrder captured) (restShape : VectorFirstOrder rest) :
    VectorFirstOrder (startArguments kind references captured rest) := by
  unfold startArguments
  cases references.reverse with
  | nil =>
      exact node_vector_all _ _ (vector_list_cons kindShape
        (vector_list_cons (.constructor _ [] (by simp)) (vector_list_cons restShape vector_list_nil)))
  | cons last later =>
      exact node_vector_all _ _ (vector_list_cons (code_vector last) (vector_list_cons capturedShape
        (vector_list_cons (node_vector_all _ _ (vector_list_cons kindShape (vector_list_cons (codes_vector later)
          (vector_list_cons capturedShape (vector_list_cons (.constructor _ [] (by simp))
            (vector_list_cons restShape vector_list_nil)))))) vector_list_nil)))

theorem instruction_shapes (pool : List OCaml.MatchPattern) (reference : OCaml.Code) (instruction : OCaml.Instruction)
    (compiled : RewriteRule) (formed : compileInstruction? pool reference instruction = some compiled) :
    VectorFirstOrder compiled.left ∧ VectorFirstOrder compiled.right ∧ compiled.premises = [] ∧
      compiled.typeContext = [] ∧ compiled.bindings = none := by
  cases instruction with
  | letValue parameter argument body =>
      cases resolved : patternReference? pool parameter with
      | none => simp [compileInstruction?, resolved] at formed
      | some encoded =>
          simp only [compileInstruction?, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at formed
          cases formed
          refine ⟨?_, ?_, rfl, rfl, rfl⟩
          · exact node_vector_all _ _ (vector_list_cons (code_vector reference)
              (vector_list_cons (.metavariable _) (vector_list_cons (.metavariable _) vector_list_nil)))
          · exact node_vector_all _ _ (vector_list_cons (code_vector argument) (vector_list_cons (.metavariable _)
              (vector_list_cons (node_vector_all _ _ (vector_list_cons (pattern_reference_vector resolved)
                (vector_list_cons (code_vector body) (vector_list_cons (.metavariable _)
                  (vector_list_cons (.metavariable _) vector_list_nil))))) vector_list_nil)))
  | matchValue scrutinee clauses =>
      cases resolved : clauseList? pool clauses with
      | none => simp [compileInstruction?, resolved] at formed
      | some encoded =>
          simp only [compileInstruction?, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at formed
          cases formed
          refine ⟨?_, ?_, rfl, rfl, rfl⟩
          · exact node_vector_all _ _ (vector_list_cons (code_vector reference)
              (vector_list_cons (.metavariable _) (vector_list_cons (.metavariable _) vector_list_nil)))
          · exact node_vector_all _ _ (vector_list_cons (code_vector scrutinee) (vector_list_cons (.metavariable _)
              (vector_list_cons (node_vector_all _ _ (vector_list_cons (clauseList?_vector pool clauses encoded resolved)
                (vector_list_cons (.metavariable _) (vector_list_cons (.metavariable _) vector_list_nil)))) vector_list_nil)))
  | «variable» index =>
      simp only [compileInstruction?, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at formed
      cases formed
      refine ⟨?_, ?_, rfl, rfl, rfl⟩
      · apply node_vector_all
        refine vector_list_cons (code_vector reference) (vector_list_cons ?_ (vector_list_cons (.metavariable _) vector_list_nil))
        apply extend_vector
        · intro item member
          obtain ⟨skip, _, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp member)
          exact .metavariable _
        · exact node_vector_all _ _ (vector_list_cons (.metavariable _) (vector_list_cons (.metavariable _) vector_list_nil))
      · exact node_vector_all _ _ (vector_list_cons (.metavariable _) (vector_list_cons (.metavariable _) vector_list_nil))
  | literal datum =>
      simp only [compileInstruction?, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at formed
      cases formed
      exact ⟨node_vector_all _ _ (vector_list_cons (code_vector reference)
        (vector_list_cons (.metavariable _) (vector_list_cons (.metavariable _) vector_list_nil))),
        node_vector_all _ _ (vector_list_cons (literal_vector datum) (vector_list_cons (.metavariable _) vector_list_nil)), rfl, rfl, rfl⟩
  | lambda parameter body =>
      simp only [compileInstruction?, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at formed
      cases formed
      exact ⟨node_vector_all _ _ (vector_list_cons (code_vector reference)
        (vector_list_cons (.metavariable _) (vector_list_cons (.metavariable _) vector_list_nil))),
        node_vector_all _ _ (vector_list_cons (node_vector_all _ _ (vector_list_cons
          (node_vector_all _ _ (vector_list_cons (code_vector reference) vector_list_nil))
          (vector_list_cons (.metavariable _) vector_list_nil))) (vector_list_cons (.metavariable _) vector_list_nil)), rfl, rfl, rfl⟩
  | letRecursive definitions body =>
      simp only [compileInstruction?, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at formed
      cases formed
      exact ⟨node_vector_all _ _ (vector_list_cons (code_vector reference)
        (vector_list_cons (.metavariable _) (vector_list_cons (.metavariable _) vector_list_nil))),
        node_vector_all _ _ (vector_list_cons (code_vector body)
          (vector_list_cons (recursive_environment_vector reference definitions _ (.metavariable _))
            (vector_list_cons (.metavariable _) vector_list_nil))), rfl, rfl, rfl⟩
  | tuple fields =>
      simp only [compileInstruction?, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at formed
      cases formed
      exact ⟨node_vector_all _ _ (vector_list_cons (code_vector reference)
        (vector_list_cons (.metavariable _) (vector_list_cons (.metavariable _) vector_list_nil))),
        startArguments_vector _ fields _ _ (.constructor _ [] (by simp)) (.metavariable _) (.metavariable _), rfl, rfl, rfl⟩
  | variant typeId constructor fields =>
      simp only [compileInstruction?, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at formed
      cases formed
      exact ⟨node_vector_all _ _ (vector_list_cons (code_vector reference)
        (vector_list_cons (.metavariable _) (vector_list_cons (.metavariable _) vector_list_nil))),
        startArguments_vector _ fields _ _ (node_vector_all _ _ (vector_list_cons (tag_vector typeId constructor) vector_list_nil))
          (.metavariable _) (.metavariable _), rfl, rfl, rfl⟩
  | primitive operator arguments =>
      simp only [compileInstruction?, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at formed
      cases formed
      exact ⟨node_vector_all _ _ (vector_list_cons (code_vector reference)
        (vector_list_cons (.metavariable _) (vector_list_cons (.metavariable _) vector_list_nil))),
        startArguments_vector _ arguments _ _ (node_vector_all _ _ (vector_list_cons (primitive_vector operator) vector_list_nil))
          (.metavariable _) (.metavariable _), rfl, rfl, rfl⟩
  | apply function argument =>
      simp only [compileInstruction?, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at formed
      cases formed
      exact ⟨node_vector_all _ _ (vector_list_cons (code_vector reference)
        (vector_list_cons (.metavariable _) (vector_list_cons (.metavariable _) vector_list_nil))),
        node_vector_all _ _ (vector_list_cons (code_vector argument) (vector_list_cons (.metavariable _)
          (vector_list_cons (node_vector_all _ _ (vector_list_cons (code_vector function)
            (vector_list_cons (.metavariable _) (vector_list_cons (.metavariable _) vector_list_nil)))) vector_list_nil))), rfl, rfl, rfl⟩
  | branch condition yes no =>
      simp only [compileInstruction?, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at formed
      cases formed
      exact ⟨node_vector_all _ _ (vector_list_cons (code_vector reference)
        (vector_list_cons (.metavariable _) (vector_list_cons (.metavariable _) vector_list_nil))),
        node_vector_all _ _ (vector_list_cons (code_vector condition) (vector_list_cons (.metavariable _)
          (vector_list_cons (node_vector_all _ _ (vector_list_cons (code_vector yes) (vector_list_cons (code_vector no)
            (vector_list_cons (.metavariable _) (vector_list_cons (.metavariable _) vector_list_nil))))) vector_list_nil))), rfl, rfl, rfl⟩
  | andThen left right =>
      simp only [compileInstruction?, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at formed
      cases formed
      exact ⟨node_vector_all _ _ (vector_list_cons (code_vector reference)
        (vector_list_cons (.metavariable _) (vector_list_cons (.metavariable _) vector_list_nil))),
        node_vector_all _ _ (vector_list_cons (code_vector left) (vector_list_cons (.metavariable _)
          (vector_list_cons (node_vector_all _ _ (vector_list_cons (code_vector right)
            (vector_list_cons (.metavariable _) (vector_list_cons (.metavariable _) vector_list_nil)))) vector_list_nil))), rfl, rfl, rfl⟩
  | orElse left right =>
      simp only [compileInstruction?, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at formed
      cases formed
      exact ⟨node_vector_all _ _ (vector_list_cons (code_vector reference)
        (vector_list_cons (.metavariable _) (vector_list_cons (.metavariable _) vector_list_nil))),
        node_vector_all _ _ (vector_list_cons (code_vector left) (vector_list_cons (.metavariable _)
          (vector_list_cons (node_vector_all _ _ (vector_list_cons (code_vector right)
            (vector_list_cons (.metavariable _) (vector_list_cons (.metavariable _) vector_list_nil)))) vector_list_nil))), rfl, rfl, rfl⟩
  | cons head tail =>
      simp only [compileInstruction?, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at formed
      cases formed
      exact ⟨node_vector_all _ _ (vector_list_cons (code_vector reference)
        (vector_list_cons (.metavariable _) (vector_list_cons (.metavariable _) vector_list_nil))),
        node_vector_all _ _ (vector_list_cons (code_vector tail) (vector_list_cons (.metavariable _)
          (vector_list_cons (node_vector_all _ _ (vector_list_cons (code_vector head)
            (vector_list_cons (.metavariable _) (vector_list_cons (.metavariable _) vector_list_nil)))) vector_list_nil))), rfl, rfl, rfl⟩

#print axioms instruction_shapes

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
