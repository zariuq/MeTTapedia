import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlExecutionData

/-! Accepted O0 module text reads back to its complete emitted program:
the shared step entries and the ordinary begin/run wrapper. Namespace
checks include the loaded O0 controller, not only the common step runtime.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlEmissionReadback

open Mettapedia.GSLT.LanguageDef ModuleFormat.OCamlCompilation
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open ExecutionData

theorem emitted_program {prepared : Prepared} {name : String} {emitted : SpaceSemantics.Program}
    (built : emit? prepared name = .ok emitted) :
    emitted = program prepared name ∧ ((library prepared name).check && wrapperReady prepared name) = true ∧
      CompleteEmission.Emitted (spec prepared) (name ++ ":step") .classes := by
  cases selected : CompleteEmission.emit? (spec prepared) (name ++ ":step") .classes with
  | error refusal => simp [emit?, selected] at built
  | ok kernel =>
    obtain ⟨same, admitted⟩ := CompleteEmission.emit?_ok selected
    cases checked : ((library prepared name).check && wrapperReady prepared name) with
    | false => simp [emit?, selected, checked] at built
    | true =>
      have output : program prepared name = emitted := by
        simpa [emit?, selected, checked, program, same] using built
      exact ⟨output.symm, rfl, admitted⟩

theorem program_expressions (prepared : Prepared) (name : String) :
    ReadAfterRender.AllExpressions (SpaceSemantics.loadedAtoms (program prepared name)) := by
  intro atom member
  change atom ∈ [
    CompleteEmission.declaration (CompleteEmission.beginHead (name ++ ":step")) 1,
    (CompleteEmission.beginEquation (spec prepared) (name ++ ":step") .classes).toAtom,
    CompleteEmission.declaration (CompleteEmission.runHead (name ++ ":step")) 3,
    (CompleteEmission.runEquation (spec prepared) (name ++ ":step") .classes).toAtom,
    CompleteEmission.declaration (CompleteEmission.exploreHead (name ++ ":step")) 2,
    (CompleteEmission.exploreEquation (spec prepared) (name ++ ":step") .classes).toAtom,
    CompleteEmission.declaration (CompleteEmission.edgesHead (name ++ ":step")) 2,
    (CompleteEmission.edgesEquation (spec prepared) (name ++ ":step") .classes).toAtom,
    CompleteEmission.declaration (beginHead name) 0,
    SpaceSemantics.Equation.toAtom ⟨beginHead name, [], beginBody prepared⟩,
    .expression [.symbol ":", .symbol (runHead name),
      .expression [.symbol "->", .symbol "Number", .symbol "Number", .symbol "%Undefined%"]],
    SpaceSemantics.Equation.toAtom ⟨runHead name, [.var "ticks", .var "quantum"], runBody name⟩] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩

theorem program_collect (prepared : Prepared) (name : String) :
    SpaceSemantics.collect (SpaceSemantics.loadedAtoms (program prepared name)) = .ok (program prepared name) := by rfl

theorem emitted_text_reads_back {prepared : Prepared} {name text : String}
    (built : emitText? prepared name = .ok text) :
    SpaceSemantics.readProgram text = .ok (program prepared name) := by
  unfold emitText? at built
  cases emitted : emit? prepared name with
  | error reason => simp [emitted] at built
  | ok produced =>
    obtain ⟨rfl, _, _⟩ := emitted_program emitted
    simp only [emitted] at built
    cases rendered : ReadAfterRender.renderProgram? (program prepared name) with
    | none => simp [rendered] at built
    | some output =>
      rw [rendered] at built
      cases built
      rw [ReadAfterRender.read_render rendered (program_expressions prepared name), program_collect]
      rfl

#print axioms emitted_program
#print axioms program_expressions
#print axioms program_collect
#print axioms emitted_text_reads_back

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlEmissionReadback
