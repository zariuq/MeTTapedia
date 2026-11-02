import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlEmissionReadback
import Mathlib.Data.Bool.Basic

/-! The emitted wrapper's actual rows and call contracts. Successful
emission derives namespace ownership and numeric demand from its checks.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlEmittedEntrySource

open Mettapedia.GSLT.LanguageDef ModuleFormat.OCamlCompilation
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Eval BridgeKit ExecutionData

def moduleRuntime (prepared : Prepared) (name : String) : SpaceSemantics.Program := (library prepared name).runtime

theorem checked {prepared : Prepared} {name : String} {emitted : SpaceSemantics.Program}
    (built : emit? prepared name = .ok emitted) : (library prepared name).check = true :=
  (Bool.and_eq_true_iff.mp (OCamlEmissionReadback.emitted_program built).2.1).1

theorem call_contracts {prepared : Prepared} {name : String} {emitted : SpaceSemantics.Program}
    (built : emit? prepared name = .ok emitted) :
    (library prepared name).headReady (beginHead name) = true ∧
      ((library prepared name).equationOf (runHead name)).any (Library.demandReady (library prepared name)) = true ∧
      argumentIsRaw (moduleRuntime prepared name) (runHead name) 0 = false ∧
      argumentIsRaw (moduleRuntime prepared name) (runHead name) 1 = false := by
  have ready := (Bool.and_eq_true_iff.mp (OCamlEmissionReadback.emitted_program built).2.1).2
  simpa only [wrapperReady, moduleRuntime, Bool.and_eq_true, Bool.not_eq_true', and_assoc] using ready

theorem begin_equation (prepared : Prepared) (name : String) :
    (library prepared name).equationOf (beginHead name) = some ⟨beginHead name, [], beginBody prepared⟩ := by
  simp [Library.equationOf, library, program, wrapper, SpaceSemantics.Program.append,
    CompleteEmission.program, CompleteEmission.beginEquation, CompleteEmission.runEquation,
    CompleteEmission.exploreEquation, CompleteEmission.edgesEquation, CompleteEmission.beginHead,
    CompleteEmission.runHead, CompleteEmission.exploreHead, CompleteEmission.edgesHead,
    beginHead, runHead, String.append_assoc, beq_iff_eq]

theorem run_equation (prepared : Prepared) (name : String) :
    (library prepared name).equationOf (runHead name) = some ⟨runHead name, [.var "ticks", .var "quantum"], runBody name⟩ := by
  simp [Library.equationOf, library, program, wrapper, SpaceSemantics.Program.append,
    CompleteEmission.program, CompleteEmission.beginEquation, CompleteEmission.runEquation,
    CompleteEmission.exploreEquation, CompleteEmission.edgesEquation, CompleteEmission.beginHead,
    CompleteEmission.runHead, CompleteEmission.exploreHead, CompleteEmission.edgesHead,
    beginHead, runHead, String.append_assoc, beq_iff_eq]

theorem begin_body (prepared : Prepared) (name : String) :
    (library prepared name).body (beginHead name) = beginBody prepared := by
  simp only [Library.body, begin_equation, Option.map_some, Option.getD_some]

theorem run_body (prepared : Prepared) (name : String) :
    (library prepared name).body (runHead name) = runBody name := by
  simp only [Library.body, run_equation, Option.map_some, Option.getD_some]

theorem begin_formals (prepared : Prepared) (name : String) :
    (library prepared name).formals (beginHead name) = [] := by
  simp only [Library.formals, begin_equation, Option.map_some, Option.getD_some, Library.formalNames, List.filterMap_nil]

theorem run_formals (prepared : Prepared) (name : String) :
    (library prepared name).formals (runHead name) = ["ticks", "quantum"] := by
  simp only [Library.formals, run_equation, Option.map_some, Option.getD_some, Library.formalNames,
    List.filterMap_cons, List.filterMap_nil]

theorem owns_of_found {prepared : Prepared} {name : String} {emitted : SpaceSemantics.Program}
    (built : emit? prepared name = .ok emitted) {head : String} {row : SpaceSemantics.Equation}
    (found : (library prepared name).equationOf head = some row) : (library prepared name).owns head = true := by
  have parts := checked built
  simp only [Library.check, Bool.and_eq_true, and_assoc] at parts
  have member := List.mem_of_find?_eq_some found
  have same : row.head = head := by simpa only [beq_iff_eq] using List.find?_some found
  have owned := List.all_eq_true.mp parts.2.2.1 row member
  simpa only [same] using owned

theorem inherited_of_registered {prepared : Prepared} {name : String} {emitted : SpaceSemantics.Program}
    (built : emit? prepared name = .ok emitted) {head : String}
    (registered : OCamlControllerSource.runtime.equations.any (·.head == head) = true) :
    (library prepared name).inherited head = true := by
  have parts := checked built
  simp only [Library.check, Bool.and_eq_true, and_assoc] at parts
  obtain ⟨row, member, same⟩ := List.any_eq_true.mp registered
  have retained := (Bool.and_eq_true_iff.mp (List.all_eq_true.mp parts.2.1 row member)).1
  simpa only [beq_iff_eq.mp same] using retained

#print axioms checked
#print axioms call_contracts
#print axioms begin_equation
#print axioms run_equation
#print axioms begin_body
#print axioms run_body
#print axioms begin_formals
#print axioms run_formals
#print axioms owns_of_found
#print axioms inherited_of_registered

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlEmittedEntrySource
