import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSourceVariableExecution

/-! Nested tuple/list/variant bindings retain source order. A newly bound
name shadows an outer occurrence at the correct reversed environment slot;
the wrong constructor and the shadowed outer value are both refused. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSourceBindingControls

open Mettapedia.Languages
open OCamlSourceLowering

private def number (value : Int) : OCaml.Value := .literal (.integer value)
private def pattern : OCaml.NamedPattern := .tuple [
  .variable "x", .cons (.variable "y") .wildcard, .variant 7 2 [.variable "z"]]
private def value : OCaml.Value := .tuple [
  number 3, .cons (number 4) (.literal .nil), .variant 7 2 [number 5]]
private def bindings : OCaml.NamedPattern.Bindings := [("x", number 3), ("y", number 4), ("z", number 5)]
private def outer : List (String × OCaml.Value) := [("x", number 99), ("outer", number 6)]
private def context : Context := {names := ["x", "outer"]}

theorem nested_named_matches : OCaml.NamedPattern.Matches pattern value bindings := by
  exact .tuple (.cons (.variable _ _) (.cons (.cons (.variable _ _) (.wildcard _))
    (.cons (.variant (.cons (.variable _ _) .nil)) .nil)))

theorem nested_runtime_matches : OCaml.matchPattern pattern.erase value = some (bindings.map Prod.snd) :=
  OCaml.NamedPattern.matches_erased nested_named_matches

theorem nested_slots : resolveName? (extendNames context pattern.names) "x" = some 2 ∧
    resolveName? (extendNames context pattern.names) "y" = some 1 ∧
    resolveName? (extendNames context pattern.names) "z" = some 0 := by
  simp [resolveName?, extendNames, pattern, OCaml.NamedPattern.names, context, List.idxOf?_cons]

theorem newest_x_evaluates (arena : Array OCaml.Instruction) (constructors : List OCaml.Constructor) :
    ∃ index, resolveName? (extendNames context pattern.names) "x" = some index ∧
      let installed := (OCaml.Assembly.variableRef index).run arena
      OCaml.Evaluates ⟨constructors, installed.2, installed.1⟩
        ((bindings.reverse ++ outer).map Prod.snd) installed.1 (.ok (number 3)) := by
  apply resolveName_evaluates _ (bindings.reverse ++ outer) "x" (number 3) arena constructors
  · simp [bindings, outer, extendNames, pattern, OCaml.NamedPattern.names, context]
  · exact .there (by decide) (.there (by decide) (.here _))

theorem shadowed_x_forbidden : ¬ List.NamedEnvironment.Lookup "x" (number 99) (bindings.reverse ++ outer) := by
  intro found
  have returned := (List.NamedEnvironment.lookup_iff _ _ _).mpr found
  simp [bindings, outer, List.NamedEnvironment.lookup?, List.find?, number] at returned

theorem wrong_constructor_refused : OCaml.matchPattern
    (OCaml.NamedPattern.variant 7 2 [.variable "z"]).erase (.variant 7 3 [number 5]) = none := by
  simp [OCaml.NamedPattern.erase, OCaml.matchPattern]

#print axioms nested_named_matches
#print axioms nested_runtime_matches
#print axioms nested_slots
#print axioms newest_x_evaluates
#print axioms shadowed_x_forbidden
#print axioms wrong_constructor_refused

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSourceBindingControls
