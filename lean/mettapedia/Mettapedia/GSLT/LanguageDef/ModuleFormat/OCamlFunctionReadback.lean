import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlRecursiveInstantiation
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlValueReading

/-! Generated function dispatch cannot confuse closure kinds, recursive
groups, slots or captured environments. Readback uses the actual generated
row and the independent source closure representation.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match

theorem lambda_dispatch_closure (reference : OCaml.Code) (captured : Pattern) (actual : OCaml.Value)
    (same : node "MlClosure" [node "MlLambdaFunction" [code reference], captured] = value actual) :
    ∃ sourceEnvironment, actual = .closure (.lambda reference) sourceEnvironment ∧ captured = environment sourceEnvironment := by
  cases actual with
  | literal datum =>
      have impossible := congrArg readLiteral? same
      change readLiteral? _ = readLiteral? (literal datum) at impossible
      rw [literal_roundTrip] at impossible
      simp [node, readLiteral?] at impossible
  | tuple | cons | variant => simp [value, node] at same
  | closure function actualEnvironment =>
      cases function with
      | recursive group slot => simp [value, node] at same
      | lambda actualReference =>
          have arguments := List.cons.inj (Pattern.apply.inj same).2
          have referenceSame := code_injective (List.cons.inj (Pattern.apply.inj arguments.1).2).1
          subst actualReference
          exact ⟨actualEnvironment, rfl, (List.cons.inj arguments.2).1⟩

theorem recursive_dispatch_closure (group slot : OCaml.Code) (captured : Pattern) (actual : OCaml.Value)
    (same : node "MlClosure" [node "MlRecursiveFunction" [code group, code slot], captured] = value actual) :
    ∃ sourceEnvironment, actual = .closure (.recursive group slot) sourceEnvironment ∧ captured = environment sourceEnvironment := by
  cases actual with
  | literal datum =>
      have impossible := congrArg readLiteral? same
      change readLiteral? _ = readLiteral? (literal datum) at impossible
      rw [literal_roundTrip] at impossible
      simp [node, readLiteral?] at impossible
  | tuple | cons | variant => simp [value, node] at same
  | closure function actualEnvironment =>
      cases function with
      | lambda reference => simp [value, node] at same
      | recursive actualGroup actualSlot =>
          have arguments := List.cons.inj (Pattern.apply.inj same).2
          have indices := List.cons.inj (Pattern.apply.inj arguments.1).2
          have groupSame := code_injective indices.1
          have slotSame := code_injective (List.cons.inj indices.2).1
          subst actualGroup
          subst actualSlot
          exact ⟨actualEnvironment, rfl, (List.cons.inj arguments.2).1⟩

theorem recursive_row_readback (group slot body : OCaml.Code) (definitions : List OCaml.Code)
    (parameter : OCaml.MatchPattern) (pool : List OCaml.MatchPattern) (patternCode : Pattern)
    (resolved : patternReference? pool parameter = some patternCode)
    (actualFunction argument : OCaml.Value) (continuation : Pattern) (assignment : Bindings)
    (input : applyBindings assignment (recursiveRow group slot body patternCode definitions).left =
      node "MlApply" [value actualFunction, value argument, continuation]) :
    ∃ sourceEnvironment,
      actualFunction = .closure (.recursive group slot) sourceEnvironment ∧
      applyBindings assignment (recursiveRow group slot body patternCode definitions).right =
        node "MlMatchOne" [patternCode, value argument, code body,
          environment (OCaml.recursiveEnvironment group definitions sourceEnvironment), continuation] := by
  simp only [recursiveRow, rule, apply_node, List.map_cons, List.map_nil, apply_code] at input
  have arguments := List.cons.inj (Pattern.apply.inj input).2
  have closureSame := arguments.1
  have argumentSame := (List.cons.inj arguments.2).1
  have continuationSame := (List.cons.inj (List.cons.inj arguments.2).2).1
  obtain ⟨sourceEnvironment, functionSame, environmentSame⟩ := recursive_dispatch_closure group slot _ actualFunction closureSame
  refine ⟨sourceEnvironment, functionSame, ?_⟩
  simp only [recursiveRow, rule, apply_node, List.map_cons, List.map_nil, apply_code,
    patternReference?_fixed _ resolved, apply_recursiveEnvironment,
    argumentSame, continuationSame, environmentSame, recursive_environment]

theorem lambda_row_readback (program : OCaml.Program) (pool : List OCaml.MatchPattern)
    (reference body : OCaml.Code) (parameter : OCaml.MatchPattern) (patternCode : Pattern)
    (rows : List RewriteRule) (row : RewriteRule)
    (resolved : patternReference? pool parameter = some patternCode)
    (compiled : functionRules? program pool reference (.lambda parameter body) = some rows)
    (member : row ∈ rows) (actualFunction argument : OCaml.Value) (continuation : Pattern) (assignment : Bindings)
    (input : applyBindings assignment row.left = node "MlApply" [value actualFunction, value argument, continuation]) :
    ∃ sourceEnvironment, actualFunction = .closure (.lambda reference) sourceEnvironment ∧
      applyBindings assignment row.right =
        node "MlMatchOne" [patternCode, value argument, code body, environment sourceEnvironment, continuation] := by
  rw [function_lambda_rows program reference body resolved] at compiled
  cases Option.some.inj compiled
  have rowSame := List.mem_singleton.mp member
  subst row
  simp only [rule, apply_node, List.map_cons, List.map_nil, apply_code] at input
  have arguments := List.cons.inj (Pattern.apply.inj input).2
  have argumentSame := (List.cons.inj arguments.2).1
  have continuationSame := (List.cons.inj (List.cons.inj arguments.2).2).1
  obtain ⟨sourceEnvironment, functionSame, environmentSame⟩ := lambda_dispatch_closure reference _ actualFunction arguments.1
  refine ⟨sourceEnvironment, functionSame, ?_⟩
  simp only [rule, apply_node, List.map_cons, List.map_nil, apply_code,
    patternReference?_fixed _ resolved, argumentSame, continuationSame, environmentSame]

#print axioms recursive_row_readback
#print axioms lambda_row_readback

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
