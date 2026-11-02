import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedCallPaths
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedMatchFailure

/-! Source-authorized cached failures complete the actual closure and let
paths to Match_failure. The failed source body is never entered, and a
source fault is independent of the target's administrative path length.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem prepared_let_failure_path (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (index : Nat) (parameter : OCaml.MatchPattern)
    (body : OCaml.Code) (captured : OCaml.Environment) (argument : OCaml.Value)
    (rest : OCaml.Continuation) (encodedRest : Pattern) (built : prepare program = .ok prepared)
    (signatures : table.signatures = provider.signatures) (meaning : ProviderMeaning (patterns program) table)
    (indexed : (patterns program)[index]? = some parameter)
    (referenced : patternReference? (patterns program) parameter = some (patternId index))
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (cached : failureRow index argument ∈ table.rows) :
    OCaml.machineStep program (.returned argument (.letValue parameter body captured :: rest)) =
      .ok (some (.halted (.error .matchFailure))) ∧
    Relation.ReflTransGen (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step
      (node "MlReturn" [value argument, node "MlKLet" [patternId index, code body, environment captured, encodedRest]])
      (node "MlFault" [fault .matchFailure]) := by
  have failed := meaning.2 index parameter argument indexed cached
  constructor
  · simp only [OCaml.machineStep, OCaml.returnValue, OCaml.enterBody, failed]
    rfl
  · exact (Relation.ReflTransGen.single (prepared_return_let_step program prepared table parameter (patternId index)
      argument body captured rest encodedRest built signatures referenced resolved)).trans
      (Relation.ReflTransGen.single (prepared_match_failure_step program prepared table index parameter argument body captured rest
        encodedRest built signatures referenced resolved cached))

theorem prepared_lambda_failure_path (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (reference body : OCaml.Code) (index : Nat) (parameter : OCaml.MatchPattern)
    (captured : OCaml.Environment) (argument : OCaml.Value) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (built : prepare program = .ok prepared) (signatures : table.signatures = provider.signatures)
    (meaning : ProviderMeaning (patterns program) table)
    (declared : program.instruction? reference = some (.lambda parameter body))
    (indexed : (patterns program)[index]? = some parameter)
    (referenced : patternReference? (patterns program) parameter = some (patternId index))
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (cached : failureRow index argument ∈ table.rows) :
    OCaml.machineStep program (.returned (.closure (.lambda reference) captured) (.function argument :: rest)) =
      .ok (some (.halted (.error .matchFailure))) ∧
    Relation.ReflTransGen (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step
      (node "MlReturn" [value (.closure (.lambda reference) captured), node "MlKFunction" [value argument, encodedRest]])
      (node "MlFault" [fault .matchFailure]) := by
  have failed := meaning.2 index parameter argument indexed cached
  constructor
  · simp [OCaml.machineStep, OCaml.returnValue, OCaml.applyClosure, declared, OCaml.enterBody, failed]
    rfl
  · obtain ⟨actualIndex, actualReference, _, dispatch⟩ := prepared_lambda_dispatch_step program prepared table reference body
      parameter captured argument rest encodedRest built signatures declared resolved
    have same : actualIndex = index := patternId_injective (Option.some.inj (actualReference.symm.trans referenced))
    subst actualIndex
    exact (Relation.ReflTransGen.single (prepared_return_function_step program prepared table (.closure (.lambda reference) captured)
      argument rest encodedRest built signatures resolved)).trans
      ((Relation.ReflTransGen.single dispatch).trans
        (Relation.ReflTransGen.single (prepared_match_failure_step program prepared table index parameter argument body captured rest
          encodedRest built signatures referenced resolved cached)))

theorem prepared_recursive_failure_path (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (group groupBody slot reference body : OCaml.Code) (index : Nat)
    (definitions : List OCaml.Code) (parameter : OCaml.MatchPattern) (captured : OCaml.Environment)
    (argument : OCaml.Value) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (built : prepare program = .ok prepared) (signatures : table.signatures = provider.signatures)
    (meaning : ProviderMeaning (patterns program) table)
    (declaredGroup : program.instruction? group = some (.letRecursive definitions groupBody))
    (declaredSlot : definitions[slot]? = some reference)
    (declaredFunction : program.instruction? reference = some (.lambda parameter body))
    (indexed : (patterns program)[index]? = some parameter)
    (referenced : patternReference? (patterns program) parameter = some (patternId index))
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (cached : failureRow index argument ∈ table.rows) :
    OCaml.machineStep program (.returned (.closure (.recursive group slot) captured) (.function argument :: rest)) =
      .ok (some (.halted (.error .matchFailure))) ∧
    Relation.ReflTransGen (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step
      (node "MlReturn" [value (.closure (.recursive group slot) captured), node "MlKFunction" [value argument, encodedRest]])
      (node "MlFault" [fault .matchFailure]) := by
  have failed := meaning.2 index parameter argument indexed cached
  constructor
  · simp [OCaml.machineStep, OCaml.returnValue, OCaml.applyClosure, declaredGroup, declaredSlot, declaredFunction,
      OCaml.enterBody, failed]
    rfl
  · obtain ⟨actualIndex, actualReference, _, dispatch⟩ := prepared_recursive_dispatch_step program prepared table group groupBody slot
      reference body definitions parameter captured argument rest encodedRest built signatures declaredGroup declaredSlot declaredFunction resolved
    have same : actualIndex = index := patternId_injective (Option.some.inj (actualReference.symm.trans referenced))
    subst actualIndex
    exact (Relation.ReflTransGen.single (prepared_return_function_step program prepared table (.closure (.recursive group slot) captured)
      argument rest encodedRest built signatures resolved)).trans
      ((Relation.ReflTransGen.single dispatch).trans
        (Relation.ReflTransGen.single (prepared_match_failure_step program prepared table index parameter argument body
          (OCaml.recursiveEnvironment group definitions captured) rest encodedRest built signatures referenced resolved cached)))

#print axioms prepared_let_failure_path
#print axioms prepared_lambda_failure_path
#print axioms prepared_recursive_failure_path

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
