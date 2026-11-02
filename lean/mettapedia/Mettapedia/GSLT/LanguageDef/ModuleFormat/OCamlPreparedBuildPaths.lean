import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedBuildSteps

/-! Final tuple and variant gathering realizes one source-machine step
through two administrative GSLT steps. Source arity and constructor
formation are explicit; the ordered value suffix and continuation agree.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem prepared_tuple_return_success_path (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (actual : OCaml.Value) (capturedEnvironment : OCaml.Environment)
    (suffix : List OCaml.Value) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (built : prepare program = .ok prepared) (signatures : table.signatures = provider.signatures)
    (formed : 2 ≤ (actual :: suffix).length) (resolved : continuation? (patterns program) rest = some encodedRest) :
    OCaml.machineStep program (.returned actual (.gather .tuple [] capturedEnvironment suffix :: rest)) =
      .ok (some (.returned (.tuple (actual :: suffix)) rest)) ∧
    state? (patterns program) (.returned (.tuple (actual :: suffix)) rest) =
      some (node "MlReturn" [value (.tuple (actual :: suffix)), encodedRest]) ∧
    Relation.ReflTransGen (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step
      (node "MlReturn" [value actual, node "MlKBuild" [build .tuple, codes [], environment capturedEnvironment, valueList suffix, encodedRest]])
      (node "MlReturn" [value (.tuple (actual :: suffix)), encodedRest]) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [OCaml.machineStep, OCaml.returnValue, OCaml.finishBuild, if_neg (Nat.not_lt.mpr formed)]
    rfl
  · simp only [state?, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  · exact (Relation.ReflTransGen.single
      (prepared_last_gather_step program prepared table .tuple actual capturedEnvironment suffix rest encodedRest built signatures resolved)).trans
      (Relation.ReflTransGen.single
        (prepared_tuple_build_step program prepared table (actual :: suffix) rest encodedRest built signatures resolved))

theorem prepared_variant_return_success_path (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (typeId constructor : Nat) (actual : OCaml.Value)
    (capturedEnvironment : OCaml.Environment) (suffix : List OCaml.Value) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (built : prepare program = .ok prepared) (signatures : table.signatures = provider.signatures)
    (formed : program.constructorDeclared typeId constructor (actual :: suffix).length = true)
    (resolved : continuation? (patterns program) rest = some encodedRest) :
    OCaml.machineStep program (.returned actual (.gather (.variant typeId constructor) [] capturedEnvironment suffix :: rest)) =
      .ok (some (.returned (.variant typeId constructor (actual :: suffix)) rest)) ∧
    state? (patterns program) (.returned (.variant typeId constructor (actual :: suffix)) rest) =
      some (node "MlReturn" [value (.variant typeId constructor (actual :: suffix)), encodedRest]) ∧
    Relation.ReflTransGen (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step
      (node "MlReturn" [value actual, node "MlKBuild" [build (.variant typeId constructor), codes [],
        environment capturedEnvironment, valueList suffix, encodedRest]])
      (node "MlReturn" [value (.variant typeId constructor (actual :: suffix)), encodedRest]) := by
  have declared : program.constructors.any (fun row => row.typeId == typeId && row.ordinal == constructor &&
      row.arity == (actual :: suffix).length) = true := formed
  refine ⟨?_, ?_, ?_⟩
  · simp only [OCaml.machineStep, OCaml.returnValue, OCaml.finishBuild, declared, if_true]
    rfl
  · simp only [state?, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  · exact (Relation.ReflTransGen.single
      (prepared_last_gather_step program prepared table (.variant typeId constructor) actual capturedEnvironment suffix rest encodedRest
        built signatures resolved)).trans
      (Relation.ReflTransGen.single
        (prepared_variant_build_step program prepared table typeId constructor (actual :: suffix) rest encodedRest built signatures resolved))

#print axioms prepared_tuple_return_success_path
#print axioms prepared_variant_return_success_path

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
