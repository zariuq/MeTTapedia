import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedBuildSteps
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedPrimitiveQuery
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSourceProviderInvariant

/-! Completing a primitive gather realizes its independent source-machine
step through build, provider query and answer consumption. Cached source
results include both ordinary values and language faults.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem prepared_primitive_return_path (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (operator : OCaml.Primitive) (actual : OCaml.Value)
    (captured : OCaml.Environment) (suffix : List OCaml.Value) (result : OCaml.Result)
    (rest : OCaml.Continuation) (encodedRest : Pattern) (built : prepare program = .ok prepared)
    (invariant : SourceProviderInvariant (patterns program) table)
    (cached : primitiveRow operator (actual :: suffix) result ∈ table.rows)
    (resolved : continuation? (patterns program) rest = some encodedRest) :
    OCaml.machineStep program (.returned actual (.gather (.primitive operator) [] captured suffix :: rest)) =
      .ok (some (finishPrimitive result rest)) ∧
    ∃ target, state? (patterns program) (finishPrimitive result rest) = some target ∧
      Relation.ReflTransGen (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step
        (node "MlReturn" [value actual, node "MlKBuild" [build (.primitive operator), codes [], environment captured,
          valueList suffix, encodedRest]]) target := by
  obtain ⟨finished, target, encoded, resultPath⟩ := prepared_cached_primitive_path program prepared table operator (actual :: suffix)
    result rest encodedRest built invariant.signatures invariant.meaningful cached resolved
  constructor
  · simp only [OCaml.machineStep, OCaml.returnValue, finished]
    rfl
  · exact ⟨target, encoded, (Relation.ReflTransGen.single (prepared_last_gather_step program prepared table (.primitive operator)
      actual captured suffix rest encodedRest built invariant.signatures resolved)).trans
      ((Relation.ReflTransGen.single (prepared_primitive_build_step program prepared table operator (actual :: suffix) rest encodedRest
        built invariant.signatures resolved)).trans resultPath)⟩

#print axioms prepared_primitive_return_path

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
