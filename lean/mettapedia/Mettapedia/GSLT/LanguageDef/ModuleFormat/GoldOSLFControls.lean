import Mettapedia.GSLT.LanguageDef.ModuleFormat.GoldOSLF
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlProgramCompilation
import Mettapedia.Languages.OCaml.Examples

/-! Independent front-door checks of the actual indexed machine LanguageDef.
These ask the reference operational relation, not the emitted runner. More
language instances are installed with their operational IRs, not their source
grammars. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.GoldOSLF.Controls

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.OSLF.NativeTypes.GeneratedLogic
open Mettapedia.Languages
open OCamlCompilation

def structuralVerdicts : List (String × Option Bool × Option Bool) :=
  OCaml.Examples.structuralExamples.filterMap fun sample =>
    match prepare sample.program, sample.expected with
    | .ok prepared, .ok expected =>
        let target := node "MlDone" [value expected]
        let wrong := node "MlDone" [literal (.integer 123456)]
        some (sample.name,
          verdict (ask prepared.compiled provider 2 32 (reaches target) (initial sample.program)),
          verdict (ask prepared.compiled provider 2 32 (reaches wrong) (initial sample.program)))
    | _, _ => none

#eval structuralVerdicts
#guard structuralVerdicts.length == 6
#guard structuralVerdicts.all fun entry => entry.2.1 == some true && entry.2.2 == some false

def primitiveArguments : Pattern := valueList [.literal (.integer 1), .literal (.integer 2)]
def primitiveResult : Pattern := node "MlPrimitiveValue" [literal (.integer 3)]
def primitiveSource : Pattern := node "MlPrimitiveRequest" [primitive .add, primitiveArguments, node "MlKDone"]
def primitiveTarget : Pattern := node "MlPrimitiveReturned" [primitiveResult, node "MlKDone"]
def answeredProvider : GeneralPremise.ProviderSnapshot :=
  {provider with rows := [⟨"ml-primitive", [primitive .add, primitiveArguments, primitiveResult]⟩]}

/- The same suspended request has no step in an unanswered snapshot and has
the declared step in its answered snapshot. This is not a verdict about all
future service environments. -/
def primitiveVerdicts : List (String × Option Bool × Bool) := [
  ("ocaml-unanswered-primitive", verdict (ask baseLanguage provider 2 3
    (.possibly .any (.is primitiveTarget)) primitiveSource), false),
  ("ocaml-answered-primitive", verdict (ask baseLanguage answeredProvider 2 3
    (.possibly .any (.is primitiveTarget)) primitiveSource), true)]

#guard primitiveVerdicts.all fun entry => entry.2.1 == some entry.2.2

end Mettapedia.GSLT.LanguageDef.ModuleFormat.GoldOSLF.Controls
