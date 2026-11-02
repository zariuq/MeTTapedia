import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCoveragePreservation
import Mettapedia.Languages.OCaml.Examples
import Mettapedia.GSLT.LanguageDef.WellSortedChecker

/-! Real pending source-machine states retain encodable, sorted closed
configurations across the core examples. Malformed runtime sorts and
unresolved pattern references are separating controls.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation.StateTypingControls

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted

def checkedState (program : OCaml.Program) (state : OCaml.MachineState) : Bool :=
  match state? (patterns program) state with
  | none => false
  | some encoded => checkHasType baseLanguage FreeTypeContext.empty [] encoded (.base "MlConfig") &&
      encoded.hasCanonicalBinderMetadata && isObjectPattern encoded && encoded.isWellScopedAt 0 &&
      encoded.freeFvarNames.isEmpty

def checkedRun (program : OCaml.Program) (budget : Nat) : Bool :=
  match OCaml.run program budget (OCaml.begin program) with
  | .pending state => checkedState program state
  | .complete (.ok actual) => checkedState program (.halted (.ok actual))
  | .complete (.error error) => checkedState program (.halted (.error error))
  | .invalid _ => false

def controls : List Bool := OCaml.Examples.examples.flatMap fun sample =>
  [0, 1, 4, 12, 40].map (checkedRun sample.program)

#eval controls.length
#guard controls.length == 50
#guard controls.all id
#guard !(checkHasType baseLanguage FreeTypeContext.empty []
  (node "MlReturn" [code 0, node "MlKDone"]) (.base "MlConfig"))
#guard state? [] (.returned (.literal .unit) [.letValue .bind 0 []]) == none
#guard (state? [.bind] (.returned (.literal .unit) [.letValue .bind 0 []])).isSome

#print axioms reachable_state_open

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation.StateTypingControls
