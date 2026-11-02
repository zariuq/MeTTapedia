import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlControlPoint

/-! A zero administrative rank gives the ordinary source-state encoding.
A pending administrative configuration is not a completed observation
merely because the source computation it realizes has a known result.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem rank_zero_encodes_source {program : OCaml.Program} {source : OCaml.MachineState} {target : Pattern}
    (point : ControlPoint program source target 0) : state? (patterns program) source = some target := by
  cases point with
  | state encoded => exact encoded

theorem primitive_request_not_source_encoding (pool : List OCaml.MatchPattern) (source : OCaml.MachineState)
    (operator : OCaml.Primitive) (arguments : List OCaml.Value) (rest : Pattern) :
    state? pool source ≠ some (node "MlPrimitiveRequest" [primitive operator, valueList arguments, rest]) := by
  intro encoded
  cases source with
  | evaluate reference captured continuation =>
    cases resolved : continuation? pool continuation <;> simp [state?, resolved, node] at encoded
  | returned actual continuation =>
    cases resolved : continuation? pool continuation <;> simp [state?, resolved, node] at encoded
  | halted result => cases result <;> simp [state?, node] at encoded

theorem primitive_request_rank_not_zero {program : OCaml.Program} {source : OCaml.MachineState}
    {operator : OCaml.Primitive} {arguments : List OCaml.Value} {rest : Pattern} :
    ¬ ControlPoint program source (node "MlPrimitiveRequest" [primitive operator, valueList arguments, rest]) 0 := by
  intro point
  exact primitive_request_not_source_encoding (patterns program) source operator arguments rest (rank_zero_encodes_source point)

#print axioms rank_zero_encodes_source
#print axioms primitive_request_not_source_encoding
#print axioms primitive_request_rank_not_zero

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
