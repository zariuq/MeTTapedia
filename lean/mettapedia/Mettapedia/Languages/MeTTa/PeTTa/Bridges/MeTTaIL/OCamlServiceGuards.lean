import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlControllerSource

/-! Literal status and empty-publication tests use the target evaluator's
structural equality, independently of any search-completion theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlServiceGuards

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval WireKit

theorem symbol_self_equal_returns (program : SpaceSemantics.Program) (caller : Subst) (state : State)
    (expression : Atom) (name : String)
    (read : PureReturns program caller state expression state (encoded (.symbol name))) :
    PureReturns program caller state (apply "==" [expression, encoded (.symbol name)]) state (Effects.boolean true) := by
  have compared := term_equal_returns program caller state expression (encoded (.symbol name))
    (.symbol name) (.symbol name) read (symbol_returns program caller state name)
  simpa only [decide_true] using compared

#print axioms symbol_self_equal_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlServiceGuards
