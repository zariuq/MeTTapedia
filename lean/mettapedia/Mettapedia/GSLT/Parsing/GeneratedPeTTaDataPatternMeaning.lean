import Mettapedia.GSLT.Parsing.GeneratedPeTTaDataPattern
import Mettapedia.Languages.MeTTa.PeTTa.StdLib

/-!
# The native constructor graph of an emitted data pattern

This relation interprets just the direct compiler's structural spine. Leaves
use the existing source reader and substitution; each spine node uses the
actual `StdLib.apply` graph of `cons-atom`. It specifies no evaluator schedule,
search procedure, computed-let continuation, or unification algorithm.

The accompanying laws compare this graph with reading and instantiating the
unencoded template. Open variables retain their supplied interpretation.
Admission and operational realization of this graph remain separate contracts.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.GeneratedPeTTaDataPattern

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)

/-- A constructor-pattern graph with the standard native primitive. Its
premises retain each intermediate world rather than assuming purity. -/
inductive ConstructorGraph (bindings : Subst) : State → SExpr → State → Atom → Prop where
  | leaf {state : State} {token : String} {atom : Atom}
      (read : SpaceSemantics.readToken token = .ok atom) :
      ConstructorGraph bindings state (.atom token) state (applySubst bindings atom)
  | empty (state : State) : ConstructorGraph bindings state (.list []) state (.expression [])
  | cons {before middle reached after : State} {first rest : SExpr}
      {head : Atom} {tail : List Atom} {value : Atom}
      (firstGraph : ConstructorGraph bindings before first middle head)
      (restGraph : ConstructorGraph bindings middle rest reached (.expression tail))
      (primitive : StdLib.apply reached "cons-atom" [head, .expression tail] = .ok (after, [value])) :
      ConstructorGraph bindings before (.list [.atom "cons-atom", first, rest]) after value

end Mettapedia.GSLT.Parsing.GeneratedPeTTaDataPattern
