import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerRawSyntax
import Lean.Elab.Command

/-!
# Declarations for scoped tower syntax

Each row introduces a declaration in the current namespace. A numeric
annotation is the context length of a term. `Head` and `Level` declare the
other two sorts of syntax. A row with a parameter declares a private term
that works in any context extending its stated minimum length.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

open Lean Elab Command
open Mettapedia.TypeTheory.UniverseLevel

declare_syntax_cat towerSyntaxRow
syntax ident ":" num ":=" term : towerSyntaxRow
syntax ident ":" ident ":=" term : towerSyntaxRow
syntax ident "(" ident ")" ":" num ":=" term : towerSyntaxRow

/-- Elaborate an ordered table of scoped syntax. Each body is checked at its
declared scope against the preceding rows and the ambient environment. -/
syntax (name := declareTowerSyntax) "declare_tower_syntax " "[" towerSyntaxRow,* "]" : command

elab_rules : command
  | `(command| declare_tower_syntax [$rows:towerSyntaxRow,*]) => do
      for row in rows.getElems do
        withRef row do
          let declaration ← match row with
            | `(towerSyntaxRow| $name:ident : $scope:num := $body:term) =>
                `(command| def $name : Tower.Tm $scope := $body)
            | `(towerSyntaxRow| $name:ident ($extra:ident) : $scope:num := $body:term) =>
                `(command| private def $name ($extra : Nat) : Tower.Tm ($extra + $scope) := $body)
            | `(towerSyntaxRow| $name:ident : $kind:ident := $body:term) =>
                match kind.getId with
                | `Head => `(command| def $name : Tower.Head := $body)
                | `Level => `(command| def $name : LevelExpr Nat := $body)
                | _ => throwErrorAt kind "expected the syntax sort Head or Level"
            | _ => throwUnsupportedSyntax
          elabCommand declaration

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
