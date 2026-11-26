import Lean.Elab.Command

/-!
# Declarations for structural replay codes

A row records the code family, the scope, and the constructor expression.
Shared templates retain their root-code parameter. Local replay bundles
use the concrete code families for their own decoder and keep local names
private. Declaration order makes each earlier witness available to later rows.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId

open Lean Elab Command

declare_syntax_cat structuralReplayRow
syntax ident ":" ident num ":=" term : structuralReplayRow

/-- Declare shared replay templates at their scoped code types. -/
syntax (name := declareScopedReplay) "declare_scoped_replay " "(" term ")"
  "[" structuralReplayRow,* "]" : command

/-- Declare the private evidence nodes of one concrete replay bundle. -/
syntax (name := declarePrivateScopedReplay) "declare_private_scoped_replay "
  "[" structuralReplayRow,* "]" : command

private def elaborateRows (rows : Array (TSyntax `structuralReplayRow))
    (rootCode : Option Term) : CommandElabM Unit := do
  for row in rows do
    withRef row do
      match row with
      | `(structuralReplayRow| $name:ident : $kind:ident $scope:num := $body:term) =>
          let declaration ← match rootCode with
            | some code => `(command| def $name : $kind $code $scope := $body)
            | none => `(command| private def $name : $kind $scope := $body)
          elabCommand declaration
      | _ => throwUnsupportedSyntax

elab_rules : command
  | `(command| declare_scoped_replay ($rootCode:term) [$rows:structuralReplayRow,*]) =>
      elaborateRows rows.getElems (some rootCode)
  | `(command| declare_private_scoped_replay [$rows:structuralReplayRow,*]) =>
      elaborateRows rows.getElems none

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
