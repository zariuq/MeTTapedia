import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaApplicationControls
import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaContinuationContexts

/-! Executable independent-source observations for application contexts. -/

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Unifying
open Mettapedia.Languages.MeTTa.ContextualTransform
open PeTTaApplicationContexts PeTTaApplicationContexts.Controls

def main : IO Unit := do
  let strict := shown (run strictRegistry 80 (start (Effects.loaded strictRegistry) wrapped))
  let held := shown (run rawRegistry 80 (start (Effects.loaded rawRegistry) wrapped))
  IO.println s!"strict argument evaluates={decide (strict = .printed [.symbol "marker"] [Effects.boolean true])}"
  IO.println s!"Atom argument holds syntax={decide (held = .printed [] [printMarker])}"
  let nestedResult := shown (run strictRegistry 100 (PeTTaContexts.atExpression base [] (plug nested printMarker)))
  IO.println s!"nested call/let/collapse={decide (nestedResult = .printed [.symbol "marker"] [.expression [Effects.boolean true]])}; entry steps={cost nested}"
  let branchResult := shown (run pairRegistry 150 (start (Effects.loaded pairRegistry) branches))
  IO.println s!"branch-local remaining arguments={decide (branchResult = .printed [.symbol "marker", .symbol "marker"] [.expression [.symbol "out", .symbol "a", Effects.boolean true], .expression [.symbol "out", .symbol "b", Effects.boolean true]])}"
  let emptyResult := shown (run pairRegistry 100 (start (Effects.loaded pairRegistry) blockedTail))
  IO.println s!"answerless operand retains effect={decide (emptyResult = .printed [.symbol "marker"] [])}"
  let collected := shown (run pairRegistry 100 (start (Effects.loaded pairRegistry)
    (.expression [.symbol "collapse", answerless])))
  IO.println s!"empty collapse retains effect and returns one value={decide (collected = .printed [.symbol "marker"] [.expression []])}"
  let selected := .expression [.symbol "case", printMarker,
    .expression [.expression [Effects.boolean true, .symbol "chosen"],
      .expression [.var "otherwise", .symbol "wrong"]]]
  IO.println s!"case resumes reached world={decide (shown (run strictRegistry 80 (start (Effects.loaded strictRegistry) selected)) = .printed [.symbol "marker"] [.symbol "chosen"])}"
