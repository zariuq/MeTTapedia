import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaApplicationContexts

/-! Executable source controls for strict and held application contexts. -/

namespace Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaApplicationContexts

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Unifying PeTTaContexts

namespace Controls

def echo : SpaceSemantics.Equation := ⟨"echo", [.var "x"], .var "x"⟩
def strictRegistry : SpaceSemantics.Program :=
  { equations := [echo], declarations := [], layout := [.equation] }
def rawRegistry : SpaceSemantics.Program :=
  { equations := [echo]
    declarations := [.expression [.symbol ":", .symbol "echo",
      .expression [.symbol "->", .symbol "Atom", .symbol "Atom"]]]
    layout := [.equation, .declaration] }
def printMarker : Atom := .expression [.symbol "println!", .symbol "marker"]
def wrapped : Atom := .expression [.symbol "echo", printMarker]

def outputOf : Outcome → List Atom
  | .complete _ _ _ output => output
  | .exhausted state | .fault _ state => state.output

def argument (registry : SpaceSemantics.Program) : Configuration :=
  atArgument (start (Effects.loaded registry) wrapped) [] (.function "echo") printMarker [] [] 0

theorem held_and_strict_enter_different_source_phases :
    (step rawRegistry (argument rawRegistry)).map Configuration.control =
      some (.returned [⟨printMarker, []⟩]) ∧
    (step strictRegistry (argument strictRegistry)).map Configuration.control =
      some (.evaluate [] printMarker) := ⟨rfl, rfl⟩

theorem typed_raw_argument_is_not_an_evaluation_context :
    compile strictRegistry [] [.call "echo" []] printMarker =
      some [.argument (.function "echo") [] [] 0] ∧
    compile rawRegistry [] [.call "echo" []] printMarker = none := ⟨rfl, rfl⟩

def nested : Context := [.call "echo" [], .shell (.letValue (.var "r") (.var "r")), .shell .collect]

theorem mixed_context_keeps_its_precise_frame_order :
    compile strictRegistry [] nested printMarker =
      some [.collect [], .bind (.var "r") (.var "r"), .argument (.function "echo") [] [] 0] ∧
      cost nested = 4 := ⟨rfl, rfl⟩

def base : Configuration := start (Effects.loaded strictRegistry) (.symbol "unused")

theorem mixed_context_reaches_its_operand (fuel : Nat) :
    run strictRegistry (4 + fuel) (atExpression base [] (plug nested printMarker)) =
      run strictRegistry fuel (atExpression
        { base with frames := [.collect [], .bind (.var "r") (.var "r"),
          .argument (.function "echo") [] [] 0] } [] printMarker) := by
  exact run_context strictRegistry nested base [] printMarker
    [.collect [], .bind (.var "r") (.var "r"), .argument (.function "echo") [] [] 0] rfl fuel

def pairRegistry : SpaceSemantics.Program :=
  { equations := [⟨"pair", [.var "x", .var "y"],
      .expression [.symbol "out", .var "x", .var "y"]⟩]
    declarations := [], layout := [.equation] }
def alternatives : Atom := .expression [.symbol "superpose", .expression [.symbol "a", .symbol "b"]]
def branches : Atom := .expression [.symbol "pair", alternatives, printMarker]

def branchPackets : List Answer :=
  [⟨.symbol "a", [("branch", .symbol "a")]⟩,
    ⟨.symbol "b", [("branch", .symbol "b")]⟩]

theorem remaining_arguments_keep_branch_substitutions :
    (step pairRegistry
      { state := Effects.loaded pairRegistry
        control := .returned branchPackets
        frames := [.argument (.function "pair") [printMarker] [] 0] }).map Configuration.control =
      some (.sequence
        [.arguments [("branch", .symbol "a")] (.function "pair") [printMarker] [.symbol "a"] 1,
         .arguments [("branch", .symbol "b")] (.function "pair") [printMarker] [.symbol "b"] 1] []) := rfl

def answerless : Atom := .expression [.symbol "let", .var "ignored", printMarker,
  .expression [.symbol "empty"]]
def blockedTail : Atom := .expression [.symbol "pair", answerless,
  .expression [.symbol "println!", .symbol "must-not-run"]]

def emptyReturned : Configuration :=
  { state := Effects.loaded pairRegistry
    control := .returned []
    frames := [.argument (.function "pair") [printMarker] [] 0]
    output := [.symbol "earlier-effect"] }

theorem empty_argument_return_keeps_effect_and_skips_pending_work :
    shown (run pairRegistry 2 emptyReturned) = .printed [.symbol "earlier-effect"] [] := rfl

end Controls

end Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaApplicationContexts
