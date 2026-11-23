import Mettapedia.Languages.MeTTa.PeTTa.Bridges.LiveMathRegion
import Mettapedia.Languages.MeTTa.PeTTa.ProgramQuotation

/-! Math-library source examples and admission controls for the live evaluator. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.LiveMathRegionControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Eval ProgramReplay ProgramQuotation

/-- The three definitions and signatures come from CeTTa's shared math library. -/
private def math : QuotedProgram :=
  petta_source% "(: math:min (-> Number Number Number))\n(: math:max (-> Number Number Number))\n(: math:clamp (-> Number Number Number Number))\n(= (math:min $a $b)\n   (if (<= $a $b) $a $b))\n\n(= (math:max $a $b)\n   (if (>= $a $b) $a $b))\n\n(= (math:clamp $min $max $v)\n   (math:min $max (math:max $v $min)))"
    sha256 "37802f36037d59550f8094047386f603eb9eb64e2e4daf96675b0573a87ee007"

private def state := Effects.loaded math.program

private def int (n : Int) : Atom := .grounded (.int n)

private def ready (head : String) (left right : Atom) : Configuration :=
  { state, control := .arguments [] (.function head) [] [left, right] 2 }

theorem library_operations_admitted :
    (LiveMathRegion.attempt (ready "math:min" (int 4) (int (-3)))).map (·.control) =
      some (.returned [int (-3)]) ∧
    (LiveMathRegion.attempt (ready "math:max" (int 4) (int (-3)))).map (·.control) =
      some (.returned [int 4]) := by
  decide +kernel

private def clamp : Configuration :=
  Eval.start state (.expression [.symbol "math:clamp", int 0, int 7, int 11])

/-- An authored caller composes both regions through the ordinary evaluator. -/
theorem clamp_composes :
    (LiveRegistry.advance 150 clamp).control = .returned [int 7] ∧
    (LiveMathRegion.advance 150 clamp).control = .returned [int 7] ∧
    (LiveMathRegion.advance 150 clamp).frames.length = 0 := by
  decide +kernel

private def request : QuotedProgram :=
  petta_source% "!(let $add (add-atom &self (= (my:minimum $a $b) (if (<= $a $b) $a $b))) (+ 10 (my:minimum 4 -3)))"
    sha256 "72e691ed8291512b79cf354485a50be210277d692b476462399b92b8aa7f9805"

private def requestStart : Configuration := Eval.start state request.program.initializers[0]

private def admitsOnPath : Nat → Configuration → Bool
  | 0, _ => false
  | fuel + 1, source =>
      (LiveMathRegion.prepare source).isSome ||
        ((LiveRegistry.step source).any (admitsOnPath fuel))

/-- A definition installed during execution can qualify under its own name. -/
theorem newly_loaded_body_admitted :
    admitsOnPath 70 requestStart = true ∧
    (LiveMathRegion.advance 100 requestStart).control = .returned [int 7] := by
  decide +kernel

private def twoAlternatives : Configuration :=
  let declared := ready "math:min" (int 4) (int (-3))
  let extra := SpaceSemantics.Equation.toAtom ⟨"math:min", [.var "a", .var "b"], .var "a"⟩
  {declared with state := {declared.state with core := declared.state.core ++ [extra]}}

/-- A new matching definition matters even if the old one is still present. -/
theorem extra_alternative_keeps_ordinary_order :
    (LiveMathRegion.prepare twoAlternatives).isNone = true ∧
    (LiveMathRegion.advance 100 twoAlternatives).control = .returned [int (-3), int 4] := by
  decide +kernel

theorem symbolic_operand_retains_dispatch :
    (LiveMathRegion.prepare (ready "math:min" (.symbol "held") (int 1))).isNone = true ∧
    (LiveMathRegion.advance 60 (ready "math:min" (.symbol "held") (int 1))).control =
      .fault (.invalidArguments "<=") := by
  decide +kernel

#print axioms library_operations_admitted
#print axioms clamp_composes
#print axioms newly_loaded_body_admitted
#print axioms extra_alternative_keeps_ordinary_order
#print axioms symbolic_operand_retains_dispatch

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.LiveMathRegionControls
