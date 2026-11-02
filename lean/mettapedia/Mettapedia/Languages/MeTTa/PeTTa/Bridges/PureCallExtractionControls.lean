import Mettapedia.Languages.MeTTa.PeTTa.Bridges.PureCallExtraction

/-! Positive and negative controls for call-specific source partial evaluation.
These retain the actual PeTTa Atom carrier and operational observation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.PureCallExtraction.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Eval SpaceSemantics MeTTaIL.WireKit

def inc : Equation := ⟨"inc", [.var "x"], apply "+" [.var "x", integer 1]⟩
def wrapper : Equation := ⟨"wrapped", [.var "y"], apply "inc" [.var "y"]⟩
def outer : Equation := ⟨"outer", [.var "z"], apply "+" [apply "wrapped" [.var "z"], integer 2]⟩
def program : Program := { equations := [inc, wrapper, outer], declarations := [] }
def callSource : Atom := apply "outer" [integer 3]

theorem nested_calls_inside_arithmetic :
    (prepare 6 program [] callSource).map Certified.value = some (integer 6) := by decide +kernel

def renamed : Program := { equations := [
  ⟨"plus-one", [.var "a"], apply "+" [.var "a", integer 1]⟩,
  ⟨"wrapper2", [.var "b"], apply "plus-one" [.var "b"]⟩,
  ⟨"outer2", [.var "c"], apply "+" [apply "wrapper2" [.var "c"], integer 2]⟩], declarations := [] }

theorem names_do_not_choose_the_algebra :
    (prepare 6 renamed [] (apply "outer2" [integer 3])).map Certified.value =
      (prepare 6 program [] callSource).map Certified.value := by decide +kernel

def irrelevant : Program := { equations := [
  ⟨"inc", [integer 99], integer 1000⟩, inc, wrapper, outer,
  ⟨"unrelated", [.var "u"], apply "println!" [.var "u"]⟩], declarations :=
  [apply ":" [.symbol "unrelated", apply "->" [.symbol "Atom", .symbol "Atom"]]] }

theorem unselected_equations_and_unrelated_declarations_are_inert_here :
    (prepare 6 irrelevant [] callSource).map Certified.value = some (integer 6) := by decide +kernel

def duplicate : Program := { equations := [inc, inc, wrapper, outer], declarations := [] }

theorem duplicate_answers_are_not_collapsed : (prepare 6 duplicate [] callSource).isNone = true := by decide +kernel

def extraEmpty : Program := { equations := [inc, ⟨"inc", [.var "x"], apply "empty" []⟩, wrapper, outer], declarations := [] }

/-- This conservative classifier has not proved operational elimination of
empty alternatives, so it declines instead of treating them as inert. -/
theorem empty_alternative_needs_a_separate_law :
    (prepare 6 extraEmpty [] callSource).isNone = true := by decide +kernel

def raw : Program := { equations := [inc, wrapper, outer], declarations :=
  [apply ":" [.symbol "wrapped", apply "->" [.symbol "Atom", .symbol "Atom"]]] }

theorem changed_argument_demand_invalidates : (prepare 6 raw [] callSource).isNone = true := by decide +kernel

def comparison : Program := { equations := [
  ⟨"less", [.var "x", .var "y"], apply "<" [.var "x", .var "y"]⟩], declarations := [] }

theorem returned_boolean_stays_boolean :
    (prepare 3 comparison [] (apply "less" [integer 1, integer 2])).map Certified.value =
      some (Effects.boolean true) := by decide +kernel

theorem boolean_is_not_the_integer_one :
    (prepare 4 comparison []
      (apply "==" [apply "less" [integer 1, integer 2], integer 1])).map Certified.value =
      some (Effects.boolean false) := by decide +kernel

theorem noninteger_order_declines :
    (prepare 4 comparison [] (apply "less" [.symbol "abc", integer 2])).isNone = true := by decide +kernel

def effectful : Program := { equations := [⟨"emit", [.var "x"], apply "println!" [.var "x"]⟩], declarations := [] }

theorem selected_effect_declines :
    (prepare 4 effectful [] (apply "emit" [integer 7])).isNone = true := by decide +kernel

theorem unselected_effect_is_not_executed :
    (prepare 4 effectful []
      (apply "if" [Effects.boolean true, integer 7, apply "emit" [integer 8]])).map Certified.value =
      some (integer 7) := by decide +kernel

def recursive : Program := { equations := [⟨"down", [.var "x"],
  apply "if" [apply "<=" [.var "x", integer 0], integer 0,
    apply "down" [apply "-" [.var "x", integer 1]]]⟩], declarations := [] }

theorem finite_recursive_unfolding :
    (prepare 14 recursive [] (apply "down" [integer 3])).map Certified.value = some (integer 0) := by decide +kernel

def looping : Program := { equations := [⟨"loop", [.var "x"], apply "loop" [.var "x"]⟩], declarations := [] }

theorem unfolding_cutoff_is_refusal :
    (prepare 6 looping [] (apply "loop" [integer 0])).isNone = true := by decide +kernel

theorem exact_zero_page_preserves_exhaustion (state : Effects.State) :
    execute .exactPage 6 0 program [] callSource state =
      .exhausted {state, control := .evaluate [] callSource} := by
  rw [exact_page_always_uses_source]
  rfl

theorem completed_and_page_observers_differ (state : Effects.State) :
    execute .completedResult 1 0 program [] (integer 7) state = .complete state [integer 7] [] [] ∧
    execute .exactPage 1 0 program [] (integer 7) state =
      .exhausted {state, control := .evaluate [] (integer 7)} := by
  constructor
  · simp [execute, prepare, fromValue, integer]
  · rw [exact_page_always_uses_source]
    rfl

def identity : Program := { equations := [⟨"id", [.var "x"], .var "x"⟩], declarations := [] }

theorem captured_boolean_is_a_value :
    (prepare 3 identity [] (apply "id" [Effects.boolean true])).map Certified.value =
      some (Effects.boolean true) := by decide +kernel

def heldCode : Subst := [("held", apply "println!" [integer 9])]

theorem captured_code_is_not_executed :
    (prepare 3 identity heldCode (apply "id" [.var "held"])).map Certified.value =
      some (apply "println!" [integer 9]) := by decide +kernel

theorem predicates_do_not_enter_integer_addition :
    (prepare 3 identity [] (apply "+" [Effects.boolean true, integer 1])).isNone = true := by decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.PureCallExtraction.Controls
