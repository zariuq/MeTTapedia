import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScalarInvocation

/-! Tuple-pattern callback extraction uses actual source clause selection.
Irrelevant clauses can remain; overlapping answer-producing clauses decline.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScalarInvocationControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Eval MeTTaIL.WireKit ScalarInvocation

def stepEquation : SpaceSemantics.Equation :=
  ⟨"step", [.expression [.var "h", .var "n"], .var "x"],
    .expression [.var "h", apply "+" [.var "n", .var "x"]]⟩

def program : SpaceSemantics.Program := {equations := [stepEquation], declarations := []}
def initial : Atom := .expression [.symbol "tag", integer 0]
def result : Atom := .expression [.symbol "tag", integer 2]
def caller : Subst := [("acc", initial), ("item", integer 2)]

local macro "compute_selection" : tactic => `(tactic|
  (simp [Eval.clauses, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom,
    Mettapedia.Languages.ProcessCalculi.MORK.matchAtom.matchAtomList, Subst.lookup,
    program, stepEquation, initial, result, integer, apply, ioHead, StdLib.known,
    List.filterMap_cons, List.filterMap_nil, Option.map, Option.bind_eq_bind]
   <;> decide))

def callee : Subst := [("x", integer 2), ("n", integer 0), ("h", .symbol "tag")]

theorem step_selected : clauses program "step" [initial, integer 2] = [.evaluate callee stepEquation.body] := by
  unfold callee
  compute_selection

def prepared : Prepared program "step" initial (integer 2) :=
  (prepare program "step" initial (integer 2)).get (by
    rw [prepare_selected program "step" initial (integer 2) callee stepEquation.body
      (by decide) (by decide) (by decide) (by decide) step_selected]
    decide)

theorem tuple_pattern_and_field_arithmetic : prepared.evaluate = some result := by
  unfold prepared
  simp only [prepare_selected program "step" initial (integer 2) callee stepEquation.body
    (by decide) (by decide) (by decide) (by decide) step_selected]
  decide

theorem actual_source_call (state : Effects.State) :
    PureReturns program caller state (apply "step" [.var "acc", .var "item"]) state result :=
  prepared.call_returns caller state "acc" "item" rfl rfl result tuple_pattern_and_field_arithmetic

def irrelevant : SpaceSemantics.Equation := ⟨"step", [integer 99, .var "x"], integer (-1)⟩
def withIrrelevant : SpaceSemantics.Program :=
  {equations := [irrelevant, stepEquation], declarations := []}
def withDuplicate : SpaceSemantics.Program :=
  {equations := [stepEquation, stepEquation], declarations := []}

theorem irrelevant_selected : clauses withIrrelevant "step" [initial, integer 2] = [.evaluate callee stepEquation.body] := by
  simp only [withIrrelevant, irrelevant, callee]
  compute_selection

theorem duplicate_selected : clauses withDuplicate "step" [initial, integer 2] =
    [.evaluate callee stepEquation.body, .evaluate callee stepEquation.body] := by
  simp only [withDuplicate, callee]
  compute_selection

theorem admission_is_call_specific :
    (prepare withIrrelevant "step" initial (integer 2)).isSome = true ∧
    (prepare withDuplicate "step" initial (integer 2)).isNone = true := by
  constructor
  · rw [prepare_selected withIrrelevant "step" initial (integer 2) callee stepEquation.body
      (by decide) (by decide) (by decide) (by decide) irrelevant_selected]
    decide
  · rw [prepare_no_singleton withDuplicate "step" initial (integer 2)
      (by intro c b; rw [duplicate_selected]; simp)]
    rfl

def booleanEquation : SpaceSemantics.Equation :=
  ⟨"step", [.expression [.var "h", .var "n"], .var "x"],
    .expression [.var "h", apply "<" [.var "n", .var "x"]]⟩
def booleanProgram : SpaceSemantics.Program := {equations := [booleanEquation], declarations := []}

theorem boolean_selected : clauses booleanProgram "step" [initial, integer 2] = [.evaluate callee booleanEquation.body] := by
  simp only [booleanProgram, booleanEquation, callee]
  compute_selection

theorem returned_boolean_field_is_not_integer :
    ((prepare booleanProgram "step" initial (integer 2)).bind Prepared.evaluate) =
      some (.expression [.symbol "tag", Effects.boolean true]) := by
  rw [prepare_selected booleanProgram "step" initial (integer 2) callee booleanEquation.body
    (by decide) (by decide) (by decide) (by decide) boolean_selected]
  decide

def changedHead : SpaceSemantics.Program :=
  {equations := [stepEquation, ⟨"tag", [.var "z"], integer 42⟩], declarations := []}

theorem changed_selected : clauses changedHead "step" [initial, integer 2] = [.evaluate callee stepEquation.body] := by
  simp only [changedHead, callee]
  compute_selection

theorem callable_result_head_declines :
    (prepare changedHead "step" initial (integer 2)).isSome = true ∧
    ((prepare changedHead "step" initial (integer 2)).bind Prepared.evaluate) = none := by
  rw [prepare_selected changedHead "step" initial (integer 2) callee stepEquation.body
    (by decide) (by decide) (by decide) (by decide) changed_selected]
  decide

def repeatedPattern : SpaceSemantics.Program :=
  {equations := [⟨"same", [.expression [.var "z", .var "z"], .var "x"], .var "x"⟩], declarations := []}

theorem repeated_mismatch : clauses repeatedPattern "same" [.expression [integer 1, integer 2], integer 3] = [] := by
  simp only [repeatedPattern]
  compute_selection

theorem repeated_match : clauses repeatedPattern "same" [.expression [integer 1, integer 1], integer 3] =
    [.evaluate [("x", integer 3), ("z", integer 1)] (.var "x")] := by
  simp only [repeatedPattern]
  compute_selection

theorem repeated_variables_use_the_matcher :
    (prepare repeatedPattern "same" (.expression [integer 1, integer 2]) (integer 3)).isNone = true ∧
    (prepare repeatedPattern "same" (.expression [integer 1, integer 1]) (integer 3)).isSome = true := by
  constructor
  · rw [prepare_no_singleton repeatedPattern "same" (.expression [integer 1, integer 2]) (integer 3)
      (by intro c b; rw [repeated_mismatch]; simp)]
    rfl
  · rw [prepare_selected repeatedPattern "same" (.expression [integer 1, integer 1]) (integer 3)
      [("x", integer 3), ("z", integer 1)] (.var "x")
      (by decide) (by decide) (by decide) (by decide) repeated_match]
    decide

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScalarInvocationControls
