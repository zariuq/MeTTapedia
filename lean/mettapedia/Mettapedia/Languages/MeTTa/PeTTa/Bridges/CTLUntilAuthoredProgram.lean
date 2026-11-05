import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilNamedRound
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilNamedCleanup
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilNamedSeed
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilNamedLoop

/-! Syntactic admission facts for the existing authored five-clause EU
program. These are declaration and argument-mode checks, not a premise
asserting what the source body computes. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilAuthoredProgram

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open ScopedQuerySource.CTLUntilDriverControls (program)
open ScopedQuerySource

def query : CTLUntilScopedRound.Query := {
  names := ⟨"f", "k1", "y", "x", "answer", "ignored"⟩
  operand := "a"
  currentRound := "k"
  frontierHandle := .self
  edgeHandle := .self
  operandHandle := .self
  satisfactionHandle := .self
  nextFrontierHandle := .self }

theorem query_distinct : (CTLUntilRoundSyntax.sourceNames query).Nodup := by decide

theorem round_declaration :
    (CTLUntilRoundSyntax.definition query (CTLUntilRoundSyntax.formals_distinct query query_distinct)).declaration =
      CTLUntilControls.roundEquation := rfl

theorem drop_body : CTLUntilNamedCleanup.source .self "f" "k" "x" =
    ScopedQuerySource.CTLUntilDriverControls.dropEquation.body := rfl

theorem strict (head : String) (index : Nat)
    (ordinary : head ∈ ["+", "==", "in", "eu-round", "drop", "eu-loop", "do-eu"]) :
    Eval.argumentIsRaw program head index = false := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ordinary
  rcases ordinary with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Eval.argumentIsRaw, program, StdLib.rawArgument]

theorem ordinary_equation_unique (index : Nat) (equation : SpaceSemantics.Equation)
    (row : program.equations[index]? = some equation)
    (occurrence : Nat) (expected : SpaceSemantics.Equation)
    (selected : program.equations[occurrence]? = some expected)
    (different : index ≠ occurrence) : equation.head ≠ expected.head := by
  have indexBound : index < 5 := by
    have bounded := (List.getElem?_eq_some_iff.mp row).1
    simpa [program] using bounded
  have occurrenceBound : occurrence < 5 := by
    have bounded := (List.getElem?_eq_some_iff.mp selected).1
    simpa [program] using bounded
  interval_cases index <;> interval_cases occurrence <;>
    simp_all [program, CTLUntilControls.guard, CTLUntilControls.roundEquation,
      ScopedQuerySource.CTLUntilDriverControls.dropEquation,
      ScopedQuerySource.CTLUntilDriverControls.loopEquation,
      ScopedQuerySource.CTLUntilDriverControls.entryEquation]
  all_goals rw [← row, ← selected]; decide

theorem guard_declaration {Label : Type} (codec : FlatQueryRowCodec.Codec Label) (label : Label) :
    NamedPresenceSource.declaration (CTLUntilPublicationSource.request codec .self label 0) =
      CTLUntilControls.guard := rfl

def guardProfile {Label : Type} (codec : FlatQueryRowCodec.Codec Label) (label : Label) :
    CTLUntilLeafAdmission.GuardProfile codec label query program where
  occurrence := 0
  row := by rw [show query.satisfactionHandle = .self from rfl, guard_declaration]; rfl
  otherHeads := by
    intro index equation row different
    exact ordinary_equation_unique index equation row 0 CTLUntilControls.guard rfl different
  leftEvaluated := strict "in" 0 (by simp)
  rightEvaluated := strict "in" 1 (by simp)

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilAuthoredProgram
