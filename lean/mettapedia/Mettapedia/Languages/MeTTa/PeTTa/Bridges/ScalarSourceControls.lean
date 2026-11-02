import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScalarBody
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScalarDependencies

/-! Executed source controls for result sorts, callability, shared captures,
program dependencies and the existing evaluator's complete observation. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScalarSourceControls

open Mettapedia.Machines.TypedScalar
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open ScalarSource MeTTaIL.WireKit Eval

def program : SpaceSemantics.Program := {equations := [], declarations := []}
def environment : Environment (Fin 2) := fun name =>
  if name = "a" then some 0 else if name = "x" then some 1 else none
def locals : Fin 2 → Data := fun i => if i.val = 0 then .integer 0 else .integer 2
def caller : Subst := [("a", integer 0), ("x", integer 2)]

theorem captured : Captured environment caller locals := by
  intro name slot found
  simp only [environment] at found
  split at found
  · rename_i same; subst name; cases found; rfl
  · split at found
    · rename_i same; subst name; cases found; rfl
    · cases found

def less : Atom := apply "<" [.var "a", .var "x"]
def nested : Atom := apply "==" [less, integer 1]
def boolArithmetic : Atom := apply "+" [apply "==" [.var "a", .var "x"], integer 1]
def tuple : Atom := .expression [.symbol "tag", less]

def execute (p : SpaceSemantics.Program) (source : Atom) (inputs : Fin 2 → Data := locals) : Option Atom := do
  let certificate ← ScalarBody.elaborate p environment source
  certificate.val.eval p inputs

theorem comparison_keeps_boolean : execute program less = some (Effects.boolean true) := by decide
theorem nested_comparison_is_false : execute program nested = some (Effects.boolean false) := by decide
theorem tuple_keeps_boolean : execute program tuple = some (.expression [.symbol "tag", Effects.boolean true]) := by decide
theorem boolean_arithmetic_declines : execute program boolArithmetic = none := by decide

theorem branch_still_works : execute program (apply "if" [less, integer 7, integer 9]) = some (integer 7) := by decide
theorem signed_arithmetic : execute program (apply "-" [integer (-5), .var "x"]) = some (integer (-7)) := by decide
theorem symbol_operand_declines : execute program (apply "+" [.symbol "abc", integer 1]) = none := by decide
theorem effects_are_not_extracted : execute program (apply "add-atom" [.symbol "&s", .var "x"]) = none := by decide
theorem duplicate_answers_are_not_extracted : execute program (apply "superpose" [.expression [integer 1, integer 1]]) = none := by decide

theorem test_encoding_preserves_branch_choice {Result : Type} (flag : Bool) (yes no : Result) :
    (if (if flag then (1 : Int) else 0) != 0 then yes else no) = (if flag then yes else no) := by
  cases flag <;> rfl

theorem test_encoding_does_not_preserve_values (flag : Bool) :
    Effects.boolean flag ≠ integer (if flag then 1 else 0) := by cases flag <;> decide

/-- The lost distinction cannot be reconstructed from an untagged register
alone. Static result-sort evidence can supply the missing information. -/
theorem no_sort_blind_decoder :
    ¬ ∃ decode : Int → Atom, (∀ n, decode n = integer n) ∧
      (∀ flag : Bool, decode (if flag then 1 else 0) = Effects.boolean flag) := by
  rintro ⟨decode, integers, booleans⟩
  have conflict := (integers 1).symm.trans (booleans true)
  cases conflict

def addEquation (head : String) : SpaceSemantics.Program :=
  {equations := [⟨head, [.var "z"], integer 0⟩], declarations := []}

theorem changed_primitive_declines : execute (addEquation "<") less = none := by decide
theorem unrelated_equation_preserves_extraction : execute (addEquation "unrelated") less = some (Effects.boolean true) := by decide
theorem declared_constructor_is_not_data : execute (addEquation "tag") tuple = none := by decide

def variableTuple : Atom := .expression [.var "a", .var "x"]

theorem live_callable_head_declines :
    execute (addEquation "callable") variableTuple (fun i => if i.val = 0 then .symbol "callable" else .integer 2) = none ∧
    execute program variableTuple (fun i => if i.val = 0 then .symbol "callable" else .integer 2) =
      some (.expression [.symbol "callable", integer 2]) := by decide

theorem shared_capture_stays_shared :
    execute program (apply "==" [.var "x", .var "x"]) = some (Effects.boolean true) := by decide

def lessCertificate : Extracted program environment less :=
  (ScalarSource.elaborate program environment less).get (by decide)

theorem dependency_revalidation_is_local :
    (ScalarDependencies.revalidate lessCertificate (addEquation "unrelated")).isSome = true ∧
    (ScalarDependencies.revalidate lessCertificate (addEquation "<")).isNone = true := by decide

theorem source_comparison_returns (state : Effects.State) :
    PureReturns program caller state less state (Effects.boolean true) :=
  lessCertificate.derivation.returns caller state locals captured true (by rfl)

theorem source_never_completes_as_integer_one (state after : Effects.State) (fuel : Nat) (input output : List Atom) :
    run program fuel {state, control := .evaluate caller less} ≠
      .complete after [integer 1] input output := by
  intro completed
  have exactAnswer := (pure_returns_completed_iff program caller state state less (Effects.boolean true)
    (source_comparison_returns state) after [integer 1] input output).mp ⟨fuel, completed⟩
  cases exactAnswer.2.1

theorem extracted_tuple_returns (state : Effects.State) :
    PureReturns program caller state tuple state (.expression [.symbol "tag", Effects.boolean true]) := by
  let certificate := (ScalarBody.elaborate program environment tuple).get (by decide)
  exact certificate.property.returns caller state locals captured _ (by decide)

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScalarSourceControls
