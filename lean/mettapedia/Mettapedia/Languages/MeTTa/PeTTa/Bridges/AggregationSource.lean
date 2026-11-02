import Mettapedia.Machines.AdditiveFoldInference
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.NumericMultiplyExecution

/-!
# Certified extraction of pure natural counter expressions

The elaborator consumes the existing PeTTa Atom carrier, not a second surface
syntax. It accepts captured natural variables, natural literals, addition,
literal scaling and an input-equality indicator. Its certificate connects the
extracted IR to the existing operational `PureReturns` judgment: exactly one
answer and unchanged state. Unsupported atoms decline elaboration, without
claiming a source error or evaluating a rejected effectful expression.

The arithmetic heads have their native meaning in this explicit PeTTa model.
General equation unfolding, tuple-body extraction, other dialect profiles and
the C implementation remain additional bridges.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.AggregationSource

open Mettapedia.Machines.AdditiveFoldInference
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open MeTTaIL.WireKit BridgeKit Eval

inductive Role (n : Nat)
  | inputValue
  | register (index : Fin n)
  deriving DecidableEq

abbrev Environment (n : Nat) := String → Option (Role n)

def Role.expression {n : Nat} : Role n → Expr n
  | .inputValue => .weight .inputValue
  | .register index => .register index

def Role.value {n : Nat} : Role n → (Fin n → Nat) → Nat → Nat
  | .inputValue, _, input => input
  | .register index, registers, _ => registers index

def Captured {n : Nat} (environment : Environment n) (caller : Subst)
    (registers : Fin n → Nat) (input : Nat) : Prop :=
  ∀ name role, environment name = some role → caller.lookup name = some (number (role.value registers input))

inductive Elaborates {n : Nat} (environment : Environment n) : Atom → Expr n → Prop
  | literal (value : Nat) : Elaborates environment (.grounded (.int value)) (.weight (.constant value))
  | bound (name : String) (role : Role n) (found : environment name = some role) :
      Elaborates environment (.var name) role.expression
  | addition {left right : Atom} {a b : Expr n} :
      Elaborates environment left a → Elaborates environment right b →
      Elaborates environment (apply "+" [left, right]) (.add a b)
  | scaling (factor : Nat) {body : Atom} {expression : Expr n} :
      Elaborates environment body expression →
      Elaborates environment (apply "*" [number factor, body]) (.scale factor expression)
  | indicator (name : String) (label : Nat) (found : environment name = some .inputValue) :
      Elaborates environment (apply "if" [apply "==" [.var name, number label], number 1, number 0])
        (.weight (.indicator label))

theorem Elaborates.returns {n : Nat} {environment : Environment n} {source : Atom} {expression : Expr n}
    (elaborated : Elaborates environment source expression) (program : SpaceSemantics.Program)
    (caller : Subst) (state : Effects.State) (registers : Fin n → Nat) (input : Nat)
    (captured : Captured environment caller registers input) :
    PureReturns program caller state source state (number (expression.eval registers input)) := by
  induction elaborated with
  | literal value => exact literal_returns program caller state value
  | bound name role found =>
    have bound := bound_returns program caller state (captured name role found)
    cases role <;> exact bound
  | addition left right ihl ihr =>
    exact natural_add_returns program caller state _ _ _ _ ihl ihr
  | scaling factor body ih =>
    exact natural_mul_returns program caller state _ _ factor _ (number_returns program caller state factor) ih
  | indicator name label found =>
    have inputReturns := bound_returns program caller state (captured name .inputValue found)
    apply pure_if_returns program caller state _ (decide (input = label)) _ _ _
      (natural_equal_returns program caller state _ _ input label inputReturns (number_returns program caller state label))
    by_cases same : input = label
    · simpa [same, Expr.eval, Weight.eval] using number_returns program caller state 1
    · simpa [same, Expr.eval, Weight.eval] using number_returns program caller state 0

/-- Recognition and its structural evidence are computed together. -/
def elaborate {n : Nat} (environment : Environment n) :
    (source : Atom) → Option {expression : Expr n // Elaborates environment source expression}
  | .grounded (.int (.ofNat value)) => some ⟨.weight (.constant value), .literal value⟩
  | .var name =>
      match found : environment name with
      | none => none
      | some role => some ⟨role.expression, .bound name role found⟩
  | .expression [.symbol "+", left, right] => do
      let a ← elaborate environment left
      let b ← elaborate environment right
      return ⟨.add a.val b.val, .addition a.property b.property⟩
  | .expression [.symbol "*", .grounded (.int (.ofNat factor)), body] => do
      let value ← elaborate environment body
      return ⟨.scale factor value.val, .scaling factor value.property⟩
  | .expression [.symbol "if", .expression [.symbol "==", .var name, .grounded (.int (.ofNat label))],
      .grounded (.int (.ofNat 1)), .grounded (.int (.ofNat 0))] =>
      if found : environment name = some .inputValue then
        some ⟨.weight (.indicator label), .indicator name label found⟩ else none
  | _ => none
termination_by structural source => source

structure SourceCertificate {n : Nat} (environment : Environment n) (source : Fin n → Atom) where
  program : Program n
  elaborated : ∀ i, Elaborates environment (source i) (program i)
  additive : Certificate program

def elaborateProgram {n : Nat} (environment : Environment n) (source : Fin n → Atom) :
    Option {program : Program n // ∀ i, Elaborates environment (source i) (program i)} :=
  if accepted : ∀ i, (elaborate environment (source i)).isSome = true then
    some ⟨fun i => ((elaborate environment (source i)).get (accepted i)).val,
      fun i => ((elaborate environment (source i)).get (accepted i)).property⟩
  else none

def inferSource {n : Nat} (environment : Environment n) (source : Fin n → Atom) :
    Option (SourceCertificate environment source) := do
  let parsed ← elaborateProgram environment source
  let certificate ← inferCertified parsed.val
  return ⟨parsed.val, parsed.property, certificate⟩

/-- Each accepted source coordinate executes in the existing operational
semantics with the exact inferred translation result and unchanged state. -/
theorem source_translation {n : Nat} {environment : Environment n} {source : Fin n → Atom}
    (certificate : SourceCertificate environment source) (program : SpaceSemantics.Program)
    (caller : Subst) (state : Effects.State) (registers : Fin n → Nat) (input : Nat)
    (captured : Captured environment caller registers input) (i : Fin n) :
    PureReturns program caller state (source i) state
      (number (registers i + (certificate.additive.weights i).eval input)) := by
  have returned := (certificate.elaborated i).returns program caller state registers input captured
  have translation := congrFun (certificate.additive.transition registers input) i
  change (certificate.program i).eval registers input = registers i + (certificate.additive.weights i).eval input at translation
  rw [translation] at returned
  exact returned

namespace Controls

def environment : Environment 1 := fun name =>
  if name = "s" then some (.register 0) else if name = "x" then some .inputValue else none

def counter : Fin 1 → Atom := fun _ =>
  apply "+" [.var "s", apply "if" [apply "==" [.var "x", number 7], number 1, number 0]]

def reassociated : Fin 1 → Atom := fun _ =>
  apply "+" [apply "+" [number 0, .var "s"],
    apply "if" [apply "==" [.var "x", number 7], number 1, number 0]]

theorem source_counter_admitted : (inferSource environment counter).isSome = true := by decide
theorem reassociated_counter_admitted : (inferSource environment reassociated).isSome = true := by decide

theorem effectful_step_declines :
    (inferSource environment (fun _ => apply "+" [.var "s", apply "add-atom" [.symbol "&s", number 7]])).isNone = true := by
  decide

theorem duplicate_choice_declines :
    (elaborate environment (apply "superpose" [.expression [number 1, number 1]])).isNone = true := by decide

theorem negative_literal_declines : (elaborate environment (.grounded (.int (-1)))).isNone = true := by decide

theorem undeclared_capture_declines : (elaborate environment (.var "unknown")).isNone = true := by decide

theorem state_dependent_indicator_declines :
    (elaborate environment
      (apply "if" [apply "==" [.var "s", number 7], number 1, number 0])).isNone = true := by decide

theorem zero_scale_does_not_hide_effect :
    (elaborate environment
      (apply "*" [number 0, apply "add-atom" [.symbol "&s", number 7]])).isNone = true := by decide

end Controls
end Mettapedia.Languages.MeTTa.PeTTa.Bridges.AggregationSource
