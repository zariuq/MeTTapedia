import Mettapedia.Machines.TypedScalar
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScalarEqualityExecution

/-!
# Typed extraction of scalar source expressions

The compiler consumes existing PeTTa atoms and emits expressions indexed by
data versus predicate results. Its derivations refine the existing evaluator,
including unchanged state and singleton answers. Accepted primitives retain
their source result type; Boolean-to-integer erasure is not a value encoding.
The explicit PeTTa model owns primitive semantics. C recognition, signed-word
layout and whole-fold invocation are separate implementation bridges.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScalarSource

open Mettapedia.Machines.TypedScalar
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Eval MeTTaIL.WireKit BridgeKit

def encode : {kind : Kind} → Value kind → Atom
  | .data, .integer value => .grounded (.int value)
  | .data, .symbol name => .symbol name
  | .test, value => Effects.boolean value

theorem encode_equality {a b : Kind} (left : Value a) (right : Value b) :
    (encode left == encode right) = valueEq left right := by
  cases a <;> cases b <;> cases left <;> cases right <;>
    apply Bool.eq_iff_iff.mpr <;> simp [encode, valueEq, Effects.boolean]

theorem binary_primitive {a b c : Kind} (op : Binary a b c) (state : Effects.State)
    (left : Value a) (right : Value b) (value : Value c)
    (computed : op.eval left right = some value) :
    StdLib.apply state op.name [encode left, encode right] = .ok (state, [encode value]) := by
  cases op with
  | equal =>
      have same : valueEq left right = value := Option.some.inj computed
      rw [← same]
      change StdLib.apply state "==" _ = _
      rw [StdLib.structural_equality, encode_equality]
      rfl
  | add | sub | lt | le | gt | ge =>
      cases left <;> cases right <;> simp only [Binary.eval] at computed
      all_goals first | contradiction | (cases computed; rfl)

def Clear (program : SpaceSemantics.Program) (head : String) : Prop :=
  program.equations.any (·.head == head) = false

instance (program : SpaceSemantics.Program) (head : String) : Decidable (Clear program head) :=
  inferInstanceAs (Decidable (_ = false))

def Inert (program : SpaceSemantics.Program) (head : String) : Prop :=
  (ioHead head || StdLib.known head || program.equations.any (·.head == head)) = false ∧
  head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique", "match"]

instance (program : SpaceSemantics.Program) (head : String) : Decidable (Inert program head) :=
  inferInstanceAs (Decidable (_ ∧ _))

abbrev Environment (Slot : Type) := String → Option Slot

def Captured {Slot : Type} (environment : Environment Slot) (caller : Subst)
    (locals : Slot → Data) : Prop :=
  ∀ name slot, environment name = some slot → caller.lookup name = some (encode (kind := .data) (locals slot))

inductive Elaborates {Slot : Type} (program : SpaceSemantics.Program) (environment : Environment Slot) :
    Atom → {kind : Kind} → Expr Slot kind → Prop
  | integer (value : Int) : Elaborates program environment (.grounded (.int value)) (.literal (.integer value))
  | symbol (name : String) (inert : Inert program name) :
      Elaborates program environment (.symbol name) (.literal (.symbol name))
  | boolean (value : Bool) : Elaborates program environment (Effects.boolean value) (.boolean value)
  | bound (name : String) (slot : Slot) (found : environment name = some slot) :
      Elaborates program environment (.var name) (.read slot)
  | binary {a b c : Kind} (op : Binary a b c) {left right : Atom} {x : Expr Slot a} {y : Expr Slot b}
      (clear : Clear program op.name) : Elaborates program environment left x →
      Elaborates program environment right y →
      Elaborates program environment (.expression [.symbol op.name, left, right]) (.binary op x y)
  | branch {kind : Kind} {test yes no : Atom} {t : Expr Slot .test} {y n : Expr Slot kind}
      (clear : Clear program "if") : Elaborates program environment test t →
      Elaborates program environment yes y → Elaborates program environment no n →
      Elaborates program environment (.expression [.symbol "if", test, yes, no]) (.branch t y n)

theorem Elaborates.returns {Slot : Type} {program : SpaceSemantics.Program} {environment : Environment Slot}
    {source : Atom} {kind : Kind} {expression : Expr Slot kind}
    (elaborated : Elaborates program environment source expression)
    (caller : Subst) (state : Effects.State) (locals : Slot → Data)
    (captured : Captured environment caller locals) (value : Value kind)
    (computed : expression.eval locals = some value) :
    PureReturns program caller state source state (encode value) := by
  induction elaborated with
  | integer v => cases computed; exact grounded_returns program caller state (.int v)
  | symbol name _ => cases computed; exact symbol_returns program caller state name
  | boolean v => cases computed; exact grounded_returns program caller state (.bool v)
  | bound name slot found =>
      cases computed
      exact bound_returns program caller state (captured name slot found)
  | @binary a b c op left right x y _ ex ey ihx ihy =>
      cases first : x.eval locals with
      | none => simp [Expr.eval, first] at computed
      | some vx =>
          cases second : y.eval locals with
          | none => simp [Expr.eval, first, second] at computed
          | some vy =>
              have result : op.eval vx vy = some value := by simpa [Expr.eval, first, second] using computed
              apply native_binary_call_returns program caller state state state state op.name
                left right (encode vx) (encode vy) (encode value)
                (by cases op <;> simp [Binary.name, ioHead]) (by cases op <;> simp [Binary.name, StdLib.known])
                (by cases op <;> simp [argumentIsRaw, Binary.name, StdLib.known, StdLib.rawArgument])
                (by cases op <;> simp [argumentIsRaw, Binary.name, StdLib.known, StdLib.rawArgument])
                (ihx vx first) (ihy vy second) (binary_primitive op state vx vy value result)
                (by cases op <;> simp [Binary.name])
  | @branch k test yes no t y n _ et ey en iht ihy ihn =>
      cases tested : t.eval locals with
      | none => simp [Expr.eval, tested] at computed
      | some flag =>
          apply pure_if_returns program caller state test flag yes no (encode value) (iht flag tested)
          cases flag
          · exact ihn value (by simpa [Expr.eval, tested] using computed)
          · exact ihy value (by simpa [Expr.eval, tested] using computed)

structure Extracted {Slot : Type} (program : SpaceSemantics.Program) (environment : Environment Slot) (source : Atom) where
  kind : Kind
  expression : Expr Slot kind
  derivation : Elaborates program environment source expression

def selectBinary (head : String) (a b : Kind) : Option (Sigma (Binary a b)) :=
  match head, a, b with
  | "+", .data, .data => some ⟨.data, .add⟩
  | "-", .data, .data => some ⟨.data, .sub⟩
  | "<", .data, .data => some ⟨.test, .lt⟩
  | "<=", .data, .data => some ⟨.test, .le⟩
  | ">", .data, .data => some ⟨.test, .gt⟩
  | ">=", .data, .data => some ⟨.test, .ge⟩
  | "==", _, _ => some ⟨.test, .equal⟩
  | _, _, _ => none

def elaborate {Slot : Type} (program : SpaceSemantics.Program) (environment : Environment Slot) :
    (source : Atom) → Option (Extracted program environment source)
  | .grounded (.int value) => some ⟨.data, .literal (.integer value), .integer value⟩
  | .grounded (.bool value) => some ⟨.test, .boolean value, .boolean value⟩
  | .symbol name => if inert : Inert program name then
      some ⟨.data, .literal (.symbol name), .symbol name inert⟩ else none
  | .var name => match found : environment name with
      | some slot => some ⟨.data, .read slot, .bound name slot found⟩
      | none => none
  | .expression [.symbol "if", test, yes, no] => do
      if clear : Clear program "if" then
        let t ← elaborate program environment test
        let y ← elaborate program environment yes
        let n ← elaborate program environment no
        match t with
        | ⟨.data, _, _⟩ => none
        | ⟨.test, t, dt⟩ =>
            match y, n with
            | ⟨.data, y, dy⟩, ⟨.data, n, dn⟩ =>
                return ⟨.data, .branch t y n, .branch clear dt dy dn⟩
            | ⟨.test, y, dy⟩, ⟨.test, n, dn⟩ =>
                return ⟨.test, .branch t y n, .branch clear dt dy dn⟩
            | _, _ => none
      else none
  | .expression [.symbol head, left, right] => do
      let x ← elaborate program environment left
      let y ← elaborate program environment right
      let ⟨kind, op⟩ ← selectBinary head x.kind y.kind
      if same : op.name = head then
        if clear : Clear program op.name then
          return ⟨kind, .binary op x.expression y.expression,
            same ▸ Elaborates.binary op clear x.derivation y.derivation⟩
        else none
      else none
  | _ => none
termination_by structural source => source

theorem extracted_completed_iff {Slot : Type} {program : SpaceSemantics.Program} {environment : Environment Slot}
    {source : Atom} (certificate : Extracted program environment source)
    (caller : Subst) (state : Effects.State) (locals : Slot → Data)
    (captured : Captured environment caller locals) (value : Value certificate.kind)
    (computed : certificate.expression.eval locals = some value)
    (after : Effects.State) (answers input output : List Atom) :
    (∃ fuel, run program fuel {state, control := .evaluate caller source} = .complete after answers input output) ↔
      after = state ∧ answers = [encode value] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff program caller state state source (encode value)
    (certificate.derivation.returns caller state locals captured value computed) after answers input output

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScalarSource
