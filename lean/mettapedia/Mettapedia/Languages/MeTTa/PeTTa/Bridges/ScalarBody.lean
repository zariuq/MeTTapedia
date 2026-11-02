import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScalarSource

/-!
# Scalar callback bodies with flat tuples and selected branches

Tuple fields retain their individual value sorts. Static head admission and
the live output-head test are separate: a variable-headed source tuple may
produce a symbol whose callability depends on the captured program. A failed
test declines privately rather than publishing a partial tuple.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScalarBody

open Mettapedia.Machines.TypedScalar
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Eval ScalarSource

abbrev Packed (Slot : Type) := Sigma (Expr Slot)

def evalField {Slot : Type} (locals : Slot → Data) (field : Packed Slot) : Option Atom :=
  (field.2.eval locals).map encode

def evalFields {Slot : Type} (locals : Slot → Data) : List (Packed Slot) → Option (List Atom)
  | [] => some []
  | first :: rest => do
      let value ← evalField locals first
      let values ← evalFields locals rest
      return value :: values

inductive Fields {Slot : Type} (program : SpaceSemantics.Program) (environment : Environment Slot) :
    List Atom → List (Packed Slot) → Prop
  | nil : Fields program environment [] []
  | cons {source : Atom} {kind : Kind} {expression : Expr Slot kind} {sources : List Atom} {fields : List (Packed Slot)} :
      Elaborates program environment source expression → Fields program environment sources fields →
      Fields program environment (source :: sources) (⟨kind, expression⟩ :: fields)

def compileFields {Slot : Type} (program : SpaceSemantics.Program) (environment : Environment Slot) :
    (sources : List Atom) → Option {fields : List (Packed Slot) // Fields program environment sources fields}
  | [] => some ⟨[], .nil⟩
  | first :: rest => do
      let field ← ScalarSource.elaborate program environment first
      let fields ← compileFields program environment rest
      return ⟨⟨field.kind, field.expression⟩ :: fields.val, .cons field.derivation fields.property⟩

theorem Fields.returns {Slot : Type} {program : SpaceSemantics.Program} {environment : Environment Slot}
    {sources : List Atom} {fields : List (Packed Slot)} (compiled : Fields program environment sources fields)
    (caller : Subst) (state : Effects.State) (locals : Slot → Data)
    (captured : Captured environment caller locals) (values : List Atom)
    (computed : evalFields locals fields = some values) :
    List.Forall₂ (fun source value => PureReturns program caller state source state value) sources values := by
  induction compiled generalizing values with
  | nil => cases computed; exact .nil
  | @cons source kind expression sources fields first rest ih =>
      cases evaluated : expression.eval locals with
      | none => simp [evalFields, evalField, evaluated] at computed
      | some value =>
          cases tail : evalFields locals fields with
          | none => simp [evalFields, evalField, evaluated, tail] at computed
          | some more =>
              have same : encode value :: more = values := by simpa [evalFields, evalField, evaluated, tail] using computed
              subst values
              exact .cons (first.returns caller state locals captured value evaluated) (ih more tail)

inductive Head (program : SpaceSemantics.Program) : Atom → Prop
  | bound (name : String) : Head program (.var name)
  | integer (value : Int) : Head program (.grounded (.int value))
  | symbol (name : String) (inert : Inert program name) : Head program (.symbol name)

def checkHead (program : SpaceSemantics.Program) : (source : Atom) → Option (PLift (Head program source))
  | .var name => some ⟨.bound name⟩
  | .grounded (.int value) => some ⟨.integer value⟩
  | .symbol name => if inert : Inert program name then some ⟨.symbol name inert⟩ else none
  | _ => none

def liveHead (program : SpaceSemantics.Program) : List Atom → Bool
  | .grounded (.int _) :: _ => true
  | .symbol head :: _ => decide (Inert program head)
  | _ => false

inductive Body (Slot : Type)
  | scalar (field : Packed Slot)
  | tuple (fields : List (Packed Slot))
  | branch (test : Expr Slot .test) (yes no : Body Slot)

def Body.eval {Slot : Type} (program : SpaceSemantics.Program) (locals : Slot → Data) : Body Slot → Option Atom
  | .scalar field => evalField locals field
  | .tuple fields => do
      let values ← evalFields locals fields
      if liveHead program values then some (.expression values) else none
  | .branch test yes no => do
      let choose ← test.eval locals
      if choose then yes.eval program locals else no.eval program locals

inductive Compiles {Slot : Type} (program : SpaceSemantics.Program) (environment : Environment Slot) :
    Atom → Body Slot → Prop
  | scalar {source : Atom} {kind : Kind} {expression : Expr Slot kind} :
      Elaborates program environment source expression → Compiles program environment source (.scalar ⟨kind, expression⟩)
  | tuple {head : Atom} {tail : List Atom} {fields : List (Packed Slot)} :
      Head program head → Fields program environment (head :: tail) fields →
      Compiles program environment (.expression (head :: tail)) (.tuple fields)
  | branch {test yes no : Atom} {t : Expr Slot .test} {y n : Body Slot} :
      Clear program "if" → Elaborates program environment test t →
      Compiles program environment yes y → Compiles program environment no n →
      Compiles program environment (.expression [.symbol "if", test, yes, no]) (.branch t y n)

theorem Compiles.returns {Slot : Type} {program : SpaceSemantics.Program} {environment : Environment Slot}
    {source : Atom} {body : Body Slot} (compiled : Compiles program environment source body)
    (caller : Subst) (state : Effects.State) (locals : Slot → Data)
    (captured : Captured environment caller locals) (value : Atom)
    (computed : body.eval program locals = some value) : PureReturns program caller state source state value := by
  induction compiled generalizing value with
  | @scalar source kind expression extracted =>
      cases result : expression.eval locals with
      | none => simp [Body.eval, evalField, result] at computed
      | some answer =>
          have same : encode answer = value := by simpa [Body.eval, evalField, result] using computed
          subst value
          exact extracted.returns caller state locals captured answer result
  | @tuple head tail fields admitted extracted =>
      cases result : evalFields locals fields with
      | none => simp [Body.eval, result] at computed
      | some values =>
          have same : Atom.expression values = value := by
            by_cases accepted : liveHead program values = true
            · simpa [Body.eval, result, accepted] using computed
            · simp [Body.eval, result, accepted] at computed
          subst value
          have returned := extracted.returns caller state locals captured values result
          cases admitted with
          | bound name =>
              exact .step (step_transition rfl) (PureData.arguments_return program caller state _ _ returned [] 0)
          | integer number =>
              exact .step (step_transition rfl) (PureData.arguments_return program caller state _ _ returned [] 0)
          | symbol name inert =>
              cases returned with
              | cons first rest =>
                  apply data_call_returns program caller state state name tail _ inert.1 _ (by simp_all [Inert])
                  exact PureData.arguments_return program caller state _ _ (.cons first rest) [] 0
  | @branch test yes no t y n clear extracted cy cn iht ihy =>
      cases result : t.eval locals with
      | none => simp [Body.eval, result] at computed
      | some choose =>
          apply BridgeKit.pure_if_returns program caller state test choose yes no value
            (extracted.returns caller state locals captured choose result)
          cases choose
          · exact ihy value (by simpa [Body.eval, result] using computed)
          · exact iht value (by simpa [Body.eval, result] using computed)

def elaborate {Slot : Type} (program : SpaceSemantics.Program) (environment : Environment Slot) :
    (source : Atom) → Option {body : Body Slot // Compiles program environment source body}
  | .expression [.symbol "if", test, yes, no] => do
      if clear : Clear program "if" then
        let predicate ← ScalarSource.elaborate program environment test
        match predicate with
        | ⟨.data, _, _⟩ => none
        | ⟨.test, t, dt⟩ =>
            let y ← elaborate program environment yes
            let n ← elaborate program environment no
            return ⟨.branch t y.val n.val, .branch clear dt y.property n.property⟩
      else none
  | source =>
      match ScalarSource.elaborate program environment source with
      | some extracted => some ⟨.scalar ⟨extracted.kind, extracted.expression⟩, .scalar extracted.derivation⟩
      | none => match source with
        | .expression (head :: tail) => do
            let admitted ← checkHead program head
            let fields ← compileFields program environment (head :: tail)
            return ⟨.tuple fields.val, .tuple admitted.down fields.property⟩
        | _ => none
termination_by structural source => source

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScalarBody
