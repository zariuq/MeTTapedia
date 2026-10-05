import Mettapedia.Languages.MM0.Presentation.Data

/-!
# Authored MM0 substitution equations

These equations are semantic input to the shared deterministic equation
evaluator. They traverse MM0 preterms and the supplied substitution list.
Only zero testing and predecessor use the small natural-number host. No
primitive invokes MM0 substitution or proof checking.

`Some` and `None` are data outcomes; evaluator exhaustion remains distinct.
Application substitution retains the reference computation's short circuit:
the argument is visited only after function substitution succeeds.

Linearity, separation and the concrete controls below do not constitute the
universal substitution correspondence theorem, which is a further obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation

open Kernel
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

private def call (head : String) (arguments : List Term) : Term :=
  .expr (.sym head :: arguments)

private def slot (name : String) : Term := .var name

private def equation (name head : String) (arguments : List Term) (body : Term) : Equation :=
  ⟨name, head, arguments, body⟩

def substitutionProgram : Program := [
  equation "subst-var" "mm0:subst" [call "MM0:Var" [slot "i"], slot "values"]
    (call "mm0:lookup" [slot "values", slot "i"]),
  equation "subst-term" "mm0:subst" [call "MM0:Term" [slot "i"], slot "values"]
    (call "Some" [call "MM0:Term" [slot "i"]]),
  equation "subst-app" "mm0:subst"
    [call "MM0:App" [slot "f", slot "x"], slot "values"]
    (call "mm0:subst-function" [call "mm0:subst" [slot "f", slot "values"],
      slot "x", slot "values"]),
  equation "subst-function-none" "mm0:subst-function"
    [.sym "None", slot "x", slot "values"] (.sym "None"),
  equation "subst-function-some" "mm0:subst-function"
    [call "Some" [slot "f"], slot "x", slot "values"]
    (call "mm0:subst-argument" [slot "f",
      call "mm0:subst" [slot "x", slot "values"]]),
  equation "subst-argument-none" "mm0:subst-argument"
    [slot "f", .sym "None"] (.sym "None"),
  equation "subst-argument-some" "mm0:subst-argument"
    [slot "f", call "Some" [slot "x"]]
    (call "Some" [call "MM0:App" [slot "f", slot "x"]]),
  equation "lookup-nil" "mm0:lookup" [.sym "LNil", slot "i"] (.sym "None"),
  equation "lookup-cons" "mm0:lookup"
    [call "LCons" [slot "h", slot "t"], slot "i"]
    (call "mm0:lookup-zero" [call "nik:nat-zero" [slot "i"],
      slot "h", slot "t", slot "i"]),
  equation "lookup-zero" "mm0:lookup-zero"
    [.sym "True", slot "h", slot "t", slot "i"] (call "Some" [slot "h"]),
  equation "lookup-successor" "mm0:lookup-zero"
    [.sym "False", slot "h", slot "t", slot "i"]
    (call "mm0:lookup" [slot "t", call "nik:nat-pred" [slot "i"]])]

def encodeValues : List Preterm → Term
  | [] => .sym "LNil"
  | first :: rest => .expr [.sym "LCons", encode first, encodeValues rest]

def encodeResult : Option Preterm → Term
  | none => .sym "None"
  | some term => .expr [.sym "Some", encode term]

theorem substitutionProgram_leftLinear : LeftLinear substitutionProgram := by
  simp [LeftLinear, substitutionProgram, equation, call, slot, patternVarsList, patternVars]

theorem substitutionProgram_dataSeparated : DataSeparated substitutionProgram naturalHost where
  undefined := by
    intro head member
    simp [constructorHeads] at member
    rcases member with rfl | rfl | rfl <;>
      simp [Program.defines, substitutionProgram, equation]
  unhandled := by
    intro head member arguments
    simp [constructorHeads] at member
    rcases member with rfl | rfl | rfl <;> rfl

theorem term_computation (symbol : Nat) :
    apply substitutionProgram naturalHost 4 "mm0:subst"
      [encode (.term symbol), encodeValues []] = .value (encodeResult (some (.term symbol))) := rfl

theorem undefined_variable_computation (index : Nat) :
    apply substitutionProgram naturalHost 6 "mm0:subst"
      [encode (.var index), encodeValues []] = .value (encodeResult none) := rfl

theorem application_computation :
    apply substitutionProgram naturalHost 16 "mm0:subst"
      [encode (.app (.term 1) (.term 2)), encodeValues []] =
        .value (encodeResult (some (.app (.term 1) (.term 2)))) := rfl

theorem application_refusal_computation :
    apply substitutionProgram naturalHost 16 "mm0:subst"
      [encode (.app (.term 1) (.var 0)), encodeValues []] =
        .value (encodeResult none) := rfl

end Mettapedia.Languages.MM0.Presentation
