import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEReturns
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ShapeTyping
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.RecognizedFolds

/-!
# HE's answers against three typed fast-path rules

HE checks the arguments of every call of a typed head, its calls to itself
included, and reads a constructor field declared `%Undefined%` as unchecked.
Three consequences for rules that skip checks, each read off HE's
interpreter (`Languages.MeTTa.HE.evalAtom`, with a grounded `+`) at the least
budget that completes the run and at budget forty, or off HE's typing rule
(`ShapeTyping`):

* **A judged position certifies no shape.** An application of a head with no
  declaration has no typing, so HE's argument check skips it at every
  parameter, whatever the parameter is (`undeclared_head_untyped`,
  `undeclared_argument_unchecked`): HE admits `(Foo 5 Nil)` where
  `(List Number)` is expected, and `(lsum (Foo 5 Nil))` is answered as
  written, with no error (`foo_admitted`). A typed fold's spine is therefore
  never certified by the check alone.
* **A recognized fold must keep the checks of a typed head's calls to
  itself.** Under `(: Nil Bar)`, `(: Cons (-> Number Bar Foo))` and
  `(: g (-> Foo Number))`, `(Cons 1 Nil)` passes `g`'s check, but the call
  `(g Nil)` the equations make does not: HE answers
  `(Error (g Nil) (BadArgType 1 Foo Bar))`, while the one walk of the spine
  answers `1` (`typed_fold_without_inversion`). With the recursive field
  declared at the formal, `(: Nil Foo)` and `(: Cons (-> Number Foo Foo))`,
  HE answers the walk's value (`typed_fold_with_inversion`); this is the
  inversion `RecognizedFolds.Inversion` asks of a typed head.
* **A field declared `%Undefined%` gives its value no static type.** With
  `(: MkBox (-> %Undefined% Box))`, `(f (MkBox (Cons "x" Nil)))` passes `f`'s
  check at `Box`, and HE's check of the field at `g`'s formal
  `(List Number)` fails: HE answers an error, where skipping that check runs
  `g`'s equations and answers `1` (`undefined_field_not_static`).
* **Re-evaluation answers a constructor value as itself, typed or untyped**
  (`value_answers_itself`); the typed run is the deeper one.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HETypedRuleControls

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.GSLT.LanguageDef.Collections.HECorrespondence.Interpreter
  (symbol apply equation typed)
open Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEReturns.Controls (num str)

/-- `(-> T₁ … Tₙ)` as an atom. -/
abbrev arrowAtom (types : List Atom) : Atom :=
  Mettapedia.GSLT.LanguageDef.Collections.HECorrespondence.Interpreter.arrow types

/-! ## An undeclared head has no typing -/

section Shape

open ShapeTyping

/-- **An application of an undeclared head has no typing** in HE's rule. -/
theorem undeclared_head_untyped (Γ : Decls) (f : String) (args : List Atom) (hf : Γ f = []) :
    (heInfo Γ (.expression (.symbol f :: args))).typs = [] := by
  rw [heInfo_expression]
  simp [heNode, heInfo_symbol, heLeaf, readRows, hf, heTupleParts]

/-- Its `get-type` answer is `%Undefined%`. -/
theorem undeclared_head_answers (Γ : Decls) (f : String) (args : List Atom) (hf : Γ f = []) :
    answers Γ (.expression (.symbol f :: args)) = [undefinedDeriv] := by
  simp [answers, answersOf, undeclared_head_untyped Γ f args hf]

/-- **HE's argument check skips it at every parameter**: whatever the
parameter `P`, the check continues with the next argument, so passing the
check says nothing about the argument's shape. -/
theorem undeclared_argument_unchecked (Γ : Decls) (f : String) (args : List Atom) (hf : Γ f = [])
    (d : Deriv) (R : Ty DVar) (i : ℕ) (P : Ty DVar) (Ps : List (Ty DVar)) (js : List HeInfo)
    (E : List (Eqn DVar)) :
    checkArgs d R i (P :: Ps) (heInfo Γ (.expression (.symbol f :: args)) :: js) E =
      checkArgs d R (i + 1) Ps js E := by
  simp [checkArgs, undeclared_head_untyped Γ f args hf]

end Shape

/-! ## HE's interpreter with a grounded `+` -/

/-- Integer addition as HE's grounded `+`. -/
def plusDispatch : GroundedDispatch where
  isExecutable op := op == symbol "+"
  execute
    | _, [.grounded (.int a), .grounded (.int b)] => .ok [(.grounded (.int (a + b)), Bindings.empty)]
    | _, _ => .incorrectArgument

/-- HE's answers for an atom at budget `fuel`, each with its bindings applied. -/
def answersWith (space : Space) (atom : Atom) (fuel : ℕ) : List Atom :=
  (evalAtom space plusDispatch atom Atom.undefinedType Bindings.empty fuel).map
    fun answer => answer.2.applyFull answer.1 20

/-- `(: List (-> Type Type))`-free list rows `(: Nil (List Number))` and
`(: Cons (-> Number (List Number) (List Number)))`, with
`(: lsum (-> (List Number) Number))` folding them. -/
def listSpace : Space := Space.ofList [
  typed "Nil" (apply "List" [symbol "Number"]),
  typed "Cons" (arrowAtom [symbol "Number", apply "List" [symbol "Number"], apply "List" [symbol "Number"]]),
  typed "lsum" (arrowAtom [apply "List" [symbol "Number"], symbol "Number"]),
  typed "+" (arrowAtom [symbol "Number", symbol "Number", symbol "Number"]),
  equation (apply "lsum" [symbol "Nil"]) (num 0),
  equation (apply "lsum" [apply "Cons" [.var "x", .var "r"]]) (apply "+" [.var "x", apply "lsum" [.var "r"]])]

set_option maxRecDepth 100000 in
/-- **HE admits `(Foo 5 Nil)` at `(List Number)`**: `(lsum (Foo 5 Nil))` is
answered as written, with no type error, at budget twelve and at budget
forty. -/
theorem foo_admitted :
    answersWith listSpace (apply "lsum" [apply "Foo" [num 5, symbol "Nil"]]) 12 =
      [apply "lsum" [apply "Foo" [num 5, symbol "Nil"]]] ∧
    answersWith listSpace (apply "lsum" [apply "Foo" [num 5, symbol "Nil"]]) 40 =
      [apply "lsum" [apply "Foo" [num 5, symbol "Nil"]]] := by
  constructor <;> decide

/-! ## A typed fold's calls to themselves -/

/-- `(: Nil N)`, `(: Cons (-> Number C Foo))`, `(: g (-> Foo Number))`,
`(= (g Nil) 0)` and `(= (g (Cons $x $r)) (+ $x (g $r)))`. -/
def foldSpace (rest nilType : Atom) : Space := Space.ofList [
  typed "Nil" nilType,
  typed "Cons" (arrowAtom [symbol "Number", rest, symbol "Foo"]),
  typed "g" (arrowAtom [symbol "Foo", symbol "Number"]),
  typed "+" (arrowAtom [symbol "Number", symbol "Number", symbol "Number"]),
  equation (apply "g" [symbol "Nil"]) (num 0),
  equation (apply "g" [apply "Cons" [.var "x", .var "r"]]) (apply "+" [.var "x", apply "g" [.var "r"]])]

/-- `g`'s equations as the machine recognizes them. -/
def gSpec : RecognizedFolds.Spec := ⟨"Nil", "Cons", 1, 0, .add, some 0, 0, false, 0⟩

/-- The walk of `(Cons 1 Nil)` answers `1`. -/
theorem walk_one :
    RecognizedFolds.runFold gSpec (.expression [.symbol "Cons", num 1, .symbol "Nil"]) = some 1 := by
  have h : (Atom.expression [.symbol "Cons", num 1, .symbol "Nil"]) =
      gSpec.family.build ⟨[⟨([num 1], []), rfl, rfl⟩], .symbol "Nil"⟩ := rfl
  rw [h]
  unfold RecognizedFolds.runFold
  rw [RecognizedFolds.readSpine_build gSpec _ rfl]
  decide

set_option maxRecDepth 100000 in
/-- **Without inversion the walk is wrong**: `(Cons 1 Nil)` is a `Foo`, but
its recursive field `Nil` is a `Bar`, and HE answers the error of the call
`(g Nil)` the equations make, at budget fourteen and at budget forty, where
the walk answers `1`. -/
theorem typed_fold_without_inversion :
    answersWith (foldSpace (symbol "Bar") (symbol "Bar"))
        (apply "g" [apply "Cons" [num 1, symbol "Nil"]]) 14 =
      [mkError (apply "g" [symbol "Nil"]) (.badArgType 1 (symbol "Foo") (symbol "Bar"))] ∧
    answersWith (foldSpace (symbol "Bar") (symbol "Bar"))
        (apply "g" [apply "Cons" [num 1, symbol "Nil"]]) 40 =
      [mkError (apply "g" [symbol "Nil"]) (.badArgType 1 (symbol "Foo") (symbol "Bar"))] ∧
    RecognizedFolds.runFold gSpec (.expression [.symbol "Cons", num 1, .symbol "Nil"]) = some 1 :=
  ⟨by decide, by decide, walk_one⟩

set_option maxRecDepth 100000 in
/-- **With inversion HE answers the walk's value**: under `(: Nil Foo)` and
`(: Cons (-> Number Foo Foo))`, `(g (Cons 1 (Cons 2 Nil)))` answers `3`, at
budget twenty-five and at budget forty. -/
theorem typed_fold_with_inversion :
    answersWith (foldSpace (symbol "Foo") (symbol "Foo"))
        (apply "g" [apply "Cons" [num 1, apply "Cons" [num 2, symbol "Nil"]]]) 25 = [num 3] ∧
    answersWith (foldSpace (symbol "Foo") (symbol "Foo"))
        (apply "g" [apply "Cons" [num 1, apply "Cons" [num 2, symbol "Nil"]]]) 40 = [num 3] := by
  constructor <;> decide

/-! ## A field declared `%Undefined%` -/

/-- `(: Nil (List $a))`, `(: Cons (-> $a (List $a) (List $a)))`,
`(: MkBox (-> %Undefined% Box))`, `(: f (-> Box Number))`,
`(= (f (MkBox $x)) (g $x))`, `(= (g Nil) 0)`, `(= (g (Cons $h $t)) 1)`, and,
when `typedG`, `(: g (-> (List Number) Number))`. -/
def boxSpace (typedG : Bool) : Space := Space.ofList ([
  typed "Nil" (apply "List" [.var "a"]),
  typed "Cons" (arrowAtom [.var "a", apply "List" [.var "a"], apply "List" [.var "a"]]),
  typed "MkBox" (arrowAtom [Atom.undefinedType, symbol "Box"]),
  typed "f" (arrowAtom [symbol "Box", symbol "Number"]),
  equation (apply "f" [apply "MkBox" [.var "x"]]) (apply "g" [.var "x"]),
  equation (apply "g" [symbol "Nil"]) (num 0),
  equation (apply "g" [apply "Cons" [.var "h", .var "t"]]) (num 1)] ++
  if typedG then [typed "g" (arrowAtom [apply "List" [symbol "Number"], symbol "Number"])] else [])

set_option maxRecDepth 100000 in
/-- **A field declared `%Undefined%` is not a static type**: HE rejects the
field `(Cons "x" Nil)` at `g`'s formal `(List Number)`, at budget twenty-two
and at budget forty; with that check skipped, `g`'s equations answer `1`. -/
theorem undefined_field_not_static :
    answersWith (boxSpace true) (apply "f" [apply "MkBox" [apply "Cons" [str "x", symbol "Nil"]]]) 22 =
      [mkError (apply "Cons" [str "x", symbol "Nil"])
        (.badType (apply "List" [symbol "Number"]) (apply "List" [symbol "String"]))] ∧
    answersWith (boxSpace true) (apply "f" [apply "MkBox" [apply "Cons" [str "x", symbol "Nil"]]]) 40 =
      [mkError (apply "Cons" [str "x", symbol "Nil"])
        (.badType (apply "List" [symbol "Number"]) (apply "List" [symbol "String"]))] ∧
    answersWith (boxSpace false) (apply "f" [apply "MkBox" [apply "Cons" [str "x", symbol "Nil"]]]) 22 =
      [num 1] ∧
    answersWith (boxSpace false) (apply "f" [apply "MkBox" [apply "Cons" [str "x", symbol "Nil"]]]) 40 =
      [num 1] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! ## Re-evaluating a constructor value -/

/-- `(Cons 1 (Cons 2 Nil))`. -/
def twoCells : Atom := apply "Cons" [num 1, apply "Cons" [num 2, symbol "Nil"]]

set_option maxRecDepth 100000 in
/-- **HE answers a constructor value as itself, typed or untyped.** Under the
typed rows of `listSpace` it does so from budget eighteen, budget seventeen
being too short; with no declarations, from budget eleven, ten being too
short. HE's own evaluator walks the typed value through its checks, deeper
than the untyped tuple: what a typed value saves is not HE's work but what an
implementation may skip once a recorded typing certifies the value
(`CompletedDelivery.evalAtom_completed`). -/
theorem value_answers_itself :
    answersWith listSpace twoCells 18 = [twoCells] ∧ answersWith listSpace twoCells 40 = [twoCells] ∧
      answersWith listSpace twoCells 17 ≠ [twoCells] ∧
      answersWith Space.empty twoCells 11 = [twoCells] ∧ answersWith Space.empty twoCells 40 = [twoCells] ∧
      answersWith Space.empty twoCells 10 ≠ [twoCells] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HETypedRuleControls
