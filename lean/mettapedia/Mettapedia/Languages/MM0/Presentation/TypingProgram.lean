import Mettapedia.Languages.MM0.Presentation.ContextData
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.ListData

/-!
# Authored MM0 expression typing

The equations look up declared symbols and context binders, retain unapplied
arguments, and distinguish bound arguments from regular saturated arguments.
Signature lookup and the typing recursion are equations, not host operations.
Only list views and unbounded natural arithmetic belong to the shared host.
The signature contains previously admitted declarations; admitting them is a
separate operation. Missing entries and ill-typed applications return `None`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.ComputationalTyping

open Kernel ComputationalContext
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

abbrev SignatureTable := List (Nat × TermDecl)

def signatureOf : SignatureTable → TermSignature
  | [], _ => none
  | (key, declaration) :: rest, index =>
      if index = key then some declaration else signatureOf rest index

def encodeTable (table : SignatureTable) : Term :=
  .list (table.map fun (index, declaration) => .list [natural index, encodeDeclaration declaration])

def encodeType : Option ExpressionType → Term
  | none => .sym "None"
  | some (remaining, sort) => .expr [.sym "MM0:Inferred", encodeContext remaining, natural sort]

def encodeBinderResult : Option Kernel.Binder → Term
  | none => .sym "None"
  | some binder => .expr [.sym "Some", encodeBinder binder]

def encodeDeclarationResult : Option TermDecl → Term
  | none => .sym "None"
  | some declaration => .expr [.sym "Some", encodeDeclaration declaration]

def encodeSortResult : Option Nat → Term
  | none => .sym "None"
  | some sort => .expr [.sym "Some", natural sort]

private def call (head : String) (arguments : List Term) : Term := .expr (.sym head :: arguments)
private def slot (name : String) : Term := .var name
private def equation (name head : String) (arguments : List Term) (body : Term) : Equation :=
  ⟨name, head, arguments, body⟩

def typingProgram : Program := [
  equation "at" "mm0:data-at" [slot "values", slot "index"]
    (call "mm0:at-view" [call "nik:list-view" [slot "values"], slot "index"]),
  equation "at-empty" "mm0:at-view" [.sym "List:Nil", slot "index"] (.sym "None"),
  equation "at-cons" "mm0:at-view"
    [call "List:Cons" [slot "first", slot "rest"], slot "index"]
    (call "mm0:at-zero" [call "nik:nat-zero" [slot "index"], slot "first", slot "rest", slot "index"]),
  equation "at-zero" "mm0:at-zero" [.sym "True", slot "first", slot "rest", slot "index"]
    (call "Some" [slot "first"]),
  equation "at-next" "mm0:at-zero" [.sym "False", slot "first", slot "rest", slot "index"]
    (call "mm0:data-at" [slot "rest", call "nik:nat-pred" [slot "index"]]),
  equation "declaration" "mm0:declaration" [slot "table", slot "index"]
    (call "mm0:declaration-view" [call "nik:list-view" [slot "table"], slot "index"]),
  equation "declaration-empty" "mm0:declaration-view" [.sym "List:Nil", slot "index"] (.sym "None"),
  equation "declaration-cons" "mm0:declaration-view"
    [call "List:Cons" [.list [slot "key", slot "declaration"], slot "rest"], slot "index"]
    (call "mm0:declaration-equal" [call "nik:nat-eq" [slot "index", slot "key"],
      slot "declaration", slot "rest", slot "index"]),
  equation "declaration-equal" "mm0:declaration-equal"
    [.sym "True", slot "declaration", slot "rest", slot "index"] (call "Some" [slot "declaration"]),
  equation "declaration-next" "mm0:declaration-equal"
    [.sym "False", slot "declaration", slot "rest", slot "index"]
    (call "mm0:declaration" [slot "rest", slot "index"]),
  equation "infer-variable" "mm0:infer" [slot "table", slot "context", call "MM0:Var" [slot "index"]]
    (call "mm0:infer-binder" [call "mm0:data-at" [slot "context", slot "index"]]),
  equation "infer-term" "mm0:infer" [slot "table", slot "context", call "MM0:Term" [slot "index"]]
    (call "mm0:infer-declaration" [call "mm0:declaration" [slot "table", slot "index"]]),
  equation "infer-application" "mm0:infer"
    [slot "table", slot "context", call "MM0:App" [slot "function", slot "argument"]]
    (call "mm0:infer-function" [call "mm0:infer" [slot "table", slot "context", slot "function"],
      slot "table", slot "context", slot "argument"]),
  equation "infer-missing-binder" "mm0:infer-binder" [.sym "None"] (.sym "None"),
  equation "infer-bound-binder" "mm0:infer-binder" [call "Some" [.list [.sym "MM0:Bound", slot "sort"]]]
    (call "MM0:Inferred" [.list [], slot "sort"]),
  equation "infer-regular-binder" "mm0:infer-binder"
    [call "Some" [.list [.sym "MM0:Regular", slot "sort", slot "dependencies"]]]
    (call "MM0:Inferred" [.list [], slot "sort"]),
  equation "infer-missing-declaration" "mm0:infer-declaration" [.sym "None"] (.sym "None"),
  equation "infer-declaration" "mm0:infer-declaration"
    [call "Some" [.list [.sym "MM0:TermDecl", slot "arguments", slot "sort", slot "dependencies"]]]
    (call "MM0:Inferred" [slot "arguments", slot "sort"]),
  equation "infer-function-none" "mm0:infer-function"
    [.sym "None", slot "table", slot "context", slot "argument"] (.sym "None"),
  equation "infer-function" "mm0:infer-function"
    [call "MM0:Inferred" [slot "arguments", slot "result"], slot "table", slot "context", slot "argument"]
    (call "mm0:infer-arguments" [call "nik:list-view" [slot "arguments"], slot "result",
      slot "table", slot "context", slot "argument"]),
  equation "infer-no-arguments" "mm0:infer-arguments"
    [.sym "List:Nil", slot "result", slot "table", slot "context", slot "argument"] (.sym "None"),
  equation "infer-bound-argument" "mm0:infer-arguments"
    [call "List:Cons" [.list [.sym "MM0:Bound", slot "sort"], slot "rest"],
      slot "result", slot "table", slot "context", slot "argument"]
    (call "mm0:infer-bound-sort" [call "mm0:bound-sort" [slot "context", slot "argument"],
      slot "sort", slot "rest", slot "result"]),
  equation "infer-regular-argument" "mm0:infer-arguments"
    [call "List:Cons" [.list [.sym "MM0:Regular", slot "sort", slot "dependencies"], slot "rest"],
      slot "result", slot "table", slot "context", slot "argument"]
    (call "mm0:infer-regular-type" [call "mm0:infer" [slot "table", slot "context", slot "argument"],
      slot "sort", slot "rest", slot "result"]),
  equation "bound-sort-var" "mm0:bound-sort" [slot "context", call "MM0:Var" [slot "index"]]
    (call "mm0:bound-binder" [call "mm0:data-at" [slot "context", slot "index"]]),
  equation "bound-sort-term" "mm0:bound-sort" [slot "context", call "MM0:Term" [slot "index"]] (.sym "None"),
  equation "bound-sort-app" "mm0:bound-sort"
    [slot "context", call "MM0:App" [slot "function", slot "argument"]] (.sym "None"),
  equation "bound-binder-none" "mm0:bound-binder" [.sym "None"] (.sym "None"),
  equation "bound-binder-bound" "mm0:bound-binder" [call "Some" [.list [.sym "MM0:Bound", slot "sort"]]]
    (call "Some" [slot "sort"]),
  equation "bound-binder-regular" "mm0:bound-binder"
    [call "Some" [.list [.sym "MM0:Regular", slot "sort", slot "dependencies"]]] (.sym "None"),
  equation "infer-bound-sort-none" "mm0:infer-bound-sort"
    [.sym "None", slot "expected", slot "rest", slot "result"] (.sym "None"),
  equation "infer-bound-sort" "mm0:infer-bound-sort"
    [call "Some" [slot "sort"], slot "expected", slot "rest", slot "result"]
    (call "mm0:infer-sort-equal" [call "nik:nat-eq" [slot "sort", slot "expected"], slot "rest", slot "result"]),
  equation "infer-regular-none" "mm0:infer-regular-type"
    [.sym "None", slot "expected", slot "rest", slot "result"] (.sym "None"),
  equation "infer-regular-type" "mm0:infer-regular-type"
    [call "MM0:Inferred" [slot "remaining", slot "sort"], slot "expected", slot "rest", slot "result"]
    (call "mm0:infer-saturated" [call "nik:list-view" [slot "remaining"], slot "sort", slot "expected",
      slot "rest", slot "result"]),
  equation "infer-saturated" "mm0:infer-saturated"
    [.sym "List:Nil", slot "sort", slot "expected", slot "rest", slot "result"]
    (call "mm0:infer-sort-equal" [call "nik:nat-eq" [slot "sort", slot "expected"], slot "rest", slot "result"]),
  equation "infer-unsaturated" "mm0:infer-saturated"
    [call "List:Cons" [slot "first", slot "tail"], slot "sort", slot "expected", slot "rest", slot "result"]
    (.sym "None"),
  equation "infer-sort-equal" "mm0:infer-sort-equal" [.sym "True", slot "rest", slot "result"]
    (call "MM0:Inferred" [slot "rest", slot "result"]),
  equation "infer-sort-different" "mm0:infer-sort-equal" [.sym "False", slot "rest", slot "result"]
    (.sym "None")]

theorem typingProgram_leftLinear : LeftLinear typingProgram := by
  simp [LeftLinear, typingProgram, equation, call, slot, patternVarsList, patternVars]

theorem typingProgram_dataSeparated : DataSeparated typingProgram computationalHost where
  undefined := by
    intro head member
    simp [constructorHeads] at member
    rcases member with rfl | rfl | rfl <;> simp [Program.defines, typingProgram, equation]
  unhandled := by
    intro head member arguments
    simp [constructorHeads] at member
    rcases member with rfl | rfl | rfl <;> rfl

theorem encodeType_injective : Function.Injective encodeType := by
  intro first second same
  cases first with
  | none => cases second <;> first | rfl | cases same
  | some first =>
    cases second with
    | none => cases same
    | some second =>
      obtain ⟨remaining, sort⟩ := first
      obtain ⟨remaining', sort'⟩ := second
      have parts : encodeContext remaining = encodeContext remaining' ∧ natural sort = natural sort' := by
        simpa only [encodeType, Term.expr.injEq, List.cons.injEq, true_and, and_true] using same
      have contexts := encodeContext_injective parts.1
      have sorts := congrArg natural? parts.2
      simp only [natural_roundtrip, Option.some.injEq] at sorts
      cases contexts
      cases sorts
      rfl

end Mettapedia.Languages.MM0.Presentation.ComputationalTyping
