import Mettapedia.Languages.VibeITP.Presentation.ComputationalData
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.ListData

/-!
# Authored Vibe signature lookup, depth and shifting equations

The signature is data: an ordered finite table of symbol identities and full
immutable symbol information. The first matching entry is used; an unknown
symbol has an empty binder list, as in the independent specification.

The equations compute depth, perform the amount/depth pruning and traverse
arguments under their individual binder counts. Word bounds are explicit
authored guards. Scalar arithmetic and typed list views are the only host
operations; there is no signature, depth or shift callback.

`Some` and `None` are completed data results. Fuel exhaustion is a different
evaluator outcome. Input indices, identities, arities and binder counts have
no incidental representation bound.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalShift

open ComputationalData
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

abbrev SignatureTable := List (Spec.SymId × Spec.SymInfo)

def signatureOf : SignatureTable → Spec.Sig
  | [], _ => none
  | (key, info) :: table, symbol =>
      if symbol = key then some info else signatureOf table symbol

def encodeKind : Spec.SymKind → Term
  | .constant => .sym "Constant"
  | .fvar => .sym "Fvar"

def encodeBinders (binders : List Nat) : Term := .list (binders.map natural)

def encodeInfo (info : Spec.SymInfo) : Term :=
  .expr [.sym "Vibe:SymInfo", encodeKind info.kind, encodeBinders info.binders]

def encodeBinding (binding : Spec.SymId × Spec.SymInfo) : Term :=
  .expr [.sym "Vibe:Binding", encodeSymbol binding.1,
    encodeKind binding.2.kind, encodeBinders binding.2.binders]

def encodeTable (table : SignatureTable) : Term := .list (table.map encodeBinding)

def encodeInfoResult : Option Spec.SymInfo → Term
  | none => .sym "None"
  | some info => .expr [.sym "Some", encodeInfo info]

def encodeResult : Option Spec.Term → Term
  | none => .sym "None"
  | some term => .expr [.sym "Some", encode term]

def encodeTermsResult : Option (List Spec.Term) → Term
  | none => .sym "None"
  | some terms => .expr [.sym "Some", .list (encodeTerms terms)]

private def call (head : String) (arguments : List Term) : Term := .expr (.sym head :: arguments)
private def slot (name : String) : Term := .var name
private def equation (name head : String) (arguments : List Term) (body : Term) : Equation :=
  ⟨name, head, arguments, body⟩

def shiftProgram : Program := [
  equation "symbol-builtin-builtin" "vibe:symbol-eq"
    [.list [.sym "Builtin", slot "i"], .list [.sym "Builtin", slot "j"]]
    (call "nik:nat-eq" [slot "i", slot "j"]),
  equation "symbol-fresh-fresh" "vibe:symbol-eq"
    [.list [.sym "Fresh", slot "i"], .list [.sym "Fresh", slot "j"]]
    (call "nik:nat-eq" [slot "i", slot "j"]),
  equation "symbol-builtin-fresh" "vibe:symbol-eq"
    [.list [.sym "Builtin", slot "i"], .list [.sym "Fresh", slot "j"]] (.sym "False"),
  equation "symbol-fresh-builtin" "vibe:symbol-eq"
    [.list [.sym "Fresh", slot "i"], .list [.sym "Builtin", slot "j"]] (.sym "False"),
  equation "lookup" "vibe:lookup-symbol" [slot "table", slot "symbol"]
    (call "vibe:lookup-view" [call "nik:list-view" [slot "table"], slot "symbol"]),
  equation "lookup-nil" "vibe:lookup-view" [.sym "List:Nil", slot "symbol"] (.sym "None"),
  equation "lookup-cons" "vibe:lookup-view"
    [call "List:Cons" [call "Vibe:Binding" [slot "key", slot "kind", slot "binders"],
      slot "tail"], slot "symbol"]
    (call "vibe:lookup-equal" [call "vibe:symbol-eq" [slot "symbol", slot "key"],
      slot "kind", slot "binders", slot "tail", slot "symbol"]),
  equation "lookup-equal" "vibe:lookup-equal"
    [.sym "True", slot "kind", slot "binders", slot "tail", slot "symbol"]
    (call "Some" [call "Vibe:SymInfo" [slot "kind", slot "binders"]]),
  equation "lookup-next" "vibe:lookup-equal"
    [.sym "False", slot "kind", slot "binders", slot "tail", slot "symbol"]
    (call "vibe:lookup-symbol" [slot "tail", slot "symbol"]),
  equation "binders" "vibe:binders" [slot "table", slot "symbol"]
    (call "vibe:binders-result" [call "vibe:lookup-symbol" [slot "table", slot "symbol"]]),
  equation "binders-unknown" "vibe:binders-result" [.sym "None"] (.list []),
  equation "binders-known" "vibe:binders-result"
    [call "Some" [call "Vibe:SymInfo" [slot "kind", slot "binders"]]] (slot "binders"),
  equation "depth-bvar" "vibe:depth" [slot "table", call "Vibe:BVar" [slot "i"]]
    (call "nik:nat-add" [slot "i", natural 1]),
  equation "depth-lit" "vibe:depth" [slot "table", call "Vibe:Lit" [slot "bytes"]] (natural 0),
  equation "depth-app" "vibe:depth"
    [slot "table", call "Vibe:App" [slot "symbol", slot "arguments"]]
    (call "vibe:depth-args" [slot "table", slot "arguments",
      call "vibe:binders" [slot "table", slot "symbol"]]),
  equation "depth-args" "vibe:depth-args" [slot "table", slot "arguments", slot "binders"]
    (call "vibe:depth-view" [slot "table", call "nik:list-view" [slot "arguments"], slot "binders"]),
  equation "depth-args-nil" "vibe:depth-view"
    [slot "table", .sym "List:Nil", slot "binders"] (natural 0),
  equation "depth-args-cons" "vibe:depth-view"
    [slot "table", call "List:Cons" [slot "first", slot "rest"], slot "binders"]
    (call "vibe:depth-binder" [slot "table", slot "first", slot "rest",
      call "nik:list-view" [slot "binders"]]),
  equation "depth-missing-binder" "vibe:depth-binder"
    [slot "table", slot "first", slot "rest", .sym "List:Nil"]
    (call "nik:nat-max" [call "nik:nat-monus" [call "vibe:depth" [slot "table", slot "first"], natural 0],
      call "vibe:depth-args" [slot "table", slot "rest", .list []]]),
  equation "depth-under-binder" "vibe:depth-binder"
    [slot "table", slot "first", slot "rest", call "List:Cons" [slot "bound", slot "tail"]]
    (call "nik:nat-max" [call "nik:nat-monus" [call "vibe:depth" [slot "table", slot "first"], slot "bound"],
      call "vibe:depth-args" [slot "table", slot "rest", slot "tail"]]),
  equation "shift-bvar" "vibe:shift"
    [slot "table", call "Vibe:BVar" [slot "i"], slot "amount", slot "cutoff"]
    (call "vibe:shift-bvar-zero" [call "nik:nat-zero" [slot "amount"],
      slot "i", slot "amount", slot "cutoff"]),
  equation "shift-lit" "vibe:shift"
    [slot "table", call "Vibe:Lit" [slot "bytes"], slot "amount", slot "cutoff"]
    (call "Some" [call "Vibe:Lit" [slot "bytes"]]),
  equation "shift-app" "vibe:shift"
    [slot "table", call "Vibe:App" [slot "symbol", slot "arguments"], slot "amount", slot "cutoff"]
    (call "vibe:shift-app-zero" [call "nik:nat-zero" [slot "amount"], slot "table",
      slot "symbol", slot "arguments", slot "amount", slot "cutoff"]),
  equation "shift-bvar-zero" "vibe:shift-bvar-zero"
    [.sym "True", slot "i", slot "amount", slot "cutoff"] (call "Some" [call "Vibe:BVar" [slot "i"]]),
  equation "shift-bvar-nonzero" "vibe:shift-bvar-zero"
    [.sym "False", slot "i", slot "amount", slot "cutoff"]
    (call "vibe:shift-bvar-closed" [call "nik:nat-le" [call "nik:nat-add" [slot "i", natural 1], slot "cutoff"],
      slot "i", slot "amount"]),
  equation "shift-bvar-closed" "vibe:shift-bvar-closed"
    [.sym "True", slot "i", slot "amount"] (call "Some" [call "Vibe:BVar" [slot "i"]]),
  equation "shift-bvar-open" "vibe:shift-bvar-closed"
    [.sym "False", slot "i", slot "amount"]
    (call "vibe:shift-bvar-word" [call "nik:nat-lt"
      [call "nik:nat-add" [call "nik:nat-add" [slot "i", slot "amount"], natural 1], natural Spec.wordBound],
      call "nik:nat-add" [slot "i", slot "amount"]]),
  equation "shift-bvar-word" "vibe:shift-bvar-word"
    [.sym "True", slot "i"] (call "Some" [call "Vibe:BVar" [slot "i"]]),
  equation "shift-bvar-overflow" "vibe:shift-bvar-word" [.sym "False", slot "i"] (.sym "None"),
  equation "shift-app-zero" "vibe:shift-app-zero"
    [.sym "True", slot "table", slot "symbol", slot "arguments", slot "amount", slot "cutoff"]
    (call "Some" [call "Vibe:App" [slot "symbol", slot "arguments"]]),
  equation "shift-app-nonzero" "vibe:shift-app-zero"
    [.sym "False", slot "table", slot "symbol", slot "arguments", slot "amount", slot "cutoff"]
    (call "vibe:shift-app-closed" [call "nik:nat-le"
      [call "vibe:depth" [slot "table", call "Vibe:App" [slot "symbol", slot "arguments"]], slot "cutoff"],
      slot "table", slot "symbol", slot "arguments", slot "amount", slot "cutoff"]),
  equation "shift-app-closed" "vibe:shift-app-closed"
    [.sym "True", slot "table", slot "symbol", slot "arguments", slot "amount", slot "cutoff"]
    (call "Some" [call "Vibe:App" [slot "symbol", slot "arguments"]]),
  equation "shift-app-open" "vibe:shift-app-closed"
    [.sym "False", slot "table", slot "symbol", slot "arguments", slot "amount", slot "cutoff"]
    (call "vibe:shift-app-result" [slot "symbol", call "vibe:shift-args"
      [slot "table", slot "arguments", call "vibe:binders" [slot "table", slot "symbol"],
        slot "amount", slot "cutoff"]]),
  equation "shift-app-none" "vibe:shift-app-result" [slot "symbol", .sym "None"] (.sym "None"),
  equation "shift-app-some" "vibe:shift-app-result"
    [slot "symbol", call "Some" [slot "arguments"]]
    (call "Some" [call "Vibe:App" [slot "symbol", slot "arguments"]]),
  equation "shift-args" "vibe:shift-args"
    [slot "table", slot "arguments", slot "binders", slot "amount", slot "cutoff"]
    (call "vibe:shift-args-view" [slot "table", call "nik:list-view" [slot "arguments"],
      slot "binders", slot "amount", slot "cutoff"]),
  equation "shift-args-nil" "vibe:shift-args-view"
    [slot "table", .sym "List:Nil", slot "binders", slot "amount", slot "cutoff"]
    (call "Some" [.list []]),
  equation "shift-args-cons" "vibe:shift-args-view"
    [slot "table", call "List:Cons" [slot "first", slot "rest"], slot "binders", slot "amount", slot "cutoff"]
    (call "vibe:shift-args-binder" [slot "table", slot "first", slot "rest",
      call "nik:list-view" [slot "binders"], slot "amount", slot "cutoff"]),
  equation "shift-args-missing-binder" "vibe:shift-args-binder"
    [slot "table", slot "first", slot "rest", .sym "List:Nil", slot "amount", slot "cutoff"]
    (call "vibe:shift-args-bound" [call "nik:nat-lt" [slot "cutoff", natural Spec.wordBound],
      slot "table", slot "first", slot "rest", .list [], slot "amount", slot "cutoff", slot "cutoff"]),
  equation "shift-args-under-binder" "vibe:shift-args-binder"
    [slot "table", slot "first", slot "rest", call "List:Cons" [slot "bound", slot "tail"],
      slot "amount", slot "cutoff"]
    (call "vibe:shift-args-bound" [call "nik:nat-lt"
      [call "nik:nat-add" [slot "cutoff", slot "bound"], natural Spec.wordBound],
      slot "table", slot "first", slot "rest", slot "tail", slot "amount", slot "cutoff",
      call "nik:nat-add" [slot "cutoff", slot "bound"]]),
  equation "shift-args-overflow" "vibe:shift-args-bound"
    [.sym "False", slot "table", slot "first", slot "rest", slot "binders", slot "amount", slot "cutoff", slot "inside"]
    (.sym "None"),
  equation "shift-args-bound" "vibe:shift-args-bound"
    [.sym "True", slot "table", slot "first", slot "rest", slot "binders", slot "amount", slot "cutoff", slot "inside"]
    (call "vibe:shift-args-first" [call "vibe:shift" [slot "table", slot "first", slot "amount", slot "inside"],
      slot "table", slot "rest", slot "binders", slot "amount", slot "cutoff"]),
  equation "shift-args-first-none" "vibe:shift-args-first"
    [.sym "None", slot "table", slot "rest", slot "binders", slot "amount", slot "cutoff"] (.sym "None"),
  equation "shift-args-first-some" "vibe:shift-args-first"
    [call "Some" [slot "first"], slot "table", slot "rest", slot "binders", slot "amount", slot "cutoff"]
    (call "vibe:shift-args-rest" [slot "first", call "vibe:shift-args"
      [slot "table", slot "rest", slot "binders", slot "amount", slot "cutoff"]]),
  equation "shift-args-rest-none" "vibe:shift-args-rest" [slot "first", .sym "None"] (.sym "None"),
  equation "shift-args-rest-some" "vibe:shift-args-rest" [slot "first", call "Some" [slot "rest"]]
    (call "Some" [call "nik:list-cons" [slot "first", slot "rest"]])]

theorem shiftProgram_leftLinear : LeftLinear shiftProgram := by
  simp [LeftLinear, shiftProgram, equation, call, slot, patternVarsList, patternVars]

theorem shiftProgram_dataSeparated : DataSeparated shiftProgram computationalHost where
  undefined := by
    intro head member
    simp [constructorHeads] at member
    rcases member with rfl | rfl | rfl <;> simp [Program.defines, shiftProgram, equation]
  unhandled := by
    intro head member arguments
    simp [constructorHeads] at member
    rcases member with rfl | rfl | rfl <;> rfl

theorem builtin_and_fresh_identifiers_remain_distinct (symbol : Spec.Builtin) (index : Nat) :
    encodeSymbol (.builtin symbol) ≠ encodeSymbol (.fresh index) := by
  intro same
  have decoded := congrArg decodeSymbol same
  simp at decoded

end Mettapedia.Languages.VibeITP.Presentation.ComputationalShift
