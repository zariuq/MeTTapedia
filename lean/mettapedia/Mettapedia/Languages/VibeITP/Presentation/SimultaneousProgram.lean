import Mettapedia.Languages.VibeITP.Presentation.InferenceFormation
import Mettapedia.Languages.VibeITP.Spec.SimultaneousInstantiation

/-!
# Authored simultaneous instantiation

The replacement environment is ordinary retained data. Validation visits every
entry; lookup selects the first match. The traversal processes original
children, then uses the existing shift and bound-variable substitution code
without revisiting the inserted replacement. The host remains the existing
generic scalar/list host. Whole-proof checking is a separate caller.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalSimultaneous

open ComputationalData ComputationalShift ComputationalSubstitution
open ComputationalInstantiation ComputationalInference
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

def encodeReplacement (replacement : Spec.SymId × Spec.Term) : Term :=
  .list [encodeSymbol replacement.1, encode replacement.2]

def encodeReplacements (replacements : List (Spec.SymId × Spec.Term)) : Term :=
  .list (replacements.map encodeReplacement)

def encodeEntry (entry : Spec.SimultaneousInstantiation.Entry) : Term :=
  .list [encodeSymbol entry.symbol, natural entry.arity, encode entry.value]

def encodeEntries (entries : List Spec.SimultaneousInstantiation.Entry) : Term :=
  .list (entries.map encodeEntry)

def encodeEntryResult : Option Spec.SimultaneousInstantiation.Entry → Term
  | none => .sym "None"
  | some entry => .expr [.sym "Some", encodeEntry entry]

def encodePreparation : Option (List Spec.SimultaneousInstantiation.Entry) → Term
  | none => .sym "None"
  | some entries => .expr [.sym "Some", encodeEntries entries]

private def call (head : String) (arguments : List Term) : Term := .expr (.sym head :: arguments)
private def slot (name : String) : Term := .var name
private def equation (name head : String) (arguments : List Term) (body : Term) : Equation :=
  ⟨name, head, arguments, body⟩
private def someResult (value : Term) : Term := call "Some" [value]

def simultaneousEquations : Program := [
  equation "many-lookup" "vibe:many-lookup" [slot "entries", slot "symbol"]
    (call "vibe:many-lookup-view" [call "nik:list-view" [slot "entries"], slot "symbol"]),
  equation "many-lookup-nil" "vibe:many-lookup-view" [.sym "List:Nil", slot "symbol"] (.sym "None"),
  equation "many-lookup-cons" "vibe:many-lookup-view"
    [call "List:Cons" [.list [slot "first", slot "arity", slot "value"], slot "rest"], slot "symbol"]
    (call "vibe:many-lookup-same" [call "vibe:symbol-eq" [slot "symbol", slot "first"],
      slot "first", slot "arity", slot "value", slot "rest", slot "symbol"]),
  equation "many-lookup-first" "vibe:many-lookup-same"
    [.sym "True", slot "first", slot "arity", slot "value", slot "rest", slot "symbol"]
    (someResult (.list [slot "first", slot "arity", slot "value"])),
  equation "many-lookup-later" "vibe:many-lookup-same"
    [.sym "False", slot "first", slot "arity", slot "value", slot "rest", slot "symbol"]
    (call "vibe:many-lookup" [slot "rest", slot "symbol"]),
  equation "many-prepare" "vibe:many-prepare" [slot "table", slot "replacements"]
    (call "vibe:many-prepare-view" [slot "table", call "nik:list-view" [slot "replacements"]]),
  equation "many-prepare-nil" "vibe:many-prepare-view" [slot "table", .sym "List:Nil"]
    (someResult (.list [])),
  equation "many-prepare-cons" "vibe:many-prepare-view"
    [slot "table", call "List:Cons" [.list [slot "symbol", slot "value"], slot "rest"]]
    (call "vibe:many-prepare-info" [call "vibe:lookup-symbol" [slot "table", slot "symbol"],
      slot "table", slot "symbol", slot "value", slot "rest"]),
  equation "many-prepare-unknown" "vibe:many-prepare-info"
    [.sym "None", slot "table", slot "symbol", slot "value", slot "rest"] (.sym "None"),
  equation "many-prepare-constant" "vibe:many-prepare-info"
    [someResult (call "Vibe:SymInfo" [.sym "Constant", slot "binders"]),
      slot "table", slot "symbol", slot "value", slot "rest"] (.sym "None"),
  equation "many-prepare-fvar" "vibe:many-prepare-info"
    [someResult (call "Vibe:SymInfo" [.sym "Fvar", slot "binders"]),
      slot "table", slot "symbol", slot "value", slot "rest"]
    (call "vibe:many-prepare-arity" [call "vibe:list-length" [slot "binders"],
      slot "table", slot "symbol", slot "value", slot "rest"]),
  equation "many-prepare-arity" "vibe:many-prepare-arity"
    [slot "arity", slot "table", slot "symbol", slot "value", slot "rest"]
    (call "vibe:many-prepare-depth" [call "nik:nat-le"
      [call "vibe:depth" [slot "table", slot "value"], slot "arity"],
      slot "arity", slot "table", slot "symbol", slot "value", slot "rest"]),
  equation "many-prepare-open" "vibe:many-prepare-depth"
    [.sym "False", slot "arity", slot "table", slot "symbol", slot "value", slot "rest"] (.sym "None"),
  equation "many-prepare-valid" "vibe:many-prepare-depth"
    [.sym "True", slot "arity", slot "table", slot "symbol", slot "value", slot "rest"]
    (call "vibe:many-prepare-rest" [call "vibe:many-prepare" [slot "table", slot "rest"],
      slot "symbol", slot "arity", slot "value"]),
  equation "many-prepare-rest-none" "vibe:many-prepare-rest"
    [.sym "None", slot "symbol", slot "arity", slot "value"] (.sym "None"),
  equation "many-prepare-rest-some" "vibe:many-prepare-rest"
    [someResult (slot "rest"), slot "symbol", slot "arity", slot "value"]
    (someResult (call "nik:list-cons" [.list [slot "symbol", slot "arity", slot "value"], slot "rest"])),
  equation "many-go-bvar" "vibe:many-go"
    [slot "table", slot "entries", slot "offset", call "Vibe:BVar" [slot "index"]]
    (someResult (call "Vibe:BVar" [slot "index"])),
  equation "many-go-literal" "vibe:many-go"
    [slot "table", slot "entries", slot "offset", call "Vibe:Lit" [slot "bytes"]]
    (someResult (call "Vibe:Lit" [slot "bytes"])),
  equation "many-go-app" "vibe:many-go"
    [slot "table", slot "entries", slot "offset", call "Vibe:App" [slot "symbol", slot "arguments"]]
    (call "vibe:many-pruned" [call "vibe:has-fvar"
      [slot "table", call "Vibe:App" [slot "symbol", slot "arguments"]],
      slot "table", slot "entries", slot "offset", slot "symbol", slot "arguments"]),
  equation "many-pruned" "vibe:many-pruned"
    [.sym "False", slot "table", slot "entries", slot "offset", slot "symbol", slot "arguments"]
    (someResult (call "Vibe:App" [slot "symbol", slot "arguments"])),
  equation "many-traverse" "vibe:many-pruned"
    [.sym "True", slot "table", slot "entries", slot "offset", slot "symbol", slot "arguments"]
    (call "vibe:many-children" [call "vibe:many-args" [slot "table", slot "entries", slot "offset",
      call "vibe:binders" [slot "table", slot "symbol"], slot "arguments"],
      slot "table", slot "entries", slot "offset", slot "symbol"]),
  equation "many-children-none" "vibe:many-children"
    [.sym "None", slot "table", slot "entries", slot "offset", slot "symbol"] (.sym "None"),
  equation "many-children-some" "vibe:many-children"
    [someResult (slot "arguments"), slot "table", slot "entries", slot "offset", slot "symbol"]
    (call "vibe:many-head" [call "vibe:many-lookup" [slot "entries", slot "symbol"],
      slot "table", slot "offset", slot "symbol", slot "arguments"]),
  equation "many-head-unchanged" "vibe:many-head"
    [.sym "None", slot "table", slot "offset", slot "symbol", slot "arguments"]
    (someResult (call "Vibe:App" [slot "symbol", slot "arguments"])),
  equation "many-head-replaced" "vibe:many-head"
    [someResult (.list [slot "target", slot "arity", slot "value"]),
      slot "table", slot "offset", slot "symbol", slot "arguments"]
    (call "vibe:inst-value" [call "vibe:shift" [slot "table", slot "value", slot "offset", slot "arity"],
      slot "table", slot "arity", slot "arguments"]),
  equation "many-args" "vibe:many-args"
    [slot "table", slot "entries", slot "offset", slot "binders", slot "arguments"]
    (call "vibe:many-args-view" [slot "table", slot "entries", slot "offset", slot "binders",
      call "nik:list-view" [slot "arguments"]]),
  equation "many-args-nil" "vibe:many-args-view"
    [slot "table", slot "entries", slot "offset", slot "binders", .sym "List:Nil"]
    (someResult (.list [])),
  equation "many-args-cons" "vibe:many-args-view"
    [slot "table", slot "entries", slot "offset", slot "binders", call "List:Cons" [slot "first", slot "rest"]]
    (call "vibe:many-args-binder" [slot "table", slot "entries", slot "offset",
      call "nik:list-view" [slot "binders"], slot "first", slot "rest"]),
  equation "many-args-no-binder" "vibe:many-args-binder"
    [slot "table", slot "entries", slot "offset", .sym "List:Nil", slot "first", slot "rest"]
    (call "vibe:many-args-bound" [call "nik:nat-lt" [slot "offset", natural Spec.wordBound],
      slot "table", slot "entries", slot "offset", .list [], slot "offset", slot "first", slot "rest"]),
  equation "many-args-binder" "vibe:many-args-binder"
    [slot "table", slot "entries", slot "offset", call "List:Cons" [slot "bound", slot "tail"],
      slot "first", slot "rest"]
    (call "vibe:many-args-bound" [call "nik:nat-lt"
      [call "nik:nat-add" [slot "offset", slot "bound"], natural Spec.wordBound],
      slot "table", slot "entries", slot "offset", slot "tail",
      call "nik:nat-add" [slot "offset", slot "bound"], slot "first", slot "rest"]),
  equation "many-args-overflow" "vibe:many-args-bound"
    [.sym "False", slot "table", slot "entries", slot "offset", slot "binders", slot "inside",
      slot "first", slot "rest"] (.sym "None"),
  equation "many-args-in-bounds" "vibe:many-args-bound"
    [.sym "True", slot "table", slot "entries", slot "offset", slot "binders", slot "inside",
      slot "first", slot "rest"]
    (call "vibe:many-args-first" [call "vibe:many-go" [slot "table", slot "entries", slot "inside", slot "first"],
      slot "table", slot "entries", slot "offset", slot "binders", slot "rest"]),
  equation "many-args-first-none" "vibe:many-args-first"
    [.sym "None", slot "table", slot "entries", slot "offset", slot "binders", slot "rest"] (.sym "None"),
  equation "many-args-first-some" "vibe:many-args-first"
    [someResult (slot "first"), slot "table", slot "entries", slot "offset", slot "binders", slot "rest"]
    (call "vibe:inst-args-rest" [slot "first",
      call "vibe:many-args" [slot "table", slot "entries", slot "offset", slot "binders", slot "rest"]]),
  equation "many-statement" "vibe:instantiate-many" [slot "table", slot "replacements", slot "statement"]
    (call "vibe:many-prepared" [call "vibe:many-prepare" [slot "table", slot "replacements"],
      slot "table", slot "statement"]),
  equation "many-prepared-none" "vibe:many-prepared" [.sym "None", slot "table", slot "statement"] (.sym "None"),
  equation "many-prepared-some" "vibe:many-prepared" [someResult (slot "entries"), slot "table", slot "statement"]
    (call "vibe:many-nonempty" [call "nik:list-view" [slot "entries"], slot "entries", slot "table", slot "statement"]),
  equation "many-empty" "vibe:many-nonempty" [.sym "List:Nil", slot "entries", slot "table", slot "statement"]
    (call "vibe:inst-statement-result" [someResult (slot "statement"), slot "table"]),
  equation "many-nonempty" "vibe:many-nonempty"
    [call "List:Cons" [slot "first", slot "rest"], slot "entries", slot "table", slot "statement"]
    (call "vibe:inst-statement-result" [call "vibe:many-go" [slot "table", slot "entries", natural 0, slot "statement"],
      slot "table"]),
  equation "many-formed" "vibe:many-formed" [slot "table", slot "replacements"]
    (call "vibe:many-formed-view" [slot "table", call "nik:list-view" [slot "replacements"]]),
  equation "many-formed-nil" "vibe:many-formed-view" [slot "table", .sym "List:Nil"] (.sym "True"),
  equation "many-formed-cons" "vibe:many-formed-view"
    [slot "table", call "List:Cons" [.list [slot "symbol", slot "value"], slot "rest"]]
    (call "vibe:many-formed-first" [call "vibe:well-formed" [slot "table", slot "value"], slot "table", slot "rest"]),
  equation "many-formed-false" "vibe:many-formed-first" [.sym "False", slot "table", slot "rest"] (.sym "False"),
  equation "many-formed-true" "vibe:many-formed-first" [.sym "True", slot "table", slot "rest"]
    (call "vibe:many-formed" [slot "table", slot "rest"]),
  equation "many-theorem" "vibe:thm-instantiate-many" [slot "table", slot "replacements", slot "statement"]
    (call "vibe:many-theorem-formed" [call "vibe:many-formed" [slot "table", slot "replacements"],
      slot "table", slot "replacements", slot "statement"]),
  equation "many-theorem-unformed" "vibe:many-theorem-formed"
    [.sym "False", slot "table", slot "replacements", slot "statement"] (.sym "None"),
  equation "many-theorem-formed" "vibe:many-theorem-formed"
    [.sym "True", slot "table", slot "replacements", slot "statement"]
    (call "vibe:instantiate-many" [slot "table", slot "replacements", slot "statement"]) ]

def simultaneousProgram : Program := inferenceProgram ++ simultaneousEquations

theorem simultaneousEquations_disjoint :
    ∀ equation ∈ simultaneousEquations, equation.head ∉ inferenceProgram.calledHeads := by
  have fresh : simultaneousEquations.all (fun equation =>
      decide (equation.head ∉ inferenceProgram.calledHeads)) = true := by decide +kernel
  intro equation member
  simpa using List.all_eq_true.mp fresh equation member

theorem simultaneousProgram_leftLinear : LeftLinear simultaneousProgram := by
  have added : LeftLinear simultaneousEquations := by
    simp [LeftLinear, simultaneousEquations, equation, call, slot, someResult, patternVarsList, patternVars]
  intro equation member
  rcases List.mem_append.mp member with old | fresh
  · exact inferenceProgram_leftLinear equation old
  · exact added equation fresh

theorem simultaneousProgram_dataSeparated : DataSeparated simultaneousProgram computationalHost where
  undefined := by
    intro head member
    have old := inferenceProgram_dataSeparated.undefined head member
    have added : simultaneousEquations.defines head = false := by
      simp [constructorHeads] at member
      rcases member with rfl | rfl | rfl <;> simp [Program.defines, simultaneousEquations, equation]
    change (inferenceProgram ++ simultaneousEquations).any _ = false
    rw [List.any_append]
    change (inferenceProgram.defines head || simultaneousEquations.defines head) = false
    rw [old, added]
    rfl
  unhandled := by
    intro head member arguments
    simp [constructorHeads] at member
    rcases member with rfl | rfl | rfl <;> rfl

theorem reuse_inference_call {head : String} {arguments : List Term} {result : Term}
    (used : head ∈ inferenceProgram.calledHeads)
    (computed : Applies inferenceProgram computationalHost head arguments result) :
    Applies simultaneousProgram computationalHost head arguments result :=
  (Applies.append_iff inferenceProgram simultaneousEquations computationalHost
    simultaneousEquations_disjoint head used arguments result).mpr computed

theorem old_inference_execution (fuel : Nat) (head : String)
    (used : head ∈ inferenceProgram.calledHeads) (arguments : List Term) :
    apply simultaneousProgram computationalHost fuel head arguments =
      apply inferenceProgram computationalHost fuel head arguments :=
  apply_append_eq inferenceProgram simultaneousEquations computationalHost
    simultaneousEquations_disjoint fuel head used arguments

end Mettapedia.Languages.VibeITP.Presentation.ComputationalSimultaneous
