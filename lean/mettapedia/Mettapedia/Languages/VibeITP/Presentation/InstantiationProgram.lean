import Mettapedia.Languages.VibeITP.Presentation.SubstitutionSignature

/-!
# Authored postorder free-variable instantiation

The program determines free-variable occurrence from explicit signature data,
prunes closed subtrees, processes arguments before replacing a target head,
and composes the authored shift and bound-variable substitution operations.
Statement admission separately checks symbol kind, value depth and final
closure. The host remains scalar arithmetic and typed list operations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalInstantiation

open ComputationalData ComputationalShift ComputationalSubstitution
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

private def call (head : String) (arguments : List Term) : Term := .expr (.sym head :: arguments)
private def slot (name : String) : Term := .var name
private def equation (name head : String) (arguments : List Term) (body : Term) : Equation :=
  ⟨name, head, arguments, body⟩

def instantiationEquations : Program := [
  equation "is-fvar" "vibe:is-fvar" [slot "table", slot "symbol"]
    (call "vibe:is-fvar-info" [call "vibe:lookup-symbol" [slot "table", slot "symbol"]]),
  equation "is-fvar-unknown" "vibe:is-fvar-info" [.sym "None"]
    (.sym "False"),
  equation "is-fvar-constant" "vibe:is-fvar-info" [call "Some" [call "Vibe:SymInfo" [.sym "Constant", slot "binders"]]]
    (.sym "False"),
  equation "is-fvar-declared" "vibe:is-fvar-info" [call "Some" [call "Vibe:SymInfo" [.sym "Fvar", slot "binders"]]]
    (.sym "True"),
  equation "has-fvar-bvar" "vibe:has-fvar" [slot "table", call "Vibe:BVar" [slot "i"]]
    (.sym "False"),
  equation "has-fvar-literal" "vibe:has-fvar" [slot "table", call "Vibe:Lit" [slot "bytes"]]
    (.sym "False"),
  equation "has-fvar-app" "vibe:has-fvar" [slot "table", call "Vibe:App" [slot "symbol", slot "arguments"]]
    (call "vibe:has-fvar-head" [call "vibe:is-fvar" [slot "table", slot "symbol"], slot "table", slot "arguments"]),
  equation "has-fvar-head-true" "vibe:has-fvar-head" [.sym "True", slot "table", slot "arguments"]
    (.sym "True"),
  equation "has-fvar-head-false" "vibe:has-fvar-head" [.sym "False", slot "table", slot "arguments"]
    (call "vibe:has-fvar-args" [slot "table", slot "arguments"]),
  equation "has-fvar-args" "vibe:has-fvar-args" [slot "table", slot "arguments"]
    (call "vibe:has-fvar-view" [slot "table", call "nik:list-view" [slot "arguments"]]),
  equation "has-fvar-nil" "vibe:has-fvar-view" [slot "table", .sym "List:Nil"]
    (.sym "False"),
  equation "has-fvar-cons" "vibe:has-fvar-view" [slot "table", call "List:Cons" [slot "first", slot "rest"]]
    (call "vibe:has-fvar-first" [call "vibe:has-fvar" [slot "table", slot "first"], slot "table", slot "rest"]),
  equation "has-fvar-first-true" "vibe:has-fvar-first" [.sym "True", slot "table", slot "rest"]
    (.sym "True"),
  equation "has-fvar-first-false" "vibe:has-fvar-first" [.sym "False", slot "table", slot "rest"]
    (call "vibe:has-fvar-args" [slot "table", slot "rest"]),
  equation "instantiate-bvar" "vibe:inst-go" [slot "table", slot "F", slot "arity", slot "value", slot "offset", call "Vibe:BVar" [slot "i"]]
    (call "Some" [call "Vibe:BVar" [slot "i"]]),
  equation "instantiate-literal" "vibe:inst-go" [slot "table", slot "F", slot "arity", slot "value", slot "offset", call "Vibe:Lit" [slot "bytes"]]
    (call "Some" [call "Vibe:Lit" [slot "bytes"]]),
  equation "instantiate-app" "vibe:inst-go" [slot "table", slot "F", slot "arity", slot "value", slot "offset", call "Vibe:App" [slot "symbol", slot "arguments"]]
    (call "vibe:inst-pruned" [call "vibe:has-fvar" [slot "table", call "Vibe:App" [slot "symbol", slot "arguments"]], slot "table", slot "F", slot "arity", slot "value", slot "offset", slot "symbol", slot "arguments"]),
  equation "instantiate-pruned" "vibe:inst-pruned" [.sym "False", slot "table", slot "F", slot "arity", slot "value", slot "offset", slot "symbol", slot "arguments"]
    (call "Some" [call "Vibe:App" [slot "symbol", slot "arguments"]]),
  equation "instantiate-traverse" "vibe:inst-pruned" [.sym "True", slot "table", slot "F", slot "arity", slot "value", slot "offset", slot "symbol", slot "arguments"]
    (call "vibe:inst-args-result" [call "vibe:inst-args" [slot "table", slot "F", slot "arity", slot "value", slot "offset", call "vibe:binders" [slot "table", slot "symbol"], slot "arguments"], slot "table", slot "F", slot "arity", slot "value", slot "offset", slot "symbol"]),
  equation "instantiate-args-none" "vibe:inst-args-result" [.sym "None", slot "table", slot "F", slot "arity", slot "value", slot "offset", slot "symbol"]
    (.sym "None"),
  equation "instantiate-args-some" "vibe:inst-args-result" [call "Some" [slot "arguments"], slot "table", slot "F", slot "arity", slot "value", slot "offset", slot "symbol"]
    (call "vibe:inst-head" [call "vibe:symbol-eq" [slot "symbol", slot "F"], slot "table", slot "F", slot "arity", slot "value", slot "offset", slot "symbol", slot "arguments"]),
  equation "instantiate-other-head" "vibe:inst-head" [.sym "False", slot "table", slot "F", slot "arity", slot "value", slot "offset", slot "symbol", slot "arguments"]
    (call "Some" [call "Vibe:App" [slot "symbol", slot "arguments"]]),
  equation "instantiate-target-head" "vibe:inst-head" [.sym "True", slot "table", slot "F", slot "arity", slot "value", slot "offset", slot "symbol", slot "arguments"]
    (call "vibe:inst-value" [call "vibe:shift" [slot "table", slot "value", slot "offset", slot "arity"], slot "table", slot "arity", slot "arguments"]),
  equation "instantiate-value-none" "vibe:inst-value" [.sym "None", slot "table", slot "arity", slot "arguments"]
    (.sym "None"),
  equation "instantiate-value-some" "vibe:inst-value" [call "Some" [slot "value"], slot "table", slot "arity", slot "arguments"]
    (call "vibe:subst" [slot "table", slot "arity", slot "arguments", slot "value", natural 0]),
  equation "instantiate-args" "vibe:inst-args" [slot "table", slot "F", slot "arity", slot "value", slot "offset", slot "binders", slot "arguments"]
    (call "vibe:inst-args-view" [slot "table", slot "F", slot "arity", slot "value", slot "offset", slot "binders", call "nik:list-view" [slot "arguments"]]),
  equation "instantiate-args-nil" "vibe:inst-args-view" [slot "table", slot "F", slot "arity", slot "value", slot "offset", slot "binders", .sym "List:Nil"]
    (call "Some" [.list []]),
  equation "instantiate-args-cons" "vibe:inst-args-view" [slot "table", slot "F", slot "arity", slot "value", slot "offset", slot "binders", call "List:Cons" [slot "first", slot "rest"]]
    (call "vibe:inst-args-binder" [slot "table", slot "F", slot "arity", slot "value", slot "offset", call "nik:list-view" [slot "binders"], slot "first", slot "rest"]),
  equation "instantiate-args-no-binder" "vibe:inst-args-binder" [slot "table", slot "F", slot "arity", slot "value", slot "offset", .sym "List:Nil", slot "first", slot "rest"]
    (call "vibe:inst-args-bound" [call "nik:nat-lt" [slot "offset", natural Spec.wordBound], slot "table", slot "F", slot "arity", slot "value", slot "offset", .list [], slot "offset", slot "first", slot "rest"]),
  equation "instantiate-args-binder" "vibe:inst-args-binder" [slot "table", slot "F", slot "arity", slot "value", slot "offset", call "List:Cons" [slot "bound", slot "tail"], slot "first", slot "rest"]
    (call "vibe:inst-args-bound" [call "nik:nat-lt" [call "nik:nat-add" [slot "offset", slot "bound"], natural Spec.wordBound], slot "table", slot "F", slot "arity", slot "value", slot "offset", slot "tail", call "nik:nat-add" [slot "offset", slot "bound"], slot "first", slot "rest"]),
  equation "instantiate-args-overflow" "vibe:inst-args-bound" [.sym "False", slot "table", slot "F", slot "arity", slot "value", slot "offset", slot "binders", slot "inside", slot "first", slot "rest"]
    (.sym "None"),
  equation "instantiate-args-in-bounds" "vibe:inst-args-bound" [.sym "True", slot "table", slot "F", slot "arity", slot "value", slot "offset", slot "binders", slot "inside", slot "first", slot "rest"]
    (call "vibe:inst-args-first" [call "vibe:inst-go" [slot "table", slot "F", slot "arity", slot "value", slot "inside", slot "first"], slot "table", slot "F", slot "arity", slot "value", slot "offset", slot "binders", slot "rest"]),
  equation "instantiate-first-none" "vibe:inst-args-first" [.sym "None", slot "table", slot "F", slot "arity", slot "value", slot "offset", slot "binders", slot "rest"]
    (.sym "None"),
  equation "instantiate-first-some" "vibe:inst-args-first" [call "Some" [slot "first"], slot "table", slot "F", slot "arity", slot "value", slot "offset", slot "binders", slot "rest"]
    (call "vibe:inst-args-rest" [slot "first", call "vibe:inst-args" [slot "table", slot "F", slot "arity", slot "value", slot "offset", slot "binders", slot "rest"]]),
  equation "instantiate-rest-none" "vibe:inst-args-rest" [slot "first", .sym "None"]
    (.sym "None"),
  equation "instantiate-rest-some" "vibe:inst-args-rest" [slot "first", call "Some" [slot "rest"]]
    (call "Some" [call "nik:list-cons" [slot "first", slot "rest"]]),
  equation "instantiate-statement" "vibe:instantiate" [slot "table", slot "F", slot "value", slot "statement"]
    (call "vibe:inst-declaration" [call "vibe:lookup-symbol" [slot "table", slot "F"], slot "table", slot "F", slot "value", slot "statement"]),
  equation "instantiate-unknown" "vibe:inst-declaration" [.sym "None", slot "table", slot "F", slot "value", slot "statement"]
    (.sym "None"),
  equation "instantiate-constant" "vibe:inst-declaration" [call "Some" [call "Vibe:SymInfo" [.sym "Constant", slot "binders"]], slot "table", slot "F", slot "value", slot "statement"]
    (.sym "None"),
  equation "instantiate-fvar" "vibe:inst-declaration" [call "Some" [call "Vibe:SymInfo" [.sym "Fvar", slot "binders"]], slot "table", slot "F", slot "value", slot "statement"]
    (call "vibe:inst-arity" [call "vibe:list-length" [slot "binders"], slot "table", slot "F", slot "value", slot "statement"]),
  equation "instantiate-arity" "vibe:inst-arity" [slot "arity", slot "table", slot "F", slot "value", slot "statement"]
    (call "vibe:inst-value-depth" [call "nik:nat-le" [call "vibe:depth" [slot "table", slot "value"], slot "arity"], slot "table", slot "F", slot "arity", slot "value", slot "statement"]),
  equation "instantiate-value-open" "vibe:inst-value-depth" [.sym "False", slot "table", slot "F", slot "arity", slot "value", slot "statement"]
    (.sym "None"),
  equation "instantiate-value-valid" "vibe:inst-value-depth" [.sym "True", slot "table", slot "F", slot "arity", slot "value", slot "statement"]
    (call "vibe:inst-statement-result" [call "vibe:inst-go" [slot "table", slot "F", slot "arity", slot "value", natural 0, slot "statement"], slot "table"]),
  equation "instantiate-statement-none" "vibe:inst-statement-result" [.sym "None", slot "table"]
    (.sym "None"),
  equation "instantiate-statement-some" "vibe:inst-statement-result" [call "Some" [slot "result"], slot "table"]
    (call "vibe:inst-statement-closed" [call "nik:nat-zero" [call "vibe:depth" [slot "table", slot "result"]], slot "result"]),
  equation "instantiate-result-closed" "vibe:inst-statement-closed" [.sym "True", slot "result"]
    (call "Some" [slot "result"]),
  equation "instantiate-result-open" "vibe:inst-statement-closed" [.sym "False", slot "result"]
    (.sym "None") ]

def instantiationProgram : Program := substitutionProgram ++ instantiationEquations

theorem instantiationEquations_disjoint :
    ∀ equation ∈ instantiationEquations, equation.head ∉ substitutionProgram.calledHeads := by
  have fresh : instantiationEquations.all (fun equation =>
      !substitutionProgram.calledHeads.contains equation.head) = true := by decide +kernel
  intro equation member
  simpa using List.all_eq_true.mp fresh equation member

theorem instantiationProgram_leftLinear : LeftLinear instantiationProgram := by
  have additional : LeftLinear instantiationEquations := by
    simp [LeftLinear, instantiationEquations, equation, call, slot, patternVarsList, patternVars]
  intro equation member
  rcases List.mem_append.mp member with old | added
  · exact substitutionProgram_leftLinear equation old
  · exact additional equation added

theorem instantiationProgram_dataSeparated : DataSeparated instantiationProgram computationalHost where
  undefined := by
    intro head member
    have old := substitutionProgram_dataSeparated.undefined head member
    have added : instantiationEquations.defines head = false := by
      simp [constructorHeads] at member
      rcases member with rfl | rfl | rfl <;> simp [Program.defines, instantiationEquations, equation]
    change (substitutionProgram ++ instantiationEquations).any _ = false
    rw [List.any_append]
    change (substitutionProgram.defines head || instantiationEquations.defines head) = false
    rw [old, added]
    rfl
  unhandled := by
    intro head member arguments
    simp [constructorHeads] at member
    rcases member with rfl | rfl | rfl <;> rfl

theorem reuse_substitution_call {head : String} {arguments : List Term} {result : Term}
    (used : head ∈ substitutionProgram.calledHeads)
    (computed : Applies substitutionProgram computationalHost head arguments result) :
    Applies instantiationProgram computationalHost head arguments result :=
  (Applies.append_iff substitutionProgram instantiationEquations computationalHost
    instantiationEquations_disjoint head used arguments result).mpr computed

end Mettapedia.Languages.VibeITP.Presentation.ComputationalInstantiation
