import Mettapedia.Languages.VibeITP.Presentation.ShiftSignature
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.ProgramExtension

/-!
# Authored Vibe bound-variable substitution

The equations extend the frozen shift program without capturing any of its
calls. They compute list length and default lookup, reverse the parameter
index, shift the selected replacement under its binders, and traverse all
application arguments with their individual offsets.

The argument count is explicit and need not equal the supplied list length.
Missing images therefore use the independent kernel's bound-variable-zero
default. Zero-count and closed-body pruning precede traversal and word guards.
The host remains scalar natural arithmetic and typed list views.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalSubstitution

open ComputationalData ComputationalShift
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

private def call (head : String) (arguments : List Term) : Term := .expr (.sym head :: arguments)
private def slot (name : String) : Term := .var name
private def equation (name head : String) (arguments : List Term) (body : Term) : Equation :=
  ⟨name, head, arguments, body⟩

def substitutionEquations : Program := [
  equation "length" "vibe:list-length" [slot "values"]
    (call "vibe:length-view" [call "nik:list-view" [slot "values"]]),
  equation "length-nil" "vibe:length-view" [.sym "List:Nil"] (natural 0),
  equation "length-cons" "vibe:length-view" [call "List:Cons" [slot "first", slot "rest"]]
    (call "nik:nat-add" [call "vibe:list-length" [slot "rest"], natural 1]),
  equation "get-default" "vibe:get-default" [slot "values", slot "index", slot "default"]
    (call "vibe:get-view" [call "nik:list-view" [slot "values"], slot "index", slot "default"]),
  equation "get-default-nil" "vibe:get-view" [.sym "List:Nil", slot "index", slot "default"]
    (slot "default"),
  equation "get-default-cons" "vibe:get-view"
    [call "List:Cons" [slot "first", slot "rest"], slot "index", slot "default"]
    (call "vibe:get-zero" [call "nik:nat-zero" [slot "index"], slot "first", slot "rest",
      slot "index", slot "default"]),
  equation "get-default-zero" "vibe:get-zero"
    [.sym "True", slot "first", slot "rest", slot "index", slot "default"] (slot "first"),
  equation "get-default-next" "vibe:get-zero"
    [.sym "False", slot "first", slot "rest", slot "index", slot "default"]
    (call "vibe:get-default" [slot "rest", call "nik:nat-pred" [slot "index"], slot "default"]),
  equation "substitute" "vibe:subst" [slot "table", slot "count", slot "images", slot "body", slot "offset"]
    (call "vibe:subst-zero" [call "nik:nat-zero" [slot "count"], slot "table", slot "count",
      slot "images", slot "body", slot "offset"]),
  equation "substitute-zero" "vibe:subst-zero"
    [.sym "True", slot "table", slot "count", slot "images", slot "body", slot "offset"]
    (call "Some" [slot "body"]),
  equation "substitute-nonzero" "vibe:subst-zero"
    [.sym "False", slot "table", slot "count", slot "images", slot "body", slot "offset"]
    (call "vibe:subst-go" [slot "table", slot "count", slot "images", slot "offset", slot "body"]),
  equation "substitute-bvar" "vibe:subst-go"
    [slot "table", slot "count", slot "images", slot "offset", call "Vibe:BVar" [slot "i"]]
    (call "vibe:subst-bvar-low" [call "nik:nat-le" [call "nik:nat-add" [slot "i", natural 1], slot "offset"],
      slot "table", slot "count", slot "images", slot "offset", slot "i"]),
  equation "substitute-literal" "vibe:subst-go"
    [slot "table", slot "count", slot "images", slot "offset", call "Vibe:Lit" [slot "bytes"]]
    (call "Some" [call "Vibe:Lit" [slot "bytes"]]),
  equation "substitute-application" "vibe:subst-go"
    [slot "table", slot "count", slot "images", slot "offset", call "Vibe:App" [slot "symbol", slot "arguments"]]
    (call "vibe:subst-app-closed" [call "nik:nat-le"
      [call "vibe:depth" [slot "table", call "Vibe:App" [slot "symbol", slot "arguments"]], slot "offset"],
      slot "table", slot "count", slot "images", slot "offset", slot "symbol", slot "arguments"]),
  equation "substitute-bvar-low" "vibe:subst-bvar-low"
    [.sym "True", slot "table", slot "count", slot "images", slot "offset", slot "i"]
    (call "Some" [call "Vibe:BVar" [slot "i"]]),
  equation "substitute-bvar-high" "vibe:subst-bvar-low"
    [.sym "False", slot "table", slot "count", slot "images", slot "offset", slot "i"]
    (call "vibe:subst-bvar-param" [call "nik:nat-lt" [call "nik:nat-monus" [slot "i", slot "offset"], slot "count"],
      slot "table", slot "count", slot "images", slot "offset", call "nik:nat-monus" [slot "i", slot "offset"]]),
  equation "substitute-parameter" "vibe:subst-bvar-param"
    [.sym "True", slot "table", slot "count", slot "images", slot "offset", slot "relative"]
    (call "vibe:shift" [slot "table", call "vibe:get-default"
      [slot "images", call "nik:nat-monus" [call "nik:nat-monus" [slot "count", natural 1], slot "relative"],
        call "Vibe:BVar" [natural 0]], slot "offset", natural 0]),
  equation "substitute-above-parameters" "vibe:subst-bvar-param"
    [.sym "False", slot "table", slot "count", slot "images", slot "offset", slot "relative"]
    (call "vibe:subst-bvar-word" [call "nik:nat-lt" [call "nik:nat-add" [slot "relative", natural 1],
      natural Spec.wordBound], slot "relative"]),
  equation "substitute-bvar-word" "vibe:subst-bvar-word" [.sym "True", slot "relative"]
    (call "Some" [call "Vibe:BVar" [slot "relative"]]),
  equation "substitute-bvar-overflow" "vibe:subst-bvar-word" [.sym "False", slot "relative"] (.sym "None"),
  equation "substitute-app-closed" "vibe:subst-app-closed"
    [.sym "True", slot "table", slot "count", slot "images", slot "offset", slot "symbol", slot "arguments"]
    (call "Some" [call "Vibe:App" [slot "symbol", slot "arguments"]]),
  equation "substitute-app-open" "vibe:subst-app-closed"
    [.sym "False", slot "table", slot "count", slot "images", slot "offset", slot "symbol", slot "arguments"]
    (call "vibe:subst-app-result" [slot "symbol", call "vibe:subst-args"
      [slot "table", slot "count", slot "images", slot "offset", call "vibe:binders" [slot "table", slot "symbol"],
        slot "arguments"]]),
  equation "substitute-app-none" "vibe:subst-app-result" [slot "symbol", .sym "None"] (.sym "None"),
  equation "substitute-app-some" "vibe:subst-app-result" [slot "symbol", call "Some" [slot "arguments"]]
    (call "Some" [call "Vibe:App" [slot "symbol", slot "arguments"]]),
  equation "substitute-args" "vibe:subst-args"
    [slot "table", slot "count", slot "images", slot "offset", slot "binders", slot "arguments"]
    (call "vibe:subst-args-view" [slot "table", slot "count", slot "images", slot "offset", slot "binders",
      call "nik:list-view" [slot "arguments"]]),
  equation "substitute-args-nil" "vibe:subst-args-view"
    [slot "table", slot "count", slot "images", slot "offset", slot "binders", .sym "List:Nil"]
    (call "Some" [.list []]),
  equation "substitute-args-cons" "vibe:subst-args-view"
    [slot "table", slot "count", slot "images", slot "offset", slot "binders", call "List:Cons" [slot "first", slot "rest"]]
    (call "vibe:subst-args-binder" [slot "table", slot "count", slot "images", slot "offset",
      call "nik:list-view" [slot "binders"], slot "first", slot "rest"]),
  equation "substitute-args-missing-binder" "vibe:subst-args-binder"
    [slot "table", slot "count", slot "images", slot "offset", .sym "List:Nil", slot "first", slot "rest"]
    (call "vibe:subst-args-bound" [call "nik:nat-lt" [slot "offset", natural Spec.wordBound],
      slot "table", slot "count", slot "images", slot "offset", .list [], slot "offset", slot "first", slot "rest"]),
  equation "substitute-args-under-binder" "vibe:subst-args-binder"
    [slot "table", slot "count", slot "images", slot "offset", call "List:Cons" [slot "bound", slot "tail"],
      slot "first", slot "rest"]
    (call "vibe:subst-args-bound" [call "nik:nat-lt"
      [call "nik:nat-add" [slot "offset", slot "bound"], natural Spec.wordBound],
      slot "table", slot "count", slot "images", slot "offset", slot "tail",
      call "nik:nat-add" [slot "offset", slot "bound"], slot "first", slot "rest"]),
  equation "substitute-args-overflow" "vibe:subst-args-bound"
    [.sym "False", slot "table", slot "count", slot "images", slot "offset", slot "binders", slot "inside",
      slot "first", slot "rest"] (.sym "None"),
  equation "substitute-args-bound" "vibe:subst-args-bound"
    [.sym "True", slot "table", slot "count", slot "images", slot "offset", slot "binders", slot "inside",
      slot "first", slot "rest"]
    (call "vibe:subst-args-first" [call "vibe:subst-go"
      [slot "table", slot "count", slot "images", slot "inside", slot "first"],
      slot "table", slot "count", slot "images", slot "offset", slot "binders", slot "rest"]),
  equation "substitute-args-first-none" "vibe:subst-args-first"
    [.sym "None", slot "table", slot "count", slot "images", slot "offset", slot "binders", slot "rest"] (.sym "None"),
  equation "substitute-args-first-some" "vibe:subst-args-first"
    [call "Some" [slot "first"], slot "table", slot "count", slot "images", slot "offset", slot "binders", slot "rest"]
    (call "vibe:subst-args-rest" [slot "first", call "vibe:subst-args"
      [slot "table", slot "count", slot "images", slot "offset", slot "binders", slot "rest"]]),
  equation "substitute-args-rest-none" "vibe:subst-args-rest" [slot "first", .sym "None"] (.sym "None"),
  equation "substitute-args-rest-some" "vibe:subst-args-rest" [slot "first", call "Some" [slot "rest"]]
    (call "Some" [call "nik:list-cons" [slot "first", slot "rest"]])]

def substitutionProgram : Program := shiftProgram ++ substitutionEquations

theorem substitutionEquations_disjoint :
    ∀ equation ∈ substitutionEquations, equation.head ∉ shiftProgram.calledHeads := by
  have fresh : substitutionEquations.all (fun equation =>
      !shiftProgram.calledHeads.contains equation.head) = true := by decide +kernel
  intro equation member
  have absent := List.all_eq_true.mp fresh equation member
  simpa using absent

theorem substitutionProgram_leftLinear : LeftLinear substitutionProgram := by
  have additional : LeftLinear substitutionEquations := by
    simp [LeftLinear, substitutionEquations, equation, call, slot, patternVarsList, patternVars]
  intro equation member
  rcases List.mem_append.mp member with old | added
  · exact shiftProgram_leftLinear equation old
  · exact additional equation added

theorem substitutionProgram_dataSeparated : DataSeparated substitutionProgram computationalHost where
  undefined := by
    intro head member
    have old := shiftProgram_dataSeparated.undefined head member
    have added : substitutionEquations.defines head = false := by
      simp [constructorHeads] at member
      rcases member with rfl | rfl | rfl <;>
        simp [Program.defines, substitutionEquations, equation]
    change (shiftProgram ++ substitutionEquations).any _ = false
    rw [List.any_append]
    change (shiftProgram.defines head || substitutionEquations.defines head) = false
    rw [old, added]
    rfl
  unhandled := by
    intro head member arguments
    simp [constructorHeads] at member
    rcases member with rfl | rfl | rfl <;> rfl

/-- Previously proved shift computations run inside the larger authored program. -/
theorem shift_computes_in_substitution (table : SignatureTable) (amount cutoff : Nat) (term : Spec.Term) :
    Applies substitutionProgram computationalHost "vibe:shift"
      [encodeTable table, encode term, natural amount, natural cutoff]
      (encodeResult (Spec.shift (signatureOf table) amount cutoff term)) := by
  apply (Applies.append_iff shiftProgram substitutionEquations computationalHost substitutionEquations_disjoint
    "vibe:shift" (by decide +kernel) _ _).mpr
  exact shift_computes table amount cutoff term

theorem depth_computes_in_substitution (table : SignatureTable) (term : Spec.Term) :
    Applies substitutionProgram computationalHost "vibe:depth" [encodeTable table, encode term]
      (natural (Spec.depth (signatureOf table) term)) := by
  apply (Applies.append_iff shiftProgram substitutionEquations computationalHost substitutionEquations_disjoint
    "vibe:depth" (by decide +kernel) _ _).mpr
  exact depth_computes table term

theorem binders_computes_in_substitution (table : SignatureTable) (symbol : Spec.SymId) :
    Applies substitutionProgram computationalHost "vibe:binders" [encodeTable table, encodeSymbol symbol]
      (encodeBinders (bindersOf (signatureOf table) symbol)) := by
  apply (Applies.append_iff shiftProgram substitutionEquations computationalHost substitutionEquations_disjoint
    "vibe:binders" (by decide +kernel) _ _).mpr
  exact binders_computes table symbol

end Mettapedia.Languages.VibeITP.Presentation.ComputationalSubstitution
