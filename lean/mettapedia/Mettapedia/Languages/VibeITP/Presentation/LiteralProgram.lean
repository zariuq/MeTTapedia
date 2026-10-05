import Mettapedia.Languages.VibeITP.Presentation.InferenceCorrespondence
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.NaturalProductDivision

/-!
# Authored computations for all seven static literal inferences

Requests retain their actual operands. Word guards, byte encoding, literal
shape, bounds, result construction and claimed-result equality are authored
equations; the host supplies only generic scalar arithmetic and list views.
An intermediate numeric result does not itself authorize a theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalLiterals

open ComputationalData ComputationalShift ComputationalInference
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

inductive LiteralRequest where
  | isNat (value : Nat)
  | lessThan (left right : Nat)
  | addition (left right : Nat)
  | multiplication (left right : Nat)
  | division (left right : Nat)
  | length (value : Spec.Term)
  | get (value : Spec.Term) (index : Nat)
  deriving Repr

/-- The independent static constructor's guards and statement, without proof
search or an appeal to unrelated derivability of the requested result. -/
def LiteralRequest.result : LiteralRequest → Option Spec.Term
  | .isNat value => if value < Spec.wordBound then some (Spec.litIsNatStatement value) else none
  | .lessThan left right =>
      if left < right ∧ right < Spec.wordBound then some (Spec.litLtStatement left right) else none
  | .addition left right =>
      if left < Spec.wordBound ∧ right < Spec.wordBound then some (Spec.litAddStatement left right) else none
  | .multiplication left right =>
      if left < Spec.wordBound ∧ right < Spec.wordBound then some (Spec.litMulStatement left right) else none
  | .division left right =>
      if left < Spec.wordBound ∧ right < Spec.wordBound ∧ right ≠ 0 then
        some (Spec.litDivStatement left right) else none
  | .length (.lit bytes) =>
      if bytes.length + 8 < Spec.wordBound then some (Spec.litLengthStatement bytes) else none
  | .length _ => none
  | .get (.lit bytes) index =>
      if bytes.length + 8 < Spec.wordBound ∧ index < bytes.length then
        some (Spec.litGetStatement bytes index) else none
  | .get _ _ => none

def encodeRequest : LiteralRequest → Term
  | .isNat value => .list [.sym "Literal:IsNat", natural value]
  | .lessThan left right => .list [.sym "Literal:Lt", natural left, natural right]
  | .addition left right => .list [.sym "Literal:Add", natural left, natural right]
  | .multiplication left right => .list [.sym "Literal:Mul", natural left, natural right]
  | .division left right => .list [.sym "Literal:Div", natural left, natural right]
  | .length value => .list [.sym "Literal:Length", encode value]
  | .get value index => .list [.sym "Literal:Get", encode value, natural index]

private def call (head : String) (arguments : List Term) : Term := .expr (.sym head :: arguments)
private def slot (name : String) : Term := .var name
private def equation (name head : String) (arguments : List Term) (body : Term) : Equation :=
  ⟨name, head, arguments, body⟩
private def lit (bytes : Term) : Term := call "Vibe:Lit" [bytes]
private def app (builtin : Spec.Builtin) (arguments : List Term) : Term :=
  call "Vibe:App" [encodeSymbol (.builtin builtin), .list arguments]
private def dynamicApp (code : Term) (arguments : List Term) : Term :=
  call "Vibe:App" [.list [.sym "Builtin", code], .list arguments]
private def someResult (value : Term) : Term := call "Some" [value]
private def numeric (name : String) : Term := call "vibe:number-literal" [slot name]

def literalEquations : Program := [
  equation "number-bytes" "vibe:number-bytes" [slot "n"]
    (call "vibe:number-small" [call "nik:nat-lt" [slot "n", natural 256], slot "n"]),
  equation "number-one-byte" "vibe:number-small" [.sym "True", slot "n"] (.list [slot "n"]),
  equation "number-eight-bytes" "vibe:number-small" [.sym "False", slot "n"]
    (call "vibe:little-endian" [natural 8, slot "n"]),
  equation "little-endian" "vibe:little-endian" [slot "width", slot "n"]
    (call "vibe:little-count" [call "nik:nat-zero" [slot "width"], slot "width", slot "n"]),
  equation "little-endian-empty" "vibe:little-count" [.sym "True", slot "width", slot "n"] (.list []),
  equation "little-endian-next" "vibe:little-count" [.sym "False", slot "width", slot "n"]
    (call "nik:list-cons" [call "nik:nat-mod" [slot "n", natural 256],
      call "vibe:little-endian" [call "nik:nat-pred" [slot "width"],
        call "nik:nat-div" [slot "n", natural 256]]]),
  equation "number-literal" "vibe:number-literal" [slot "n"]
    (lit (call "vibe:number-bytes" [slot "n"])),
  equation "byte-at" "vibe:byte-at" [slot "bytes", slot "index"]
    (call "vibe:byte-view" [call "nik:list-view" [slot "bytes"], slot "index"]),
  equation "byte-at-empty" "vibe:byte-view" [.sym "List:Nil", slot "index"] (.sym "None"),
  equation "byte-at-next" "vibe:byte-view"
    [call "List:Cons" [slot "first", slot "rest"], slot "index"]
    (call "vibe:byte-zero" [call "nik:nat-zero" [slot "index"], slot "first", slot "rest", slot "index"]),
  equation "byte-at-first" "vibe:byte-zero" [.sym "True", slot "first", slot "rest", slot "index"]
    (someResult (slot "first")),
  equation "byte-at-later" "vibe:byte-zero" [.sym "False", slot "first", slot "rest", slot "index"]
    (call "vibe:byte-at" [slot "rest", call "nik:nat-pred" [slot "index"]]),
  equation "literal-isnat" "vibe:literal-query" [.list [.sym "Literal:IsNat", slot "n"]]
    (call "vibe:literal-isnat-word" [call "nik:nat-lt" [slot "n", natural Spec.wordBound], slot "n"]),
  equation "literal-isnat-overflow" "vibe:literal-isnat-word" [.sym "False", slot "n"] (.sym "None"),
  equation "literal-isnat-word" "vibe:literal-isnat-word" [.sym "True", slot "n"]
    (someResult (app .litIsNat [numeric "n"])),
  equation "literal-lt" "vibe:literal-query" [.list [.sym "Literal:Lt", slot "a", slot "b"]]
    (call "vibe:literal-words" [.sym "Literal:Lt", slot "a", slot "b"]),
  equation "literal-add" "vibe:literal-query" [.list [.sym "Literal:Add", slot "a", slot "b"]]
    (call "vibe:literal-words" [.sym "Literal:Add", slot "a", slot "b"]),
  equation "literal-mul" "vibe:literal-query" [.list [.sym "Literal:Mul", slot "a", slot "b"]]
    (call "vibe:literal-words" [.sym "Literal:Mul", slot "a", slot "b"]),
  equation "literal-div" "vibe:literal-query" [.list [.sym "Literal:Div", slot "a", slot "b"]]
    (call "vibe:literal-words" [.sym "Literal:Div", slot "a", slot "b"]),
  equation "literal-word-operands" "vibe:literal-words" [slot "kind", slot "a", slot "b"]
    (call "vibe:literal-left-word" [call "nik:nat-lt" [slot "a", natural Spec.wordBound],
      slot "kind", slot "a", slot "b"]),
  equation "literal-left-overflow" "vibe:literal-left-word"
    [.sym "False", slot "kind", slot "a", slot "b"] (.sym "None"),
  equation "literal-left-word" "vibe:literal-left-word"
    [.sym "True", slot "kind", slot "a", slot "b"]
    (call "vibe:literal-right-word" [call "nik:nat-lt" [slot "b", natural Spec.wordBound],
      slot "kind", slot "a", slot "b"]),
  equation "literal-right-overflow" "vibe:literal-right-word"
    [.sym "False", slot "kind", slot "a", slot "b"] (.sym "None"),
  equation "literal-right-word" "vibe:literal-right-word"
    [.sym "True", slot "kind", slot "a", slot "b"]
    (call "vibe:literal-binary" [slot "kind", slot "a", slot "b"]),
  equation "literal-less-than" "vibe:literal-binary" [.sym "Literal:Lt", slot "a", slot "b"]
    (call "vibe:literal-order" [call "nik:nat-lt" [slot "a", slot "b"], slot "a", slot "b"]),
  equation "literal-less-refused" "vibe:literal-order" [.sym "False", slot "a", slot "b"] (.sym "None"),
  equation "literal-less-accepted" "vibe:literal-order" [.sym "True", slot "a", slot "b"]
    (someResult (app .litLt [numeric "a", numeric "b"])),
  equation "literal-addition" "vibe:literal-binary" [.sym "Literal:Add", slot "a", slot "b"]
    (call "vibe:numeric-equation" [natural Spec.Builtin.litAdd.slot, slot "a", slot "b",
      call "nik:nat-mod" [call "nik:nat-add" [slot "a", slot "b"], natural Spec.wordBound]]),
  equation "literal-multiplication" "vibe:literal-binary" [.sym "Literal:Mul", slot "a", slot "b"]
    (call "vibe:numeric-equation" [natural Spec.Builtin.litMul.slot, slot "a", slot "b",
      call "nik:nat-mod" [call "nik:nat-mul" [slot "a", slot "b"], natural Spec.wordBound]]),
  equation "literal-division" "vibe:literal-binary" [.sym "Literal:Div", slot "a", slot "b"]
    (call "vibe:literal-divisor" [call "nik:nat-zero" [slot "b"], slot "a", slot "b"]),
  equation "literal-zero-divisor" "vibe:literal-divisor" [.sym "True", slot "a", slot "b"] (.sym "None"),
  equation "literal-nonzero-divisor" "vibe:literal-divisor" [.sym "False", slot "a", slot "b"]
    (call "vibe:numeric-equation" [natural Spec.Builtin.litDiv.slot, slot "a", slot "b",
      call "nik:nat-div" [slot "a", slot "b"]]),
  equation "numeric-equation" "vibe:numeric-equation" [slot "code", slot "a", slot "b", slot "result"]
    (someResult (app .eq [dynamicApp (slot "code") [numeric "a", numeric "b"], numeric "result"])),
  equation "literal-length" "vibe:literal-query"
    [.list [.sym "Literal:Length", lit (slot "bytes")]]
    (call "vibe:literal-length-formed" [call "vibe:well-formed" [.list [], lit (slot "bytes")], slot "bytes"]),
  equation "literal-length-wrong-shape" "vibe:literal-query" [.list [.sym "Literal:Length", slot "term"]]
    (.sym "None"),
  equation "literal-length-malformed" "vibe:literal-length-formed" [.sym "False", slot "bytes"] (.sym "None"),
  equation "literal-length-formed" "vibe:literal-length-formed" [.sym "True", slot "bytes"]
    (someResult (app .eq [app .litLength [lit (slot "bytes")],
      call "vibe:number-literal" [call "vibe:list-length" [slot "bytes"]]])),
  equation "literal-get" "vibe:literal-query"
    [.list [.sym "Literal:Get", lit (slot "bytes"), slot "index"]]
    (call "vibe:literal-get-formed" [call "vibe:well-formed" [.list [], lit (slot "bytes")],
      slot "bytes", slot "index"]),
  equation "literal-get-wrong-shape" "vibe:literal-query" [.list [.sym "Literal:Get", slot "term", slot "index"]]
    (.sym "None"),
  equation "literal-get-malformed" "vibe:literal-get-formed" [.sym "False", slot "bytes", slot "index"] (.sym "None"),
  equation "literal-get-formed" "vibe:literal-get-formed" [.sym "True", slot "bytes", slot "index"]
    (call "vibe:literal-get-bounds" [call "nik:nat-lt" [slot "index", call "vibe:list-length" [slot "bytes"]],
      slot "bytes", slot "index"]),
  equation "literal-get-out-of-range" "vibe:literal-get-bounds" [.sym "False", slot "bytes", slot "index"] (.sym "None"),
  equation "literal-get-in-range" "vibe:literal-get-bounds" [.sym "True", slot "bytes", slot "index"]
    (call "vibe:literal-get-byte" [call "vibe:byte-at" [slot "bytes", slot "index"], slot "bytes", slot "index"]),
  equation "literal-get-no-byte" "vibe:literal-get-byte" [.sym "None", slot "bytes", slot "index"] (.sym "None"),
  equation "literal-get-byte" "vibe:literal-get-byte" [someResult (slot "byte"), slot "bytes", slot "index"]
    (someResult (app .eq [app .litGet [lit (slot "bytes"), numeric "index"], numeric "byte"])),
  equation "check-literal" "vibe:check-literal" [slot "request", slot "claimed"]
    (call "vibe:check-result" [call "vibe:literal-query" [slot "request"], slot "claimed"]) ]

def literalProgram : Program := inferenceProgram ++ literalEquations

theorem literalEquations_disjoint :
    ∀ equation ∈ literalEquations, equation.head ∉ inferenceProgram.calledHeads := by
  have fresh : literalEquations.all (fun equation => decide (equation.head ∉ inferenceProgram.calledHeads)) = true :=
    by decide +kernel
  intro equation member
  simpa using List.all_eq_true.mp fresh equation member

theorem literalHost_agreement : computationalHost.AgreesOn productDivisionHost inferenceProgram.calledHeads := by
  apply productDivisionHost_agrees
  have prior : inferenceProgram.calledHeads.all (fun head => decide (naturalProduct? head = none)) = true :=
    by decide +kernel
  intro head member
  simpa using List.all_eq_true.mp prior head member

theorem literalProgram_leftLinear : LeftLinear literalProgram := by
  have additional : LeftLinear literalEquations := by
    simp [LeftLinear, literalEquations, equation, call, slot, lit, app, dynamicApp, someResult, numeric,
      natural, encodeSymbol, Spec.Builtin.slot, patternVarsList, patternVars]
  intro equation member
  rcases List.mem_append.mp member with old | added
  · exact inferenceProgram_leftLinear equation old
  · exact additional equation added

theorem literalProgram_dataSeparated : DataSeparated literalProgram productDivisionHost where
  undefined := by
    intro head member
    have old := inferenceProgram_dataSeparated.undefined head member
    have added : literalEquations.defines head = false := by
      simp [constructorHeads] at member
      rcases member with rfl | rfl | rfl <;> simp [Program.defines, literalEquations, equation]
    change (inferenceProgram ++ literalEquations).any _ = false
    rw [List.any_append]
    change (inferenceProgram.defines head || literalEquations.defines head) = false
    rw [old, added]
    rfl
  unhandled := by
    intro head member arguments
    simp [constructorHeads] at member
    rcases member with rfl | rfl | rfl <;> rfl

theorem reuse_inference_call {head : String} {arguments : List Term} {result : Term}
    (used : head ∈ inferenceProgram.calledHeads)
    (computed : Applies inferenceProgram computationalHost head arguments result) :
    Applies literalProgram productDivisionHost head arguments result := by
  apply (Applies.append_iff inferenceProgram literalEquations productDivisionHost literalEquations_disjoint
    head used arguments result).mpr
  exact (Applies.host_iff inferenceProgram literalHost_agreement head used arguments result).mp computed

private theorem old_undefined (head : String) (used : head ∈ literalEquations.map Equation.head) :
    inferenceProgram.defines head = false := by
  obtain ⟨new, member, rfl⟩ := List.mem_map.mp used
  simp only [Program.defines, List.any_eq_false]
  intro old oldMember
  have different : old.head ≠ new.head := fun same =>
    literalEquations_disjoint new member (same ▸ Program.calledHeads_head oldMember)
  simp [different]

theorem literal_dispatch :
    DispatchAgreement literalEquations literalProgram (literalEquations.map Equation.head) := by
  constructor
  · intro head used arity
    unfold literalProgram Program.definesAt
    rw [List.any_append]
    change literalEquations.definesAt head arity =
      (inferenceProgram.definesAt head arity || literalEquations.definesAt head arity)
    rw [Program.definesAt_false_of_defines_false (old_undefined head used) arity, Bool.false_or]
  · intro head used
    unfold literalProgram Program.defines
    rw [List.any_append]
    change literalEquations.defines head = (inferenceProgram.defines head || literalEquations.defines head)
    rw [old_undefined head used, Bool.false_or]
  · intro head used arguments
    unfold literalProgram Program.select
    rw [List.findSome?_append]
    change literalEquations.select head arguments =
      (inferenceProgram.select head arguments).or (literalEquations.select head arguments)
    rw [Program.select_none_of_undefined (old_undefined head used) arguments, Option.none_or]

theorem literal_equation {head : String} {arguments : List Term} {equation : Equation}
    {environment : Env} {result : Term} (used : head ∈ literalEquations.map Equation.head)
    (defined : literalEquations.definesAt head arguments.length = true)
    (selected : literalEquations.select head arguments = some (equation, environment))
    (body : Evaluates literalProgram productDivisionHost environment equation.body result) :
    Applies literalProgram productDivisionHost head arguments result := by
  apply Applies.equation
  · rw [← literal_dispatch.definesAt head used arguments.length]
    exact defined
  · rw [← literal_dispatch.select head used arguments]
    exact selected
  · exact body

theorem literal_apply (head : String) (used : head ∈ literalEquations.map Equation.head)
    (fuel : Nat) (arguments : List Term) :
    apply literalProgram productDivisionHost fuel head arguments =
      applyWith literalEquations productDivisionHost (eval literalProgram productDivisionHost fuel) head arguments := by
  change applyWith literalProgram productDivisionHost _ _ _ = _
  simp only [applyWith, ← literal_dispatch.definesAt head used arguments.length,
    ← literal_dispatch.defines head used, ← literal_dispatch.select head used arguments]

end Mettapedia.Languages.VibeITP.Presentation.ComputationalLiterals
