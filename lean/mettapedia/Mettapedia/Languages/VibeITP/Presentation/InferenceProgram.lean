import Mettapedia.Languages.VibeITP.Presentation.InstantiationSignature

/-!
# Authored static inference operand checks

Term equality traverses all ordered children and literal bytes. Formation
checks use actual symbol declarations and the kernel's strict word guards.
Modus ponens checks the supplied implication and premise; instantiation also
checks the supplied value's formation. Claimed conclusions are compared with
the computed conclusion, rather than justified by an unrelated derivation.

The host is unchanged scalar arithmetic and list operations. These equations
do not provide arithmetic literal rules, definition admission, or a complete
proof-tree checker yet.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalInference

open ComputationalData ComputationalShift ComputationalSubstitution ComputationalInstantiation
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

private def call (head : String) (arguments : List Term) : Term := .expr (.sym head :: arguments)
private def slot (name : String) : Term := .var name
private def equation (name head : String) (arguments : List Term) (body : Term) : Equation :=
  ⟨name, head, arguments, body⟩

def inferenceEquations : Program := [
  equation "term-equal-bound" "vibe:term-eq"
    [call "Vibe:BVar" [slot "i"], call "Vibe:BVar" [slot "j"]]
    (call "nik:nat-eq" [slot "i", slot "j"]),
  equation "term-equal-literal" "vibe:term-eq"
    [call "Vibe:Lit" [slot "left"], call "Vibe:Lit" [slot "right"]]
    (call "vibe:bytes-eq" [slot "left", slot "right"]),
  equation "term-equal-application" "vibe:term-eq"
    [call "Vibe:App" [slot "left-head", slot "left-args"],
      call "Vibe:App" [slot "right-head", slot "right-args"]]
    (call "vibe:term-eq-head" [call "vibe:symbol-eq" [slot "left-head", slot "right-head"],
      slot "left-args", slot "right-args"]),
  equation "term-equal-different-shapes" "vibe:term-eq" [slot "left", slot "right"]
    (.sym "False"),
  equation "term-equal-different-heads" "vibe:term-eq-head"
    [.sym "False", slot "left", slot "right"] (.sym "False"),
  equation "term-equal-same-head" "vibe:term-eq-head"
    [.sym "True", slot "left", slot "right"] (call "vibe:terms-eq" [slot "left", slot "right"]),
  equation "terms-equal" "vibe:terms-eq" [slot "left", slot "right"]
    (call "vibe:terms-eq-view" [call "nik:list-view" [slot "left"], call "nik:list-view" [slot "right"]]),
  equation "terms-equal-empty" "vibe:terms-eq-view" [.sym "List:Nil", .sym "List:Nil"]
    (.sym "True"),
  equation "terms-equal-pair" "vibe:terms-eq-view"
    [call "List:Cons" [slot "left", slot "left-rest"], call "List:Cons" [slot "right", slot "right-rest"]]
    (call "vibe:terms-eq-first" [call "vibe:term-eq" [slot "left", slot "right"],
      slot "left-rest", slot "right-rest"]),
  equation "terms-equal-different-lengths" "vibe:terms-eq-view" [slot "left", slot "right"]
    (.sym "False"),
  equation "terms-equal-first-different" "vibe:terms-eq-first"
    [.sym "False", slot "left", slot "right"] (.sym "False"),
  equation "terms-equal-first-same" "vibe:terms-eq-first"
    [.sym "True", slot "left", slot "right"] (call "vibe:terms-eq" [slot "left", slot "right"]),
  equation "bytes-equal" "vibe:bytes-eq" [slot "left", slot "right"]
    (call "vibe:bytes-eq-view" [call "nik:list-view" [slot "left"], call "nik:list-view" [slot "right"]]),
  equation "bytes-equal-empty" "vibe:bytes-eq-view" [.sym "List:Nil", .sym "List:Nil"]
    (.sym "True"),
  equation "bytes-equal-pair" "vibe:bytes-eq-view"
    [call "List:Cons" [slot "left", slot "left-rest"], call "List:Cons" [slot "right", slot "right-rest"]]
    (call "vibe:bytes-eq-first" [call "nik:nat-eq" [slot "left", slot "right"],
      slot "left-rest", slot "right-rest"]),
  equation "bytes-equal-different-lengths" "vibe:bytes-eq-view" [slot "left", slot "right"]
    (.sym "False"),
  equation "bytes-equal-first-different" "vibe:bytes-eq-first"
    [.sym "False", slot "left", slot "right"] (.sym "False"),
  equation "bytes-equal-first-same" "vibe:bytes-eq-first"
    [.sym "True", slot "left", slot "right"] (call "vibe:bytes-eq" [slot "left", slot "right"]),
  equation "formed-bound" "vibe:well-formed" [slot "table", call "Vibe:BVar" [slot "index"]]
    (call "nik:nat-lt" [call "nik:nat-add" [slot "index", natural 1], natural Spec.wordBound]),
  equation "formed-literal" "vibe:well-formed" [slot "table", call "Vibe:Lit" [slot "bytes"]]
    (call "nik:nat-lt" [call "nik:nat-add" [call "vibe:list-length" [slot "bytes"], natural 8],
      natural Spec.wordBound]),
  equation "formed-application" "vibe:well-formed"
    [slot "table", call "Vibe:App" [slot "symbol", slot "arguments"]]
    (call "vibe:formed-info" [call "vibe:lookup-symbol" [slot "table", slot "symbol"],
      slot "table", slot "arguments"]),
  equation "formed-unknown-symbol" "vibe:formed-info" [.sym "None", slot "table", slot "arguments"]
    (.sym "False"),
  equation "formed-declared-symbol" "vibe:formed-info"
    [call "Some" [call "Vibe:SymInfo" [slot "kind", slot "binders"]], slot "table", slot "arguments"]
    (call "vibe:formed-arity" [call "nik:nat-eq" [call "vibe:list-length" [slot "arguments"],
      call "vibe:list-length" [slot "binders"]], slot "table", slot "arguments"]),
  equation "formed-wrong-arity" "vibe:formed-arity" [.sym "False", slot "table", slot "arguments"]
    (.sym "False"),
  equation "formed-right-arity" "vibe:formed-arity" [.sym "True", slot "table", slot "arguments"]
    (call "vibe:well-formed-args" [slot "table", slot "arguments"]),
  equation "formed-arguments" "vibe:well-formed-args" [slot "table", slot "arguments"]
    (call "vibe:formed-view" [slot "table", call "nik:list-view" [slot "arguments"]]),
  equation "formed-empty-arguments" "vibe:formed-view" [slot "table", .sym "List:Nil"]
    (.sym "True"),
  equation "formed-argument-pair" "vibe:formed-view"
    [slot "table", call "List:Cons" [slot "first", slot "rest"]]
    (call "vibe:formed-first" [call "vibe:well-formed" [slot "table", slot "first"],
      slot "table", slot "rest"]),
  equation "formed-first-invalid" "vibe:formed-first" [.sym "False", slot "table", slot "rest"]
    (.sym "False"),
  equation "formed-first-valid" "vibe:formed-first" [.sym "True", slot "table", slot "rest"]
    (call "vibe:well-formed-args" [slot "table", slot "rest"]),
  equation "modus-ponens" "vibe:modus-ponens"
    [call "Vibe:App" [.list [.sym "Builtin", natural Spec.Builtin.impl.slot],
      .list [slot "antecedent", slot "conclusion"]], slot "premise"]
    (call "vibe:mp-equal" [call "vibe:term-eq" [slot "antecedent", slot "premise"], slot "conclusion"]),
  equation "modus-ponens-wrong-shape" "vibe:modus-ponens" [slot "implication", slot "premise"]
    (.sym "None"),
  equation "modus-ponens-wrong-premise" "vibe:mp-equal" [.sym "False", slot "conclusion"]
    (.sym "None"),
  equation "modus-ponens-right-premise" "vibe:mp-equal" [.sym "True", slot "conclusion"]
    (call "Some" [slot "conclusion"]),
  equation "check-missing-result" "vibe:check-result" [.sym "None", slot "claimed"]
    (.sym "False"),
  equation "check-produced-result" "vibe:check-result" [call "Some" [slot "actual"], slot "claimed"]
    (call "vibe:term-eq" [slot "actual", slot "claimed"]),
  equation "check-modus-ponens" "vibe:check-mp" [slot "implication", slot "premise", slot "claimed"]
    (call "vibe:check-result" [call "vibe:modus-ponens" [slot "implication", slot "premise"], slot "claimed"]),
  equation "instantiate-formed-value" "vibe:thm-instantiate"
    [slot "table", slot "F", slot "value", slot "statement"]
    (call "vibe:thm-inst-formed" [call "vibe:well-formed" [slot "table", slot "value"],
      slot "table", slot "F", slot "value", slot "statement"]),
  equation "instantiate-malformed-value" "vibe:thm-inst-formed"
    [.sym "False", slot "table", slot "F", slot "value", slot "statement"] (.sym "None"),
  equation "instantiate-valid-value" "vibe:thm-inst-formed"
    [.sym "True", slot "table", slot "F", slot "value", slot "statement"]
    (call "vibe:instantiate" [slot "table", slot "F", slot "value", slot "statement"]),
  equation "check-instantiation" "vibe:check-inst"
    [slot "table", slot "F", slot "value", slot "statement", slot "claimed"]
    (call "vibe:check-result" [call "vibe:thm-instantiate" [slot "table", slot "F", slot "value", slot "statement"],
      slot "claimed"]),
  equation "formed-statement" "vibe:formed-statement" [slot "table", slot "statement"]
    (call "vibe:formed-statement-value" [call "vibe:well-formed" [slot "table", slot "statement"],
      slot "table", slot "statement"]),
  equation "formed-statement-invalid" "vibe:formed-statement-value"
    [.sym "False", slot "table", slot "statement"] (.sym "False"),
  equation "formed-statement-valid" "vibe:formed-statement-value"
    [.sym "True", slot "table", slot "statement"]
    (call "nik:nat-zero" [call "vibe:depth" [slot "table", slot "statement"]]) ]

def inferenceProgram : Program := instantiationProgram ++ inferenceEquations

theorem inferenceEquations_disjoint :
    ∀ equation ∈ inferenceEquations, equation.head ∉ instantiationProgram.calledHeads := by
  have fresh : inferenceEquations.all (fun equation =>
      !instantiationProgram.calledHeads.contains equation.head) = true := by decide +kernel
  intro equation member
  simpa using List.all_eq_true.mp fresh equation member

theorem inferenceProgram_leftLinear : LeftLinear inferenceProgram := by
  have additional : LeftLinear inferenceEquations := by
    simp [LeftLinear, inferenceEquations, equation, call, slot, natural, Spec.Builtin.slot,
      patternVarsList, patternVars]
  intro equation member
  rcases List.mem_append.mp member with old | added
  · exact instantiationProgram_leftLinear equation old
  · exact additional equation added

theorem inferenceProgram_dataSeparated : DataSeparated inferenceProgram computationalHost where
  undefined := by
    intro head member
    have old := instantiationProgram_dataSeparated.undefined head member
    have added : inferenceEquations.defines head = false := by
      simp [constructorHeads] at member
      rcases member with rfl | rfl | rfl <;> simp [Program.defines, inferenceEquations, equation]
    change (instantiationProgram ++ inferenceEquations).any _ = false
    rw [List.any_append]
    change (instantiationProgram.defines head || inferenceEquations.defines head) = false
    rw [old, added]
    rfl
  unhandled := by
    intro head member arguments
    simp [constructorHeads] at member
    rcases member with rfl | rfl | rfl <;> rfl

theorem reuse_instantiation_call {head : String} {arguments : List Term} {result : Term}
    (used : head ∈ instantiationProgram.calledHeads)
    (computed : Applies instantiationProgram computationalHost head arguments result) :
    Applies inferenceProgram computationalHost head arguments result :=
  (Applies.append_iff instantiationProgram inferenceEquations computationalHost
    inferenceEquations_disjoint head used arguments result).mpr computed

/-- The earlier component has no definitions for any new inference head. -/
private theorem old_undefined (head : String) (used : head ∈ inferenceEquations.map Equation.head) :
    instantiationProgram.defines head = false := by
  obtain ⟨new, member, rfl⟩ := List.mem_map.mp used
  simp only [Program.defines, List.any_eq_false]
  intro old oldMember
  have different : old.head ≠ new.head := fun same =>
    inferenceEquations_disjoint new member (same ▸ Program.calledHeads_head oldMember)
  simp [different]

/-- Only dispatcher fields are compared here. Bodies still execute in the
complete program, including their calls to the earlier component. -/
theorem inference_dispatch :
    DispatchAgreement inferenceEquations inferenceProgram (inferenceEquations.map Equation.head) := by
  constructor
  · intro head used arity
    unfold inferenceProgram Program.definesAt
    rw [List.any_append]
    change inferenceEquations.definesAt head arity =
      (instantiationProgram.definesAt head arity || inferenceEquations.definesAt head arity)
    rw [Program.definesAt_false_of_defines_false (old_undefined head used) arity, Bool.false_or]
  · intro head used
    unfold inferenceProgram Program.defines
    rw [List.any_append]
    change inferenceEquations.defines head =
      (instantiationProgram.defines head || inferenceEquations.defines head)
    rw [old_undefined head used, Bool.false_or]
  · intro head used arguments
    unfold inferenceProgram Program.select
    rw [List.findSome?_append]
    change inferenceEquations.select head arguments =
      (instantiationProgram.select head arguments).or (inferenceEquations.select head arguments)
    rw [Program.select_none_of_undefined (old_undefined head used) arguments, Option.none_or]

theorem inference_equation {head : String} {arguments : List Term} {equation : Equation}
    {environment : Env} {result : Term} (used : head ∈ inferenceEquations.map Equation.head)
    (defined : inferenceEquations.definesAt head arguments.length = true)
    (selected : inferenceEquations.select head arguments = some (equation, environment))
    (body : Evaluates inferenceProgram computationalHost environment equation.body result) :
    Applies inferenceProgram computationalHost head arguments result := by
  apply Applies.equation
  · rw [← inference_dispatch.definesAt head used arguments.length]
    exact defined
  · rw [← inference_dispatch.select head used arguments]
    exact selected
  · exact body

theorem inference_apply (head : String) (used : head ∈ inferenceEquations.map Equation.head)
    (fuel : Nat) (arguments : List Term) :
    apply inferenceProgram computationalHost fuel head arguments =
      applyWith inferenceEquations computationalHost (eval inferenceProgram computationalHost fuel) head arguments := by
  change applyWith inferenceProgram computationalHost _ _ _ = _
  simp only [applyWith, ← inference_dispatch.definesAt head used arguments.length,
    ← inference_dispatch.defines head used, ← inference_dispatch.select head used arguments]

end Mettapedia.Languages.VibeITP.Presentation.ComputationalInference
