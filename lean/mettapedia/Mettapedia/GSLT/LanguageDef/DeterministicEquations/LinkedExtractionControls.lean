import Mettapedia.GSLT.LanguageDef.DeterministicEquations.LinkedExtraction

/-! # Generated-caller and dependency-capture controls -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction.Linked.Controls

open Lean Meta Elab Command
open Mettapedia.Languages

private def listHead : String :=
  "nik:extracted:Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction.Linked.listProgram"

private def childHead : String :=
  "nik:extracted:Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction.Paired.substitutionProgram"

theorem empty_list_computes (values : List MM0.Kernel.Preterm) :
    Applies listProgram productDivisionHost listHead
      [encodeList MM0.Presentation.encode values, .list []] (named "Some" [.list []]) :=
  list_computes values []

theorem caller_keeps_source_order :
    Applies listProgram productDivisionHost listHead
      [encodeList MM0.Presentation.encode [.term 3, .term 7],
        encodeList MM0.Presentation.encode [.var 1, .var 0]]
      (encodeOption (encodeList MM0.Presentation.encode) (some [.term 7, .term 3])) :=
  list_computes [.term 3, .term 7] [.var 1, .var 0]

theorem caller_keeps_duplicate_occurrences :
    Applies listProgram productDivisionHost listHead
      [encodeList MM0.Presentation.encode [.term 3],
        encodeList MM0.Presentation.encode [.var 0, .var 0]]
      (encodeOption (encodeList MM0.Presentation.encode) (some [.term 3, .term 3])) :=
  list_computes [.term 3] [.var 0, .var 0]

theorem caller_keeps_simultaneous_substitution :
    Applies listProgram productDivisionHost listHead
      [encodeList MM0.Presentation.encode [.var 1, .term 7],
        encodeList MM0.Presentation.encode [.var 0]]
      (encodeOption (encodeList MM0.Presentation.encode) (some [.var 1])) :=
  list_computes [.var 1, .term 7] [.var 0]

theorem later_missing_image_is_none :
    Applies listProgram productDivisionHost listHead
      [encodeList MM0.Presentation.encode [.term 3],
        encodeList MM0.Presentation.encode [.var 0, .var 1]] (.sym "None") :=
  list_computes [.term 3] [.var 0, .var 1]

theorem first_missing_image_is_none :
    Applies listProgram productDivisionHost listHead
      [encodeList MM0.Presentation.encode [],
        encodeList MM0.Presentation.encode [.var 0, .term 7]] (.sym "None") :=
  list_computes [] [.var 0, .term 7]

theorem no_invented_list_result (values sources : List MM0.Kernel.Preterm) (observed : Term) :
    Applies listProgram productDivisionHost listHead
      [encodeList MM0.Presentation.encode values, encodeList MM0.Presentation.encode sources]
      observed ↔ observed = encodeOption (encodeList MM0.Presentation.encode)
        (MM0.Kernel.Substitution.substituteList (MM0.Kernel.Substitution.ofList values) sources) :=
  list_computes_result_exact values sources observed

theorem reversed_result_refuses :
    ¬ Applies listProgram productDivisionHost listHead
      [encodeList MM0.Presentation.encode [.term 3, .term 7],
        encodeList MM0.Presentation.encode [.var 1, .var 0]]
      (encodeOption (encodeList MM0.Presentation.encode) (some [.term 3, .term 7])) := by
  intro accepted
  have same := accepted.deterministic caller_keeps_source_order
  cases same

theorem dependency_is_linked_once :
    (listProgram.filter (fun row => row.head == childHead)).length = 1 := by decide

theorem original_pair_sizes_remain :
    Paired.bytesProgram.length = 3 ∧ Paired.substitutionProgram.length = 12 := by decide

private def override (head : String) : Program := [⟨"capture", head, [], .sym "changed"⟩]

theorem source_head_capture_refuses :
    avoidsCalls Paired.substitutionProgram (override childHead) = false := by decide

theorem constructor_capture_refuses :
    avoidsCalls Paired.substitutionProgram (override "MM0:App") = false := by decide

theorem primitive_capture_refuses :
    avoidsCalls Paired.substitutionProgram (override "nik:list-view") = false := by decide

theorem unrelated_head_is_admitted :
    avoidsCalls Paired.substitutionProgram (override "test:unrelated-dispatch") = true := by decide

theorem unrelated_head_preserves_every_outcome (fuel : Nat) (arguments : List Term) :
    apply (override "test:unrelated-dispatch" ++ Paired.substitutionProgram)
      productDivisionHost fuel childHead arguments =
    apply Paired.substitutionProgram productDivisionHost fuel childHead arguments := by
  simpa using linked_apply_exact Paired.substitutionProgram
    (override "test:unrelated-dispatch") [] productDivisionHost
    unrelated_head_is_admitted (by decide) fuel childHead (by decide) arguments

theorem zero_fuel_is_exhaustion :
    apply listProgram productDivisionHost 0 listHead [.list [], .list []] = .exhausted := rfl

theorem wrong_arity_is_failure :
    apply listProgram productDivisionHost 32 listHead [.list []] = .failure := rfl

theorem completed_caller_is_exact (values sources : List MM0.Kernel.Preterm) (fuel : Nat)
    (finished : apply listProgram productDivisionHost fuel listHead
      [encodeList MM0.Presentation.encode values, encodeList MM0.Presentation.encode sources] ≠
        .exhausted) :
    apply listProgram productDivisionHost fuel listHead
      [encodeList MM0.Presentation.encode values, encodeList MM0.Presentation.encode sources] =
      .value (encodeOption (encodeList MM0.Presentation.encode)
        (MM0.Kernel.Substitution.substituteList (MM0.Kernel.Substitution.ofList values) sources)) :=
  list_computes_completed_exact values sources fuel finished

private def shiftedAdapter (values : List MM0.Kernel.Preterm) : MM0.Kernel.Substitution :=
  fun index => values[index + 1]?

private def requireRefusal (operation : Elab.Term.TermElabM Unit) : Elab.Term.TermElabM Unit := do
  let saved ← saveState
  let refused ← try
    operation
    pure false
  catch _ =>
    saved.restore
    pure true
  unless refused do throwError "invalid dependency was silently admitted"

run_cmd liftTermElabM do
  requireRefusal do
    let root ← inspectRoot ``MM0.Kernel.Substitution.substituteList "test:unregistered-child"
      (some ``MM0.Kernel.Substitution.ofList)
    let _ ← compileRoot { root with dependencies := #[] }
  requireRefusal do
    registerDependency {
      sourceName := ``VibeITP.Spec.leBytes
      programName := ``Paired.bytesProgram
      certificateName := ``Paired.substitution_computes }
  requireRefusal do
    registerDependency {
      sourceName := ``MM0.Kernel.Preterm.substitute
      programName := ``Paired.substitutionProgram
      certificateName := ``Paired.substitution_computes
      adapter := some ``MM0.Kernel.Substitution.ofList }
  requireRefusal do
    let _ ← inspectRoot ``MM0.Kernel.Substitution.substituteList "test:shifted-adapter"
      (some ``shiftedAdapter)
  for head in #[childHead, "MM0:App", "nik:list-view"] do
    requireRefusal do
      let root ← inspectRoot ``MM0.Kernel.Substitution.substituteList head
        (some ``MM0.Kernel.Substitution.ofList)
      let _ ← compileRoot root

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction.Linked.Controls
