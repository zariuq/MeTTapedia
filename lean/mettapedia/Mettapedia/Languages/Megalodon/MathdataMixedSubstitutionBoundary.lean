import Mettapedia.Languages.Megalodon.SortedABTRefinement
import Mettapedia.Languages.Megalodon.HenkinTermInterpretation
import Mettapedia.GSLT.LanguageDef.SortedABTSubstitution

/-!
# Mixed-variable scope of the Lean Mathdata term substitution

The current Lean raw term substitution traverses type binders but shifts an
inserted term only along its term-variable axis. A replacement with a free type
variable can therefore be captured by a crossed type binder. Raw type inference
and scope checking can accept both the intended and captured expressions; even
placing the complete example beneath an outer type binder does not repair the
local operation.

The all-sort ABT substitution keeps the outer type variable distinct. The
existing Henkin interpretation excludes the type-abstraction body in this
example, so its substitution, normalization and proof-soundness results do not
assert correctness on these raw inputs. Nothing here changes native checking
or proves soundness for an enlarged fragment.

These controls concern the Lean `MathdataKernel` operation. The external OCaml
Mathdata term substitution has a different traversal boundary at type syntax;
its equivalence with this port is a separate question. This module does not
assert a counterexample to the external checker or its admitted documents.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.MathdataMixedSubstitutionBoundary

open MathdataKernel
open Mettapedia.GSLT.LanguageDef.SortedSignatureIndexedABT

/-- A proposition term with no free term variables but one free type variable. -/
def replacement : Tm := .all (.var 0) (.all .prop (.db 0))

/-- The outer term variable occurs beneath a new type binder. -/
def body : Tm := .typeLam (.db 0)

def redex : Tm := .app (.lam .prop body) replacement

def capturedResult : Tm := .typeLam replacement

/-- The independent reference shifts the replacement's outer type variable. -/
def outerTypeResult : Tm := .typeLam (Tm.typeShift 0 1 replacement)

theorem raw_inputs_infer :
    inferTerm {} 1 [] replacement = some .prop ∧
      inferTerm {} 1 [.prop] body = some (.all .prop) ∧
      inferTerm {} 1 [] redex = some (.all .prop) ∧
      Tp.polyWellFormed 1 (.all .prop) = true := by decide

theorem current_substitution_captures :
    Tm.instantiate replacement body = capturedResult := rfl

theorem actual_beta_step_captures :
    Tm.normalizeOne redex = (capturedResult, false) := rfl

theorem outer_type_reference :
    outerTypeResult = .typeLam (.all (.var 1) (.all .prop (.db 0))) := rfl

theorem captured_and_outer_type_results_differ : capturedResult ≠ outerTypeResult := by decide

/-- Ordinary formation and bounded scope do not prove binding identity. -/
theorem both_results_pass_raw_checks :
    inferTerm {} 1 [] capturedResult = some (.all .prop) ∧
      inferTerm {} 1 [] outerTypeResult = some (.all .prop) ∧
      SortedABTRefinement.supportedAt 1 0 capturedResult = true ∧
      SortedABTRefinement.supportedAt 1 0 outerTypeResult = true := by decide

/-- Global closure is not the same as closing every replacement at its
particular substitution site. The crossed binder is still an inner binder. -/
theorem globally_closed_source_still_has_boundary :
    inferTerm {} 0 [] (.typeLam redex) = some (.all (.all .prop)) ∧
      Tp.polyWellFormed 0 (.all (.all .prop)) = true ∧
      SortedABTRefinement.supportedAt 0 0 (.typeLam redex) = true ∧
      Tm.normalizeOne (.typeLam redex) = (.typeLam capturedResult, false) := by decide

/-- The old refinement is exact for the old operation, including this input;
it does not establish unrestricted mixed-sort capture avoidance. -/
theorem old_sorted_operation_agrees_with_port :
    Term.instantiate .term (SortedABTRefinement.encode replacement)
      (SortedABTRefinement.encode body) = SortedABTRefinement.encode capturedResult := by
  rw [← SortedABTRefinement.encode_instantiate]
  rfl

/-- The general simultaneous operation weakens all free axes when entering
the type-binding field, including axes different from the replaced variable. -/
theorem all_sort_substitution_preserves_outer_type :
    Term.substituteTop .term (SortedABTRefinement.encode replacement)
      (SortedABTRefinement.encode body) = SortedABTRefinement.encode outerTypeResult := rfl

theorem old_and_all_sort_operations_differ :
    Term.instantiate .term (SortedABTRefinement.encode replacement)
        (SortedABTRefinement.encode body) ≠
      Term.substituteTop .term (SortedABTRefinement.encode replacement)
        (SortedABTRefinement.encode body) := by
  rw [old_sorted_operation_agrees_with_port, all_sort_substitution_preserves_outer_type]
  intro equal
  have sourceEqual := congrArg SortedABTRefinement.decode? equal
  simp only [SortedABTRefinement.decode_encode] at sourceEqual
  exact captured_and_outer_type_results_differ (Option.some.inj sourceEqual)

/-- The published constructorwise Henkin fragment rejects the mixed binder,
although the replacement itself belongs to that fragment. -/
theorem henkin_fragment_boundary :
    HenkinTermInterpretation.supported replacement = true ∧
      HenkinTermInterpretation.plainAnnotations 1 replacement = true ∧
      HenkinTermInterpretation.supported body = false ∧
      HenkinTermInterpretation.plainAnnotations 1 body = false ∧
      HenkinTermInterpretation.supported redex = false := by decide

/-- In particular, no typed erasure can meet the existing Henkin normalization
theorem's input premise for this raw redex. -/
theorem redex_has_no_existing_henkin_erasure
    {environment : Environment} {context : Mettapedia.Logic.HOL.Ctx HenkinTermInterpretation.Base}
    {type : Mettapedia.Logic.HOL.Ty HenkinTermInterpretation.Base} :
    ¬ ∃ interpreted : Mettapedia.Logic.HOL.Term
        (HenkinTermInterpretation.Constant environment) context type,
      HenkinTermInterpretation.erase interpreted = some redex := by
  rintro ⟨interpreted, erased⟩
  have supported := HenkinTermInterpretation.supported_of_erase interpreted erased
  rw [henkin_fragment_boundary.2.2.2.2] at supported
  cases supported

#print axioms raw_inputs_infer
#print axioms current_substitution_captures
#print axioms actual_beta_step_captures
#print axioms outer_type_reference
#print axioms captured_and_outer_type_results_differ
#print axioms both_results_pass_raw_checks
#print axioms globally_closed_source_still_has_boundary
#print axioms old_sorted_operation_agrees_with_port
#print axioms all_sort_substitution_preserves_outer_type
#print axioms old_and_all_sort_operations_differ
#print axioms henkin_fragment_boundary
#print axioms redex_has_no_existing_henkin_erasure

end Mettapedia.Languages.Megalodon.MathdataMixedSubstitutionBoundary
