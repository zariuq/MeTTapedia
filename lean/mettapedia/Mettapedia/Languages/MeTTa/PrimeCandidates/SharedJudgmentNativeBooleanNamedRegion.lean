import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNativeBooleanConstancy
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNamedIdentityRegions

/-!
# A derived Boolean region in retained, named contexts

One rules instance contains both native J and the two-constructor Boolean
datatype with its genuine computation rules. A Boolean uniqueness proof is
derived there, stored with its original syntax, and applied in a larger
current context by a checked nonidentity substitution.

Losing the selected current binding makes that named application unavailable;
it neither erases the original proof nor invalidates its source judgment.
An explicitly retained binding can still be used. The source context assumes
only Boolean endpoints and paths, not uniqueness or a decision oracle.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNativeBooleanNamedRegion

open Mettapedia.TypeTheory.NamedValueContexts
open Mettapedia.TypeTheory.RetainedPresentationViews
open Mettapedia.Machines
open Mettapedia.GSLT.LanguageDef.FiniteEnvironmentCompilation
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation Presentation.Declaration Presentation.FormationSensitive RussellTarski
open SharedJudgmentNamedIdentityRegions

abbrev rules : Rules Tower.Head := SharedJudgmentNativeBooleanRegion.rules

/-- Both Boolean endpoints and both paths are parameters. There is no
uniqueness hypothesis, and neither endpoint is chosen by a host-language case. -/
def sourceContext : Tower.Ctx 4 :=
  .snoc (.snoc (.snoc (.snoc .nil SharedJudgmentNativeBooleanRegion.boolTm)
    SharedJudgmentNativeBooleanRegion.boolTm)
    (.id SharedJudgmentNativeBooleanRegion.boolTm (.var 1) (.var 0)))
    (.id SharedJudgmentNativeBooleanRegion.boolTm (.var 2) (.var 1))

theorem source_context_formed : ContextFormation rules sourceContext :=
  .snoc (.snoc (.snoc (.snoc .nil (SharedJudgmentNativeBooleanRegion.bool_typed .nil)
    (.sort SharedJudgmentNativeBooleanRegion.zero))
    (SharedJudgmentNativeBooleanRegion.bool_typed _) (.sort SharedJudgmentNativeBooleanRegion.zero))
    (.idForm (SharedJudgmentNativeBooleanRegion.bool_typed _) (.sort SharedJudgmentNativeBooleanRegion.zero)
      (.var 1) (.var 0))
    (.sort SharedJudgmentNativeBooleanRegion.zero))
    (.idForm (SharedJudgmentNativeBooleanRegion.bool_typed _) (.sort SharedJudgmentNativeBooleanRegion.zero)
      (.var 2) (.var 1))
    (.sort SharedJudgmentNativeBooleanRegion.zero)

def derivedProof : ProofPresentation 4 :=
  ⟨sourceContext,
    SharedJudgmentNativeBooleanConstancy.regionPoint (.var 3) (.var 2) (.var 1) (.var 0),
    .id (.id SharedJudgmentNativeBooleanRegion.boolTm (.var 3) (.var 2))
      (.var 1) (.var 0)⟩

theorem derived_proof_typed :
    Judgment rules derivedProof.context derivedProof.term derivedProof.type :=
  ⟨source_context_formed,
    SharedJudgmentNativeBooleanConstancy.regionPoint_typed source_context_formed
      (.var 3) (.var 2) (.var 1) (.var 0)⟩

/-- An extra Boolean parameter changes every old variable index. The
original endpoints and paths are not replaced by the new local parameter. -/
def extendedBinding : Binding 4 5 :=
  ⟨.snoc sourceContext SharedJudgmentNativeBooleanRegion.boolTm, projection⟩

theorem extended_context_formed : ContextFormation rules extendedBinding.target :=
  .snoc source_context_formed (SharedJudgmentNativeBooleanRegion.bool_typed sourceContext)
    (.sort SharedJudgmentNativeBooleanRegion.zero)

theorem extended_binding_typed :
    FormationSensitive.CtxMor rules derivedProof.context extendedBinding.target extendedBinding.substitution := by
  intro index
  change Typing rules (.snoc sourceContext SharedJudgmentNativeBooleanRegion.boolTm) (.var index.succ)
    (subst projection (Ctx.lookup sourceContext index))
  simpa only [extendedBinding, subst_projection, Ctx.lookup_snoc_succ]
    using (Typing.var (R := rules) (Γ := extendedBinding.target) index.succ)

theorem extended_claim_keeps_the_original_endpoints :
    (derivedProof.instantiate extendedBinding).type =
      .id (.id SharedJudgmentNativeBooleanRegion.boolTm (.var 4) (.var 3))
        (.var 2) (.var 1) := rfl

def proofVersion : StoreReadToken String Nat := ⟨"Boolean-region-proof", 0⟩
def bindingVersion : StoreReadToken String Nat := ⟨"Boolean-region-parameters", 0⟩
def before : RevisionEnvironment String Nat := ⟨fun _ => 0⟩
def afterWithdrawal : RevisionEnvironment String Nat := before.update "Boolean-region-parameters" 1

def proofs : ProofStore String Nat 4 := writeSource (fun _ => none) (proofVersion, derivedProof)
def bindings : BindingStore String Nat 4 5 := writeSource (fun _ => none) (bindingVersion, extendedBinding)
def view : ProofView String Nat 4 := ⟨derivedProof.claim, proofVersion⟩

theorem capture_original :
    captureView proofs before "Boolean-region-proof" ProofPresentation.claim = some view := by
  simp [captureView, proofs, before, writeSource, proofVersion, view]

theorem recover_original : recover proofs view = some derivedProof := by
  simp [recover, proofs, view, writeSource]

theorem current_binding_resolves :
    resolve bindings before (.live "Boolean-region-parameters") = some extendedBinding := by
  simp [resolve, bindings, before, bindingVersion, writeSource]

theorem derived_named_application_typed :
    ∃ output, resolveApplication proofs bindings before view (.live "Boolean-region-parameters") = some output ∧
      Judgment rules output.context output.term output.type :=
  resolved_application_typed rules proofs bindings before view (.live "Boolean-region-parameters")
    derivedProof extendedBinding recover_original current_binding_resolves derived_proof_typed
    extended_context_formed extended_binding_typed

theorem unavailable_binding_preserves_original_inspection :
    recover proofs view = some derivedProof ∧
      Judgment rules derivedProof.context derivedProof.term derivedProof.type ∧
      resolveApplication proofs bindings afterWithdrawal view (.live "Boolean-region-parameters") = none := by
  refine ⟨recover_original, derived_proof_typed, ?_⟩
  apply missing_binding_no_application
  simp [resolve, bindings, afterWithdrawal, before, bindingVersion, writeSource,
    RevisionEnvironment.update]

theorem retained_binding_application_typed :
    ∃ output, resolveApplication proofs bindings afterWithdrawal view (.versioned bindingVersion) = some output ∧
      Judgment rules output.context output.term output.type := by
  apply resolved_application_typed rules proofs bindings afterWithdrawal view (.versioned bindingVersion)
    derivedProof extendedBinding recover_original
  · simp [resolve, bindings, writeSource]
  · exact derived_proof_typed
  · exact extended_context_formed
  · exact extended_binding_typed

theorem unrelated_change_preserves_named_application :
    resolveApplication proofs bindings (before.update "unrelated" 1) view (.live "Boolean-region-parameters") =
      resolveApplication proofs bindings before view (.live "Boolean-region-parameters") :=
  unrelated_revision_preserves_application proofs bindings before view "Boolean-region-parameters"
    "unrelated" 1 (by decide)

/-- One actual language instance witnesses derivation, retained inspection,
typed nonidentity application and the live-versus-retained binding distinction. -/
theorem derived_boolean_region_named_context_contract :
    Judgment rules derivedProof.context derivedProof.term derivedProof.type ∧
      recover proofs view = some derivedProof ∧
      (∃ output, resolveApplication proofs bindings before view (.live "Boolean-region-parameters") = some output ∧
        Judgment rules output.context output.term output.type) ∧
      resolveApplication proofs bindings afterWithdrawal view (.live "Boolean-region-parameters") = none ∧
      (∃ output, resolveApplication proofs bindings afterWithdrawal view (.versioned bindingVersion) = some output ∧
        Judgment rules output.context output.term output.type) :=
  ⟨derived_proof_typed, recover_original, derived_named_application_typed,
    unavailable_binding_preserves_original_inspection.2.2, retained_binding_application_typed⟩

def checks : List Bool :=
  [((recover proofs view).map fun proof => proof.term == derivedProof.term).getD false,
   ((resolveApplication proofs bindings before view (.live "Boolean-region-parameters")).map
      fun proof => proof.term == subst projection derivedProof.term).getD false,
   (resolveApplication proofs bindings afterWithdrawal view (.live "Boolean-region-parameters")).isNone,
   ((resolveApplication proofs bindings afterWithdrawal view (.versioned bindingVersion)).map
      fun proof => proof.term == subst projection derivedProof.term).getD false,
   ((resolveApplication proofs bindings (before.update "unrelated" 1) view (.live "Boolean-region-parameters")).map
      fun proof => proof.term == subst projection derivedProof.term).getD false,
   decide (extendedBinding.substitution (0 : Fin 4) ≠ (.var 0 : Tower.Tm 5))]

theorem checks_pass : checks = [true, true, true, true, true, true] := by decide

#eval checks

#print axioms source_context_formed
#print axioms derived_proof_typed
#print axioms extended_binding_typed
#print axioms derived_named_application_typed
#print axioms unavailable_binding_preserves_original_inspection
#print axioms retained_binding_application_typed
#print axioms derived_boolean_region_named_context_contract
#print axioms checks_pass

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNativeBooleanNamedRegion
