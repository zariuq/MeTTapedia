import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentIdentityRegions
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNamedContext
import Mettapedia.TypeTheory.RetainedPresentationViews

/-!
# Named contexts for conditional native identity proofs

The proof store contains actual native terms, source contexts and types.
Its retained-reference view exposes the claim while preserving exact source
inspection. A separate named binding supplies the current native substitution
and target context. Applicability is derived by the existing native substitution
theorem; neither a name nor a retained reference is a typing certificate.

The concrete interpretation uses the native List/J/ListRel rules at the identity
level instance over the common HOL/List/wire signature. Its direct congruence
proof and its exported conditional proof applied to a hypothesis have distinct
syntax, the same typed claim and an actual beta conversion. Updating a live
binding can make current application unavailable while leaving the original
proof inspectable. Unrelated-name changes and retained old bindings preserve
application. No native proof checker or execution history is introduced.

This qualifies one named-context interface; it does not assert a model of all
candidate features or turn failure to resolve a binding into non-derivability.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNamedIdentityRegions

open Mettapedia.TypeTheory.NamedValueContexts
open Mettapedia.TypeTheory.RetainedPresentationViews
open Mettapedia.Machines
open Mettapedia.GSLT.LanguageDef.FiniteEnvironmentCompilation
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation Presentation.Declaration Presentation.FormationSensitive RussellTarski
open SharedJudgmentIdentityRegions

variable {Name Revision : Type} {n m : Nat}

/-- Raw native syntax and its advertised scope. Validity is proved separately. -/
structure ProofPresentation (n : Nat) where
  context : Tower.Ctx n
  term : Tower.Tm n
  type : Tower.Tm n

/-- The scoped claim is the value view; it does not expose the proof term. -/
def ProofPresentation.claim (proof : ProofPresentation n) : Tower.Ctx n × Tower.Tm n :=
  (proof.context, proof.type)

structure Binding (n m : Nat) where
  target : Tower.Ctx m
  substitution : Sub Tower.Head n m

def ProofPresentation.instantiate (proof : ProofPresentation n) (binding : Binding n m) :
    ProofPresentation m :=
  ⟨binding.target, subst binding.substitution proof.term, subst binding.substitution proof.type⟩

abbrev ProofStore (Name Revision : Type) (n : Nat) :=
  ContextTable Name Revision (ProofPresentation n)

abbrev BindingStore (Name Revision : Type) (n m : Nat) :=
  ContextTable Name Revision (Binding n m)

abbrev ProofView (Name Revision : Type) (n : Nat) :=
  View Name Revision (Tower.Ctx n × Tower.Tm n)

/-- Resolve original proof and independently selected current binding.
The resulting operation is actual capture-avoiding native substitution. -/
def resolveApplication (proofs : ProofStore Name Revision n)
    (bindings : BindingStore Name Revision n m)
    (current : RevisionEnvironment Name Revision) (view : ProofView Name Revision n)
    (reference : Reference Name Revision) : Option (ProofPresentation m) := do
  let proof ← recover proofs view
  let binding ← resolve bindings current reference
  pure (proof.instantiate binding)

theorem resolved_application_exact
    (proofs : ProofStore Name Revision n) (bindings : BindingStore Name Revision n m)
    (current : RevisionEnvironment Name Revision) (view : ProofView Name Revision n)
    (reference : Reference Name Revision) (proof : ProofPresentation n) (binding : Binding n m)
    (original : recover proofs view = some proof)
    (environment : resolve bindings current reference = some binding) :
    resolveApplication proofs bindings current view reference = some (proof.instantiate binding) := by
  simp [resolveApplication, original, environment]

/-- The rules are fixed across source proof, environment admission and
result. Typed substitution is used to derive the result, not assumed as its type. -/
theorem resolved_application_typed
    (rules : Rules Tower.Head)
    (proofs : ProofStore Name Revision n) (bindings : BindingStore Name Revision n m)
    (current : RevisionEnvironment Name Revision) (view : ProofView Name Revision n)
    (reference : Reference Name Revision) (proof : ProofPresentation n) (binding : Binding n m)
    (original : recover proofs view = some proof)
    (environment : resolve bindings current reference = some binding)
    (source : Judgment rules proof.context proof.term proof.type)
    (targetFormed : ContextFormation rules binding.target)
    (typed : FormationSensitive.CtxMor rules proof.context binding.target binding.substitution) :
    ∃ output, resolveApplication proofs bindings current view reference = some output ∧
      Judgment rules output.context output.term output.type :=
  ⟨proof.instantiate binding,
    resolved_application_exact proofs bindings current view reference proof binding original environment,
    source.substitute targetFormed typed⟩

theorem missing_binding_no_application
    (proofs : ProofStore Name Revision n) (bindings : BindingStore Name Revision n m)
    (current : RevisionEnvironment Name Revision) (view : ProofView Name Revision n)
    (reference : Reference Name Revision)
    (missing : resolve bindings current reference = none) :
    resolveApplication proofs bindings current view reference = none := by
  simp [resolveApplication, missing]

theorem unrelated_revision_preserves_application [DecidableEq Name]
    (proofs : ProofStore Name Revision n) (bindings : BindingStore Name Revision n m)
    (current : RevisionEnvironment Name Revision) (view : ProofView Name Revision n)
    (observed changed : Name) (revision : Revision) (different : observed ≠ changed) :
    resolveApplication proofs bindings (current.update changed revision) view (.live observed) =
      resolveApplication proofs bindings current view (.live observed) := by
  simp only [resolveApplication, live_resolution_update_other bindings current observed changed
    revision different]

/-- A newly published proof never retargets the old retained proof view.
This is same-store-lineage preservation, not authentication of an arbitrary store. -/
theorem proof_publication_preserves_application [DecidableEq Name] [DecidableEq Revision]
    (proofs updated : ProofStore Name Revision n) (bindings : BindingStore Name Revision n m)
    (current : RevisionEnvironment Name Revision) (view : ProofView Name Revision n)
    (reference : Reference Name Revision) (original newProof : ProofPresentation n)
    (newVersion : StoreReadToken Name Revision)
    (found : recover proofs view = some original)
    (published : publishVersion? proofs newVersion newProof = some updated) :
    resolveApplication updated bindings current view reference =
      resolveApplication proofs bindings current view reference := by
  have preserved := recover_preserved_by_publication proofs updated newVersion newProof original
    view published found
  simp only [resolveApplication, preserved, found]

namespace Controls

def levels : Nat → LevelExpr := LevelExpr.param

def rules : Rules Tower.Head :=
  NativeIdentityLevelInstantiation.rules levels HOLNativeRelatorCompatibility.signature

def sourceContext : Tower.Ctx 6 := SharedJudgmentIdentityRegions.Controls.assumedContext levels

def conclusion : Tower.Tm 6 :=
  .id (.var 4) (.app (.var 3) (.var 2)) (.app (.var 3) (.var 1))

def direct : ProofPresentation 6 :=
  ⟨sourceContext, congruenceTerm (.var 5) (.var 2) (.var 4) (.var 3) (.var 1) (.var 0),
    conclusion⟩

def exportedConditional : Tower.Tm 6 :=
  conditionalCongruence (.var 5) (.var 2) (.var 4) (.var 3) (.var 1)

def discharged : ProofPresentation 6 :=
  ⟨sourceContext, .app exportedConditional (.var 0), conclusion⟩

theorem context_formed : ContextFormation rules sourceContext :=
  SharedJudgmentIdentityRegions.Controls.assumed_context_formed levels HOLNativeRelatorCompatibility.signature

theorem direct_typed : Judgment rules direct.context direct.term direct.type :=
  SharedJudgmentIdentityRegions.Controls.assumed_example levels HOLNativeRelatorCompatibility.signature

theorem exported_conditional_typed :
    Judgment rules sourceContext exportedConditional
      (arrow (.id (.var 5) (.var 2) (.var 1)) conclusion) :=
  conditionalCongruence_typed context_formed (.var 5) (.var 4) (.var 2) (.var 1) (.var 3)

theorem discharged_typed : Judgment rules discharged.context discharged.term discharged.type :=
  discharge_conditional context_formed (.var 5) (.var 4) (.var 2) (.var 1) (.var 3) (.var 0)

theorem same_claim_distinct_proofs :
    direct.claim = discharged.claim ∧ direct.term ≠ discharged.term := by
  exact ⟨rfl, by decide⟩

theorem actual_discharge_conversion :
    Conv rules.headEq discharged.term direct.term rules.computation := discharge_beta ..

theorem proof_claim_has_no_original_decoder :
    ¬ ∃ decode : Erased (ProofPresentation.claim (n := 6)) → ProofPresentation 6,
      ∀ original, decode (erase ProofPresentation.claim original) = original := by
  apply collision_prevents_exact_recovery ProofPresentation.claim direct discharged rfl
  intro same
  exact same_claim_distinct_proofs.2 (congrArg ProofPresentation.term same)

def identityBinding : Binding 6 6 := ⟨sourceContext, ids⟩

theorem identity_binding_typed :
    FormationSensitive.CtxMor rules direct.context identityBinding.target identityBinding.substitution :=
  FormationSensitiveContextual.identityTyped _

def originalVersion : StoreReadToken String Nat := ⟨"region-proof", 0⟩
def newVersion : StoreReadToken String Nat := ⟨"region-proof", 1⟩
def bindingVersion : StoreReadToken String Nat := ⟨"region-assumptions", 0⟩
def before : RevisionEnvironment String Nat := ⟨fun _ => 0⟩
def afterWithdrawal : RevisionEnvironment String Nat := before.update "region-assumptions" 1

def proofStore : ProofStore String Nat 6 :=
  writeSource (fun _ => none) (originalVersion, discharged)

def extendedProofStore : ProofStore String Nat 6 := writeSource proofStore (newVersion, direct)

def bindings : BindingStore String Nat 6 6 :=
  writeSource (fun _ => none) (bindingVersion, identityBinding)

def view : ProofView String Nat 6 := ⟨discharged.claim, originalVersion⟩

theorem original_capture :
    captureView proofStore before "region-proof" ProofPresentation.claim = some view := by
  simp [captureView, proofStore, before, writeSource, originalVersion, view]

theorem original_resolves : recover proofStore view = some discharged := by
  simp [recover, proofStore, view, writeSource]

theorem current_binding_resolves : resolve bindings before (.live "region-assumptions") = some identityBinding := by
  simp [resolve, bindings, before, bindingVersion, writeSource]

theorem original_application_admitted :
    ∃ output, resolveApplication proofStore bindings before view (.live "region-assumptions") =
        some output ∧ Judgment rules output.context output.term output.type :=
  resolved_application_typed rules proofStore bindings before view (.live "region-assumptions")
    discharged identityBinding original_resolves current_binding_resolves discharged_typed
    context_formed identity_binding_typed

/-- Withdrawing the live binding changes availability, not the stored native
proof's syntax or its validity under the retained original hypotheses. -/
theorem original_inspection_survives_unavailable_current_application :
    recover proofStore view = some discharged ∧
      Judgment rules discharged.context discharged.term discharged.type ∧
      resolveApplication proofStore bindings afterWithdrawal view (.live "region-assumptions") = none := by
  refine ⟨original_resolves, discharged_typed, ?_⟩
  apply missing_binding_no_application
  simp [resolve, bindings, afterWithdrawal, before, bindingVersion, writeSource,
    RevisionEnvironment.update]

theorem retained_binding_still_applies :
    ∃ output, resolveApplication proofStore bindings afterWithdrawal view (.versioned bindingVersion) =
        some output ∧ Judgment rules output.context output.term output.type := by
  apply resolved_application_typed rules proofStore bindings afterWithdrawal view (.versioned bindingVersion)
    discharged identityBinding original_resolves
  · simp [resolve, bindings, writeSource]
  · exact discharged_typed
  · exact context_formed
  · exact identity_binding_typed

theorem unrelated_change_keeps_current_application :
    resolveApplication proofStore bindings (before.update "unrelated" 1) view (.live "region-assumptions") =
      resolveApplication proofStore bindings before view (.live "region-assumptions") :=
  unrelated_revision_preserves_application proofStore bindings before view "region-assumptions"
    "unrelated" 1 (by decide)

theorem fresh_proof_publication : publishVersion? proofStore newVersion direct = some extendedProofStore := by
  simp [publishVersion?, proofStore, newVersion, originalVersion, writeSource, extendedProofStore]

theorem original_not_replaced_by_equivalent_proof :
    recover extendedProofStore view = some discharged ∧
      resolveApplication extendedProofStore bindings before view (.live "region-assumptions") =
        resolveApplication proofStore bindings before view (.live "region-assumptions") :=
  ⟨recover_preserved_by_publication proofStore extendedProofStore newVersion direct discharged view
      fresh_proof_publication original_resolves,
    proof_publication_preserves_application proofStore extendedProofStore bindings before view
      (.live "region-assumptions") discharged direct newVersion original_resolves fresh_proof_publication⟩

/-- A larger current scope supplies a genuinely nonidentity substitution:
every retained proof variable moves past a new, independently formed binder. -/
def extendedBinding : Binding 6 7 :=
  ⟨.snoc sourceContext (sortTm (.param 0)), projection⟩

theorem extended_target_formed : ContextFormation rules extendedBinding.target :=
  .snoc context_formed (.headType (.sort (.param 0))) (.sort (.succ (.param 0)))

theorem extended_binding_typed :
    FormationSensitive.CtxMor rules discharged.context extendedBinding.target extendedBinding.substitution := by
  intro index
  change Typing rules (.snoc sourceContext (sortTm (.param 0))) (.var index.succ)
    (subst projection (Ctx.lookup sourceContext index))
  simpa only [extendedBinding, subst_projection, Ctx.lookup_snoc_succ]
    using (Typing.var (R := rules) (Γ := extendedBinding.target) index.succ)

def extendedBindings : BindingStore String Nat 6 7 :=
  writeSource (fun _ => none) (bindingVersion, extendedBinding)

theorem nonidentity_named_application_admitted :
    ∃ output, resolveApplication proofStore extendedBindings before view (.live "region-assumptions") =
        some output ∧ Judgment rules output.context output.term output.type := by
  apply resolved_application_typed rules proofStore extendedBindings before view (.live "region-assumptions")
    discharged extendedBinding original_resolves
  · simp [resolve, extendedBindings, before, bindingVersion, writeSource]
  · exact discharged_typed
  · exact extended_target_formed
  · exact extended_binding_typed

/-- The actual native motive and its equality witness are reindexed. The
newest binder is not accidentally substituted for the old hypothesis. -/
theorem nonidentity_substitution_retains_native_motive :
    (direct.instantiate extendedBinding).term =
      congruenceTerm (.var 6) (.var 3) (.var 5) (.var 4) (.var 2) (.var 1) := by
  exact congruenceTerm_substitute projection
    (.var 5) (.var 2) (.var 4) (.var 3) (.var 1) (.var 0)

/-- These booleans inspect native proof syntax and actual lookup/substitution
outputs. They do not re-run the judgment or infer logical falsity from absence. -/
def checks : List Bool :=
  [decide (direct.term ≠ discharged.term),
   ((recover extendedProofStore view).map fun proof => proof.term == discharged.term).getD false,
   ((resolveApplication proofStore bindings before view (.live "region-assumptions")).map
      fun proof => proof.term == discharged.term).getD false,
   (resolveApplication proofStore bindings afterWithdrawal view (.live "region-assumptions")).isNone,
   ((resolveApplication proofStore bindings afterWithdrawal view (.versioned bindingVersion)).map
      fun proof => proof.term == discharged.term).getD false,
   ((resolveApplication proofStore bindings (before.update "unrelated" 1) view (.live "region-assumptions")).map
      fun proof => proof.term == discharged.term).getD false,
   ((resolveApplication proofStore extendedBindings before view (.live "region-assumptions")).map
      fun proof => proof.term == subst projection discharged.term).getD false,
   decide (extendedBinding.substitution (0 : Fin 6) ≠ (.var 0 : Tower.Tm 7))]

theorem checks_pass : checks = [true, true, true, true, true, true, true, true] := by decide

#eval checks

end Controls

#print axioms resolved_application_typed
#print axioms proof_publication_preserves_application
#print axioms Controls.direct_typed
#print axioms Controls.exported_conditional_typed
#print axioms Controls.discharged_typed
#print axioms Controls.actual_discharge_conversion
#print axioms Controls.proof_claim_has_no_original_decoder
#print axioms Controls.original_application_admitted
#print axioms Controls.original_inspection_survives_unavailable_current_application
#print axioms Controls.retained_binding_still_applies
#print axioms Controls.nonidentity_named_application_admitted
#print axioms Controls.nonidentity_substitution_retains_native_motive
#print axioms Controls.checks_pass

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNamedIdentityRegions
