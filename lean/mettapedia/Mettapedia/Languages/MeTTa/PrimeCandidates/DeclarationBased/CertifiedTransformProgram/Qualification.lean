import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ArtifactComparison
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.DraftComparison
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.EtaConversion
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.IdentityEquality.Carriers
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.IdentityEquality.Controls
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.IdentityEquality.KernelSpelling
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.IdentityEquality.Linking
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.IdentityEquality.Translation
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.Controls
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.HOTGConsumer
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.Preservation
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.SetProfile.Models

/-!
Independent qualification of the Prime candidate's equality bridge.

The admitted `pf:equality` declaration gives `subst@num` the type of
substitution over `num → prop`. The candidate theorem
`identity_from_hosted_induction` assumes that same constant is typed at an
identity-valued transport. Those are different types. The conditional
theorem can still be valid. It is not a discharged application, and the
difference is not a Lean inconsistency.

The linked construction derives the substitution map. `linked_exists`
keeps an explicit `compiles` hypothesis, so it is not a totality theorem.
Unfolding a compiler equation by `rfl` is not this bridge.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.Qualification

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation Presentation.FormationSensitive
open CertifiedTransformProgram.Package
open CertifiedTransformProgram.IdentityEquality
open CertifiedTransformProgram.IdentityEquality.Carriers
open CertifiedTransformProgram.IdentityEquality.Controls
open CertifiedTransformProgram.IdentityEquality.Linking
open CertifiedTransformProgram.IdentityEquality.Metatheory
open CertifiedTransformProgram.IdentityEquality.Translation
open Mettapedia.Logic
open CertifiedTransformProgram.ArtifactComparison
open CertifiedTransformProgram.EtaConversion
open SetProfile (numTy)

/-- The shape of the occupied `transportAt`. Binders, outer to inner:
the index `i : num`, the hosted equation `eq@num (add zero i) i`, and
`Id num (add zero i) (add zero i)`. The result is `Id num (add zero i) i`.
`substTyped` assumes `subst@num` has this type. The admitted decoding does not. -/
def transportShape : Tower.Tm 0 :=
  .pi numT <|
    .pi (SetProfile.eqNumNative (SetProfile.addNative SetProfile.zeroNative (.var 0)) (.var 0)) <|
      .pi (.id numT
          (SetProfile.addNative SetProfile.zeroNative (.var 1))
          (SetProfile.addNative SetProfile.zeroNative (.var 1))) <|
        .id numT (SetProfile.addNative SetProfile.zeroNative (.var 2)) (.var 2)

/-- The occupied candidate calls this shape `transportAt`. -/
abbrev transportAt : Tower.Tm 0 := transportShape

/-- The admitted declaration, specialized at `num`, is `SetProfile.substAxiom`. -/
theorem admitted_subst_at_num :
    substitution numTy = SetProfile.substAxiom :=
  substitution_num

/-- The admitted decoding and the identity-valued transport are different types.
Assuming a typing at `transportShape` is therefore not discharged by the
admitted document's decoding. -/
theorem admitted_decoding_is_not_transport :
    substDecodedAt numTy ≠ transportShape := by
  intro same
  cases same

/-- A valid conditional use of an extra typing hypothesis is not yet an
application discharged by the admitted declaration. -/
theorem identity_valued_typing_is_not_discharged
    (identified : substDecodedAt numTy = transportShape) : False :=
  admitted_decoding_is_not_transport identified

/-- The linked source proof at an open index. Source assumptions are discharged
by `zeroAddPublished`: induction, reflexivity at `num`, substitution at `num`.
The identity reading is discharged by `identity_decodes` and `toIdentity`. -/
theorem linked_open_index_derivation :
    Typing identityRules (.snoc .nil numT)
      (.app (liftClosed linkedZeroAdd) (.var 0)) (eqAtApp (.var 0)) :=
  linkedZeroAdd_open

/-- Extending the empty context by `num` preserves the linked statement. -/
theorem linked_statement_extends :
    Typing identityRules (.snoc .nil numT)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.rename
        Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.wk linkedZeroAdd)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.rename
        Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.wk zeroAddDecoded) :=
  linkedZeroAdd_decoded.weaken (extension := numT)

/-- At `num → num`, the linked symmetry proof consumes the derived substitution
map. `Published.substitution` discharges the source axiom; `jApp` discharges
the eliminator inside `substRealizationAt`. -/
theorem function_carrier_consumption :
    Typing identityRules .nil linkedSymmetry symmetryDecoded :=
  linkedSymmetry_decoded

/-- The Power congruence statement is exactly `∀ a b. a = b → Power a = Power b`. -/
theorem power_congruence_is_one_statement :
    congruenceStatement =
      .all (σ := sets) (.all (σ := sets)
        (.imp (.eq (.var (.vs .vz)) (.var .vz))
          (.eq (powerT (.var (.vs .vz))) (powerT (.var .vz))))) :=
  rfl

/-- Decoding an identity path is not equality reflection. -/
theorem equality_reflection_fails :
    Typing identityLinearRules IdentityEquality.Controls.pathContext (.var 0)
        (.id numT (.var 2) (.var 1)) ∧
      ¬ Conv identityLinearRules.headEq (.var 2 : Tower.Tm 3) (.var 1)
        identityLinearRules.computation :=
  IdentityEquality.Controls.not_reflection

/-- Plain reflexivity is not `eqAt` at an open index. -/
theorem open_reflexivity_is_not_the_linked_evidence :
    ¬ Typing identityLinearRules (.snoc .nil numT) (.refl (.var 0)) (eqAtApp (.var 0)) :=
  refl_not_eqAt_open

/-- Opened captured text is the admitted zero-add term and its proof-family type. -/
theorem article_renders_as_admitted_package :
    capturedTerm.toTmAt 0 = some SetProfile.zeroAddTerm ∧
      capturedType.toTmAt 0 =
        some (FormationSensitiveHOLGenericProofFamily.proof SetProfile.holdsName
          SetProfile.zeroAddCode) :=
  And.intro capturedTerm_erases capturedType_translates

/-- The captured proof is an application. The unrelated marker is a declaration name. -/
theorem unrelated_marker_is_not_the_article :
    capturedTerm ≠ KTerm.declConst "(not-a-proof-term)" := by
  intro same
  cases same

/-- Which surface a control qualifies. -/
inductive EvidenceClass
  | rawInput
  | typedTerm
  | ordinaryExecution
  | proofSearch

/-- A control carries its class and the fact it establishes. -/
structure Labeled (class_ : EvidenceClass) (fact : Prop) : Prop where
  established : fact

/-! ## Commuting comparisons -/

/-- Context extension commutes with the linked reading: weakening the closed
typing is the typing of the renamed term in the context extended by `num`. -/
theorem context_extension_commutes :
    Typing identityRules (.snoc .nil numT)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.rename
        Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.wk linkedZeroAdd)
      (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.rename
        Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.wk zeroAddDecoded) :=
  linked_statement_extends

/-- Substitution commutes with representation. The hypothesis is the represented
source formula. The conclusion is the identity-profile typing of its realization.
The admitted formula is `subst@num`, not `transportAt`. -/
theorem substitution_commutes
    {code : Tower.Tm 0}
    (represented : FormationSensitiveHOLInterface.represent SetProfile.signature
      (substitution numTy) = some code) :
    Typing identityRules .nil (substRealizationAt numTy)
      (IdentityEquality.Realizations.Holds code) :=
  substRealizationAt_typed numTy represented

/-- Type specialization commutes with the linked reading: the closed proof,
applied at the open index, is `eqAt` at that index. -/
theorem type_specialization_commutes :
    Typing identityRules (.snoc .nil numT)
      (.app (liftClosed linkedZeroAdd) (.var 0)) (eqAtApp (.var 0)) :=
  linkedZeroAdd_open

/-- The same specialization at the function carrier `num → num`. -/
theorem function_specialization_commutes :
    Typing identityRules IdentityEquality.Linking.pathContext
      (.app (.app (.app (liftClosed linkedSymmetry) (.var 2)) (.var 1)) (.var 0))
      (.id (carrier functions) (.var 1) (.var 2)) :=
  linkedSymmetry_open

/-- Conversion evidence commutes from the linearized rules into the identity
profile. The converse, equality reflection, is the separate negative below. -/
theorem conversion_evidence_commutes
    {n : Nat} {left right : Tower.Tm n}
    (conversion : Conv Confluence.linearRules.headEq left right Confluence.linearRules.computation) :
    Conv identityLinearRules.headEq left right identityLinearRules.computation :=
  IdentityEquality.Controls.toProfile_conversion conversion

/-- Assumptions commute with compilation: a source proof whose assumptions are
published facts, compiled against their realizations, is typed at its statement.
`linked_exists` still requires an explicit `compiles` witness, so this is not
totality. -/
theorem assumptions_commute
    {assumptions : List (HOL.Formula SetProfile.SetConst [])}
    {statement : HOL.Formula SetProfile.SetConst []}
    (proof : HOL.ProofSyntaxModulo SetProfile.sourceEquations assumptions statement)
    (published : ∀ index : Fin assumptions.length, Published (assumptions.get index))
    {term : Tower.Tm 0}
    (compiled : HOLNativeGenericProofCompiler.Modulo.compileModulo SetProfile.signature
      proof Fin.elim0 (fun index => (published index).realization) = some term) :
    ∃ code, FormationSensitiveHOLInterface.represent SetProfile.signature statement = some code ∧
      Typing identityRules .nil term (IdentityEquality.Realizations.Holds code) :=
  linked_typed proof published compiled

theorem linked_exists_keeps_compiles
    {assumptions : List (HOL.Formula SetProfile.SetConst [])}
    {statement : HOL.Formula SetProfile.SetConst []}
    (proof : HOL.ProofSyntaxModulo SetProfile.sourceEquations assumptions statement)
    (published : ∀ index : Fin assumptions.length, Published (assumptions.get index))
    (compiles : ∃ term, HOLNativeGenericProofCompiler.Modulo.compileModulo
      SetProfile.signature proof Fin.elim0
        (fun index => (published index).realization) = some term) :
    ∃ term code, FormationSensitiveHOLInterface.represent SetProfile.signature statement = some code ∧
      Typing identityRules .nil term (IdentityEquality.Realizations.Holds code) :=
  linked_exists proof published compiles

/-! ## Covered induction, and axioms that stay assumptions -/

private theorem zeroAddLength : SetProfile.zeroAddAssumptions.length = 3 := rfl

private def publishedIndex0 : Fin SetProfile.zeroAddAssumptions.length :=
  ⟨0, zeroAddLength.symm ▸ Nat.zero_lt_succ 2⟩

private def publishedIndex1 : Fin SetProfile.zeroAddAssumptions.length :=
  ⟨1, zeroAddLength.symm ▸ Nat.succ_lt_succ (Nat.zero_lt_succ 1)⟩

private def publishedIndex2 : Fin SetProfile.zeroAddAssumptions.length :=
  ⟨2, zeroAddLength.symm ▸ Nat.lt_succ_self 2⟩

/-- The zero-add support is induction, reflexivity at `num`, and substitution
at `num`. Each realization is that published fact. -/
theorem induction_covers_num :
    (zeroAddPublished publishedIndex0).realization =
        IdentityEquality.Realizations.inductionRealization ∧
      (zeroAddPublished publishedIndex1).realization =
        IdentityEquality.Realizations.reflRealization ∧
      (zeroAddPublished publishedIndex2).realization =
        substRealizationAt numTy :=
  ⟨rfl, rfl, rfl⟩

/-- Without the induction assumption, reflexivity and substitution do not prove
`zero-add`. The recursor hypothesis is limited to that covered class. -/
theorem induction_cannot_be_dropped :
    Labeled .proofSearch
      (¬ Nonempty (HOL.ProofSyntaxModulo SetProfile.sourceEquations
        [SetProfile.reflAxiom, SetProfile.substAxiom] SetProfile.zeroAddStatement)) :=
  ⟨SetProfile.Models.induction_needed⟩

/-- Revising the successor equation of `add` withdraws `zero-add` from the three
assumed facts. Stale support is not a proof. -/
theorem revised_support_withdraws_zero_add :
    Labeled .proofSearch
      (¬ Nonempty (HOL.ProofSyntaxModulo SetProfile.Models.revisedEquations
        SetProfile.zeroAddAssumptions SetProfile.zeroAddStatement)) :=
  ⟨SetProfile.Models.revision_invalidates⟩

/-- Choice (`Eps_set`), separation, replacement and `UnivOf` stay declarations
of the captured vocabulary. The zero-add proof does not discharge them:
its published support is the three facts above. -/
theorem vocabulary_declaration_is_not_the_proof_support
    (entry : String × KTerm) (listed : entry ∈ capturedContext) :
    Labeled .typedTerm
      (∃ type, entry.2.toTmAt 0 = some type ∧
        SetProfile.targetRules.constantType (.mkSimple entry.1) = some type) :=
  ⟨capturedContext_types entry listed⟩

/-- Universe closure stays an assumption. Membership of a set in the singleton
interpretation of its universe does not prove the HOTG step. That singleton
interpretation is a comparison, not Prime's foundation. -/
theorem universe_closure_stays_an_assumption :
    Labeled .proofSearch
      (¬ Nonempty (HOL.ProofSyntaxModulo SetProfile.sourceEquations
        [HOTGConsumer.univMemAxiom] HOTGConsumer.hotgStepStatement)) :=
  ⟨HOTGConsumer.closure_needed⟩

/-- Power congruence is one formula. It is not the HOTG universe step. -/
theorem power_congruence_is_not_the_universe_step :
    congruenceStatement ≠ HOTGConsumer.hotgStepStatement := by
  intro same
  cases same

/-- The represented formula, its native identity decoding, and equality
reflection are three readings. Reflection fails. -/
theorem three_readings_stay_separate :
    (∃ code, FormationSensitiveHOLInterface.represent SetProfile.signature
        (substitution numTy) = some code) ∧
      (FormationSensitiveHOLIdentityEquality.decode SetProfile.signature SetProfile.holdsName
        (substitution numTy) = some (substDecodedAt numTy)) ∧
      ¬ Conv identityLinearRules.headEq (.var 2 : Tower.Tm 3) (.var 1)
        identityLinearRules.computation :=
  ⟨substitution_represented numTy, substitution_decoded numTy, equality_reflection_fails.2⟩

/-! ## Profiles: J-free conversion, declared J, no global K, no univalence -/

/-- The identity profile types a path and does not reflect it. This is the
J-free conversion boundary. -/
theorem j_free_conversion_rejects_reflection :
    Labeled .typedTerm
      (Typing identityLinearRules IdentityEquality.Controls.pathContext (.var 0)
          (.id numT (.var 2) (.var 1)) ∧
        ¬ Conv identityLinearRules.headEq (.var 2 : Tower.Tm 3) (.var 1)
          identityLinearRules.computation) :=
  ⟨equality_reflection_fails⟩

/-- Two distinct paths are not convertible. Global K/UIP is not the conversion
of this profile. Scoped uniqueness stays a profile assumption, exercised by
the executable matrix. -/
theorem global_uip_is_not_conversion :
    Labeled .typedTerm
      (¬ Conv identityLinearRules.headEq (.var 0 : Tower.Tm 2) (.var 1)
        identityLinearRules.computation) :=
  ⟨fun conversion => by
      have same := identityConstructors.eq_of_normal
        (identityConstructors.normal_var 0) (identityConstructors.normal_var 1) conversion
      cases same⟩

/-- J at reflexivity, under a formed context and a typing of the eliminator
at a reflexivity path. The method is the result. This does not add K. -/
theorem j_at_reflexivity
    {n : Nat} {Γ : Tower.Ctx n}
    (formed : ContextFormation Preservation.linearHost.rules Γ)
    (σ : Sub Tower.Head 6 n) {displayed : Tower.Tm n}
    (observed : Typing Preservation.linearHost.rules Γ
      (subst σ (jApp (.var 5) (.var 4) (.var 3) (.var 2) (.var 1) (.refl (.var 0))))
      displayed) :
    Labeled .typedTerm (Typing Preservation.linearHost.rules Γ (σ 2) displayed) :=
  ⟨Preservation.linearHost.jLinear_preserves formed σ observed⟩

/-- Reflexivity at a variable function is not evidence for its eta expansion.
Univalence and function extensionality are not this conversion. -/
theorem univalence_is_not_identity_conversion :
    Labeled .typedTerm
      (¬ Typing identityLinearRules (.snoc .nil (.pi numT numT)) (.refl (.var 0))
        (.id (.pi numT numT) (.var 0) EtaConversion.expansion)) :=
  ⟨IdentityEquality.Controls.eta_not_typed⟩

/-- The identity schema is left-linear: a repeated pattern variable on the
right already occurs on the left. The draft's repeated point is the separated
iota rule used by `j_at_reflexivity`, not a second global principle. -/
theorem repeated_pattern_variables_stay_linear :
    Labeled .typedTerm (Presentation.AlgebraicSchema.LeftLinearFamily IdentitySchema) :=
  ⟨identitySchema_linear⟩

/-! ## Defect controls on the authored program and its emitted artifacts -/

theorem raw_input_unrelated_text :
    Labeled .rawInput (capturedTerm ≠ KTerm.declConst "(not-a-proof-term)") :=
  ⟨unrelated_marker_is_not_the_article⟩

theorem typed_term_wrong_index
    {n : Nat} {Γ : Tower.Ctx n} (count : Nat) :
    Labeled .typedTerm
      (¬ Typing Confluence.linearRules Γ CertifiedTransformProgram.Execution.holdsBase
        (holdsAtApp (CertifiedTransformProgram.Execution.numeral (count + 1)))) :=
  ⟨CertifiedTransformProgram.Controls.holdsBase_not_successor count⟩

theorem typed_term_malformed_substitution
    {n : Nat} {Γ : Tower.Ctx n}
    (formed : ContextFormation Confluence.linearRules Γ)
    {count step value evidence type : Tower.Tm n}
    (countTyped : Typing Confluence.linearRules Γ count numT) :
    Labeled .typedTerm
      (¬ Typing Confluence.linearRules Γ
        (iterApp count numT (.lam (.var 0)) step value evidence) type) :=
  ⟨CertifiedTransformProgram.Controls.iterCall_malformedFamily formed countTyped⟩

theorem typed_term_different_endpoints
    {n : Nat} {left right carrier point endpoint : Tower.Tm n} :
    Labeled .typedTerm
      (¬ Conv Confluence.linearRules.headEq
        (CertifiedTransformProgram.Controls.equation left right)
        (.id carrier point endpoint) Confluence.linearRules.computation) :=
  ⟨fun conversion =>
      CertifiedTransformProgram.Controls.equation_not_identity conversion⟩

theorem typed_term_bad_certificate
    {n : Nat} {Γ : Tower.Ctx n}
    (formed : ContextFormation Confluence.linearRules Γ) {type : Tower.Tm n} :
    Labeled .typedTerm
      (¬ Typing Confluence.linearRules Γ
        (iterApp (CertifiedTransformProgram.Execution.numeral 1) numT
          (.const eqAtName) (.const sucStepName) SetProfile.zeroNative SetProfile.zeroNative) type) :=
  ⟨CertifiedTransformProgram.Controls.iterCall_numberAsEvidence formed⟩

theorem ordinary_execution_capture :
    Labeled .ordinaryExecution
      (CertifiedTransformProgram.Execution.Runs
        (.app (.app (.lam (.lam (.var 1))) (.var 1)) (.var 0) : Tower.Tm 2) (.var 1)) :=
  ⟨CertifiedTransformProgram.Controls.binding_control⟩

theorem proof_search_altered_equation :
    Labeled .proofSearch
      (¬ HOL.CoreConversion SetProfile.sourceEquations (Γ := [numTy])
        (SetProfile.addT SetProfile.zeroT (SetProfile.sucT (.var .vz)))
        (SetProfile.sucT (SetProfile.sucT
          (SetProfile.addT SetProfile.zeroT (.var .vz))))) :=
  ⟨SetProfile.Models.no_altered_article⟩

theorem proof_search_wrong_conclusion :
    Labeled .proofSearch
      (¬ Nonempty (HOL.ProofSyntaxModulo SetProfile.sourceEquations
        SetProfile.zeroAddAssumptions SetProfile.Models.wrongStatement)) :=
  ⟨SetProfile.Models.no_wrong_conclusion⟩

/-! ## Article, package, index, and support -/

theorem article_relates_text_package_index_and_support :
    capturedTerm.render = capturedTermText ∧
      (capturedTerm.toTmAt 0 = some SetProfile.zeroAddTerm ∧
        capturedType.toTmAt 0 =
          some (FormationSensitiveHOLGenericProofFamily.proof SetProfile.holdsName
            SetProfile.zeroAddCode)) ∧
      (zeroAddPublished publishedIndex0).realization =
        IdentityEquality.Realizations.inductionRealization ∧
      (∀ entry ∈ capturedContext, ∃ type, entry.2.toTmAt 0 = some type ∧
        SetProfile.targetRules.constantType (.mkSimple entry.1) = some type) :=
  ⟨capturedTerm_text, article_renders_as_admitted_package, rfl, capturedContext_types⟩

#print transportAt
#print transportShape
#print substDecodedAt
#print substitution
#print axioms admitted_subst_at_num
#print axioms admitted_decoding_is_not_transport
#print axioms identity_valued_typing_is_not_discharged
#print axioms linked_open_index_derivation
#print axioms linked_statement_extends
#print axioms function_carrier_consumption
#print axioms power_congruence_is_one_statement
#check linked_exists
#print axioms equality_reflection_fails
#print axioms open_reflexivity_is_not_the_linked_evidence
#print axioms article_renders_as_admitted_package
#print axioms unrelated_marker_is_not_the_article
#print axioms j_at
#print axioms eta_not_separating
#print axioms linked_exists
#print axioms zeroAdd_linked_typed
#print axioms linkedZeroAdd_open
#print axioms IdentityEquality.Controls.refl_not_eqAt_open
#print axioms IdentityEquality.Controls.not_reflection
#print axioms substRealizationAt_typed
#print axioms eta_identifies
#print axioms capturedTerm_erases
#check admitted_subst_at_num
#check admitted_decoding_is_not_transport
#check context_extension_commutes
#check substitution_commutes
#check type_specialization_commutes
#check function_specialization_commutes
#check conversion_evidence_commutes
#check assumptions_commute
#check linked_exists_keeps_compiles
#check induction_covers_num
#check induction_cannot_be_dropped
#check revised_support_withdraws_zero_add
#check universe_closure_stays_an_assumption
#check power_congruence_is_not_the_universe_step
#check three_readings_stay_separate
#check j_free_conversion_rejects_reflection
#check global_uip_is_not_conversion
#check j_at_reflexivity
#check univalence_is_not_identity_conversion
#check repeated_pattern_variables_stay_linear
#check raw_input_unrelated_text
#check typed_term_wrong_index
#check typed_term_malformed_substitution
#check typed_term_different_endpoints
#check typed_term_bad_certificate
#check ordinary_execution_capture
#check proof_search_altered_equation
#check proof_search_wrong_conclusion
#check article_relates_text_package_index_and_support
#check HOTGConsumer.hotgStep_typed
#check HOTGConsumer.singletonUniverse
#check SetProfile.Models.zeroAdd_holds
#print axioms context_extension_commutes
#print axioms substitution_commutes
#print axioms type_specialization_commutes
#print axioms function_specialization_commutes
#print axioms conversion_evidence_commutes
#print axioms assumptions_commute
#print axioms linked_exists_keeps_compiles
#print axioms induction_covers_num
#print axioms induction_cannot_be_dropped
#print axioms revised_support_withdraws_zero_add
#print axioms vocabulary_declaration_is_not_the_proof_support
#print axioms universe_closure_stays_an_assumption
#print axioms power_congruence_is_not_the_universe_step
#print axioms three_readings_stay_separate
#print axioms j_free_conversion_rejects_reflection
#print axioms global_uip_is_not_conversion
#print axioms j_at_reflexivity
#print axioms univalence_is_not_identity_conversion
#print axioms repeated_pattern_variables_stay_linear
#print axioms raw_input_unrelated_text
#print axioms typed_term_wrong_index
#print axioms typed_term_malformed_substitution
#print axioms typed_term_different_endpoints
#print axioms typed_term_bad_certificate
#print axioms ordinary_execution_capture
#print axioms proof_search_altered_equation
#print axioms proof_search_wrong_conclusion
#print axioms article_relates_text_package_index_and_support
#print axioms HOTGConsumer.hotgStep_typed
#print axioms HOTGConsumer.closure_needed
#print axioms SetProfile.Models.zeroAdd_holds
#print axioms SetProfile.Models.induction_needed
#print axioms SetProfile.Models.no_wrong_conclusion
#print axioms IdentityEquality.Controls.not_reflection
#print axioms IdentityEquality.Controls.refl_not_eqAt_open

/-! Milestone-4 bridge results, imported. These commands print the existing
theorems. They do not re-prove them. `rfl` on a compiler equation is the
compiler's own check, recorded here with its hypotheses. -/

#check substRealizationAt_decoded
#print axioms substRealizationAt_decoded
#check zeroAdd_links
#print axioms zeroAdd_links
#check functions_links
#print axioms functions_links
#check sets_links
#print axioms sets_links
#check linkedSymmetry_runs
#print axioms linkedSymmetry_runs
#check linkedCongruence_decoded
#print axioms linkedCongruence_decoded
#check linkedCongruence_open
#print axioms linkedCongruence_open
#check linkedCongruence_runs
#print axioms linkedCongruence_runs
#check IdentityEquality.KernelSpelling.captured_links
#print axioms IdentityEquality.KernelSpelling.captured_links
#check IdentityEquality.KernelSpelling.capturedSymmetry_erases
#print axioms IdentityEquality.KernelSpelling.capturedSymmetry_erases
#check IdentityEquality.KernelSpelling.capturedSymmetry_links
#print axioms IdentityEquality.KernelSpelling.capturedSymmetry_links
#check IdentityEquality.KernelSpelling.capturedCongruence_erases
#print axioms IdentityEquality.KernelSpelling.capturedCongruence_erases
#check IdentityEquality.KernelSpelling.capturedCongruence_links
#print axioms IdentityEquality.KernelSpelling.capturedCongruence_links
#check libraryRulesCurrent_equations
#print axioms libraryRulesCurrent_equations
#check DraftComparison.stopped_unique
#print axioms DraftComparison.stopped_unique

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.Qualification
