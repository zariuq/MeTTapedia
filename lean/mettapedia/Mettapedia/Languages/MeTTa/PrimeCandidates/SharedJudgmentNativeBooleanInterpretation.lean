import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNativeBooleanNamedRegion
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNativeDecidableIdentity
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveQuotientInterpretation
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeQuotientInterpretationControls
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientIdentity

/-!
# Native Boolean regions in their actual formed quotient interpretation

The rules contain the genuine Boolean and native J computation roots. Their
formed-context quotient, rather than an opaque replacement signature, supplies
the interpretation. Retained motives are actual typed conversion classes.
Native J descends on its independently admitted input image and commutes with
typed substitution. The derived Boolean region and its retained named-context
application use this same interpretation.

The quotient construction does not itself establish normalization, confluence,
or unrestricted subject reduction of the complete computation extension. Those
are separate source-calculus properties, not premises smuggled into its graphs.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNativeBooleanInterpretation

open _root_.CategoryTheory
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation Presentation.Declaration Presentation.FormationSensitive RussellTarski
open NativeIndexedFamilies NativeIndexedFamilies.Intrinsic
open FormationSensitiveContextual

abbrev rules : Rules Tower.Head := SharedJudgmentNativeBooleanRegion.rules

theorem extension_rules :
    SharedJudgmentNativeIdentityExtension.rules (fun _ => SharedJudgmentNativeBooleanRegion.one)
      SharedJudgmentNativeBooleanRegion.signature = rules := rfl

theorem universes : UniverseRegularity rules :=
  (NativeIdentityLevelInstantiation.universes (fun _ => SharedJudgmentNativeBooleanRegion.one) Signature.empty).includeSignature SharedJudgmentNativeBooleanRegion.signature

noncomputable def model := QuotientCwf.cwf rules

/-! ## Actual admitted judgments and semantic classes -/

noncomputable def annotation {context : Context rules} {term type : Tower.Tm context.arity}
    (admitted : Judgment rules context.raw term type) : TypeOver context :=
  ⟨type, (admitted.regularity universes).choose,
    (admitted.regularity universes).choose_spec.1,
    (admitted.regularity universes).choose_spec.2.typing⟩

noncomputable def representative {context : Context rules} {term type : Tower.Tm context.arity}
    (admitted : Judgment rules context.raw term type) : Term context (annotation admitted) :=
  ⟨term, admitted.typing⟩

noncomputable def classOf {context : Context rules} {term type : Tower.Tm context.arity}
    (admitted : Judgment rules context.raw term type) : QTerm context :=
  QTerm.mk (representative admitted)

theorem classOf_eq_iff {context : Context rules}
    {first firstType second secondType : Tower.Tm context.arity}
    (firstAdmitted : Judgment rules context.raw first firstType)
    (secondAdmitted : Judgment rules context.raw second secondType) :
    classOf firstAdmitted = classOf secondAdmitted ↔
      Conv rules.headEq firstType secondType rules.computation ∧
        Conv rules.headEq first second rules.computation :=
  QTerm.mk_eq_iff (representative firstAdmitted) (representative secondAdmitted)

theorem classOf_substitution {source target : Context rules}
    {term type : Tower.Tm target.arity}
    (admitted : Judgment rules target.raw term type) (sigma : source ⟶ target) :
    QuotientCwf.totalSub (classOf admitted) (QuotientCwf.project sigma) =
      classOf (admitted.substitute source.formed sigma.typed) := by
  apply (QTerm.mk_eq_iff _ _).mpr
  exact ⟨.refl _, .refl _⟩

theorem admitted_iff_interpreted (context : Context rules) (term type : Tower.Tm context.arity) :
    Judgment rules context.raw term type ↔
      ∃ semanticType : QType context, QuotientInterpretation.TypeMeaning context type semanticType ∧
        ∃ value : TermFibre semanticType,
          QuotientInterpretation.TermMeaning context term type semanticType value :=
  QuotientInterpretation.admitted_iff_interpreted context universes term type

theorem judgment_meaning {context : Context rules} {term type : Tower.Tm context.arity}
    (admitted : Judgment rules context.raw term type) :
    QuotientInterpretation.TermMeaning context term type
      (QType.mk (annotation admitted)) (TermFibre.mk (representative admitted)) :=
  QuotientInterpretation.term_meaning context (representative admitted)

/-! ## Native J with the motive function retained -/

structure JInput (context : Context rules) where
  carrier : Tower.Tm context.arity
  left : Tower.Tm context.arity
  motive : Tower.Tm context.arity
  method : Tower.Tm context.arity
  right : Tower.Tm context.arity
  witness : Tower.Tm context.arity
  parameters : SharedJudgmentNativeIdentityExtension.Parameters (fun _ => SharedJudgmentNativeBooleanRegion.one) SharedJudgmentNativeBooleanRegion.signature context.raw carrier left motive method
  rightTyped : Typing rules context.raw right carrier
  witnessTyped : Typing rules context.raw witness (.id carrier left right)

def JInput.resultType {context : Context rules} (input : JInput context) : Tower.Tm context.arity :=
  .app (.app input.motive input.right) input.witness

def JInput.result {context : Context rules} (input : JInput context) : Tower.Tm context.arity :=
  identityEliminateApp input.carrier input.left input.motive input.method input.right input.witness

theorem JInput.point_typed {context : Context rules} (input : JInput context) :
    FormationSensitive.CtxMor rules
      (FormationSensitiveBasedIdentity.basedContext context.raw input.carrier input.left) context.raw
      (FormationSensitiveBasedIdentity.pointSub input.right input.witness) := by
  have identity := identityTyped (rules := rules) context.raw
  have point : Typing rules context.raw input.right (subst ids input.carrier) := by
    simpa only [subst_ids] using input.rightTyped
  refine (identity.extend point).extend ?_
  simpa only [subst, subst_consSub_rename_wk, subst_ids, consSub_zero] using input.witnessTyped

theorem JInput.judgment {context : Context rules} (input : JInput context) :
    Judgment rules context.raw input.result input.resultType := by
  simpa only [extension_rules, JInput.result, JInput.resultType,
    FormationSensitiveBasedIdentity.pointSub_genericTerm,
    FormationSensitiveBasedIdentity.pointSub_motiveBody] using
      (SharedJudgmentNativeIdentityExtension.generic_judgment input.parameters).substitute context.formed input.point_typed

def JInput.reindex {source target : Context rules} (input : JInput target)
    (sigma : source ⟶ target) : JInput source where
  carrier := subst sigma.substitution input.carrier
  left := subst sigma.substitution input.left
  motive := subst sigma.substitution input.motive
  method := subst sigma.substitution input.method
  right := subst sigma.substitution input.right
  witness := subst sigma.substitution input.witness
  parameters := by
    refine ⟨source.formed, ?_⟩
    rw [extension_rules]
    have composed := compositionTyped sigma.typed input.parameters.2
    convert composed using 1
    funext index
    fin_cases index <;> rfl
  rightTyped := input.rightTyped.substitute sigma.typed
  witnessTyped := input.witnessTyped.substitute sigma.typed

@[simp] theorem JInput.reindex_result {source target : Context rules} (input : JInput target)
    (sigma : source ⟶ target) :
    (input.reindex sigma).result = subst sigma.substitution input.result := rfl

@[simp] theorem JInput.reindex_resultType {source target : Context rules} (input : JInput target)
    (sigma : source ⟶ target) :
    (input.reindex sigma).resultType = subst sigma.substitution input.resultType := rfl

structure JObservation (context : Context rules) where
  carrier : QTerm context
  left : QTerm context
  motive : QTerm context
  method : QTerm context
  right : QTerm context
  witness : QTerm context

@[ext] theorem JObservation.ext {context : Context rules} {first second : JObservation context}
    (carrier : first.carrier = second.carrier) (left : first.left = second.left)
    (motive : first.motive = second.motive) (method : first.method = second.method)
    (right : first.right = second.right) (witness : first.witness = second.witness) : first = second := by
  cases first; cases second
  cases carrier; cases left; cases motive; cases method; cases right; cases witness
  rfl

noncomputable def observeJ {context : Context rules} (input : JInput context) : JObservation context where
  carrier := classOf ⟨context.formed, input.parameters.2 3⟩
  left := classOf ⟨context.formed, input.parameters.2 2⟩
  motive := classOf ⟨context.formed, input.parameters.2 1⟩
  method := classOf ⟨context.formed, input.parameters.2 0⟩
  right := classOf ⟨context.formed, input.rightTyped⟩
  witness := classOf ⟨context.formed, input.witnessTyped⟩

def JObservation.reindex {source target : Context rules} (observation : JObservation target)
    (sigma : source ⟶ target) : JObservation source where
  carrier := observation.carrier.reindex sigma
  left := observation.left.reindex sigma
  motive := observation.motive.reindex sigma
  method := observation.method.reindex sigma
  right := observation.right.reindex sigma
  witness := observation.witness.reindex sigma

theorem observeJ_reindex {source target : Context rules} (input : JInput target)
    (sigma : source ⟶ target) : observeJ (input.reindex sigma) = (observeJ input).reindex sigma := by
  apply JObservation.ext <;> apply (QTerm.mk_eq_iff _ _).mpr <;> constructor
  all_goals try exact .refl _
  change Conv rules.headEq
    (subst (identitySchemaSubstitution (subst sigma.substitution input.carrier)
      (subst sigma.substitution input.left) (subst sigma.substitution input.motive)
      (subst sigma.substitution input.method))
      (Ctx.lookup (NativeIdentityLevelInstantiation.parametersContext
        (fun _ => SharedJudgmentNativeBooleanRegion.one)) 1))
    (subst sigma.substitution (subst (identitySchemaSubstitution input.carrier input.left
      input.motive input.method) (Ctx.lookup (NativeIdentityLevelInstantiation.parametersContext
        (fun _ => SharedJudgmentNativeBooleanRegion.one)) 1))) rules.computation
  rw [subst_subComp]
  have composed : identitySchemaSubstitution (subst sigma.substitution input.carrier)
      (subst sigma.substitution input.left) (subst sigma.substitution input.motive)
      (subst sigma.substitution input.method) =
      subComp sigma.substitution (identitySchemaSubstitution input.carrier input.left
        input.motive input.method) := by
    funext index
    fin_cases index <;> rfl
  rw [composed]
  exact .refl _

theorem observeJ_reindex_congruent {source target : Context rules} (input : JInput target)
    {first second : source ⟶ target} (same : homConversion rules first second) :
    observeJ (input.reindex first) = observeJ (input.reindex second) := by
  rw [observeJ_reindex, observeJ_reindex]
  apply JObservation.ext <;> dsimp only [JObservation.reindex] <;>
    exact QTerm.reindex_pointwise _ same

/-- The constructor meaning factors through retained typed classes. It does
not factor merely because two applied motive families happen to agree. -/
theorem retained_j_coherent {context : Context rules} (first second : JInput context)
    (same : observeJ first = observeJ second) : classOf first.judgment = classOf second.judgment := by
  have carrier := (classOf_eq_iff _ _).mp (congrArg JObservation.carrier same)
  have left := (classOf_eq_iff _ _).mp (congrArg JObservation.left same)
  have motive := (classOf_eq_iff _ _).mp (congrArg JObservation.motive same)
  have method := (classOf_eq_iff _ _).mp (congrArg JObservation.method same)
  have right := (classOf_eq_iff _ _).mp (congrArg JObservation.right same)
  have witness := (classOf_eq_iff _ _).mp (congrArg JObservation.witness same)
  apply (classOf_eq_iff _ _).mpr
  exact ⟨.congApp (.congApp motive.2 right.2) witness.2,
    .congApp (.congApp (.congApp (.congApp (.congApp (.congApp (.refl _) carrier.2)
      left.2) motive.2) method.2) right.2) witness.2⟩

def jSetoid (context : Context rules) : Setoid (JInput context) where
  r first second := observeJ first = observeJ second
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

def JRequest (context : Context rules) := Quotient (jSetoid context)
def requestOf {context : Context rules} (input : JInput context) : JRequest context := Quotient.mk _ input

noncomputable def runJ {context : Context rules} (request : JRequest context) : QTerm context :=
  Quotient.lift (fun input => classOf input.judgment) retained_j_coherent request

theorem runJ_native {context : Context rules} (input : JInput context) :
    runJ (requestOf input) = classOf input.judgment := rfl

theorem native_j_substitution {source target : Context rules} (input : JInput target)
    (sigma : source ⟶ target) :
    QuotientCwf.totalSub (runJ (requestOf input)) (QuotientCwf.project sigma) =
      runJ (requestOf (input.reindex sigma)) := by
  exact classOf_substitution input.judgment sigma

def reindexRequest {source target : Context rules} (request : JRequest target)
    (sigma : source ⟶ target) : JRequest source :=
  Quotient.map (fun input => input.reindex sigma) (by
    intro first second same
    change observeJ (first.reindex sigma) = observeJ (second.reindex sigma)
    rw [observeJ_reindex, observeJ_reindex]
    exact congrArg (fun observation => observation.reindex sigma) same) request

theorem reindexRequest_congruent {source target : Context rules} (request : JRequest target)
    {first second : source ⟶ target} (same : homConversion rules first second) :
    reindexRequest request first = reindexRequest request second := by
  induction request using Quotient.inductionOn with
  | h input => exact Quotient.sound (observeJ_reindex_congruent input same)

/-- Substitution uses the semantic arrow class; no preferred raw substitution
or original declaration spelling is imposed on the consumer. -/
def semanticReindex {source target : QuotientCwf.QContext rules} (request : JRequest target.as)
    (sigma : source ⟶ target) : JRequest source.as :=
  Quot.liftOn sigma (reindexRequest request) (by
    intro first second same
    exact reindexRequest_congruent request
      ((HomRel.compClosure_iff_self (homConversion rules) first second).mp same))

theorem semantic_j_substitution {source target : QuotientCwf.QContext rules}
    (request : JRequest target.as) (sigma : source ⟶ target) :
    QuotientCwf.totalSub (runJ request) sigma = runJ (semanticReindex request sigma) := by
  induction sigma using Quot.inductionOn with
  | h sigma =>
    induction request using Quotient.inductionOn with
    | h input => exact native_j_substitution input sigma

def JInput.atReflexivity {context : Context rules} (input : JInput context) : JInput context :=
  { input with
    right := input.left
    witness := .refl input.left
    rightTyped := SharedJudgmentNativeIdentityExtension.parameters_left input.parameters
    witnessTyped := .reflIntro (SharedJudgmentNativeIdentityExtension.parameters_left input.parameters) }

/-- Beta is the inherited native J root observed in the same quotient; the
Boolean signature is still computational, and no UIP conversion is added. -/
theorem semantic_j_beta {context : Context rules} (input : JInput context) :
    runJ (requestOf input.atReflexivity) = (observeJ input).method := by
  apply (classOf_eq_iff _ _).mpr
  refine ⟨.refl _, ?_⟩
  exact .rel _ _ (.root (SharedJudgmentNativeIdentityExtension.beta ..))

/-- Every semantic result is in its actual dependent term fibre. -/
noncomputable def resultType {context : Context rules} (request : JRequest context) : QType context :=
  (runJ request).type

noncomputable def resultValue {context : Context rules} (request : JRequest context) :
    TermFibre (resultType request) := ⟨runJ request, rfl⟩

theorem semantic_j_type_substitution {source target : QuotientCwf.QContext rules}
    (request : JRequest target.as) (sigma : source ⟶ target) :
    QuotientCwf.tySub (resultType request) sigma = resultType (semanticReindex request sigma) := by
  exact (QuotientCwf.totalSub_type (runJ request) sigma).symm.trans
    (congrArg QTerm.type (semantic_j_substitution request sigma))

def emptyContext : Context rules := ⟨0, .nil, .nil⟩

theorem closed_hedberg_judgment : Judgment rules (.nil : Tower.Ctx 0)
    SharedJudgmentNativeHedberg.hedbergClosed
    (SharedJudgmentNativeHedberg.hedbergClosedType SharedJudgmentNativeBooleanRegion.one) :=
  ⟨.nil, SharedJudgmentNativeHedberg.hedbergClosed_includeSignature
    SharedJudgmentNativeBooleanRegion.one Signature.empty SharedJudgmentNativeBooleanRegion.signature⟩

theorem closed_hedberg_meaning :
    ∃ semanticType : QType emptyContext,
      QuotientInterpretation.TypeMeaning emptyContext
        (SharedJudgmentNativeHedberg.hedbergClosedType SharedJudgmentNativeBooleanRegion.one) semanticType ∧
      ∃ value : TermFibre semanticType,
        QuotientInterpretation.TermMeaning emptyContext SharedJudgmentNativeHedberg.hedbergClosed
          (SharedJudgmentNativeHedberg.hedbergClosedType SharedJudgmentNativeBooleanRegion.one) semanticType value :=
  (admitted_iff_interpreted emptyContext _ _).mp closed_hedberg_judgment

theorem closed_boolean_region_meaning :
    ∃ semanticType : QType emptyContext,
      QuotientInterpretation.TypeMeaning emptyContext SharedJudgmentNativeBooleanConstancy.regionType semanticType ∧
      ∃ value : TermFibre semanticType,
        QuotientInterpretation.TermMeaning emptyContext SharedJudgmentNativeBooleanConstancy.region
          SharedJudgmentNativeBooleanConstancy.regionType semanticType value :=
  (admitted_iff_interpreted emptyContext _ _).mp SharedJudgmentNativeBooleanConstancy.closed_region_judgment

/-- This native motive actually computes with the new Boolean eliminator:
its value is Bool on the chosen constructor and the empty encoding on the
other constructor. It is not a motive borrowed from an opaque presentation. -/
def discriminatorInput {context : Context rules} (side : Bool)
    (right witness : Tower.Tm context.arity)
    (rightTyped : Typing rules context.raw right SharedJudgmentNativeBooleanRegion.boolTm)
    (witnessTyped : Typing rules context.raw witness
      (.id SharedJudgmentNativeBooleanRegion.boolTm (SharedJudgmentNativeBooleanRegion.point side) right)) :
    JInput context where
  carrier := SharedJudgmentNativeBooleanRegion.boolTm
  left := SharedJudgmentNativeBooleanRegion.point side
  motive := .lam (.lam (SharedJudgmentNativeBooleanRegion.codeRow side (.var 1)))
  method := SharedJudgmentNativeBooleanRegion.trueTm
  right := right
  witness := witness
  parameters := by
    apply SharedJudgmentNativeIdentityExtension.ofBody context.formed
      (SharedJudgmentNativeBooleanRegion.bool_typed_one context.raw)
      (SharedJudgmentNativeBooleanRegion.point_typed side context.raw)
      (SharedJudgmentNativeBooleanRegion.codeRow side (.var 1))
    · exact SharedJudgmentNativeBooleanRegion.codeRow_typed side (.var 1)
    · rw [SharedJudgmentNativeBooleanRegion.codeRow_subst]
      exact .conv (SharedJudgmentNativeBooleanRegion.true_typed context.raw)
        (SharedJudgmentNativeBooleanRegion.codeRow_typed side
          (SharedJudgmentNativeBooleanRegion.point_typed side context.raw))
        (.sort SharedJudgmentNativeBooleanRegion.one)
        (SharedJudgmentNativeBooleanRegion.codeRow_same side).symm
  rightTyped := rightTyped
  witnessTyped := witnessTyped

def closedDiscriminator : JInput emptyContext :=
  discriminatorInput false SharedJudgmentNativeBooleanRegion.falseTm
    (.refl SharedJudgmentNativeBooleanRegion.falseTm)
    (SharedJudgmentNativeBooleanRegion.false_typed .nil)
    (.reflIntro (SharedJudgmentNativeBooleanRegion.false_typed .nil))

theorem discriminator_beta_meaning :
    runJ (requestOf closedDiscriminator) =
      classOf (context := emptyContext)
        (show Judgment rules .nil SharedJudgmentNativeBooleanRegion.trueTm
          SharedJudgmentNativeBooleanRegion.boolTm from
            ⟨.nil, SharedJudgmentNativeBooleanRegion.true_typed .nil⟩) := by
  have first := semantic_j_beta closedDiscriminator
  apply first.trans
  apply (classOf_eq_iff _ _).mpr
  refine ⟨?_, .refl _⟩
  exact .trans _ _ _
    (NativeIdentityLevelInstantiation.abstract_motive_beta rules
      (SharedJudgmentNativeBooleanRegion.codeRow false (.var 1))
      SharedJudgmentNativeBooleanRegion.falseTm (.refl SharedJudgmentNativeBooleanRegion.falseTm))
    (SharedJudgmentNativeBooleanRegion.codeRow_same false)

/-! ## One derived Boolean region and its nonidentity named application -/

def sourceContext : Context rules := ⟨4, SharedJudgmentNativeBooleanNamedRegion.sourceContext, SharedJudgmentNativeBooleanNamedRegion.source_context_formed⟩
def targetContext : Context rules := ⟨5, SharedJudgmentNativeBooleanNamedRegion.extendedBinding.target, SharedJudgmentNativeBooleanNamedRegion.extended_context_formed⟩
def namedSubstitution : targetContext ⟶ sourceContext :=
  ⟨SharedJudgmentNativeBooleanNamedRegion.extendedBinding.substitution, SharedJudgmentNativeBooleanNamedRegion.extended_binding_typed⟩

noncomputable def regionClass : QTerm sourceContext := classOf SharedJudgmentNativeBooleanNamedRegion.derived_proof_typed

theorem derived_region_meaning :
    QuotientInterpretation.TermMeaning sourceContext SharedJudgmentNativeBooleanNamedRegion.derivedProof.term SharedJudgmentNativeBooleanNamedRegion.derivedProof.type
      (QType.mk (annotation SharedJudgmentNativeBooleanNamedRegion.derived_proof_typed))
      (TermFibre.mk (representative SharedJudgmentNativeBooleanNamedRegion.derived_proof_typed)) :=
  judgment_meaning SharedJudgmentNativeBooleanNamedRegion.derived_proof_typed

theorem named_application_commutes :
    QuotientCwf.totalSub regionClass (QuotientCwf.project namedSubstitution) =
      classOf (SharedJudgmentNativeBooleanNamedRegion.derived_proof_typed.substitute SharedJudgmentNativeBooleanNamedRegion.extended_context_formed SharedJudgmentNativeBooleanNamedRegion.extended_binding_typed) :=
  classOf_substitution SharedJudgmentNativeBooleanNamedRegion.derived_proof_typed namedSubstitution

open SharedJudgmentNativeBooleanRegion (boolTm bool_typed zero one)
open SharedJudgmentNativeBooleanNamedRegion (derivedProof derived_proof_typed extendedBinding
  extended_context_formed extended_binding_typed proofs bindings before afterWithdrawal
  view recover_original current_binding_resolves bindingVersion)
open SharedJudgmentNamedIdentityRegions (resolveApplication)
open Mettapedia.TypeTheory.NamedValueContexts
open Mettapedia.TypeTheory.RetainedPresentationViews

def booleanType : TypeOver sourceContext := ⟨boolTm, .sort zero, .sort zero, bool_typed _⟩
def leftTerm : Term sourceContext booleanType := ⟨.var (3 : Fin 4), .var (3 : Fin 4)⟩
def rightTerm : Term sourceContext booleanType := ⟨.var (2 : Fin 4), .var (2 : Fin 4)⟩
def pathType : TypeOver sourceContext := QuotientIdentity.nativeId booleanType leftTerm rightTerm
def firstPath : Term sourceContext pathType := ⟨.var (1 : Fin 4), .var (1 : Fin 4)⟩
def secondPath : Term sourceContext pathType := ⟨.var (0 : Fin 4), .var (0 : Fin 4)⟩

theorem path_type_is_semantic_identity : QType.mk pathType =
    QuotientIdentity.idTy (context := (quotientProjection rules).obj sourceContext)
      (QType.mk booleanType) (TermFibre.mk leftTerm) (TermFibre.mk rightTerm) :=
  (QuotientIdentity.idTy_mk booleanType leftTerm rightTerm).symm

/-- The region inhabits propositional identity between arbitrary Boolean
paths; this does not identify the paths in the conversion quotient. -/
theorem derived_region_has_identity_meaning : regionClass.type =
    QuotientIdentity.idTy (context := (quotientProjection rules).obj sourceContext)
      (QType.mk pathType) (TermFibre.mk firstPath) (TermFibre.mk secondPath) := by
  rw [QuotientIdentity.idTy_mk]
  apply (QType.mk_eq_iff _ _).mpr
  exact .refl _

noncomputable def regionIdentityValue :
    TermFibre (QuotientIdentity.idTy (context := (quotientProjection rules).obj sourceContext)
      (QType.mk pathType) (TermFibre.mk firstPath) (TermFibre.mk secondPath)) :=
  ⟨regionClass, derived_region_has_identity_meaning⟩

theorem named_substitution_meaning :
    QuotientInterpretation.SubstitutionMeaning sourceContext targetContext extendedBinding.substitution
      (QuotientCwf.project namedSubstitution) := ⟨extended_binding_typed, rfl⟩

theorem named_application_semantic :
    resolveApplication proofs bindings before view (.live "Boolean-region-parameters") =
      some (derivedProof.instantiate extendedBinding) ∧
    QuotientInterpretation.TermMeaning targetContext (derivedProof.instantiate extendedBinding).term
      (derivedProof.instantiate extendedBinding).type
      (QuotientCwf.tySub (QType.mk (annotation derived_proof_typed)) (QuotientCwf.project namedSubstitution))
      (QuotientCwf.tmSub (TermFibre.mk (representative derived_proof_typed))
        (QuotientCwf.project namedSubstitution)) :=
  ⟨SharedJudgmentNamedIdentityRegions.resolved_application_exact proofs bindings before view
    (.live "Boolean-region-parameters") derivedProof extendedBinding recover_original current_binding_resolves,
    QuotientInterpretation.term_substitution named_substitution_meaning derived_region_meaning⟩

theorem missing_live_binding_does_not_erase_meaning :
    recover proofs view = some derivedProof ∧
      resolveApplication proofs bindings afterWithdrawal view (.live "Boolean-region-parameters") = none ∧
      QuotientInterpretation.TermMeaning sourceContext derivedProof.term derivedProof.type
        (QType.mk (annotation derived_proof_typed)) (TermFibre.mk (representative derived_proof_typed)) :=
  ⟨recover_original,
    SharedJudgmentNativeBooleanNamedRegion.unavailable_binding_preserves_original_inspection.2.2,
    derived_region_meaning⟩

theorem retained_binding_has_same_semantic_application :
    resolveApplication proofs bindings afterWithdrawal view (.versioned bindingVersion) =
      some (derivedProof.instantiate extendedBinding) ∧
    QuotientInterpretation.TermMeaning targetContext (derivedProof.instantiate extendedBinding).term
      (derivedProof.instantiate extendedBinding).type
      (QuotientCwf.tySub (QType.mk (annotation derived_proof_typed)) (QuotientCwf.project namedSubstitution))
      (QuotientCwf.tmSub (TermFibre.mk (representative derived_proof_typed))
        (QuotientCwf.project namedSubstitution)) := by
  refine ⟨?_, named_application_semantic.2⟩
  apply SharedJudgmentNamedIdentityRegions.resolved_application_exact _ _ _ _ _ _ _ recover_original
  simp [resolve, bindings, Mettapedia.GSLT.LanguageDef.FiniteEnvironmentCompilation.writeSource]

def expandedOriginal : Tower.Tm 4 := .app (.lam (.var 0)) derivedProof.term

theorem original_type_formed : Typing rules sourceContext.raw derivedProof.type (sortTm zero) :=
  .idForm (.idForm (bool_typed _) (.sort zero) (.var (3 : Fin 4)) (.var (2 : Fin 4)))
    (.sort zero) (.var (1 : Fin 4)) (.var (0 : Fin 4))

theorem expanded_original_judgment : Judgment rules sourceContext.raw expandedOriginal derivedProof.type := by
  refine ⟨SharedJudgmentNativeBooleanNamedRegion.source_context_formed, ?_⟩
  have arrow : Typing rules sourceContext.raw
      (.pi derivedProof.type (rename wk derivedProof.type)) (sortTm (.max zero zero)) :=
    .piForm original_type_formed (.sort zero) original_type_formed.weaken (.sort zero) (.sorts zero zero)
  have identity : Typing rules sourceContext.raw (.lam (.var 0))
      (.pi derivedProof.type (rename wk derivedProof.type)) :=
    .lamIntro arrow (.sort (.max zero zero)) (.var 0)
  simpa only [expandedOriginal, inst0_rename_wk] using .appElim identity derived_proof_typed.typing

theorem expanded_original_same_semantics :
    classOf expanded_original_judgment = regionClass :=
  (classOf_eq_iff _ _).mpr ⟨.refl _, .rel _ _ (.betaPi _ _)⟩

theorem expanded_original_distinct_syntax : expandedOriginal ≠ derivedProof.term := by
  intro same
  have heads := congrArg (fun term => match term with | .app function _ => function | _ => term) same
  cases heads

/-- The semantic view legitimately forgets this beta expansion. An exact
original-recovery operation must still distinguish its retained source. -/
theorem equivalent_not_original :
    expandedOriginal ≠ derivedProof.term ∧ classOf expanded_original_judgment = regionClass :=
  ⟨expanded_original_distinct_syntax, expanded_original_same_semantics⟩

#print axioms universes
#print axioms admitted_iff_interpreted
#print axioms retained_j_coherent
#print axioms native_j_substitution
#print axioms semantic_j_substitution
#print axioms semantic_j_beta
#print axioms closed_hedberg_meaning
#print axioms closed_boolean_region_meaning
#print axioms discriminator_beta_meaning
#print axioms derived_region_meaning
#print axioms named_application_commutes
#print axioms derived_region_has_identity_meaning
#print axioms named_application_semantic
#print axioms missing_live_binding_does_not_erase_meaning
#print axioms retained_binding_has_same_semantic_application
#print axioms equivalent_not_original

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNativeBooleanInterpretation
