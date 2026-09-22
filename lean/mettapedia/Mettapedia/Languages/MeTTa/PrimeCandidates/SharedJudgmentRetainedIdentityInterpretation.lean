import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentTypeInterpretation
import Mettapedia.TypeTheory.ContextualRetainedIdentityOperations

/-!
# Native identity interpretation retaining the submitted motive function

The original based frame retains its endpoint/path family and method. This
companion additionally retains a typed semantic value for the actual motive
function in the original context. Independent meaning clauses bind both
observations to the same submitted native syntax. Scope admission contains
no proof of the desired J result.

Coverage includes every original admitted parameter tuple and every qualified
frame, not a chosen subset of motives or interpretations. The native consumers
retain the original source, annotation and typed-substitution premises. The
old total-operation profile is unchanged; restricting such an operation gives
meaning on a retained scope but supplies no scope-closure theorem.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentRetainedIdentityInterpretation

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation Presentation.FormationSensitive SharedJudgmentFragment
open Mettapedia.TypeTheory
open ContextualRetainedIdentityOperations (Input Run)
open SharedJudgmentTypeInterpretation (FrameOperations Operations)

universe u v w w'

variable {assembly : Assembly} {C : Cwf.{u, v, w, w'}}

/-- The actual declaration's motive-function annotation, including its
original universe parameters. It is not the applied family `P y q`. -/
def motiveAnnotation {n : Nat} (type left motive method : Tower.Tm n) : Tower.Tm n :=
  subst (NativeIndexedFamilies.Intrinsic.identitySchemaSubstitution type left motive method)
    (rename wk (rename wk NativeIndexedFamilies.Intrinsic.identityMotiveType))

theorem motive_judgment {n : Nat} {source : SharedJudgmentInterpretation.Context assembly n}
    {type left motive method : Tower.Tm n}
    (parameters : FormationSensitiveBasedIdentity.Parameters assembly.declarations
      source.raw type left motive method) :
    Judgment assembly.rules source motive (motiveAnnotation type left motive method) :=
  ⟨parameters.1, parameters.2 (1 : Fin 4)⟩

theorem motiveAnnotation_substitution {n m : Nat} (sigma : Sub Tower.Head n m)
    (type left motive method : Tower.Tm n) :
    subst sigma (motiveAnnotation type left motive method) =
      motiveAnnotation (subst sigma type) (subst sigma left)
        (subst sigma motive) (subst sigma method) := by
  have composite : subComp sigma
      (NativeIndexedFamilies.Intrinsic.identitySchemaSubstitution type left motive method) =
      NativeIndexedFamilies.Intrinsic.identitySchemaSubstitution
        (subst sigma type) (subst sigma left) (subst sigma motive) (subst sigma method) := by
    funext index
    fin_cases index <;> rfl
  simp only [motiveAnnotation, subst_subComp, composite]

/-- Raw retained data. The method remains in the old frame's original
context; there is no second method field and no result-meaning premise. -/
structure JFrame (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (operations : FrameOperations C) {n : Nat}
    (source : SharedJudgmentInterpretation.Context assembly n)
    (type left motive method : Tower.Tm n) where
  frame : SharedJudgmentTypeInterpretation.JFrame interpretation operations source type left motive method
  functionType : C.Ty (interpretation.ctx source)
  function : C.Tm (interpretation.ctx source) functionType

@[reducible] def JFrame.input {interpretation : SharedJudgmentInterpretation.Data assembly C}
    {operations : FrameOperations C} {n : Nat}
    {source : SharedJudgmentInterpretation.Context assembly n}
    {type left motive method : Tower.Tm n}
    (retained : JFrame interpretation operations source type left motive method) :
    Input operations.identity operations.reflSection where
  body := {
    context := interpretation.ctx source
    type := retained.frame.semanticType
    left := retained.frame.semanticLeft
    motive := retained.frame.motive
    base := retained.frame.base }
  functionType := retained.functionType
  function := retained.function

/-- The original eleven frame clauses and the independent type/value
meaning of the same submitted motive function. -/
structure JFrameMeaning (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (operations : FrameOperations C) {n : Nat}
    {source : SharedJudgmentInterpretation.Context assembly n}
    {type left motive method : Tower.Tm n}
    (retained : JFrame interpretation operations source type left motive method) : Prop where
  frameMeaning : SharedJudgmentTypeInterpretation.JFrameMeaning interpretation operations retained.frame
  functionTypeMeaning : interpretation.ty source (motiveAnnotation type left motive method)
    retained.functionType
  functionMeaning : interpretation.term source motive (motiveAnnotation type left motive method)
    retained.functionType retained.function

/-- Existence on every native tuple is separate from extending every
independently qualified old frame. Neither implication can replace the other. -/
def FrameCoverage (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (operations : FrameOperations C) : Prop :=
  SharedJudgmentTypeInterpretation.BasedMotiveCoverage interpretation operations ∧
    ∀ (n : Nat) (source : SharedJudgmentInterpretation.Context assembly n)
      (type left motive method : Tower.Tm n)
      (frame : SharedJudgmentTypeInterpretation.JFrame interpretation operations source type left motive method),
      FormationSensitiveBasedIdentity.Parameters assembly.declarations source.raw type left motive method →
      SharedJudgmentTypeInterpretation.JFrameMeaning interpretation operations frame →
        ∃ retained : JFrame interpretation operations source type left motive method,
          retained.frame = frame ∧ JFrameMeaning interpretation operations retained

theorem frameCoverage_of_admittedTotal
    (interpretation : SharedJudgmentInterpretation.Data assembly C) (operations : FrameOperations C)
    (coverage : SharedJudgmentTypeInterpretation.BasedMotiveCoverage interpretation operations)
    (total : SharedJudgmentInterpretation.AdmittedTotal interpretation) :
    FrameCoverage interpretation operations := by
  refine ⟨coverage, ?_⟩
  intro n source type left motive method frame parameters meaning
  obtain ⟨functionType, typeMeaning, function, functionMeaning⟩ :=
    total n source motive (motiveAnnotation type left motive method) (motive_judgment parameters)
  exact ⟨⟨frame, functionType, function⟩, rfl, ⟨meaning, typeMeaning, functionMeaning⟩⟩

theorem FrameCoverage.exists_frame
    {interpretation : SharedJudgmentInterpretation.Data assembly C} {operations : FrameOperations C}
    (coverage : FrameCoverage interpretation operations)
    {n : Nat} {source : SharedJudgmentInterpretation.Context assembly n}
    {type left motive method : Tower.Tm n}
    (parameters : FormationSensitiveBasedIdentity.Parameters assembly.declarations
      source.raw type left motive method) :
    ∃ retained : JFrame interpretation operations source type left motive method,
      JFrameMeaning interpretation operations retained := by
  obtain ⟨frame, meaning⟩ := coverage.1 n source type left motive method parameters
  obtain ⟨retained, _, retainedMeaning⟩ :=
    coverage.2 n source type left motive method frame parameters meaning
  exact ⟨retained, retainedMeaning⟩

/-- Every retained meaning of every required source belongs to the run's
scope. The proposed scope cannot choose just one semantic representative. -/
def ScopeCoverage (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (operations : FrameOperations C)
    (scope : Input operations.identity operations.reflSection → Prop) : Prop :=
  ∀ (n : Nat) (source : SharedJudgmentInterpretation.Context assembly n)
    (type left motive method : Tower.Tm n)
    (retained : JFrame interpretation operations source type left motive method),
    FormationSensitiveBasedIdentity.Parameters assembly.declarations source.raw type left motive method →
    JFrameMeaning interpretation operations retained → scope retained.input

def ConstructorMeaning (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (operations : FrameOperations C)
    (scope : Input operations.identity operations.reflSection → Prop) (run : Run scope) : Prop :=
  ∀ (n : Nat) (source : SharedJudgmentInterpretation.Context assembly n)
    (type left motive method : Tower.Tm n)
    (retained : JFrame interpretation operations source type left motive method),
    FormationSensitiveBasedIdentity.Parameters assembly.declarations source.raw type left motive method →
    JFrameMeaning interpretation operations retained →
    ∀ admitted : scope retained.input,
      interpretation.term retained.frame.context
        (FormationSensitiveBasedIdentity.genericTerm type left motive method)
        (FormationSensitiveBasedIdentity.motiveBody motive)
        (C.tySub retained.frame.motive retained.frame.comparison.forward)
        (C.tmSub (run retained.input admitted) retained.frame.comparison.forward)

def AdmittedBeta (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (operations : FrameOperations C)
    (scope : Input operations.identity operations.reflSection → Prop) (run : Run scope) : Prop :=
  ∀ (n : Nat) (source : SharedJudgmentInterpretation.Context assembly n)
    (type left motive method : Tower.Tm n)
    (retained : JFrame interpretation operations source type left motive method),
    FormationSensitiveBasedIdentity.Parameters assembly.declarations source.raw type left motive method →
    JFrameMeaning interpretation operations retained →
    ∀ admitted : scope retained.input,
      C.tmSub (run retained.input admitted) (operations.reflSection retained.frame.semanticLeft) =
        retained.frame.base

theorem admittedBeta_of_beta
    (interpretation : SharedJudgmentInterpretation.Data assembly C) (operations : FrameOperations C)
    (scope : Input operations.identity operations.reflSection → Prop) (run : Run scope)
    (beta : ContextualRetainedIdentityOperations.Beta run) :
    AdmittedBeta interpretation operations scope run := by
  intro n source type left motive method retained _ _ admitted
  exact beta retained.input admitted

/-- This is the old operation, not a new implementation. Forgetting the
function is possible in this direction without claiming converse exactness. -/
def fullRun (operations : Operations C)
    (scope : Input operations.frames.identity operations.frames.reflSection → Prop) : Run scope :=
  ContextualRetainedIdentityOperations.restrict ⟨operations.based.elimination, rfl⟩ scope

theorem full_induces_meaning
    (interpretation : SharedJudgmentInterpretation.Data assembly C) (operations : Operations C)
    (scope : Input operations.frames.identity operations.frames.reflSection → Prop)
    (meaning : SharedJudgmentTypeInterpretation.BasedJMeaning interpretation operations) :
    ConstructorMeaning interpretation operations.frames scope (fullRun operations scope) := by
  intro n source type left motive method retained parameters retainedMeaning _
  exact meaning n source type left motive method retained.frame parameters retainedMeaning.frameMeaning

theorem full_induces_beta
    (interpretation : SharedJudgmentInterpretation.Data assembly C) (operations : Operations C)
    (scope : Input operations.frames.identity operations.frames.reflSection → Prop)
    (beta : SharedJudgmentTypeInterpretation.AdmittedBasedBeta interpretation operations) :
    AdmittedBeta interpretation operations.frames scope (fullRun operations scope) := by
  intro n source type left motive method retained parameters meaning _
  exact beta n source type left motive method retained.frame parameters meaning.frameMeaning

/-- The retained function itself transports under every related native
substitution, with its actual dependent annotation and semantic value. -/
theorem function_meaning_substitution
    (interpretation : SharedJudgmentInterpretation.Data assembly C) (operations : FrameOperations C)
    (stable : SharedJudgmentInterpretation.SubstitutionStable interpretation)
    {n m : Nat} {source : SharedJudgmentInterpretation.Context assembly n}
    {target : SharedJudgmentInterpretation.Context assembly m}
    {type left motive method : Tower.Tm n}
    (parameters : FormationSensitiveBasedIdentity.Parameters assembly.declarations
      source.raw type left motive method)
    (retained : JFrame interpretation operations source type left motive method)
    (meaning : JFrameMeaning interpretation operations retained)
    (sigma : Sub Tower.Head n m)
    (semantic : C.Sub (interpretation.ctx target) (interpretation.ctx source))
    (formed : ContextFormation assembly.rules target.raw)
    (typed : FormationSensitive.CtxMor assembly.rules source target sigma)
    (substitutionMeaning : interpretation.sub source target sigma semantic) :
    interpretation.ty target
        (motiveAnnotation (subst sigma type) (subst sigma left) (subst sigma motive) (subst sigma method))
        (C.tySub retained.functionType semantic) ∧
      interpretation.term target (subst sigma motive)
        (motiveAnnotation (subst sigma type) (subst sigma left) (subst sigma motive) (subst sigma method))
        (C.tySub retained.functionType semantic) (C.tmSub retained.function semantic) := by
  have typeMeaning := stable.1 n m source target sigma semantic _ retained.functionType
    formed typed substitutionMeaning meaning.functionTypeMeaning
  have termMeaning := stable.2 n m source target sigma semantic _ _ _ retained.function
    formed typed (motive_judgment parameters) substitutionMeaning
    meaning.functionTypeMeaning meaning.functionMeaning
  simpa only [motiveAnnotation_substitution] using And.intro typeMeaning termMeaning

/-- The original arbitrary endpoint/path application consumer. Argument
recovery, frame coverage and actual point substitution supply the result;
the retained run never decodes or replaces the submitted native expression. -/
theorem native_j_application_meaning
    (interpretation : SharedJudgmentInterpretation.Data assembly C) (operations : FrameOperations C)
    (scope : Input operations.identity operations.reflSection → Prop) (run : Run scope)
    (opacity : OpaqueRelatorExtension.Opacity assembly.declarations)
    (coverage : FrameCoverage interpretation operations)
    (scopeCoverage : ScopeCoverage interpretation operations scope)
    (subTotal : SharedJudgmentInterpretation.AdmittedSubstitutionsTotal interpretation)
    (stable : SharedJudgmentInterpretation.SubstitutionStable interpretation)
    (constructor : ConstructorMeaning interpretation operations scope run)
    {n : Nat} {source : SharedJudgmentInterpretation.Context assembly n}
    {type left motive method right witness displayed : Tower.Tm n}
    (admitted : Judgment assembly.rules source
      (NativeIndexedFamilies.Intrinsic.identityEliminateApp type left motive method right witness) displayed) :
    ∃ (retained : JFrame interpretation operations source type left motive method)
      (inScope : scope retained.input)
      (semantic : C.Sub (interpretation.ctx source) (interpretation.ctx retained.frame.context)),
      JFrameMeaning interpretation operations retained ∧
      interpretation.sub retained.frame.context source
        (FormationSensitiveBasedIdentity.pointSub right witness) semantic ∧
      Judgment assembly.rules source
        (NativeIndexedFamilies.Intrinsic.identityEliminateApp type left motive method right witness)
        (.app (.app motive right) witness) ∧
      interpretation.ty source (.app (.app motive right) witness)
        (C.tySub retained.frame.motive (C.compS retained.frame.comparison.forward semantic)) ∧
      interpretation.term source
        (NativeIndexedFamilies.Intrinsic.identityEliminateApp type left motive method right witness)
        (.app (.app motive right) witness)
        (C.tySub retained.frame.motive (C.compS retained.frame.comparison.forward semantic))
        (C.tmSub (run retained.input inScope) (C.compS retained.frame.comparison.forward semantic)) := by
  obtain ⟨parameters, rightTyped, witnessTyped, _⟩ :=
    FormationSensitiveBasedIdentity.arguments_of_judgment opacity admitted
  obtain ⟨retained, meaning⟩ := coverage.exists_frame parameters
  have inScope := scopeCoverage n source type left motive method retained parameters meaning
  have pointTyped := FormationSensitiveBasedIdentity.pointSub_typed parameters rightTyped witnessTyped
  obtain ⟨semantic, subMeaning⟩ := subTotal (n + 2) n
    retained.frame.context source (FormationSensitiveBasedIdentity.pointSub right witness)
    parameters.1 pointTyped
  have typeMeaning := stable.1 (n + 2) n retained.frame.context source
    (FormationSensitiveBasedIdentity.pointSub right witness) semantic _ _
    parameters.1 pointTyped subMeaning meaning.frameMeaning.motiveMeaning
  have termMeaning := stable.2 (n + 2) n retained.frame.context source
    (FormationSensitiveBasedIdentity.pointSub right witness) semantic _ _ _ _
    parameters.1 pointTyped (FormationSensitiveBasedIdentity.generic_judgment parameters)
    subMeaning meaning.frameMeaning.motiveMeaning
    (constructor n source type left motive method retained parameters meaning inScope)
  simp only [FormationSensitiveBasedIdentity.pointSub_genericTerm,
    FormationSensitiveBasedIdentity.pointSub_motiveBody] at typeMeaning termMeaning
  rw [← C.tySub_comp] at typeMeaning
  exact ⟨retained, inScope, semantic, meaning, subMeaning,
    FormationSensitiveBasedIdentity.point_judgment parameters rightTyped witnessTyped, typeMeaning,
    SharedJudgmentTypeInterpretation.termMeaning_transport interpretation (C.tySub_comp _ _ _).symm
      (TypeOver.tmSub_comp_heq _ _ _).symm termMeaning⟩

theorem native_j_beta_meaning
    (interpretation : SharedJudgmentInterpretation.Data assembly C) (operations : FrameOperations C)
    (scope : Input operations.identity operations.reflSection → Prop) (run : Run scope)
    (stable : SharedJudgmentInterpretation.TermSubstitutionStable interpretation)
    (constructor : ConstructorMeaning interpretation operations scope run)
    (beta : AdmittedBeta interpretation operations scope run)
    {n : Nat} {source : SharedJudgmentInterpretation.Context assembly n}
    {type left motive method : Tower.Tm n}
    (parameters : FormationSensitiveBasedIdentity.Parameters assembly.declarations
      source.raw type left motive method)
    (retained : JFrame interpretation operations source type left motive method)
    (meaning : JFrameMeaning interpretation operations retained) (inScope : scope retained.input) :
    interpretation.term source
      (NativeIndexedFamilies.Intrinsic.identityEliminateApp type left motive method left (.refl left))
      (FormationSensitiveBasedIdentity.methodType left motive)
      (C.tySub retained.frame.motive (operations.reflSection retained.frame.semanticLeft))
      retained.frame.base := by
  have generic := constructor n source type left motive method retained parameters meaning inScope
  have substituted := stable (n + 2) n retained.frame.context source
    (FormationSensitiveBasedIdentity.reflexivitySub left) retained.frame.reflexivityMap
    (FormationSensitiveBasedIdentity.genericTerm type left motive method)
    (FormationSensitiveBasedIdentity.motiveBody motive)
    (C.tySub retained.frame.motive retained.frame.comparison.forward)
    (C.tmSub (run retained.input inScope) retained.frame.comparison.forward)
    parameters.1 (FormationSensitiveBasedIdentity.reflexivitySub_typed parameters)
    (FormationSensitiveBasedIdentity.generic_judgment parameters)
    meaning.frameMeaning.reflexivityMeaning meaning.frameMeaning.motiveMeaning generic
  simp only [FormationSensitiveBasedIdentity.reflexivitySub_genericTerm,
    FormationSensitiveBasedIdentity.reflexivitySub_motiveBody] at substituted
  have typesEqual :
      C.tySub (C.tySub retained.frame.motive retained.frame.comparison.forward) retained.frame.reflexivityMap =
      C.tySub retained.frame.motive (operations.reflSection retained.frame.semanticLeft) := by
    rw [← C.tySub_comp, meaning.frameMeaning.reflexivitySquare]
  have valuesEqual : HEq
      (C.tmSub (C.tmSub (run retained.input inScope) retained.frame.comparison.forward)
        retained.frame.reflexivityMap) retained.frame.base := by
    apply (TypeOver.tmSub_comp_heq _ _ _).symm.trans
    rw [meaning.frameMeaning.reflexivitySquare]
    exact heq_of_eq (beta n source type left motive method retained parameters meaning inScope)
  exact SharedJudgmentTypeInterpretation.termMeaning_transport interpretation
    typesEqual valuesEqual substituted

/-- The same arbitrary caller substitution preserves the redex, its actual
method, both independently admitted annotations, and their shared meaning. -/
theorem native_j_beta_substitution
    (interpretation : SharedJudgmentInterpretation.Data assembly C) (operations : FrameOperations C)
    (scope : Input operations.identity operations.reflSection → Prop) (run : Run scope)
    (stable : SharedJudgmentInterpretation.TermSubstitutionStable interpretation)
    (constructor : ConstructorMeaning interpretation operations scope run)
    (beta : AdmittedBeta interpretation operations scope run)
    {n m : Nat} {source : SharedJudgmentInterpretation.Context assembly n}
    {target : SharedJudgmentInterpretation.Context assembly m}
    {type left motive method : Tower.Tm n}
    (parameters : FormationSensitiveBasedIdentity.Parameters assembly.declarations
      source.raw type left motive method)
    (retained : JFrame interpretation operations source type left motive method)
    (meaning : JFrameMeaning interpretation operations retained) (inScope : scope retained.input)
    (sigma : Sub Tower.Head n m)
    (semantic : C.Sub (interpretation.ctx target) (interpretation.ctx source))
    (formed : ContextFormation assembly.rules target.raw)
    (typed : FormationSensitive.CtxMor assembly.rules source target sigma)
    (substitutionMeaning : interpretation.sub source target sigma semantic) :
    let redex := NativeIndexedFamilies.Intrinsic.identityEliminateApp
      type left motive method left (.refl left)
    let nativeType := FormationSensitiveBasedIdentity.methodType left motive
    let semanticType := C.tySub retained.frame.motive (operations.reflSection retained.frame.semanticLeft)
    Judgment assembly.rules target (subst sigma redex) (subst sigma nativeType) ∧
    Judgment assembly.rules target (subst sigma method) (subst sigma nativeType) ∧
    assembly.rules.computation.step (subst sigma redex) (subst sigma method) ∧
    interpretation.term target (subst sigma redex) (subst sigma nativeType)
      (C.tySub semanticType semantic) (C.tmSub retained.frame.base semantic) ∧
    interpretation.term target (subst sigma method) (subst sigma nativeType)
      (C.tySub semanticType semantic) (C.tmSub retained.frame.base semantic) := by
  dsimp only
  have redex := FormationSensitiveBasedIdentity.reflexivity_judgment parameters
  have result := FormationSensitiveBasedIdentity.method_judgment parameters
  refine ⟨redex.substitute formed typed, result.substitute formed typed, ?_, ?_, ?_⟩
  · simpa only [Assembly.rules, NativeIndexedFamilies.Intrinsic.subst_identityEliminateApp, subst] using
      FormationSensitiveBasedIdentity.authored_beta assembly.declarations
        (subst sigma type) (subst sigma left) (subst sigma motive) (subst sigma method)
  · exact stable n m source target sigma semantic _ _ _ retained.frame.base formed typed redex
      substitutionMeaning meaning.frameMeaning.methodTypeMeaning
      (native_j_beta_meaning interpretation operations scope run stable constructor beta
        parameters retained meaning inScope)
  · exact stable n m source target sigma semantic _ _ _ retained.frame.base formed typed result
      substitutionMeaning meaning.frameMeaning.methodTypeMeaning meaning.frameMeaning.methodMeaning

/-- Closure and output agreement along every independently admitted native
substitution and every related semantic arrow. Every method satisfying the
original heterogeneous transport premise remains quantified explicitly. -/
def AdmittedSubstitution (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (operations : FrameOperations C)
    (scope : Input operations.identity operations.reflSection → Prop) (run : Run scope)
    (reindexing : ContextualBasedIdentityOperations.Reindexing operations.identity) : Prop :=
  ∀ (n m : Nat) (source : SharedJudgmentInterpretation.Context assembly n)
    (target : SharedJudgmentInterpretation.Context assembly m)
    (type left motive method : Tower.Tm n)
    (retained : JFrame interpretation operations source type left motive method)
    (sigma : Sub Tower.Head n m)
    (semantic : C.Sub (interpretation.ctx target) (interpretation.ctx source)),
    FormationSensitiveBasedIdentity.Parameters assembly.declarations source.raw type left motive method →
    JFrameMeaning interpretation operations retained →
    ∀ inScope : scope retained.input,
      ContextFormation assembly.rules target.raw →
      FormationSensitive.CtxMor assembly.rules source target sigma →
      interpretation.sub source target sigma semantic →
        C.compS (reindexing.map semantic retained.frame.semanticLeft)
            (operations.reflSection (C.tmSub retained.frame.semanticLeft semantic)) =
          C.compS (operations.reflSection retained.frame.semanticLeft) semantic ∧
        ∀ reindexedBase : C.Tm (interpretation.ctx target)
            (C.tySub (C.tySub retained.frame.motive (reindexing.map semantic retained.frame.semanticLeft))
              (operations.reflSection (C.tmSub retained.frame.semanticLeft semantic))),
          HEq (C.tmSub retained.frame.base semantic) reindexedBase →
            ∃ reindexedInScope : scope (retained.input.reindexWithBase reindexing semantic reindexedBase),
              C.tmSub (run retained.input inScope) (reindexing.map semantic retained.frame.semanticLeft) =
                run (retained.input.reindexWithBase reindexing semantic reindexedBase) reindexedInScope

/-- The stronger neutral closure law supplies this admitted specialization.
This theorem does not infer that closure from the old total profile. -/
theorem admittedSubstitution_of_full
    (interpretation : SharedJudgmentInterpretation.Data assembly C) (operations : FrameOperations C)
    (scope : Input operations.identity operations.reflSection → Prop) (run : Run scope)
    (reindexing : ContextualBasedIdentityOperations.Reindexing operations.identity)
    (square : ContextualRetainedIdentityOperations.SectionSquare operations.reflSection reindexing)
    (stable : ContextualRetainedIdentityOperations.Substitution run reindexing) :
    AdmittedSubstitution interpretation operations scope run reindexing := by
  intro n m source target type left motive method retained sigma semantic _ _ inScope _ _ _
  exact ⟨square semantic retained.frame.semanticLeft,
    fun reindexedBase same => stable retained.input inScope (interpretation.ctx target)
      semantic reindexedBase same⟩

/-- On the same native-related semantic substitution, reindexing the J
value and then returning to reflexivity yields the transported actual method. -/
theorem admitted_j_reindex_beta
    (interpretation : SharedJudgmentInterpretation.Data assembly C) (operations : FrameOperations C)
    (scope : Input operations.identity operations.reflSection → Prop) (run : Run scope)
    (reindexing : ContextualBasedIdentityOperations.Reindexing operations.identity)
    (beta : AdmittedBeta interpretation operations scope run)
    (stable : AdmittedSubstitution interpretation operations scope run reindexing)
    {n m : Nat} {source : SharedJudgmentInterpretation.Context assembly n}
    {target : SharedJudgmentInterpretation.Context assembly m}
    {type left motive method : Tower.Tm n}
    (parameters : FormationSensitiveBasedIdentity.Parameters assembly.declarations
      source.raw type left motive method)
    (retained : JFrame interpretation operations source type left motive method)
    (meaning : JFrameMeaning interpretation operations retained) (inScope : scope retained.input)
    (sigma : Sub Tower.Head n m)
    (semantic : C.Sub (interpretation.ctx target) (interpretation.ctx source))
    (formed : ContextFormation assembly.rules target.raw)
    (typed : FormationSensitive.CtxMor assembly.rules source target sigma)
    (substitutionMeaning : interpretation.sub source target sigma semantic) :
    HEq (C.tmSub
      (C.tmSub (run retained.input inScope) (reindexing.map semantic retained.frame.semanticLeft))
        (operations.reflSection (C.tmSub retained.frame.semanticLeft semantic)))
      (C.tmSub retained.frame.base semantic) := by
  obtain ⟨square, _⟩ := stable n m source target type left motive method retained sigma semantic
    parameters meaning inScope formed typed substitutionMeaning
  apply (TypeOver.tmSub_comp_heq _ _ _).symm.trans
  rw [square]
  apply (TypeOver.tmSub_comp_heq _ _ _).trans
  rw [beta n source type left motive method retained parameters meaning inScope]

namespace Controls

/-- The full variable telescope already admits a motive function; its
endpoint and path arguments are not replaced by a constant family. -/
theorem variable_motive_admitted :
    Judgment assembly.rules (SharedJudgmentTypeInterpretation.Controls.sourceContext assembly).raw
      (.var 1) (motiveAnnotation (.var 3) (.var 2) (.var 1) (.var 0)) :=
  motive_judgment (SharedJudgmentTypeInterpretation.Controls.parameters assembly)

theorem retained_function_weakening :
    subst SharedJudgmentTypeInterpretation.Controls.substitution (.var 1 : Tower.Tm 4) =
      (.var 2 : Tower.Tm 5) ∧
    subst SharedJudgmentTypeInterpretation.Controls.substitution (.var 1 : Tower.Tm 4) ≠
      (.var 0 : Tower.Tm 5) := ⟨rfl, by decide⟩

/-- Empty raw meaning relations cannot pass the existence part of retained
coverage. This is a negative raw-data control, not a model. -/
theorem empty_raw_not_covered (context : C.Ctx) (operations : FrameOperations C) :
    ¬ FrameCoverage (SharedJudgmentInterpretation.emptyRaw assembly C context) operations := by
  intro coverage
  obtain ⟨frame, meaning⟩ := coverage.1 4
    (SharedJudgmentTypeInterpretation.Controls.sourceContext assembly) _ _ _ _
    (SharedJudgmentTypeInterpretation.Controls.parameters assembly)
  exact meaning.typeMeaning.elim

end Controls

#print axioms frameCoverage_of_admittedTotal
#print axioms full_induces_meaning
#print axioms full_induces_beta
#print axioms function_meaning_substitution
#print axioms native_j_application_meaning
#print axioms native_j_beta_meaning
#print axioms native_j_beta_substitution
#print axioms admittedSubstitution_of_full
#print axioms admitted_j_reindex_beta
#print axioms Controls.empty_raw_not_covered

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentRetainedIdentityInterpretation
