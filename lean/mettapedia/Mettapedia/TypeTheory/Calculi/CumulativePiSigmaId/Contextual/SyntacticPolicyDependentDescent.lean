import Mettapedia.GSLT.Core.PolicyFamilyDependentDescent
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Contextual.SyntacticJudgmentalIdentityEliminator
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveDependentComputation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.DependentComputation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeIdentity

/-!
# Substitution and admitted dependent fibres of syntactic policy views

The existing syntactic context category retains both the raw code of a
formed type and its chosen universe level. The code-only subfamily forgets
that level, yet supports the actual dependent fibre of raw typed terms and
every typed context substitution. These facts are derived from the existing
substitution operations, not supplied as an assumed preservation interface.

Raw `HasType` and formation-sensitive judgments remain distinct. Refined
values below use their own existing judgment and require refined typed
substitutions; only the established forward erasure is used. Native identity
computations retain their authored iota evidence rather than identifying
their endpoint codes. No K, UIP or evaluation strategy is selected.
-/

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace SyntacticPolicyDependentDescent

open _root_.CategoryTheory SyntacticContextual
open Mettapedia.GSLT.Core
open Mettapedia.GSLT.Core.PolicyFamily
open Mettapedia.TypeTheory.DependentFamilyObserverFactorization

variable {Head : Type} {rules : Rules Head}

/-! ## One heterogeneous family and its code-only restriction -/

inductive TypePolicy where
  | code
  | level
  deriving DecidableEq

/-- The two retained data fields have different result types. -/
def typeFamily (context : FormedContext rules) : PolicyFamily (TypeOver context) where
  Policy := TypePolicy
  Result
    | .code => Tm Head context.arity
    | .level => Head
  decide
    | .code => TypeOver.code
    | .level => TypeOver.level

def codeSelection (_ : Unit) : TypePolicy := .code

/-- This subrequest does not ask for the chosen formation level. -/
def codeFamily (context : FormedContext rules) : PolicyFamily (TypeOver context) :=
  (typeFamily context).reindex codeSelection

/-- Actual typed substitution is closed on both coordinates: code is
substituted capture-avoidantly, while the chosen level is unchanged. -/
def typeSubstitutionWitness {source target : FormedContext rules}
    (morphism : source ⟶ target) :
    OperationReindex (typeFamily target) (typeFamily source)
      (fun type => type.reindex morphism) where
  select := id
  mapResult
    | .code => subst morphism.substitution
    | .level => id
  agrees := by
    intro policy type
    cases policy <;> rfl

/-- The code subrequest is actually closed, so restriction preserves
substitution support. The generic restriction construction retains its square. -/
def codeSubstitutionWitness {source target : FormedContext rules}
    (morphism : source ⟶ target) :
    OperationReindex (codeFamily target) (codeFamily source)
      (fun type => type.reindex morphism) :=
  (typeSubstitutionWitness morphism).reindex
    codeSelection codeSelection id (fun _ => rfl)

theorem substitution_preserves_code_equivalence
    {source target : FormedContext rules} (morphism : source ⟶ target)
    {first second : TypeOver target}
    (same : (codeFamily target).PolicyEquivalent first second) :
    (codeFamily source).PolicyEquivalent
      (first.reindex morphism) (second.reindex morphism) :=
  (codeSubstitutionWitness morphism).preserves_policyEquivalent same

/-- Identity and composition hold on arbitrary policy vectors, including
vectors not asserted to represent a formed type. -/
theorem typeVectorMap_id (context : FormedContext rules) :
    (typeSubstitutionWitness (𝟙 context)).vectorMap = id := by
  funext values policy
  cases policy with
  | code => exact subst_ids (values .code)
  | level => rfl

theorem typeVectorMap_comp {source middle target : FormedContext rules}
    (earlier : source ⟶ middle) (later : middle ⟶ target) :
    (typeSubstitutionWitness (earlier ≫ later)).vectorMap =
      (typeSubstitutionWitness earlier).vectorMap ∘
        (typeSubstitutionWitness later).vectorMap := by
  funext values policy
  cases policy with
  | code => exact (subst_subComp earlier.substitution later.substitution (values .code)).symm
  | level => rfl

theorem codeClassMap_id (context : FormedContext rules) :
    (codeSubstitutionWitness (𝟙 context)).classMap = id := by
  funext observed
  induction observed using Quotient.inductionOn with
  | _ type =>
      exact congrArg (codeFamily context).toObservationClass (TypeOver.reindex_id type)

theorem codeClassMap_comp {source middle target : FormedContext rules}
    (earlier : source ⟶ middle) (later : middle ⟶ target) :
    (codeSubstitutionWitness (earlier ≫ later)).classMap =
      (codeSubstitutionWitness earlier).classMap ∘
        (codeSubstitutionWitness later).classMap := by
  funext observed
  induction observed using Quotient.inductionOn with
  | _ type =>
      exact congrArg (codeFamily source).toObservationClass
        (TypeOver.reindex_comp type earlier later)

/-- Forgetting the level commutes with the same typed substitution on
compatible observational classes. -/
theorem codeRestriction_substitution_square
    {source target : FormedContext rules} (morphism : source ⟶ target) :
    (codeSubstitutionWitness morphism).classMap ∘
        (OperationReindex.restriction (typeFamily target) codeSelection).classMap =
      (OperationReindex.restriction (typeFamily source) codeSelection).classMap ∘
        (typeSubstitutionWitness morphism).classMap :=
  (typeSubstitutionWitness morphism).classMap_reindex
    codeSelection codeSelection id (fun _ => rfl)

theorem typeFamily_jointlySeparating (context : FormedContext rules) :
    (typeFamily context).observationFamily.JointlySeparating := by
  intro first second same
  exact TypeOver.ext (congrFun same .code) (congrFun same .level)

/-! ## The admitted raw term fibre and its actual substitution -/

/-- Raw typed syntax at an observed type code, without a selected level. -/
def CodeTerm (context : FormedContext rules) (code : Tm Head context.arity) :=
  { term : Tm Head context.arity // HasType rules context.context term code }

/-- Forgetting the formation level changes neither the term code nor its
actual raw typing judgment. -/
def termCodeEquiv {context : FormedContext rules} (type : TypeOver context) :
    Term context type ≃ CodeTerm context type.code where
  toFun term := ⟨term.code, term.typed⟩
  invFun term := ⟨term.val, term.property⟩
  left_inv term := by cases term; rfl
  right_inv term := by cases term; rfl

/-- An object-language dependent consumer of the code view. -/
def termVectorFactorization (context : FormedContext rules) :
    FamilyFactorization (codeFamily context).vector (Term context) where
  targetFamily values := CodeTerm context (values ())
  identify := termCodeEquiv

def termClassFactorization (context : FormedContext rules) :
    FamilyFactorization (codeFamily context).toObservationClass (Term context) :=
  factorizationOnClasses (termVectorFactorization context)

/-- Substitute the descended raw term using the same existing typing
substitution theorem as `Term.reindex`. -/
def codeTermSubstitute {source target : FormedContext rules}
    (morphism : source ⟶ target) {code : Tm Head target.arity}
    (term : CodeTerm target code) :
    CodeTerm source (subst morphism.substitution code) :=
  ⟨subst morphism.substitution term.val, term.property.substitute morphism.typed⟩

theorem termCodeEquiv_reindex {source target : FormedContext rules}
    (morphism : source ⟶ target) {type : TypeOver target} (term : Term target type) :
    termCodeEquiv (type.reindex morphism) (term.reindex morphism) =
      codeTermSubstitute morphism (termCodeEquiv type term) := rfl

theorem codeTermSubstitute_id {context : FormedContext rules}
    {code : Tm Head context.arity} (term : CodeTerm context code) :
    HEq (codeTermSubstitute (𝟙 context) term) term := by
  apply (Subtype.heq_iff_coe_eq (fun value => ?_)).2 (subst_ids term.val)
  change HasType rules context.context value (subst ids code) ↔
    HasType rules context.context value code
  rw [subst_ids]

/-- Equality of codes is the dependent substitution coherence, without any
identification of object-language conversion with host equality. -/
theorem codeTermSubstitute_comp {source middle target : FormedContext rules}
    (earlier : source ⟶ middle) (later : middle ⟶ target)
    {code : Tm Head target.arity} (term : CodeTerm target code) :
    HEq (codeTermSubstitute (earlier ≫ later) term)
      (codeTermSubstitute earlier (codeTermSubstitute later term)) := by
  have codeEq := (subst_subComp earlier.substitution later.substitution code).symm
  have termEq := (subst_subComp earlier.substitution later.substitution term.val).symm
  apply (Subtype.heq_iff_coe_eq (fun value => ?_)).2 termEq
  change HasType rules source.context value
      (subst (subComp earlier.substitution later.substitution) code) ↔ _
  rw [codeEq]

/-- The generic operation/descent theorem now concerns actual object
substitution and the actual reindexed term fibre. -/
def termSubstitutionFactorization {source target : FormedContext rules}
    (morphism : source ⟶ target) :
    FamilyFactorization (codeFamily target).vector
      (fun type => Term source (type.reindex morphism)) :=
  (codeSubstitutionWitness morphism).reindexFactorization
    (termVectorFactorization source)

/-- Read the requested type code directly from its compatible class. -/
def classTypeCode (context : FormedContext rules)
    (observed : (codeFamily context).ObservationClass) : Tm Head context.arity :=
  (codeFamily context).observationClassRealization.run () observed

theorem classTypeCode_substitution {source target : FormedContext rules}
    (morphism : source ⟶ target) (observed : (codeFamily target).ObservationClass) :
    classTypeCode source ((codeSubstitutionWitness morphism).classMap observed) =
      subst morphism.substitution (classTypeCode target observed) := by
  induction observed using Quotient.inductionOn with
  | _ type => rfl

/-- Actual substitution runs on descended term fibres without choosing a
representative type or recovering its forgotten formation level. -/
def classTermSubstitute {source target : FormedContext rules}
    (morphism : source ⟶ target) (observed : (codeFamily target).ObservationClass)
    (term : (termClassFactorization target).targetFamily observed) :
    (termClassFactorization source).targetFamily
      ((codeSubstitutionWitness morphism).classMap observed) := by
  refine ⟨subst morphism.substitution term.val, ?_⟩
  change HasType rules source.context (subst morphism.substitution term.val)
    (classTypeCode source ((codeSubstitutionWitness morphism).classMap observed))
  rw [classTypeCode_substitution]
  exact term.property.substitute morphism.typed

theorem classTermSubstitute_identify {source target : FormedContext rules}
    (morphism : source ⟶ target) {type : TypeOver target} (term : Term target type) :
    classTermSubstitute morphism ((codeFamily target).toObservationClass type)
        ((termClassFactorization target).identify type term) =
      (termClassFactorization source).identify (type.reindex morphism)
        (term.reindex morphism) := by
  apply Subtype.ext
  rfl

theorem classTermSubstitute_id {context : FormedContext rules}
    (observed : (codeFamily context).ObservationClass)
    (term : (termClassFactorization context).targetFamily observed) :
    HEq (classTermSubstitute (𝟙 context) observed term) term := by
  apply (Subtype.heq_iff_coe_eq (fun code => ?_)).2 (subst_ids term.val)
  change HasType rules context.context code
      (classTypeCode context ((codeSubstitutionWitness (𝟙 context)).classMap observed)) ↔ _
  rw [classTypeCode_substitution]
  change HasType rules context.context code (subst ids (classTypeCode context observed)) ↔ _
  rw [subst_ids]
  rfl

theorem classTermSubstitute_comp {source middle target : FormedContext rules}
    (earlier : source ⟶ middle) (later : middle ⟶ target)
    (observed : (codeFamily target).ObservationClass)
    (term : (termClassFactorization target).targetFamily observed) :
    HEq (classTermSubstitute (earlier ≫ later) observed term)
      (classTermSubstitute earlier ((codeSubstitutionWitness later).classMap observed)
        (classTermSubstitute later observed term)) := by
  apply (Subtype.heq_iff_coe_eq (fun code => ?_)).2
    (subst_subComp earlier.substitution later.substitution term.val).symm
  change HasType rules source.context code
      (classTypeCode source ((codeSubstitutionWitness (earlier ≫ later)).classMap observed)) ↔
    HasType rules source.context code
      (classTypeCode source ((codeSubstitutionWitness earlier).classMap
        ((codeSubstitutionWitness later).classMap observed)))
  rw [classTypeCode_substitution, classTypeCode_substitution, classTypeCode_substitution]
  change HasType rules source.context code
      (subst (subComp earlier.substitution later.substitution) (classTypeCode target observed)) ↔ _
  rw [← subst_subComp]

/-! ## Independently admitted formation-sensitive values -/

open FormationSensitive.DependentComputation

/-- A refined dependent value family is admitted to the same code view.
Its members carry the existing refined judgment, not merely raw typing. -/
def refinedValueVectorFactorization (context : FormedContext rules) :
    FamilyFactorization (codeFamily context).vector
      (fun type => TypedValue rules context.context type.code) :=
  FamilyFactorization.pullback (codeFamily context).vector
    (fun values => TypedValue rules context.context (values ()))

/-- Refined admission erases in the proved direction to the raw CwF fibre.
There is no converse conversion from raw typing to refined admission. -/
def refinedValueToTerm {context : FormedContext rules} {type : TypeOver context}
    (value : TypedValue rules context.context type.code) : Term context type :=
  ⟨value.val, value.property.toRaw⟩

theorem refinedValueToTerm_substitute {source target : FormedContext rules}
    (morphism : source ⟶ target)
    (formed : FormationSensitive.ContextFormation rules source.context)
    (typed : FormationSensitive.CtxMor rules target.context source.context
      morphism.substitution)
    {type : TypeOver target} (value : TypedValue rules target.context type.code) :
    refinedValueToTerm (type := type.reindex morphism)
        (TypedValue.substitute formed typed value) =
      (refinedValueToTerm (type := type) value).reindex morphism := rfl

/-- The existing refined component typings prove that the same categorical
composite is a refined typed substitution. -/
theorem refinedSubstitution_comp {source middle target : FormedContext rules}
    (earlier : source ⟶ middle) (later : middle ⟶ target)
    (earlierTyped : FormationSensitive.CtxMor rules middle.context source.context
      earlier.substitution)
    (laterTyped : FormationSensitive.CtxMor rules target.context middle.context
      later.substitution) :
    FormationSensitive.CtxMor rules target.context source.context
      (earlier ≫ later).substitution := by
  intro index
  change FormationSensitive.Typing rules source.context
    (subst earlier.substitution (later.substitution index))
    (subst (subComp earlier.substitution later.substitution) (Ctx.lookup target.context index))
  rw [← subst_subComp]
  exact (laterTyped index).substitute earlierTyped

theorem refinedValueSubstitute_comp {source middle target : FormedContext rules}
    (earlier : source ⟶ middle) (later : middle ⟶ target)
    (sourceFormed : FormationSensitive.ContextFormation rules source.context)
    (middleFormed : FormationSensitive.ContextFormation rules middle.context)
    (earlierTyped : FormationSensitive.CtxMor rules middle.context source.context
      earlier.substitution)
    (laterTyped : FormationSensitive.CtxMor rules target.context middle.context
      later.substitution)
    {code : Tm Head target.arity} (value : TypedValue rules target.context code) :
    HEq
      (TypedValue.substitute sourceFormed
        (refinedSubstitution_comp earlier later earlierTyped laterTyped) value)
      (TypedValue.substitute sourceFormed earlierTyped
        (TypedValue.substitute middleFormed laterTyped value)) := by
  apply (Subtype.heq_iff_coe_eq (fun term => ?_)).2
    (subst_subComp earlier.substitution later.substitution value.val).symm
  change FormationSensitive.Judgment rules source.context term
      (subst (subComp earlier.substitution later.substitution) code) ↔ _
  rw [← subst_subComp]

/-- The admitted refined family after the actual substitution. The
substitution of its values additionally uses refined component typings. -/
def refinedValueSubstitutionFactorization {source target : FormedContext rules}
    (morphism : source ⟶ target) :
    FamilyFactorization (codeFamily target).vector
      (fun type => TypedValue rules source.context (type.reindex morphism).code) :=
  (codeSubstitutionWitness morphism).reindexFactorization
    (refinedValueVectorFactorization source)

/-- Forward erasure of a refined formed telescope. -/
theorem rawContextFormation {n : Nat} {context : Ctx Head n}
    (formed : FormationSensitive.ContextFormation rules context) :
    Declaration.ContextWellFormed rules context := by
  induction formed with
  | nil => exact .nil
  | snoc _ typing universeWitness ih => exact .snoc ih typing.toRaw universeWitness

def formedContextOfRefined {n : Nat} (context : Ctx Head n)
    (formed : FormationSensitive.ContextFormation rules context) : FormedContext rules where
  arity := n
  context := context
  wellFormed := rawContextFormation formed

/-! ## Native J/iota remains a proof-relevant dependent consumer -/

open NativeIndexedFamilies
open SyntacticJudgmentalIdentityEliminator

/-- Native evidence over two descended raw endpoints. The rule witness is
retained even though the selected formation level is absent. -/
def CodeIota {nativeRules : Rules Tower.Head} (context : FormedContext nativeRules)
    (code : Tower.Tm context.arity) :=
  Σ source : CodeTerm context code, Σ target : CodeTerm context code,
    Intrinsic.IotaEvidence context.arity source.val target.val

def nativeCellObservation {context : FormedContext Intrinsic.rules}
    (cell : NativeIotaCell context) : CodeIota context cell.resultType.code :=
  ⟨termCodeEquiv cell.resultType cell.source,
    termCodeEquiv cell.resultType cell.target, cell.evidence⟩

def codeIotaSubstitute {nativeRules : Rules Tower.Head}
    {source target : FormedContext nativeRules} (morphism : source ⟶ target)
    {code : Tower.Tm target.arity} (cell : CodeIota target code) :
    CodeIota source (subst morphism.substitution code) :=
  ⟨codeTermSubstitute morphism cell.1, codeTermSubstitute morphism cell.2.1,
    cell.2.2.substitute morphism.substitution⟩

/-- The code view, the native evidence, and its judgmental embedding use
one and the same actual typed substitution. -/
theorem nativeCell_substitution_square
    {source target : FormedContext Intrinsic.rules}
    (morphism : source ⟶ target) (cell : NativeIotaCell target) :
    nativeCellObservation (cell.reindex morphism) =
        codeIotaSubstitute morphism (nativeCellObservation cell) ∧
      (cell.reindex morphism).toStep =
        cell.toStep.substitute morphism.substitution :=
  ⟨rfl, cell.toStep_reindex morphism⟩

theorem nativeCell_evidence_reindex_id {context : FormedContext Intrinsic.rules}
    (cell : NativeIotaCell context) :
    HEq (cell.reindex (𝟙 context)).evidence cell.evidence :=
  Intrinsic.proofRelevantIotaSubstitutionCoherent.substitute_ids cell.evidence

theorem nativeCell_evidence_reindex_comp
    {source middle target : FormedContext Intrinsic.rules}
    (earlier : source ⟶ middle) (later : middle ⟶ target)
    (cell : NativeIotaCell target) :
    HEq ((cell.reindex later).reindex earlier).evidence
      (cell.reindex (earlier ≫ later)).evidence :=
  Intrinsic.proofRelevantIotaSubstitutionCoherent.substitute_comp
    earlier.substitution later.substitution cell.evidence

/-- A real arity-changing substitution of the canonical J schema. -/
def weakenedIdentityCell :
    NativeIotaCell (extendContext formedIdentityContext identityIotaResult) :=
  identityIotaInstance (projectionHom formedIdentityContext identityIotaResult)

theorem weakened_identity_target :
    weakenedIdentityCell.target.code = (.var 1 : Tower.Tm 5) := rfl

theorem weakened_identity_endpoints_differ :
    weakenedIdentityCell.source.code ≠ weakenedIdentityCell.target.code := by decide

theorem weakened_identity_wrong_target :
    IsEmpty (Intrinsic.IotaEvidence 5 weakenedIdentityCell.source.code (.var 0)) := by
  constructor
  intro evidence
  cases evidence

/-! ## The same code family admits independently refined J instances -/

/-- These endpoints use the combined native package's existing refined
judgment. This is not an alias of the raw native-cell family. -/
def RefinedIota (context : FormedContext IntrinsicRelator.rules)
    (code : Tower.Tm context.arity) :=
  Σ source : TypedValue IntrinsicRelator.rules context.context code,
    Σ target : TypedValue IntrinsicRelator.rules context.context code,
      Intrinsic.IotaEvidence context.arity source.val target.val

def refinedIotaVectorFactorization (context : FormedContext IntrinsicRelator.rules) :
    FamilyFactorization (codeFamily context).vector
      (fun type => RefinedIota context type.code) :=
  FamilyFactorization.pullback (codeFamily context).vector
    (fun values => RefinedIota context (values ()))

def refinedIotaClassFactorization (context : FormedContext IntrinsicRelator.rules) :
    FamilyFactorization (codeFamily context).toObservationClass
      (fun type => RefinedIota context type.code) :=
  factorizationOnClasses (refinedIotaVectorFactorization context)

def refinedIotaSubstitute {source target : FormedContext IntrinsicRelator.rules}
    (morphism : source ⟶ target)
    (formed : FormationSensitive.ContextFormation IntrinsicRelator.rules source.context)
    (typed : FormationSensitive.CtxMor IntrinsicRelator.rules target.context source.context
      morphism.substitution)
    {code : Tower.Tm target.arity} (cell : RefinedIota target code) :
    RefinedIota source (subst morphism.substitution code) :=
  ⟨TypedValue.substitute formed typed cell.1,
    TypedValue.substitute formed typed cell.2.1,
    cell.2.2.substitute morphism.substitution⟩

/-- Refined endpoints and proof-relevant native evidence use the same
composite substitution; the evidence law is inherited from the authored iota
package, not from proof irrelevance of typing judgments. -/
theorem refinedIotaSubstitute_evidence_comp
    {source middle target : FormedContext IntrinsicRelator.rules}
    (earlier : source ⟶ middle) (later : middle ⟶ target)
    (sourceFormed : FormationSensitive.ContextFormation IntrinsicRelator.rules source.context)
    (middleFormed : FormationSensitive.ContextFormation IntrinsicRelator.rules middle.context)
    (earlierTyped : FormationSensitive.CtxMor IntrinsicRelator.rules
      middle.context source.context earlier.substitution)
    (laterTyped : FormationSensitive.CtxMor IntrinsicRelator.rules
      target.context middle.context later.substitution)
    {code : Tower.Tm target.arity} (cell : RefinedIota target code) :
    HEq
      (refinedIotaSubstitute (earlier ≫ later) sourceFormed
        (refinedSubstitution_comp earlier later earlierTyped laterTyped) cell).2.2
      (refinedIotaSubstitute earlier sourceFormed earlierTyped
        (refinedIotaSubstitute later middleFormed laterTyped cell)).2.2 :=
  (Intrinsic.proofRelevantIotaSubstitutionCoherent.substitute_comp
    earlier.substitution later.substitution cell.2.2).symm

def refinedIdentityContext : FormedContext IntrinsicRelator.rules :=
  formedContextOfRefined Intrinsic.contextAXPD
    FormationSensitiveNativeIdentity.contextAXPD_formed

theorem refinedIdentityResult_typing :
    FormationSensitive.Typing IntrinsicRelator.rules Intrinsic.contextAXPD
      Intrinsic.identityIotaResultType (sortTm Intrinsic.motiveLevel) := by
  have weakened := FormationSensitiveNativeIdentity.identityReflCaseType_hasType.weaken
    (extension := Intrinsic.identityReflCaseType)
  convert weakened using 1 <;> rfl

def refinedIdentityType : TypeOver refinedIdentityContext where
  code := Intrinsic.identityIotaResultType
  level := .sort Intrinsic.motiveLevel
  isUniverse := .sort Intrinsic.motiveLevel
  formed := refinedIdentityResult_typing.toRaw

def refinedIdentityCell : RefinedIota refinedIdentityContext refinedIdentityType.code :=
  ⟨⟨Intrinsic.identityIotaLeft, FormationSensitiveNativeIdentity.identityIota_judgments.1⟩,
    ⟨Intrinsic.identityIotaRight, FormationSensitiveNativeIdentity.identityIota_judgments.2⟩,
    Intrinsic.identityIotaReceipt.evidence⟩

/-- Instantiation calls the independently proved refined J theorem. -/
def refinedIdentityInstance {context : FormedContext IntrinsicRelator.rules}
    (morphism : context ⟶ refinedIdentityContext)
    (formed : FormationSensitive.ContextFormation IntrinsicRelator.rules context.context)
    (typed : FormationSensitive.CtxMor IntrinsicRelator.rules
      Intrinsic.contextAXPD context.context morphism.substitution) :
    RefinedIota context (refinedIdentityType.reindex morphism).code :=
  ⟨⟨subst morphism.substitution Intrinsic.identityIotaLeft,
      (FormationSensitiveNativeIdentity.identityIota_substitute formed typed).1⟩,
    ⟨subst morphism.substitution Intrinsic.identityIotaRight,
      (FormationSensitiveNativeIdentity.identityIota_substitute formed typed).2⟩,
    FormationSensitiveNativeIdentity.identityIota_substitutedEvidence morphism.substitution⟩

theorem refinedIdentityInstance_substitution_square
    {context : FormedContext IntrinsicRelator.rules}
    (morphism : context ⟶ refinedIdentityContext)
    (formed : FormationSensitive.ContextFormation IntrinsicRelator.rules context.context)
    (typed : FormationSensitive.CtxMor IntrinsicRelator.rules
      Intrinsic.contextAXPD context.context morphism.substitution) :
    refinedIdentityInstance morphism formed typed =
      refinedIotaSubstitute morphism formed typed refinedIdentityCell := rfl

/-- The admitted-family identification and refined J substitution commute
in the same code-view fibre. -/
theorem refinedIdentityInstance_descent_square
    {context : FormedContext IntrinsicRelator.rules}
    (morphism : context ⟶ refinedIdentityContext)
    (formed : FormationSensitive.ContextFormation IntrinsicRelator.rules context.context)
    (typed : FormationSensitive.CtxMor IntrinsicRelator.rules
      Intrinsic.contextAXPD context.context morphism.substitution) :
    (refinedIotaVectorFactorization context).identify (refinedIdentityType.reindex morphism)
        (refinedIdentityInstance morphism formed typed) =
      refinedIotaSubstitute morphism formed typed
        ((refinedIotaVectorFactorization refinedIdentityContext).identify
          refinedIdentityType refinedIdentityCell) := rfl

theorem refinedIdentityExtended_formed :
    FormationSensitive.ContextFormation IntrinsicRelator.rules
      (extendContext refinedIdentityContext refinedIdentityType).context :=
  .snoc FormationSensitiveNativeIdentity.contextAXPD_formed
    refinedIdentityResult_typing (.sort Intrinsic.motiveLevel)

theorem refinedIdentityProjection_typed :
    FormationSensitive.CtxMor IntrinsicRelator.rules Intrinsic.contextAXPD
      (extendContext refinedIdentityContext refinedIdentityType).context
      (projectionHom refinedIdentityContext refinedIdentityType).substitution := by
  intro index
  change FormationSensitive.Typing IntrinsicRelator.rules
    (.snoc Intrinsic.contextAXPD Intrinsic.identityIotaResultType) (.var index.succ)
      (subst projection (Ctx.lookup Intrinsic.contextAXPD index))
  rw [subst_projection]
  exact .var index.succ

def weakenedRefinedIdentity :
    RefinedIota (extendContext refinedIdentityContext refinedIdentityType)
      (refinedIdentityType.reindex
        (projectionHom refinedIdentityContext refinedIdentityType)).code :=
  refinedIdentityInstance (projectionHom refinedIdentityContext refinedIdentityType)
    refinedIdentityExtended_formed refinedIdentityProjection_typed

theorem weakened_refined_identity_control :
    weakenedRefinedIdentity.2.1.val = (.var 1 : Tower.Tm 5) ∧
      weakenedRefinedIdentity.1.val ≠ weakenedRefinedIdentity.2.1.val := by
  exact ⟨rfl, by decide⟩

/-! ## Loss and the unsupported retained-level consumer -/

/-- The actual J result code also forms one cumulative level higher. -/
def liftedIdentityType : TypeOver formedIdentityContext where
  code := identityIotaResult.code
  level := .sort (.succ Intrinsic.motiveLevel)
  isUniverse := .sort (.succ Intrinsic.motiveLevel)
  formed := .cumul identityIotaResult.formed (fun _ => Nat.le_succ _)

def liftedIdentityCell : NativeIotaCell formedIdentityContext where
  resultType := liftedIdentityType
  source := ⟨identityIotaCell.source.code, identityIotaCell.source.typed⟩
  target := ⟨identityIotaCell.target.code, identityIotaCell.target.typed⟩
  evidence := identityIotaCell.evidence

theorem identity_levels_differ : liftedIdentityType.level ≠ identityIotaResult.level := by
  decide

/-- Genuine loss, with the exact native J endpoints and authored evidence
still retained by the admitted consumer. -/
theorem code_view_forgets_level_but_retains_iota :
    liftedIdentityType ≠ identityIotaResult ∧
      (codeFamily formedIdentityContext).vector liftedIdentityType =
        (codeFamily formedIdentityContext).vector identityIotaResult ∧
      nativeCellObservation liftedIdentityCell = nativeCellObservation identityIotaCell :=
  ⟨fun same => identity_levels_differ (congrArg TypeOver.level same), rfl, rfl⟩

theorem codeFamily_not_jointlySeparating :
    ¬ (codeFamily formedIdentityContext).observationFamily.JointlySeparating := by
  intro separates
  exact code_view_forgets_level_but_retains_iota.1
    (separates code_view_forgets_level_but_retains_iota.2.1)

/-- A consumer requiring the retained formation level is a different,
genuinely dependent request from asking for raw terms at the type code. -/
def SelectedLevel {context : FormedContext rules} (level : Head) (type : TypeOver context) :=
  PLift (type.level = level)

def selectedLevelFullFactorization (context : FormedContext rules) (level : Head) :
    FamilyFactorization (typeFamily context).vector (SelectedLevel level) :=
  FamilyFactorization.pullback (typeFamily context).vector
    (fun values => PLift (values .level = level))

theorem selectedLevel_refuses_code_view :
    ¬ Nonempty (FamilyFactorization (codeFamily formedIdentityContext).vector
      (SelectedLevel identityIotaResult.level)) := by
  rintro ⟨factorization⟩
  have reflected := factorization.fibreEquiv
    (left := identityIotaResult) (right := liftedIdentityType) rfl
  exact identity_levels_differ (reflected ⟨rfl⟩).down

theorem selectedLevel_refuses_code_classes :
    ¬ Nonempty (FamilyFactorization (codeFamily formedIdentityContext).toObservationClass
      (SelectedLevel identityIotaResult.level)) := by
  rintro ⟨factorization⟩
  have same := (codeFamily formedIdentityContext).observationClass_eq_iff
    identityIotaResult liftedIdentityType |>.2 (fun _ => rfl)
  exact identity_levels_differ (factorization.fibreEquiv same ⟨rfl⟩).down

/-- Actual substitutions do not make the lost level recoverable. -/
theorem selectedLevel_refuses_code_view_after_substitution
    {context : FormedContext Intrinsic.rules} (morphism : context ⟶ formedIdentityContext) :
    ¬ Nonempty (FamilyFactorization (codeFamily context).vector
      (SelectedLevel identityIotaResult.level)) := by
  rintro ⟨factorization⟩
  have same : (codeFamily context).vector (identityIotaResult.reindex morphism) =
      (codeFamily context).vector (liftedIdentityType.reindex morphism) := rfl
  exact identity_levels_differ (factorization.fibreEquiv same ⟨rfl⟩).down

theorem scoped_dependent_descent_boundary :
    Nonempty (FamilyFactorization (codeFamily formedIdentityContext).vector
      (Term formedIdentityContext)) ∧
      Nonempty (FamilyFactorization (typeFamily formedIdentityContext).vector
        (SelectedLevel identityIotaResult.level)) ∧
      ¬ Nonempty (FamilyFactorization (codeFamily formedIdentityContext).vector
        (SelectedLevel identityIotaResult.level)) :=
  ⟨⟨termVectorFactorization formedIdentityContext⟩,
    ⟨selectedLevelFullFactorization formedIdentityContext identityIotaResult.level⟩,
    selectedLevel_refuses_code_view⟩

/-- One refined J substitution satisfies the code-stability, restriction,
raw/refined admitted-family and native descent-square obligations together.
All conjuncts concern the same source context, target context, policy family
and morphism. The retained-level counterexample above excludes universal
dependent descent; this result selects no identity or evaluation principle. -/
theorem substitution_admitted_descent_and_refinedJ
    {context : FormedContext IntrinsicRelator.rules}
    (morphism : context ⟶ refinedIdentityContext)
    (formed : FormationSensitive.ContextFormation IntrinsicRelator.rules context.context)
    (typed : FormationSensitive.CtxMor IntrinsicRelator.rules
      Intrinsic.contextAXPD context.context morphism.substitution) :
    (∀ first second : TypeOver refinedIdentityContext,
      (codeFamily refinedIdentityContext).PolicyEquivalent first second →
        (codeFamily context).PolicyEquivalent
          (first.reindex morphism) (second.reindex morphism)) ∧
    ((codeSubstitutionWitness morphism).classMap ∘
        (OperationReindex.restriction (typeFamily refinedIdentityContext) codeSelection).classMap =
      (OperationReindex.restriction (typeFamily context) codeSelection).classMap ∘
        (typeSubstitutionWitness morphism).classMap) ∧
    Nonempty (FamilyFactorization (codeFamily refinedIdentityContext).vector
      (fun type => Term context (type.reindex morphism))) ∧
    Nonempty (FamilyFactorization (codeFamily refinedIdentityContext).vector
      (fun type => TypedValue IntrinsicRelator.rules context.context
        (type.reindex morphism).code)) ∧
    ((refinedIotaVectorFactorization context).identify (refinedIdentityType.reindex morphism)
        (refinedIdentityInstance morphism formed typed) =
      refinedIotaSubstitute morphism formed typed
        ((refinedIotaVectorFactorization refinedIdentityContext).identify
          refinedIdentityType refinedIdentityCell)) :=
  ⟨fun _ _ same => substitution_preserves_code_equivalence morphism same,
    codeRestriction_substitution_square morphism,
    ⟨termSubstitutionFactorization morphism⟩,
    ⟨refinedValueSubstitutionFactorization morphism⟩,
    refinedIdentityInstance_descent_square morphism formed typed⟩

/-! ## Axiom audit -/

#print axioms codeSubstitutionWitness
#print axioms substitution_preserves_code_equivalence
#print axioms typeVectorMap_id
#print axioms typeVectorMap_comp
#print axioms codeClassMap_id
#print axioms codeClassMap_comp
#print axioms codeRestriction_substitution_square
#print axioms typeFamily_jointlySeparating
#print axioms termVectorFactorization
#print axioms termClassFactorization
#print axioms termCodeEquiv_reindex
#print axioms codeTermSubstitute_id
#print axioms codeTermSubstitute_comp
#print axioms termSubstitutionFactorization
#print axioms classTypeCode_substitution
#print axioms classTermSubstitute
#print axioms classTermSubstitute_identify
#print axioms classTermSubstitute_id
#print axioms classTermSubstitute_comp
#print axioms refinedValueVectorFactorization
#print axioms refinedValueToTerm_substitute
#print axioms refinedSubstitution_comp
#print axioms refinedValueSubstitute_comp
#print axioms nativeCell_substitution_square
#print axioms nativeCell_evidence_reindex_id
#print axioms nativeCell_evidence_reindex_comp
#print axioms weakened_identity_endpoints_differ
#print axioms weakened_identity_wrong_target
#print axioms refinedIotaClassFactorization
#print axioms refinedIotaSubstitute_evidence_comp
#print axioms refinedIdentityInstance
#print axioms refinedIdentityInstance_substitution_square
#print axioms refinedIdentityInstance_descent_square
#print axioms weakened_refined_identity_control
#print axioms code_view_forgets_level_but_retains_iota
#print axioms codeFamily_not_jointlySeparating
#print axioms selectedLevel_refuses_code_view
#print axioms selectedLevel_refuses_code_classes
#print axioms selectedLevel_refuses_code_view_after_substitution
#print axioms scoped_dependent_descent_boundary
#print axioms substitution_admitted_descent_and_refinedJ

end SyntacticPolicyDependentDescent
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
