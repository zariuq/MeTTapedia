import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.AuthoredConstantInference
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareTypedConversion
import Mettapedia.GSLT.LanguageDef.CalculusLanguageExtension
import Mettapedia.GSLT.LanguageDef.CanonicalPremiseClosure

open Mettapedia.GSLT.LanguageDef

/-!
# Finite inference facts generated from authored Prime equations

An authored equation has two distinct boundary roles.

* At a raw boundary, a finite proof may authenticate that an exact equation
  occurrence belongs to the admitted source document.
* Inside the native dependent calculus, a formed equation occurrence may
  construct typed conversion directly.

This module implements only the first role.  Every equation, including a
duplicate endpoint pair, receives a source position and an equation position.
The generated V2 rules are ground facts, and accepted raw proofs reflect to the
exact authored occurrence.  No typing or computation authority is inferred
from source membership.

The final negative theorem explains why this separation is necessary.  Prime
terms encode their own de Bruijn binders as ground `Pattern` data, so ordinary
checker-schema instantiation of the current exact codec cannot implement
object-level substitution.  A stronger native typed-construction bridge must
consume the authenticated occurrence instead of pretending that a ground fact
is an open conversion rule.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace AuthoredEquationInference

open AuthoredDeclarationSignature
open DeclarationAwarePatternCodec
open DeclarationAwareTypedConversion
open Mettapedia.GSLT.LanguageDef.CanonicalPremiseClosure
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CalculusLanguageExtension
open Mettapedia.GSLT.LanguageDef.KernelAuthority.Checker
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation.Declaration
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Exact equation positions in the complete source document -/

/-- A path to one equation in an ordered authored declaration list.  The path
retains constants and prior equations rather than quotienting the source to an
equation bag. -/
inductive SourceEquation :
    List SourceDeclaration -> EquationSchema -> Type where
  | here (schema : EquationSchema) (rest : List SourceDeclaration) :
      SourceEquation (.equation schema :: rest) schema
  | afterConstant (name : DeclName) (entry : Entry Tower.Head)
      {declarations : List SourceDeclaration} {schema : EquationSchema}
      (later : SourceEquation declarations schema) :
      SourceEquation (.constant name entry :: declarations) schema
  | afterEquation (prior : EquationSchema)
      {declarations : List SourceDeclaration} {schema : EquationSchema}
      (later : SourceEquation declarations schema) :
      SourceEquation (.equation prior :: declarations) schema

namespace SourceEquation

/-- Position in the complete authored declaration sequence. -/
def sourceIndex : {declarations : List SourceDeclaration} ->
    {schema : EquationSchema} -> SourceEquation declarations schema -> Nat
  | _, _, .here _ _ => 0
  | _, _, .afterConstant _ _ later => later.sourceIndex + 1
  | _, _, .afterEquation _ later => later.sourceIndex + 1

/-- Position in the equation-only projection used by
`EquationOccurrence`. -/
def equationIndex : {declarations : List SourceDeclaration} ->
    {schema : EquationSchema} -> SourceEquation declarations schema -> Nat
  | _, _, .here _ _ => 0
  | _, _, .afterConstant _ _ later => later.equationIndex
  | _, _, .afterEquation _ later => later.equationIndex + 1

theorem sourceIndex_lt : {declarations : List SourceDeclaration} ->
    {schema : EquationSchema} -> (occurrence : SourceEquation declarations schema) ->
    occurrence.sourceIndex < declarations.length
  | _, _, .here _ _ => by simp [sourceIndex]
  | _, _, .afterConstant _ _ later => by
      simpa [sourceIndex] using Nat.succ_lt_succ later.sourceIndex_lt
  | _, _, .afterEquation _ later => by
      simpa [sourceIndex] using Nat.succ_lt_succ later.sourceIndex_lt

theorem equationIndex_lt : {declarations : List SourceDeclaration} ->
    {schema : EquationSchema} -> (occurrence : SourceEquation declarations schema) ->
    occurrence.equationIndex < (equationSchemas declarations).length
  | _, _, .here _ _ => by simp [equationIndex, equationSchemas]
  | _, _, .afterConstant _ _ later => by
      simpa [equationIndex, equationSchemas] using later.equationIndex_lt
  | _, _, .afterEquation _ later => by
      simpa [equationIndex, equationSchemas] using
        Nat.succ_lt_succ later.equationIndex_lt

/-- Reading the full source position recovers the exact equation declaration. -/
theorem get_sourceIndex : {declarations : List SourceDeclaration} ->
    {schema : EquationSchema} -> (occurrence : SourceEquation declarations schema) ->
    declarations[occurrence.sourceIndex]'occurrence.sourceIndex_lt =
      .equation schema
  | _, _, .here _ _ => by simp [sourceIndex]
  | _, _, .afterConstant _ _ later => by
      simpa [sourceIndex] using later.get_sourceIndex
  | _, _, .afterEquation _ later => by
      simpa [sourceIndex] using later.get_sourceIndex

/-- Reading the filtered equation position recovers the same schema. -/
theorem get_equationIndex : {declarations : List SourceDeclaration} ->
    {schema : EquationSchema} -> (occurrence : SourceEquation declarations schema) ->
    (equationSchemas declarations).get
        ⟨occurrence.equationIndex, occurrence.equationIndex_lt⟩ = schema
  | _, _, .here _ _ => by simp [equationIndex, equationSchemas]
  | _, _, .afterConstant _ _ later => by
      simpa [equationIndex, equationSchemas] using later.get_equationIndex
  | _, _, .afterEquation _ later => by
      simpa [equationIndex, equationSchemas] using later.get_equationIndex

/-- The source path constructs the canonical identity-substitution occurrence
used by the proof-relevant equation computation. -/
def canonicalOccurrence : {declarations : List SourceDeclaration} ->
    {schema : EquationSchema} -> (occurrence : SourceEquation declarations schema) ->
    EquationOccurrence (equationSchemas declarations) schema.left schema.right
  | _, _, .here schema rest =>
      EquationOccurrence.canonical (schema :: equationSchemas rest) 0
  | _, _, .afterConstant _ _ later => later.canonicalOccurrence
  | _, _, .afterEquation prior later =>
      let tail := later.canonicalOccurrence
      { index := Fin.succ tail.index
        substitution := tail.substitution
        sourceEquation := tail.sourceEquation
        targetEquation := tail.targetEquation }

end SourceEquation

/-- One equation and its complete proof-relevant source path. -/
structure LocatedEquation (declarations : List SourceDeclaration) where
  schema : EquationSchema
  occurrence : SourceEquation declarations schema

def liftConstant (name : DeclName) (entry : Entry Tower.Head)
    {declarations : List SourceDeclaration}
    (located : LocatedEquation declarations) :
    LocatedEquation (.constant name entry :: declarations) where
  schema := located.schema
  occurrence := .afterConstant name entry located.occurrence

def liftPriorEquation (prior : EquationSchema)
    {declarations : List SourceDeclaration}
    (located : LocatedEquation declarations) :
    LocatedEquation (.equation prior :: declarations) where
  schema := located.schema
  occurrence := .afterEquation prior located.occurrence

/-- Executable proof-producing inventory of every authored equation. -/
def equationInventory :
    (declarations : List SourceDeclaration) -> List (LocatedEquation declarations)
  | [] => []
  | .constant name entry :: declarations =>
      (equationInventory declarations).map (liftConstant name entry)
  | .equation schema :: declarations =>
      { schema := schema
        occurrence := .here schema declarations } ::
      (equationInventory declarations).map (liftPriorEquation schema)

/-! ## Exact ground-fact wire -/

/-- Scope-coherent authored equation data.  Both the full source position and
the equation-only position are retained. -/
structure EquationClaim where
  sourceIndex : Nat
  equationIndex : Nat
  label : DeclName
  arity : Nat
  context : Tower.Ctx arity
  left : Tower.Tm arity
  right : Tower.Tm arity
  type : Tower.Tm arity

/-- Reassemble the exact authored schema represented by a claim. -/
def EquationClaim.schema (claim : EquationClaim) : EquationSchema where
  label := claim.label
  arity := claim.arity
  context := claim.context
  left := claim.left
  right := claim.right
  type := claim.type

def equationFactPattern (sourceIndex equationIndex label arity context left
    right type : Pattern) : Pattern :=
  .apply "prime-authored-equation"
    [sourceIndex, equationIndex, label, arity, context, left, right, type]

def encodeEquationClaim (claim : EquationClaim) : Pattern :=
  equationFactPattern (encodeNat claim.sourceIndex)
    (encodeNat claim.equationIndex) (encodeDeclName claim.label)
    (encodeNat claim.arity) (encodeCtx towerHeadCodec claim.context)
    (encodeTm towerHeadCodec claim.left)
    (encodeTm towerHeadCodec claim.right)
    (encodeTm towerHeadCodec claim.type)

def decodeEquationClaim? : Pattern -> Option EquationClaim
  | .apply "prime-authored-equation"
      [sourceIndex, equationIndex, label, arity, context, left, right, type] => do
      let n <- decodeNat? arity
      pure
        { sourceIndex := <- decodeNat? sourceIndex
          equationIndex := <- decodeNat? equationIndex
          label := <- decodeDeclName? label
          arity := n
          context := <- decodeCtx? towerHeadCodec n context
          left := <- decodeTm? towerHeadCodec n left
          right := <- decodeTm? towerHeadCodec n right
          type := <- decodeTm? towerHeadCodec n type }
  | _ => none

@[simp] theorem decodeEquationClaim?_encode (claim : EquationClaim) :
    decodeEquationClaim? (encodeEquationClaim claim) = some claim := by
  cases claim
  simp [encodeEquationClaim, equationFactPattern, decodeEquationClaim?]

def equationClaimCodec : PartialCodec EquationClaim Pattern where
  encode := encodeEquationClaim
  decode := decodeEquationClaim?
  decode_encode := decodeEquationClaim?_encode

theorem encodeEquationClaim_ground (claim : EquationClaim) :
    (encodeEquationClaim claim).isGroundAt 0 = true := by
  cases claim with
  | mk sourceIndex equationIndex label arity context left right type =>
      simp [encodeEquationClaim, equationFactPattern, Pattern.isGroundAt,
        Pattern.isGroundListAt, encodeNat_ground, encodeDeclName_ground,
        encodeCtx_ground towerHeadCodec encodeTowerHead_ground,
        encodeTm_ground towerHeadCodec encodeTowerHead_ground]

def LocatedEquation.claim {declarations : List SourceDeclaration}
    (located : LocatedEquation declarations) : EquationClaim where
  sourceIndex := located.occurrence.sourceIndex
  equationIndex := located.occurrence.equationIndex
  label := located.schema.label
  arity := located.schema.arity
  context := located.schema.context
  left := located.schema.left
  right := located.schema.right
  type := located.schema.type

/-- Semantic evidence for one fact keeps the complete source path.  The path
is indexed directly by the schema reassembled from the claim, avoiding any
proof-irrelevant endpoint cast. -/
structure EquationEvidence (declarations : List SourceDeclaration)
    (claim : EquationClaim) where
  occurrence : SourceEquation declarations claim.schema
  sourceIndex : occurrence.sourceIndex = claim.sourceIndex
  equationIndex : occurrence.equationIndex = claim.equationIndex

def LocatedEquation.evidence {declarations : List SourceDeclaration}
    (located : LocatedEquation declarations) :
    EquationEvidence declarations located.claim := by
  rcases located with ⟨schema, occurrence⟩
  rcases schema with ⟨label, arity, context, left, right, type⟩
  exact
    { occurrence := occurrence
      sourceIndex := rfl
      equationIndex := rfl }

/-- Recover the canonical proof-relevant equation occurrence from an exact
source fact. -/
def EquationEvidence.canonicalOccurrence
    {declarations : List SourceDeclaration} {claim : EquationClaim}
    (evidence : EquationEvidence declarations claim) :
    EquationOccurrence (equationSchemas declarations) claim.left
      claim.right :=
  evidence.occurrence.canonicalOccurrence

def EquationFactMeaning (declarations : List SourceDeclaration)
    (goal : Pattern) : Type :=
  UniversalFibre equationClaimCodec (EquationEvidence declarations) goal

/-! ## Generated facts -/

def generatedRuleId (ordinal : Nat) : RuleId :=
  { value := "prime-authored-equation." ++
      AuthoredConstantInference.unaryOrdinal ordinal }

theorem generatedRuleId_injective : Function.Injective generatedRuleId := by
  intro left right equality
  have lengthEquality := congrArg (fun ruleId => ruleId.value.length) equality
  simp [generatedRuleId, AuthoredConstantInference.unaryOrdinal_length]
    at lengthEquality
  omega

def generatedRule (ordinal : Nat) {declarations : List SourceDeclaration}
    (located : LocatedEquation declarations) : RuleSchema :=
  { id := generatedRuleId ordinal
    metavariables := []
    premises := []
    conclusion := encodeEquationClaim located.claim }

def generatedRules (declarations : List SourceDeclaration) : List RuleSchema :=
  (equationInventory declarations).zipIdx.map fun (located, ordinal) =>
    generatedRule ordinal located

theorem generatedRule_application_meaning
    {declarations : List SourceDeclaration}
    (ordinal : Nat) (located : LocatedEquation declarations)
    {presentation : ValidatedCalculusLanguageDef}
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {conclusion : Pattern}
    (lookup : presentation.1.lookupRule? ruleInstance.ruleId =
      some (generatedRule ordinal located))
    (application :
      RuleApplication presentation ruleInstance premises conclusion) :
    Nonempty (EquationFactMeaning declarations conclusion) := by
  cases application with
  | intro actualRule actualLookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
      have ruleEquality : actualRule = generatedRule ordinal located := by
        rw [actualLookup] at lookup
        exact Option.some.inj lookup
      subst actualRule
      have argumentsEmpty : ruleInstance.arguments = [] := by
        cases arguments : ruleInstance.arguments with
        | nil => rfl
        | cons argument arguments =>
            simp [generatedRule, argumentsValidAt, arguments] at argumentsValid
      rw [argumentsEmpty] at conclusionInstantiates
      have selfInstantiation :
          Instantiates [] [] (encodeEquationClaim located.claim)
            (encodeEquationClaim located.claim) :=
        instantiateSchemaAt?_sound
          (instantiateSchemaAt?_eq_self_of_ground [] [] 0
            (encodeEquationClaim located.claim)
            (encodeEquationClaim_ground located.claim))
      have conclusionEquality :
          conclusion = encodeEquationClaim located.claim :=
        conclusionInstantiates.functional selfInstantiation
      refine ⟨fun claim encoding => ?_⟩
      ·
        have claimEquality : claim = located.claim :=
          equationClaimCodec.encode_injective
            (encoding.trans conclusionEquality)
        subst claim
        exact located.evidence

theorem generated_rule_semantic_sound
    {declarations : List SourceDeclaration} {rule : RuleSchema}
    (member : rule ∈ generatedRules declarations)
    {presentation : ValidatedCalculusLanguageDef}
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {conclusion : Pattern}
    (lookup : presentation.1.lookupRule? ruleInstance.ruleId = some rule)
    (application :
      RuleApplication presentation ruleInstance premises conclusion) :
    Nonempty (EquationFactMeaning declarations conclusion) := by
  rcases List.mem_map.mp member with ⟨pair, pairMember, ruleEquality⟩
  rcases pair with ⟨located, ordinal⟩
  subst rule
  exact generatedRule_application_meaning ordinal located lookup application

/-! ## Executable admission and exact checked/source reflection -/

def equationFactDelta (source : SourceDocument) : CalculusLanguageExtension :=
  { newTerms := []
    newJudgments := [{ head := "prime-authored-equation", arity := 8 }]
    newRules := generatedRules (elaborate source) }

/-- Equation facts are layered over the already rooted typed-conversion
presentation.  They authenticate source membership but add no derivations to
the conversion judgment. -/
abbrev basePresentation : ValidatedCalculusLanguageDef :=
  typedConversionExtension.target

/-- Validate the generated source-fact delta through the ordinary V2
extension boundary. -/
def admit? (source : SourceDocument) :
    Option (ValidatedCalculusLanguageExtension basePresentation) :=
  let delta := equationFactDelta source
  if disjoint : delta.disjointFrom basePresentation.1 = true then
    if policy : delta.policyHolds basePresentation.1
        .newJudgmentsOnly = true then
      if valid : (delta.apply basePresentation.1).isValid = true then
        some
          { extension := delta
            policy := .newJudgmentsOnly
            disjoint := disjoint
            policyHolds := policy
            valid := valid }
      else
        none
    else
      none
  else
    none

structure AdmittedFacts (source : SourceDocument) where
  extension : ValidatedCalculusLanguageExtension basePresentation
  admission : admit? source = some extension

namespace AdmittedFacts

theorem extension_eq {source : SourceDocument}
    (admitted : AdmittedFacts source) :
    admitted.extension.extension = equationFactDelta source := by
  have admission := admitted.admission
  unfold admit? at admission
  dsimp only at admission
  by_cases disjoint :
      (equationFactDelta source).disjointFrom basePresentation.1 = true
  · rw [dif_pos disjoint] at admission
    by_cases policy :
        (equationFactDelta source).policyHolds basePresentation.1
          .newJudgmentsOnly = true
    · rw [dif_pos policy] at admission
      by_cases valid :
          ((equationFactDelta source).apply
            basePresentation.1).isValid = true
      · rw [dif_pos valid] at admission
        have equality := Option.some.inj admission
        exact (congrArg
          (fun extension : ValidatedCalculusLanguageExtension basePresentation =>
            extension.extension) equality).symm
      · rw [dif_neg valid] at admission
        contradiction
    · rw [dif_neg policy] at admission
      contradiction
  · rw [dif_neg disjoint] at admission
    contradiction

theorem policy_eq {source : SourceDocument}
    (admitted : AdmittedFacts source) :
    admitted.extension.policy = .newJudgmentsOnly := by
  have admission := admitted.admission
  unfold admit? at admission
  dsimp only at admission
  by_cases disjoint :
      (equationFactDelta source).disjointFrom basePresentation.1 = true
  · rw [dif_pos disjoint] at admission
    by_cases policy :
        (equationFactDelta source).policyHolds basePresentation.1
          .newJudgmentsOnly = true
    · rw [dif_pos policy] at admission
      by_cases valid :
          ((equationFactDelta source).apply
            basePresentation.1).isValid = true
      · rw [dif_pos valid] at admission
        have equality := Option.some.inj admission
        exact congrArg
          (fun extension : ValidatedCalculusLanguageExtension basePresentation =>
            extension.policy) equality.symm
      · rw [dif_neg valid] at admission
        contradiction
    · rw [dif_neg policy] at admission
      contradiction
  · rw [dif_neg disjoint] at admission
    contradiction

end AdmittedFacts

theorem base_equationFact_not_shaped (claim : EquationClaim) :
    basePresentation.1.hasJudgmentShape (encodeEquationClaim claim) = false := by
  rfl

def generatedRawProof (ordinal : Nat) : RawProof :=
  .node
    { ruleId := generatedRuleId ordinal
      arguments := [] }
    []

/-- Every admitted generated equation fact has a canonical one-node raw
artifact. -/
theorem admitted_generatedRule_raw_accepted
    {source : SourceDocument} (admitted : AdmittedFacts source)
    (ordinal : Nat) (located : LocatedEquation (elaborate source))
    (member : generatedRule ordinal located ∈
      generatedRules (elaborate source)) :
    checkRaw admitted.extension.target (encodeEquationClaim located.claim)
      (generatedRawProof ordinal) = true := by
  have targetMember :
      generatedRule ordinal located ∈ admitted.extension.target.1.rules := by
    change generatedRule ordinal located ∈
      basePresentation.1.rules ++ admitted.extension.extension.newRules
    apply List.mem_append_right basePresentation.1.rules
    rw [admitted.extension_eq]
    exact member
  have lookup :
      admitted.extension.target.1.lookupRule? (generatedRuleId ordinal) =
        some (generatedRule ordinal located) :=
    lookupRule?_eq_some_of_mem admitted.extension.target targetMember
  have application :
      RuleApplication admitted.extension.target
        { ruleId := generatedRuleId ordinal
          arguments := [] }
        [] (encodeEquationClaim located.claim) := by
    refine .intro (generatedRule ordinal located) lookup ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · exact .nil 0
    · exact instantiateSchemaAt?_sound
        (instantiateSchemaAt?_eq_self_of_ground [] [] 0
          (encodeEquationClaim located.claim)
          (encodeEquationClaim_ground located.claim))
  let derivation :
      Derivation admitted.extension.target
        (encodeEquationClaim located.claim) :=
    .byRule
      { ruleId := generatedRuleId ordinal
        arguments := [] }
      application .nil
  simpa [generatedRawProof, derivation, Derivation.erase,
    DerivationList.erase] using checkRaw_erase derivation

/-- Any accepted equation fact reflects to its exact source path and both
authored positions. -/
theorem checkRaw_reflects_equation_source
    {source : SourceDocument} (admitted : AdmittedFacts source)
    {claim : EquationClaim} {proof : RawProof}
    (accepted :
      checkRaw admitted.extension.target (encodeEquationClaim claim) proof =
        true) :
    Nonempty (EquationEvidence (elaborate source) claim) := by
  cases proof with
  | node ruleInstance children =>
      simp only [checkRaw] at accepted
      cases localResultEq :
          instantiateRule? admitted.extension.target ruleInstance with
      | none => simp [localResultEq] at accepted
      | some localResult =>
          rcases localResult with ⟨premises, conclusion⟩
          simp only [localResultEq, Bool.and_eq_true, decide_eq_true_eq]
            at accepted
          have application :
              RuleApplication admitted.extension.target ruleInstance
                premises conclusion :=
            instantiateRule?_eq_some_iff_application.mp localResultEq
          have conclusionEq : conclusion = encodeEquationClaim claim :=
            accepted.1
          subst conclusion
          rcases
              Mettapedia.GSLT.LanguageDef.InferenceSemanticExtension.SemanticExtension.target_application_classifies
                application with
            baseApplication | ⟨rule, member, lookup⟩
          · have shaped := baseApplication.conclusion_hasJudgmentShape
            rw [base_equationFact_not_shaped claim] at shaped
            contradiction
          · have generatedMember :
                rule ∈ generatedRules (elaborate source) := by
              simpa [admitted.extension_eq, equationFactDelta] using member
            rcases generated_rule_semantic_sound generatedMember lookup
                application with
              ⟨meaning⟩
            exact ⟨meaning claim rfl⟩

/-! ## Why direct ground-schema compilation is not substitution -/

private def openVariable : Tower.Tm 1 := .var 0

private def closeWithLegacy : Sub Tower.Head 1 0 :=
  fun _ => .head .legacyGround

/-- Object-language openness is represented inside the exact term codec; the
encoded value is nevertheless closed at the generic checker's schema level. -/
theorem encoded_open_variable_is_pattern_ground :
    (encodeTm towerHeadCodec openVariable).isGroundAt 0 = true :=
  encodeTm_ground towerHeadCodec encodeTowerHead_ground openVariable

/-- Instantiating that ground checker schema is the identity, whereas actual
Prime substitution changes the encoded term.  Therefore the current exact
codec must not be treated as an open inference schema compiler. -/
theorem ground_schema_instantiation_is_not_object_substitution :
    instantiateSchemaAt? [] [] 0 (encodeTm towerHeadCodec openVariable) =
        some (encodeTm towerHeadCodec openVariable) ∧
      encodeTm towerHeadCodec
          (Presentation.subst closeWithLegacy openVariable) ≠
        encodeTm towerHeadCodec openVariable := by
  constructor
  · exact instantiateSchemaAt?_eq_self_of_ground [] [] 0 _
      encoded_open_variable_is_pattern_ground
  · decide

/-! ## Positive and negative checked controls -/

private def duplicateSchema : EquationSchema where
  label := .anonymous
  arity := 0
  context := .nil
  left := .head .legacyGround
  right := .head .legacyGround
  type := .head (.sort Tower.zero)

private def interleavedEntry : Entry Tower.Head where
  type := .head (.sort Tower.zero)

private def exampleDeclarations : List SourceDeclaration :=
  [.equation duplicateSchema,
   .constant .anonymous interleavedEntry,
   .equation duplicateSchema]

private def exampleSource : SourceDocument :=
  sourceCodec.quote exampleDeclarations

private theorem example_elaborates :
    elaborate exampleSource = exampleDeclarations := by
  simp [exampleSource]

private def firstClaim : EquationClaim :=
  { sourceIndex := 0
    equationIndex := 0
    label := duplicateSchema.label
    arity := duplicateSchema.arity
    context := duplicateSchema.context
    left := duplicateSchema.left
    right := duplicateSchema.right
    type := duplicateSchema.type }

private def secondClaim : EquationClaim :=
  { sourceIndex := 2
    equationIndex := 1
    label := duplicateSchema.label
    arity := duplicateSchema.arity
    context := duplicateSchema.context
    left := duplicateSchema.left
    right := duplicateSchema.right
    type := duplicateSchema.type }

/-- This forged claim points at the interleaved constant while pretending it
is the second equation. -/
private def forgedClaim : EquationClaim :=
  { sourceIndex := 1
    equationIndex := 1
    label := duplicateSchema.label
    arity := duplicateSchema.arity
    context := duplicateSchema.context
    left := duplicateSchema.left
    right := duplicateSchema.right
    type := duplicateSchema.type }

theorem example_inventory_retains_both_duplicate_schemas :
    (equationInventory (elaborate exampleSource)).map LocatedEquation.claim =
      [firstClaim, secondClaim] := by
  rw [example_elaborates]
  rfl

theorem example_positions_cross_interleaved_constant :
    firstClaim.sourceIndex = 0 ∧ firstClaim.equationIndex = 0 ∧
      secondClaim.sourceIndex = 2 ∧ secondClaim.equationIndex = 1 := by
  simp [firstClaim, secondClaim]

private def firstFactRule : RuleSchema :=
  { id := generatedRuleId 0
    metavariables := []
    premises := []
    conclusion := encodeEquationClaim firstClaim }

private def secondFactRule : RuleSchema :=
  { id := generatedRuleId 1
    metavariables := []
    premises := []
    conclusion := encodeEquationClaim secondClaim }

private def firstRuleInstance : RuleInstance :=
  { ruleId := generatedRuleId 0
    arguments := [] }

private def secondRuleInstance : RuleInstance :=
  { ruleId := generatedRuleId 1
    arguments := [] }

private theorem example_generated_rules_exact :
    generatedRules (elaborate exampleSource) =
      [firstFactRule, secondFactRule] := by
  rw [example_elaborates]
  rfl

private theorem base_language_validate :
    basePresentation.1.toLanguageDef.validate = [] := by
  have v2 := basePresentation.2
  have v2Left := (Bool.and_eq_true_iff.mp v2).1
  have v2Left' := (Bool.and_eq_true_iff.mp v2Left).1
  have v1 : basePresentation.1.hasValidLocalRules = true :=
    (Bool.and_eq_true_iff.mp v2Left').1
  have v1Left := (Bool.and_eq_true_iff.mp v1).1
  have empty : basePresentation.1.toLanguageDef.validate.isEmpty = true :=
    (Bool.and_eq_true_iff.mp v1Left).1
  simpa using empty

private theorem example_target_language_validate :
    ((equationFactDelta exampleSource).apply
      basePresentation.1).toLanguageDef.validate = [] := by
  simpa [equationFactDelta, CalculusLanguageExtension.apply] using
    base_language_validate

set_option maxRecDepth 20000 in
private theorem example_delta_disjoint :
    (equationFactDelta exampleSource).disjointFrom
      basePresentation.1 = true := by
  unfold equationFactDelta
  rw [example_elaborates]
  simp [CalculusLanguageExtension.disjointFrom, basePresentation,
    generatedRules, exampleDeclarations, equationInventory, liftConstant,
    liftPriorEquation, generatedRule, generatedRuleId,
    AuthoredConstantInference.unaryOrdinal,
    typedConversionExtension, typedConversionDelta,
    DeclarationAwareFormedTyping.formedTypingExtension,
    ValidatedCalculusLanguageExtension.target, DeclarationAwareFormedTyping.formedTypingDelta,
    DeclarationAwareCheckedContext.contextFormationExtension,
    DeclarationAwareCheckedContext.contextFormationDelta,
    CalculusLanguageExtension.apply,
    DeclarationAwareCheckedContext.Structural.checked,
    DeclarationAwareStructuralTyping.checked,
    DeclarationAwareStructuralTyping.definition,
    DeclarationAwareStructuralTyping.definition,
    DeclarationAwareStructuralTyping.Data.definition,
    DeclarationAwareDataLanguage.definition]
  decide

set_option maxRecDepth 20000 in
private theorem example_delta_policy :
    (equationFactDelta exampleSource).policyHolds basePresentation.1
      .newJudgmentsOnly = true := by
  unfold equationFactDelta
  rw [example_elaborates]
  simp [CalculusLanguageExtension.policyHolds, basePresentation,
    generatedRules, exampleDeclarations, equationInventory, liftConstant,
    liftPriorEquation, generatedRule, LocatedEquation.claim,
    encodeEquationClaim, equationFactPattern,
    typedConversionExtension, typedConversionDelta,
    DeclarationAwareFormedTyping.formedTypingExtension,
    ValidatedCalculusLanguageExtension.target, DeclarationAwareFormedTyping.formedTypingDelta,
    DeclarationAwareCheckedContext.contextFormationExtension,
    DeclarationAwareCheckedContext.contextFormationDelta,
    CalculusLanguageExtension.apply,
    DeclarationAwareCheckedContext.Structural.checked,
    DeclarationAwareStructuralTyping.checked,
    DeclarationAwareStructuralTyping.definition,
    DeclarationAwareStructuralTyping.definition,
    DeclarationAwareStructuralTyping.Data.definition,
    DeclarationAwareDataLanguage.definition]

set_option maxRecDepth 20000 in
private theorem example_target_valid :
    ((equationFactDelta exampleSource).apply
      basePresentation.1).isValid = true := by
  unfold equationFactDelta
  rw [example_elaborates]
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  have languageValidate :
      (({ newTerms := []
          newJudgments := [{ head := "prime-authored-equation", arity := 8 }]
          newRules := generatedRules exampleDeclarations } :
        CalculusLanguageExtension).apply
        basePresentation.1).toLanguageDef.validate = [] := by
    simpa [equationFactDelta, example_elaborates] using
      example_target_language_validate
  rw [languageValidate]
  simp [basePresentation, generatedRules, exampleDeclarations,
    equationInventory, liftConstant, liftPriorEquation, generatedRule,
    generatedRuleId, AuthoredConstantInference.unaryOrdinal,
    LocatedEquation.claim, encodeEquationClaim, equationFactPattern,
    duplicateSchema, interleavedEntry,
    SourceEquation.sourceIndex, SourceEquation.equationIndex,
    typedConversionExtension, typedConversionDelta,
    typedConversionReflRule, typedConversionPattern,
    DeclarationAwareFormedTyping.formedTypingExtension,
    ValidatedCalculusLanguageExtension.target, DeclarationAwareFormedTyping.formedTypingDelta,
    DeclarationAwareFormedTyping.formedTypingRule,
    DeclarationAwareFormedTyping.formedHasTypePattern,
    DeclarationAwareCheckedContext.contextFormationExtension,
    DeclarationAwareCheckedContext.contextFormationDelta,
    DeclarationAwareCheckedContext.Structural.checked,
    DeclarationAwareStructuralTyping.checked,
    DeclarationAwareStructuralTyping.definition,
    DeclarationAwareStructuralTyping.definition,
    DeclarationAwareStructuralTyping.Data.definition,
    DeclarationAwareStructuralTyping.legacyGroundRule,
    DeclarationAwareStructuralTyping.sortRule,
    DeclarationAwareStructuralTyping.reflRule,
    DeclarationAwareStructuralTyping.piFormRule,
    DeclarationAwareStructuralTyping.hasTypePattern,
    DeclarationAwareStructuralTyping.tmHeadPattern,
    DeclarationAwareStructuralTyping.tmReflPattern,
    DeclarationAwareStructuralTyping.tmIdPattern,
    DeclarationAwareStructuralTyping.tmPiPattern,
    DeclarationAwareStructuralTyping.headSortPattern,
    DeclarationAwareStructuralTyping.levelSuccPattern,
    DeclarationAwareStructuralTyping.levelMaxPattern,
    DeclarationAwareStructuralTyping.natSuccPattern,
    DeclarationAwareStructuralTyping.ctxSnocPattern,
    DeclarationAwareCheckedContext.contextNilRule,
    DeclarationAwareCheckedContext.contextSnocRule,
    DeclarationAwareCheckedContext.contextFormedPattern,
    DeclarationAwareCheckedContext.encodeLevelSpine,
    DeclarationAwareCheckedContext.levelSpineNilConstructor,
    DeclarationAwareCheckedContext.levelSpineSnocConstructor,
    DeclarationAwareDataLanguage.dataConstructor,
    DeclarationAwareDataLanguage.definition,
    DeclarationAwareDataLanguage.constructorArities,
    DeclarationAwareDataLanguage.kernelDataType, TypeDecl.plain,
    DeclarationAwarePatternCodec.encodeNat,
    DeclarationAwarePatternCodec.encodeDeclName,
    DeclarationAwarePatternCodec.encodeLevel,
    DeclarationAwarePatternCodec.encodeTowerHead,
    DeclarationAwarePatternCodec.towerHeadCodec,
    DeclarationAwarePatternCodec.encodeCtx,
    DeclarationAwarePatternCodec.encodeTm,
    Tower.zero, CalculusLanguageExtension.apply, CalculusLanguageDef.ruleIds,
    CalculusLanguageDef.judgmentSignatureValid, CalculusLanguageDef.judgmentHeads,
    CalculusLanguageDef.conversionDeclarationValid,
    CalculusLanguageDef.lookupJudgment?, RuleSchema.isValidIn,
    RuleSchema.isLocallyValid, RuleSchema.metavariableNames,
    RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    CalculusLanguageDef.judgmentSchemaValid, fixedConstructorsValid,
    fixedConstructorListsValid, languageHasConstructorArity,
    Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, Pattern.zipHead,
    Pattern.mapHead, Pattern.evalHead]
  decide

private def exampleExtension : ValidatedCalculusLanguageExtension basePresentation where
  extension := equationFactDelta exampleSource
  policy := .newJudgmentsOnly
  disjoint := example_delta_disjoint
  policyHolds := example_delta_policy
  valid := example_target_valid

private theorem example_admission_exact :
    admit? exampleSource = some exampleExtension := by
  simp [admit?, example_delta_disjoint, example_delta_policy,
    example_target_valid, exampleExtension]

private def exampleAdmitted : AdmittedFacts exampleSource where
  extension := exampleExtension
  admission := example_admission_exact

private theorem firstFactRule_mem_target :
    firstFactRule ∈ exampleExtension.target.1.rules := by
  change firstFactRule ∈
    basePresentation.1.rules ++ generatedRules (elaborate exampleSource)
  rw [example_generated_rules_exact]
  simp

private theorem secondFactRule_mem_target :
    secondFactRule ∈ exampleExtension.target.1.rules := by
  change secondFactRule ∈
    basePresentation.1.rules ++ generatedRules (elaborate exampleSource)
  rw [example_generated_rules_exact]
  simp

private theorem firstFactRule_lookup :
    exampleExtension.target.1.lookupRule? firstRuleInstance.ruleId =
      some firstFactRule := by
  exact lookupRule?_eq_some_of_mem exampleExtension.target
    firstFactRule_mem_target

private theorem secondFactRule_lookup :
    exampleExtension.target.1.lookupRule? secondRuleInstance.ruleId =
      some secondFactRule := by
  exact lookupRule?_eq_some_of_mem exampleExtension.target
    secondFactRule_mem_target

private theorem firstFactApplication :
    RuleApplication exampleExtension.target firstRuleInstance []
      (encodeEquationClaim firstClaim) := by
  refine .intro firstFactRule firstFactRule_lookup ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · exact .nil 0
  · exact instantiateSchemaAt?_sound
      (instantiateSchemaAt?_eq_self_of_ground [] [] 0
        (encodeEquationClaim firstClaim)
        (encodeEquationClaim_ground firstClaim))

private theorem secondFactApplication :
    RuleApplication exampleExtension.target secondRuleInstance []
      (encodeEquationClaim secondClaim) := by
  refine .intro secondFactRule secondFactRule_lookup ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · exact .nil 0
  · exact instantiateSchemaAt?_sound
      (instantiateSchemaAt?_eq_self_of_ground [] [] 0
        (encodeEquationClaim secondClaim)
        (encodeEquationClaim_ground secondClaim))

private def firstDerivation :
    Derivation exampleExtension.target (encodeEquationClaim firstClaim) :=
  .byRule firstRuleInstance firstFactApplication .nil

private def secondDerivation :
    Derivation exampleExtension.target (encodeEquationClaim secondClaim) :=
  .byRule secondRuleInstance secondFactApplication .nil

/-- Both duplicate equation occurrences have distinct accepted one-node facts. -/
theorem example_duplicate_facts_accepted :
    checkRaw exampleExtension.target (encodeEquationClaim firstClaim)
        (generatedRawProof 0) = true ∧
      checkRaw exampleExtension.target (encodeEquationClaim secondClaim)
        (generatedRawProof 1) = true := by
  exact ⟨checkRaw_erase firstDerivation, checkRaw_erase secondDerivation⟩

private theorem example_source_equation_index_ne_one
    {schema : EquationSchema}
    (occurrence : SourceEquation exampleDeclarations schema) :
    occurrence.sourceIndex ≠ 1 := by
  cases occurrence with
  | here => simp [SourceEquation.sourceIndex]
  | afterEquation prior later =>
      cases later with
      | afterConstant name entry later' =>
          cases later' with
          | here => simp [SourceEquation.sourceIndex]
          | afterEquation prior later'' => cases later''

private theorem forged_evidence_uninhabited :
    ¬ Nonempty
      (EquationEvidence (elaborate exampleSource) forgedClaim) := by
  rw [example_elaborates]
  rintro ⟨evidence⟩
  exact example_source_equation_index_ne_one evidence.occurrence
    (by simpa [forgedClaim] using evidence.sourceIndex)

/-- No proof tree can authenticate an equation at the source position occupied
by the interleaved constant. -/
theorem example_forged_position_rejected (proof : RawProof) :
    checkRaw exampleExtension.target (encodeEquationClaim forgedClaim) proof =
      false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  exact forged_evidence_uninhabited
    (checkRaw_reflects_equation_source exampleAdmitted accepted)

theorem example_admission_succeeds : (admit? exampleSource).isSome = true := by
  rw [example_admission_exact]
  rfl

#print axioms SourceEquation.canonicalOccurrence
#print axioms decodeEquationClaim?_encode
#print axioms EquationEvidence.canonicalOccurrence
#print axioms generated_rule_semantic_sound
#print axioms AdmittedFacts.extension_eq
#print axioms admitted_generatedRule_raw_accepted
#print axioms checkRaw_reflects_equation_source
#print axioms encoded_open_variable_is_pattern_ground
#print axioms ground_schema_instantiation_is_not_object_substitution
#print axioms example_inventory_retains_both_duplicate_schemas
#print axioms example_duplicate_facts_accepted
#print axioms example_forged_position_rejected
#print axioms example_admission_succeeds

end AuthoredEquationInference
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
