import Mettapedia.Languages.MeTTa.PureKernel.Universe.AuthoredConstantIngress
import Mettapedia.GSLT.LanguageDef.InferencePresentationExtension
import Mettapedia.GSLT.LanguageDef.CanonicalPremiseClosure

/-!
# Finite inference facts generated from authored Prime constants

The source-faithful `FirstConstant` relation identifies exactly the nominal
declarations that survive first-wins interpretation.  This module turns that
relation into finite checker-boundary data without moving checking into native
construction.

`activeInventory` is an executable, proof-producing traversal.  Every retained
record contains its first-occurrence derivation and exact source index.  Later
same-name declarations are filtered while remaining present in the authored
document.  The generated inference rules are ground facts indexed by their
inventory occurrence.  Admission runs through the existing generic V2
presentation validator; validity is returned as evidence rather than assumed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PureKernel.Universe
namespace AuthoredConstantInference

open AuthoredDeclarationSignature
open AuthoredConstantIngress
open DeclarationAwarePatternCodec
open DeclarationAwareCheckedContext
open DeclarationAwareFormedTyping
open Mettapedia.GSLT.LanguageDef.CanonicalPremiseClosure
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferencePresentationExtension
open Mettapedia.GSLT.LanguageDef.KernelAuthority.Checker
open Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation
open Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation.Declaration
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Proof-producing finite inventory -/

/-- One active nominal constant together with the exact source path that made
it active. -/
structure ActiveConstant (declarations : List SourceDeclaration) where
  name : DeclName
  entry : Entry Tower.Head
  occurrence : FirstConstant declarations name entry

namespace ActiveConstant

/-- Source position retained by the first-occurrence proof. -/
def sourceIndex {declarations : List SourceDeclaration}
    (active : ActiveConstant declarations) : Nat :=
  active.occurrence.index

end ActiveConstant

/-- Lift every active record across an authored equation without losing its
position in the full source document. -/
def liftEquation (schema : EquationSchema)
    {declarations : List SourceDeclaration}
    (active : ActiveConstant declarations) :
    ActiveConstant (.equation schema :: declarations) where
  name := active.name
  entry := active.entry
  occurrence := .equation schema active.occurrence

/-- Lift a tail record across a differently named constant.  A same-name
record is discarded because the new head is now the active declaration. -/
def liftOther? (headName : DeclName) (headEntry : Entry Tower.Head)
    {declarations : List SourceDeclaration}
    (active : ActiveConstant declarations) :
    Option (ActiveConstant (.constant headName headEntry :: declarations)) :=
  if same : active.name = headName then
    none
  else
    some
      { name := active.name
        entry := active.entry
        occurrence := .other (Ne.symm same) headEntry active.occurrence }

/-- Executable inventory of exactly the active first-wins constants.  Its
elements are proof carrying; no later lookup is needed to justify a generated
fact. -/
def activeInventory :
    (declarations : List SourceDeclaration) -> List (ActiveConstant declarations)
  | [] => []
  | .equation schema :: declarations =>
      (activeInventory declarations).map (liftEquation schema)
  | .constant name entry :: declarations =>
      { name := name
        entry := entry
        occurrence := .here name entry declarations } ::
      (activeInventory declarations).filterMap (liftOther? name entry)

/-- Every inventory record is already a sound semantic lookup certificate. -/
theorem ActiveConstant.entries_lookup
    {declarations : List SourceDeclaration}
    (active : ActiveConstant declarations) :
    (semanticSignature declarations).entries active.name = some active.entry :=
  active.occurrence.entries_lookup

/-! ## Exact fact wire -/

/-- Canonical raw claim generated for an active constant occurrence. -/
structure ConstantClaim where
  sourceIndex : Nat
  name : DeclName
  type : Tower.Tm 0

def constantFactPattern (sourceIndex : Pattern) (name : Pattern)
    (type : Pattern) : Pattern :=
  .apply "prime-authored-constant" [sourceIndex, name, type]

def encodeConstantClaim (claim : ConstantClaim) : Pattern :=
  constantFactPattern (encodeNat claim.sourceIndex)
    (encodeDeclName claim.name) (encodeTm towerHeadCodec claim.type)

def decodeConstantClaim? : Pattern -> Option ConstantClaim
  | .apply "prime-authored-constant" [sourceIndex, name, type] => do
      pure
        { sourceIndex := ← decodeNat? sourceIndex
          name := ← decodeDeclName? name
          type := ← decodeTm? towerHeadCodec 0 type }
  | _ => none

@[simp] theorem decodeConstantClaim?_encode (claim : ConstantClaim) :
    decodeConstantClaim? (encodeConstantClaim claim) = some claim := by
  cases claim
  simp [encodeConstantClaim, constantFactPattern, decodeConstantClaim?]

def constantClaimCodec : PartialCodec ConstantClaim Pattern where
  encode := encodeConstantClaim
  decode := decodeConstantClaim?
  decode_encode := decodeConstantClaim?_encode

theorem encodeConstantClaim_ground (claim : ConstantClaim) :
    (encodeConstantClaim claim).isGroundAt 0 = true := by
  simp [encodeConstantClaim, constantFactPattern, Pattern.isGroundAt,
    Pattern.isGroundListAt, encodeNat_ground, encodeDeclName_ground,
    encodeTm_ground towerHeadCodec encodeTowerHead_ground]

/-- The semantic fibre of a generated fact retains the complete entry and the
proof-relevant first-occurrence path. -/
structure ConstantEvidence (declarations : List SourceDeclaration)
    (claim : ConstantClaim) where
  entry : Entry Tower.Head
  occurrence : FirstConstant declarations claim.name entry
  sourceIndex : occurrence.index = claim.sourceIndex
  displayedType : entry.type = claim.type

def ActiveConstant.claim {declarations : List SourceDeclaration}
    (active : ActiveConstant declarations) : ConstantClaim where
  sourceIndex := active.sourceIndex
  name := active.name
  type := active.entry.type

def ActiveConstant.evidence {declarations : List SourceDeclaration}
    (active : ActiveConstant declarations) :
    ConstantEvidence declarations active.claim where
  entry := active.entry
  occurrence := active.occurrence
  sourceIndex := rfl
  displayedType := rfl

/-- Implication-shaped meaning for unrestricted raw proof interpretation. -/
def ConstantFactMeaning (declarations : List SourceDeclaration)
    (goal : Pattern) : Type :=
  UniversalFibre constantClaimCodec (ConstantEvidence declarations) goal

/-! ## Generated rules and executable admission -/

/-- A structurally reducible unary ordinal keeps generated identifiers
collision-free without delegating theorem reduction to a numeral printer. -/
def unaryOrdinal : Nat → String
  | 0 => "z"
  | ordinal + 1 => "s" ++ unaryOrdinal ordinal

def generatedRuleId (ordinal : Nat) : RuleId :=
  { value := "prime-authored-constant." ++ unaryOrdinal ordinal }

@[simp] theorem unaryOrdinal_length (ordinal : Nat) :
    (unaryOrdinal ordinal).length = ordinal + 1 := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih =>
      simp only [unaryOrdinal, String.length_append, ih]
      change 1 + (ordinal + 1) = ordinal + 2
      omega

theorem unaryOrdinal_injective : Function.Injective unaryOrdinal := by
  intro left right equality
  have lengthEquality := congrArg String.length equality
  simp only [unaryOrdinal_length] at lengthEquality
  omega

theorem generatedRuleId_injective : Function.Injective generatedRuleId := by
  intro left right equality
  have lengthEquality := congrArg (fun ruleId => ruleId.value.length) equality
  simp [generatedRuleId, unaryOrdinal_length] at lengthEquality
  omega

def generatedRule (ordinal : Nat) {declarations : List SourceDeclaration}
    (active : ActiveConstant declarations) : RuleSchema :=
  { id := generatedRuleId ordinal
    metavariables := []
    premises := []
    conclusion := encodeConstantClaim active.claim }

def generatedRules (declarations : List SourceDeclaration) : List RuleSchema :=
  (activeInventory declarations).zipIdx.map fun (active, ordinal) =>
    generatedRule ordinal active

/-- Applying one generated ground fact reconstructs the exact source evidence
that generated it.  The checker contributes only structural replay; the
proof-relevant first-occurrence path comes from the authored inventory. -/
theorem generatedRule_application_meaning
    {declarations : List SourceDeclaration}
    (ordinal : Nat) (active : ActiveConstant declarations)
    {presentation : ValidatedPresentation}
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {conclusion : Pattern}
    (lookup : presentation.1.lookupRule? ruleInstance.ruleId =
      some (generatedRule ordinal active))
    (application :
      RuleApplication presentation ruleInstance premises conclusion) :
    Nonempty (ConstantFactMeaning declarations conclusion) := by
  cases application with
  | intro actualRule actualLookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
      have ruleEquality : actualRule = generatedRule ordinal active := by
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
          Instantiates [] [] (encodeConstantClaim active.claim)
            (encodeConstantClaim active.claim) :=
        instantiateSchemaAt?_sound
          (instantiateSchemaAt?_eq_self_of_ground [] [] 0
            (encodeConstantClaim active.claim)
            (encodeConstantClaim_ground active.claim))
      have conclusionEquality :
          conclusion = encodeConstantClaim active.claim :=
        conclusionInstantiates.functional selfInstantiation
      exact ⟨fun claim encoding => by
        have claimEquality : claim = active.claim :=
          constantClaimCodec.encode_injective
            (encoding.trans conclusionEquality)
        subst claim
        exact active.evidence⟩

/-- Every member of the generated rule table has the exact authored
proof-relevant meaning. -/
theorem generated_rule_semantic_sound
    {declarations : List SourceDeclaration} {rule : RuleSchema}
    (member : rule ∈ generatedRules declarations)
    {presentation : ValidatedPresentation}
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {conclusion : Pattern}
    (lookup : presentation.1.lookupRule? ruleInstance.ruleId = some rule)
    (application :
      RuleApplication presentation ruleInstance premises conclusion) :
    Nonempty (ConstantFactMeaning declarations conclusion) := by
  rcases List.mem_map.mp member with ⟨pair, pairMember, ruleEquality⟩
  rcases pair with ⟨active, ordinal⟩
  subst rule
  exact generatedRule_application_meaning ordinal active lookup application

/-- Proof-relevant semantic interpretation selected from the finite generated
inventory.  The existence theorem above is constructive; choice is confined
to crossing Lean's proposition-valued list-membership interface into a
Type-valued semantic fibre. -/
noncomputable def generatedRuleMeaning
    {declarations : List SourceDeclaration} {rule : RuleSchema}
    (member : rule ∈ generatedRules declarations)
    {presentation : ValidatedPresentation}
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {conclusion : Pattern}
    (lookup : presentation.1.lookupRule? ruleInstance.ruleId = some rule)
    (application :
      RuleApplication presentation ruleInstance premises conclusion) :
    ConstantFactMeaning declarations conclusion :=
  Classical.choice
    (generated_rule_semantic_sound member lookup application)

def constantFactDelta (source : SourceDocument) : PresentationExtension :=
  { newTerms := []
    newJudgments := [{ head := "prime-authored-constant", arity := 3 }]
    newRules := generatedRules (elaborate source) }

abbrev basePresentation : ValidatedPresentation := formedTypingExtension.target

/-- Validate the complete generated delta through the ordinary structural
extension boundary.  Failure remains explicit `none`; no validity proposition
is accepted as input. -/
def admit? (source : SourceDocument) :
    Option (ValidatedExtension basePresentation) :=
  let delta := constantFactDelta source
  if disjoint : delta.disjointFrom basePresentation.1 = true then
    if policy : delta.policyHolds basePresentation.1
        .newJudgmentsOnly = true then
      if valid : (delta.apply basePresentation.1).isValidV2 = true then
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

/-- A source package together with the exact validator result that admitted
its generated fact presentation. -/
structure AdmittedFacts (source : SourceDocument) where
  extension : ValidatedExtension basePresentation
  admission : admit? source = some extension

namespace AdmittedFacts

/-- Successful admission retains exactly the source-generated delta; it
cannot silently substitute a different rule table. -/
theorem extension_eq {source : SourceDocument}
    (admitted : AdmittedFacts source) :
    admitted.extension.extension = constantFactDelta source := by
  have admission := admitted.admission
  unfold admit? at admission
  dsimp only at admission
  by_cases disjoint :
      (constantFactDelta source).disjointFrom basePresentation.1 = true
  · rw [dif_pos disjoint] at admission
    by_cases policy :
        (constantFactDelta source).policyHolds basePresentation.1
          .newJudgmentsOnly = true
    · rw [dif_pos policy] at admission
      by_cases valid :
          ((constantFactDelta source).apply
            basePresentation.1).isValidV2 = true
      · rw [dif_pos valid] at admission
        have equality := Option.some.inj admission
        exact (congrArg
          (fun extension : ValidatedExtension basePresentation =>
            extension.extension) equality).symm
      · rw [dif_neg valid] at admission
        contradiction
    · rw [dif_neg policy] at admission
      contradiction
  · rw [dif_neg disjoint] at admission
    contradiction

/-- The admitted fact layer has the declared new-judgment conservativity
policy, not an unrestricted extension policy. -/
theorem policy_eq {source : SourceDocument}
    (admitted : AdmittedFacts source) :
    admitted.extension.policy = .newJudgmentsOnly := by
  have admission := admitted.admission
  unfold admit? at admission
  dsimp only at admission
  by_cases disjoint :
      (constantFactDelta source).disjointFrom basePresentation.1 = true
  · rw [dif_pos disjoint] at admission
    by_cases policy :
        (constantFactDelta source).policyHolds basePresentation.1
          .newJudgmentsOnly = true
    · rw [dif_pos policy] at admission
      by_cases valid :
          ((constantFactDelta source).apply
            basePresentation.1).isValidV2 = true
      · rw [dif_pos valid] at admission
        have equality := Option.some.inj admission
        exact congrArg
          (fun extension : ValidatedExtension basePresentation =>
            extension.policy) equality.symm
      · rw [dif_neg valid] at admission
        contradiction
    · rw [dif_neg policy] at admission
      contradiction
  · rw [dif_neg disjoint] at admission
    contradiction

end AdmittedFacts

/-- The fixed Prime typing base does not already claim the generated authored
constant judgment. -/
theorem base_constantFact_not_shaped (claim : ConstantClaim) :
    basePresentation.1.hasJudgmentShape (encodeConstantClaim claim) = false := by
  rfl

/-- Canonical one-node raw artifact for a generated ground fact. -/
def generatedRawProof (ordinal : Nat) : RawProof :=
  .node
    { ruleId := generatedRuleId ordinal
      arguments := [] }
    []

/-- **Generated-source completeness.**  Once the source delta is admitted,
every exact member of its generated fact table has an accepted one-node raw
proof. -/
theorem admitted_generatedRule_raw_accepted
    {source : SourceDocument} (admitted : AdmittedFacts source)
    (ordinal : Nat) (active : ActiveConstant (elaborate source))
    (member : generatedRule ordinal active ∈
      generatedRules (elaborate source)) :
    Mettapedia.GSLT.LanguageDef.InferenceChecker.checkRaw
      admitted.extension.target (encodeConstantClaim active.claim)
      (generatedRawProof ordinal) = true := by
  have targetMember :
      generatedRule ordinal active ∈ admitted.extension.target.1.rules := by
    change generatedRule ordinal active ∈
      basePresentation.1.rules ++ admitted.extension.extension.newRules
    apply List.mem_append_right basePresentation.1.rules
    rw [admitted.extension_eq]
    exact member
  have lookup :
      admitted.extension.target.1.lookupRule? (generatedRuleId ordinal) =
        some (generatedRule ordinal active) :=
    lookupRule?_eq_some_of_mem admitted.extension.target targetMember
  have application :
      RuleApplication admitted.extension.target
        { ruleId := generatedRuleId ordinal
          arguments := [] }
        [] (encodeConstantClaim active.claim) := by
    refine .intro (generatedRule ordinal active) lookup ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · exact .nil 0
    · exact instantiateSchemaAt?_sound
        (instantiateSchemaAt?_eq_self_of_ground [] [] 0
          (encodeConstantClaim active.claim)
          (encodeConstantClaim_ground active.claim))
  let derivation :
      Derivation admitted.extension.target
        (encodeConstantClaim active.claim) :=
    .byRule
      { ruleId := generatedRuleId ordinal
        arguments := [] }
      application .nil
  simpa [generatedRawProof, derivation, Derivation.erase,
    DerivationList.erase] using checkRaw_erase derivation

/-- Every generated table member therefore has some accepted raw artifact;
the witness above sharpens this existence to a canonical one-node tree. -/
theorem admitted_generated_rule_has_accepted_raw
    {source : SourceDocument} (admitted : AdmittedFacts source)
    {rule : RuleSchema} (member : rule ∈ generatedRules (elaborate source)) :
    ∃ proof : RawProof,
      Mettapedia.GSLT.LanguageDef.InferenceChecker.checkRaw
        admitted.extension.target rule.conclusion proof = true := by
  rcases List.mem_map.mp member with ⟨pair, pairMember, ruleEquality⟩
  rcases pair with ⟨active, ordinal⟩
  subst rule
  exact ⟨generatedRawProof ordinal,
    admitted_generatedRule_raw_accepted admitted ordinal active
      (List.mem_map.mpr ⟨(active, ordinal), pairMember, rfl⟩)⟩

/-- **Exact checked/source reflection.**  Any raw proof accepted for a
generated constant claim reconstructs a genuine active first occurrence in
the authored source, including its source index and displayed type. -/
theorem checkRaw_reflects_active_source
    {source : SourceDocument} (admitted : AdmittedFacts source)
    {claim : ConstantClaim} {proof : RawProof}
    (accepted :
      Mettapedia.GSLT.LanguageDef.InferenceChecker.checkRaw
        admitted.extension.target
      (encodeConstantClaim claim) proof = true) :
    Nonempty (ConstantEvidence (elaborate source) claim) := by
  cases proof with
  | node ruleInstance children =>
      simp only [Mettapedia.GSLT.LanguageDef.InferenceChecker.checkRaw]
        at accepted
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
          have conclusionEq : conclusion = encodeConstantClaim claim :=
            accepted.1
          subst conclusion
          rcases
              Mettapedia.GSLT.LanguageDef.InferenceSemanticExtension.SemanticExtension.target_application_classifies
                application with
            baseApplication | ⟨rule, member, lookup⟩
          · have shaped := baseApplication.conclusion_hasJudgmentShape
            rw [base_constantFact_not_shaped claim] at shaped
            contradiction
          · have generatedMember :
                rule ∈ generatedRules (elaborate source) := by
              simpa [admitted.extension_eq, constantFactDelta] using member
            rcases generated_rule_semantic_sound generatedMember lookup
                application with
              ⟨meaning⟩
            exact ⟨meaning claim rfl⟩

/-! ## Positive and negative controls -/

private def exampleName : DeclName := `Prime.AuthoredInference.A

private def exampleEntry : Entry Tower.Head where
  type := .head (.sort Tower.zero)

private def shadowedEntry : Entry Tower.Head where
  type := .head (.sort (.succ Tower.zero))

private def exampleDeclarations : List SourceDeclaration :=
    [.constant exampleName exampleEntry,
     .constant exampleName shadowedEntry]

private def exampleSource : SourceDocument :=
  sourceCodec.quote exampleDeclarations

private def exampleClaim : ConstantClaim :=
  { sourceIndex := 0
    name := exampleName
    type := exampleEntry.type }

private def shadowedClaim : ConstantClaim :=
  { sourceIndex := 1
    name := exampleName
    type := shadowedEntry.type }

private def exampleFactRule : RuleSchema :=
  { id := generatedRuleId 0
    metavariables := []
    premises := []
    conclusion := encodeConstantClaim exampleClaim }

private def exampleRuleInstance : RuleInstance :=
  { ruleId := generatedRuleId 0
    arguments := [] }

/-- Two same-name source declarations generate exactly one active fact. -/
theorem example_inventory_has_one_active_constant :
    (activeInventory (elaborate exampleSource)).length = 1 := by
  have elaborates : elaborate exampleSource = exampleDeclarations := by
    exact elaborate_quote exampleDeclarations
  rw [elaborates]
  rfl

/-- The retained fact points to the first source position. -/
theorem example_generated_conclusion_is_first :
    (generatedRules (elaborate exampleSource)).map RuleSchema.conclusion =
      [encodeConstantClaim
        { sourceIndex := 0
          name := exampleName
          type := exampleEntry.type }] := by
  have elaborates : elaborate exampleSource = exampleDeclarations := by
    exact elaborate_quote exampleDeclarations
  rw [elaborates]
  rfl

private theorem example_generated_rules_exact :
    generatedRules (elaborate exampleSource) = [exampleFactRule] := by
  have elaborates : elaborate exampleSource = exampleDeclarations :=
    elaborate_quote exampleDeclarations
  rw [elaborates]
  rfl

/-- The later shadowed declaration cannot generate a raw fact. -/
theorem shadowed_conclusion_not_generated :
    encodeConstantClaim
        { sourceIndex := 1
          name := exampleName
          type := shadowedEntry.type } ∉
      (generatedRules (elaborate exampleSource)).map RuleSchema.conclusion := by
  have elaborates : elaborate exampleSource = exampleDeclarations := by
    exact elaborate_quote exampleDeclarations
  rw [elaborates]
  decide

private theorem base_language_validate :
    basePresentation.1.language.validate = [] := by
  have v2 := basePresentation.2
  have v2Left := (Bool.and_eq_true_iff.mp v2).1
  have v2Left' := (Bool.and_eq_true_iff.mp v2Left).1
  have v1 : basePresentation.1.isValidV1 = true :=
    (Bool.and_eq_true_iff.mp v2Left').1
  have v1Left := (Bool.and_eq_true_iff.mp v1).1
  have empty : basePresentation.1.language.validate.isEmpty = true :=
    (Bool.and_eq_true_iff.mp v1Left).1
  simpa using empty

private theorem example_target_language_validate :
    ((constantFactDelta exampleSource).apply
      basePresentation.1).language.validate = [] := by
  simpa [constantFactDelta, PresentationExtension.apply] using
    base_language_validate

private theorem example_elaborates :
    elaborate exampleSource = exampleDeclarations :=
  elaborate_quote exampleDeclarations

private theorem example_delta_disjoint :
    (constantFactDelta exampleSource).disjointFrom
      basePresentation.1 = true := by
  unfold constantFactDelta
  rw [example_elaborates]
  simp [basePresentation, generatedRules, exampleDeclarations,
    activeInventory, liftOther?,
    generatedRule, generatedRuleId, unaryOrdinal, formedTypingExtension,
    ValidatedExtension.target, formedTypingDelta, contextFormationExtension,
    contextFormationDelta, PresentationExtension.apply,
    PresentationExtension.disjointFrom,
    DeclarationAwareCheckedContext.Structural.checked,
    DeclarationAwareStructuralTyping.checked,
    DeclarationAwareStructuralTyping.presentation,
    DeclarationAwareStructuralTyping.definition,
    DeclarationAwareStructuralTyping.Data.definition,
    DeclarationAwareDataLanguage.definition]
  decide

private theorem example_delta_policy :
    (constantFactDelta exampleSource).policyHolds basePresentation.1
      .newJudgmentsOnly = true := by
  unfold constantFactDelta
  rw [example_elaborates]
  simp [PresentationExtension.policyHolds, basePresentation,
    generatedRules, exampleDeclarations, activeInventory, liftOther?,
    generatedRule, ActiveConstant.claim, encodeConstantClaim,
    constantFactPattern, formedTypingExtension, ValidatedExtension.target,
    formedTypingDelta, contextFormationExtension, contextFormationDelta,
    PresentationExtension.apply,
    DeclarationAwareCheckedContext.Structural.checked,
    DeclarationAwareStructuralTyping.checked,
    DeclarationAwareStructuralTyping.presentation,
    DeclarationAwareStructuralTyping.definition,
    DeclarationAwareStructuralTyping.Data.definition,
    DeclarationAwareDataLanguage.definition]

set_option maxRecDepth 10000 in
private theorem example_target_valid :
    ((constantFactDelta exampleSource).apply
      basePresentation.1).isValidV2 = true := by
  unfold constantFactDelta
  rw [example_elaborates]
  unfold Presentation.isValidV2 Presentation.isValidV1
  have languageValidate :
      (({ newTerms := []
          newJudgments := [{ head := "prime-authored-constant", arity := 3 }]
          newRules := generatedRules exampleDeclarations } :
        PresentationExtension).apply
        basePresentation.1).language.validate = [] := by
    simpa [constantFactDelta, example_elaborates] using
      example_target_language_validate
  rw [languageValidate]
  simp [basePresentation, generatedRules, exampleDeclarations,
    activeInventory, liftOther?,
    generatedRule, generatedRuleId, unaryOrdinal, ActiveConstant.claim,
    ActiveConstant.sourceIndex, formedTypingExtension,
    ValidatedExtension.target, formedTypingDelta, contextFormationExtension,
    contextFormationDelta, PresentationExtension.apply,
    encodeConstantClaim, constantFactPattern, exampleName, exampleEntry,
    shadowedEntry, FirstConstant.index,
    DeclarationAwarePatternCodec.encodeNat,
    DeclarationAwarePatternCodec.encodeChars,
    DeclarationAwarePatternCodec.encodeString,
    DeclarationAwarePatternCodec.encodeDeclName,
    DeclarationAwarePatternCodec.encodeLevel,
    DeclarationAwarePatternCodec.encodeTowerHead,
    DeclarationAwarePatternCodec.towerHeadCodec,
    DeclarationAwarePatternCodec.encodeTm,
    DeclarationAwareCheckedContext.Structural.checked, formedTypingRule,
    formedHasTypePattern, DeclarationAwareStructuralTyping.checked,
    DeclarationAwareStructuralTyping.presentation,
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
    contextNilRule, contextSnocRule, contextFormedPattern,
    encodeLevelSpine, levelSpineNilConstructor, levelSpineSnocConstructor,
    DeclarationAwareDataLanguage.dataConstructor,
    DeclarationAwareDataLanguage.definition,
    DeclarationAwareDataLanguage.constructorArities,
    DeclarationAwareDataLanguage.kernelDataType, TypeDecl.plain,
    encodeTowerHead, Tower.zero, encodeLevel, encodeNat, encodeCtx,
    Presentation.ruleIds, Presentation.judgmentSignatureValid,
    Presentation.judgmentHeads, Presentation.conversionDeclarationValid,
    Presentation.lookupJudgment?, RuleSchema.isValidIn,
    RuleSchema.isValidV1, RuleSchema.metavariableNames,
    RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    Presentation.judgmentSchemaValid, fixedConstructorsValid,
    fixedConstructorListsValid, languageHasConstructorArity,
    Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, Pattern.zipHead,
    Pattern.mapHead, Pattern.evalHead]
  decide

private def exampleExtension : ValidatedExtension basePresentation where
  extension := constantFactDelta exampleSource
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

private theorem exampleFactRule_mem_target :
    exampleFactRule ∈ exampleExtension.target.1.rules := by
  change exampleFactRule ∈
    basePresentation.1.rules ++ generatedRules (elaborate exampleSource)
  rw [example_generated_rules_exact]
  simp

private theorem exampleFactRule_lookup :
    exampleExtension.target.1.lookupRule? exampleRuleInstance.ruleId =
      some exampleFactRule := by
  exact lookupRule?_eq_some_of_mem exampleExtension.target
    exampleFactRule_mem_target

private theorem exampleFactApplication :
    RuleApplication exampleExtension.target exampleRuleInstance []
      (encodeConstantClaim exampleClaim) := by
  refine .intro exampleFactRule exampleFactRule_lookup ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · exact .nil 0
  · exact instantiateSchemaAt?_sound
      (instantiateSchemaAt?_eq_self_of_ground [] [] 0
        (encodeConstantClaim exampleClaim)
        (encodeConstantClaim_ground exampleClaim))

private def exampleDerivation :
    Derivation exampleExtension.target (encodeConstantClaim exampleClaim) :=
  .byRule exampleRuleInstance exampleFactApplication .nil

/-- The accepted artifact is exactly one ground fact node, with no hidden
premise replay. -/
def exampleRawProof : RawProof := exampleDerivation.erase

theorem exampleRawProof_is_single_node :
    exampleRawProof = .node exampleRuleInstance [] := rfl

/-- Positive checker/source canary: the active first declaration has an
accepted finite proof. -/
theorem example_active_raw_accepted :
    Mettapedia.GSLT.LanguageDef.InferenceChecker.checkRaw
      exampleExtension.target (encodeConstantClaim exampleClaim)
      exampleRawProof = true :=
  checkRaw_erase exampleDerivation

private theorem shadowed_evidence_uninhabited :
    ¬ Nonempty
      (ConstantEvidence (elaborate exampleSource) shadowedClaim) := by
  rw [example_elaborates]
  rintro ⟨evidence⟩
  have shadowedLookup :
      (semanticSignature exampleDeclarations).entries exampleName =
        some evidence.entry := by
    simpa [shadowedClaim] using evidence.occurrence.entries_lookup
  have firstLookup :
      (semanticSignature exampleDeclarations).entries exampleName =
        some exampleEntry :=
    (FirstConstant.here exampleName exampleEntry
      [.constant exampleName shadowedEntry]).entries_lookup
  rw [firstLookup] at shadowedLookup
  have entryEquality : exampleEntry = evidence.entry :=
    Option.some.inj shadowedLookup
  have typeEquality : exampleEntry.type = shadowedEntry.type :=
    (congrArg Entry.type entryEquality).trans (by
      simpa [shadowedClaim] using evidence.displayedType)
  simp [exampleEntry, shadowedEntry] at typeEquality
  cases typeEquality

/-- Negative checker/source canary: no raw proof tree can turn a later
same-name declaration into an active fact. -/
theorem example_shadowed_raw_rejected (proof : RawProof) :
    Mettapedia.GSLT.LanguageDef.InferenceChecker.checkRaw
      exampleExtension.target (encodeConstantClaim shadowedClaim) proof =
        false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  exact shadowed_evidence_uninhabited
    (checkRaw_reflects_active_source exampleAdmitted accepted)

/-- The concrete generated extension passes the existing V2 validator. -/
theorem example_admission_succeeds : (admit? exampleSource).isSome = true := by
  rw [example_admission_exact]
  rfl

#print axioms ActiveConstant.entries_lookup
#print axioms decodeConstantClaim?_encode
#print axioms instantiateSchemaAt?_eq_self_of_ground
#print axioms instantiateSchemasAt?_eq_self_of_ground
#print axioms example_inventory_has_one_active_constant
#print axioms example_generated_conclusion_is_first
#print axioms shadowed_conclusion_not_generated
#print axioms generated_rule_semantic_sound
#print axioms AdmittedFacts.extension_eq
#print axioms admitted_generatedRule_raw_accepted
#print axioms checkRaw_reflects_active_source
#print axioms exampleRawProof_is_single_node
#print axioms example_active_raw_accepted
#print axioms example_shadowed_raw_rejected
#print axioms example_admission_succeeds

end AuthoredConstantInference
end Mettapedia.Languages.MeTTa.PureKernel.Universe
