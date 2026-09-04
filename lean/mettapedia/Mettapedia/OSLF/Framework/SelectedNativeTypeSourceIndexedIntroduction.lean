import Mettapedia.OSLF.Framework.SelectedNativeTypeAuthoredOccurrenceSyntax
import Mettapedia.OSLF.Framework.DisplayedRewriteVariableProfile
import Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedCarrierSupport
import Mettapedia.OSLF.Framework.SelectedNativeTypeOccurrenceStepClaim

/-!
# Source-indexed formation and introduction for selected native types

The selected native-type signature can be generated independently of an
authored source language, but its introduction rules cannot: introduction is
about one exact displayed rewrite occurrence.  This module therefore exposes
the sound formation/introduction fragment as a `CalculusLanguageExtension`
whose rules retain the selected source focus, complete rewrite source, and
specified right-hand side as literal source syntax.

Only ordinary free-variable names are moved into an occurrence-local
namespace.  The authored constructor, binder, substitution, and collection
structure is otherwise unchanged.  The extension must consequently be
validated only after the source language and generated signature have both
been attached.

The manuscript's present rule covers occurrences whose fixed-context and
focus supports are disjoint.  Construction of the public extension requires
that evidence.  Shared support remains rejected until an explicit matching
constraint is represented.  Elimination is deliberately absent: it requires
the separately reviewed binder/eigenvariable repair.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedIntroduction

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ContextualInference
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.SelectedNativeTypeContextualCalculus
open Mettapedia.OSLF.Framework.SelectedNativeTypeAuthoredOccurrenceSyntax

/-- Ambient variable-context hole used by every generated source-indexed
rule. -/
def gamma : ContextSchema := .hole "Gamma"

/-- Ambient relation-context hole used by every generated source-indexed
rule. -/
def delta : ContextSchema := .hole "Delta"

@[simp] theorem encode_gamma :
    ContextualInference.encodeContext gamma = .fvar "Gamma" := by
  rfl

@[simp] theorem encode_delta :
    ContextualInference.encodeContext delta = .fvar "Delta" := by
  rfl

/-! ## Syntax-derived formal parameters -/

/-- Close a generated contextual rule over exactly the metavariable
occurrences present in its lowered syntax.  First-occurrence order is stable,
and the full `(name, binderDepth)` coordinate is retained.  This construction
does not inspect a derivation or a semantic interpretation. -/
def inferMetavariables (rule : ContextualInference.Rule) :
    ContextualInference.Rule :=
  { rule with
    metavariables :=
      (RuleSchema.occurrences
        (ContextualInference.lowerRule rule)).eraseDups }

@[simp] theorem inferMetavariables_id (rule : ContextualInference.Rule) :
    (inferMetavariables rule).id = rule.id := by
  rfl

@[simp] theorem inferMetavariables_premises
    (rule : ContextualInference.Rule) :
    (inferMetavariables rule).premises = rule.premises := by
  rfl

@[simp] theorem inferMetavariables_conclusion
    (rule : ContextualInference.Rule) :
    (inferMetavariables rule).conclusion = rule.conclusion := by
  rfl

@[simp] theorem inferMetavariables_sideConditions
    (rule : ContextualInference.Rule) :
    (inferMetavariables rule).sideConditions = rule.sideConditions := by
  rfl

/-- Independent shape evidence needed after the formal row has been inferred
from actual syntax.  In particular, a name used at two binder depths violates
`occurrenceNamesNodup`, so inference cannot hide an ambiguous schema. -/
structure InferredRuleAdmission (rule : ContextualInference.Rule) : Prop where
  identifierNonempty : rule.id.value ≠ ""
  occurrenceNamesNonempty :
    ∀ occurrence ∈ RuleSchema.occurrences
        (ContextualInference.lowerRule rule),
      occurrence.1 ≠ ""
  occurrenceNamesNodup :
    (((RuleSchema.occurrences
      (ContextualInference.lowerRule rule)).eraseDups).map Prod.fst).Nodup
  patternsWellScoped :
    ∀ pattern ∈ RuleSchema.patterns (ContextualInference.lowerRule rule),
      Pattern.isWellScoped pattern = true
  patternsHaveNoCollectionRest :
    ∀ pattern ∈ RuleSchema.patterns (ContextualInference.lowerRule rule),
      patternHasNoCollectionRest pattern = true
  patternsHaveCanonicalBinders :
    ∀ pattern ∈ RuleSchema.patterns (ContextualInference.lowerRule rule),
      Pattern.hasCanonicalBinderMetadata pattern = true

/-- Compositional structural evidence for one generated schema pattern.  All
free schema variables have nonempty names and occur at depth zero; the other
three fields are precisely the checker's pattern-shape gates. -/
structure SchemaPatternAdmission (pattern : Pattern) : Prop where
  occurrenceNamesNonempty :
    ∀ occurrence ∈ patternMetavariableOccurrencesAt 0 pattern,
      occurrence.1 ≠ ""
  metavariablesAtTop :
    ∀ occurrence ∈ patternMetavariableOccurrencesAt 0 pattern,
      occurrence.2 = 0
  wellScoped : pattern.isWellScoped = true
  noCollectionRest : patternHasNoCollectionRest pattern = true
  canonicalBinders : pattern.hasCanonicalBinderMetadata = true

/-- Ordered-list companion to `SchemaPatternAdmission`. -/
structure SchemaPatternsAdmission (patterns : List Pattern) : Prop where
  occurrenceNamesNonempty :
    ∀ occurrence ∈ patternsMetavariableOccurrencesAt 0 patterns,
      occurrence.1 ≠ ""
  metavariablesAtTop :
    ∀ occurrence ∈ patternsMetavariableOccurrencesAt 0 patterns,
      occurrence.2 = 0
  wellScoped : Pattern.isWellScopedListAt 0 patterns = true
  noCollectionRest : patternsHaveNoCollectionRest patterns = true
  canonicalBinders : Pattern.hasCanonicalBinderMetadataList patterns = true

protected theorem SchemaPatternsAdmission.nil :
    SchemaPatternsAdmission [] := by
  constructor <;>
    simp [patternsMetavariableOccurrencesAt,
      Pattern.isWellScopedListAt, patternsHaveNoCollectionRest,
      Pattern.hasCanonicalBinderMetadataList]

protected theorem SchemaPatternsAdmission.cons
    {pattern : Pattern} {patterns : List Pattern}
    (head : SchemaPatternAdmission pattern)
    (tail : SchemaPatternsAdmission patterns) :
    SchemaPatternsAdmission (pattern :: patterns) := by
  refine
    { occurrenceNamesNonempty := ?_
      metavariablesAtTop := ?_
      wellScoped := ?_
      noCollectionRest := ?_
      canonicalBinders := ?_ }
  · intro occurrence membership
    simp only [patternsMetavariableOccurrencesAt, List.mem_append] at membership
    exact membership.elim
      (head.occurrenceNamesNonempty occurrence)
      (tail.occurrenceNamesNonempty occurrence)
  · intro occurrence membership
    simp only [patternsMetavariableOccurrencesAt, List.mem_append] at membership
    exact membership.elim
      (head.metavariablesAtTop occurrence)
      (tail.metavariablesAtTop occurrence)
  · rw [Pattern.isWellScopedListAt, Bool.and_eq_true]
    exact
      ⟨by simpa [Pattern.isWellScoped] using head.wellScoped,
        tail.wellScoped⟩
  · simp [patternsHaveNoCollectionRest, head.noCollectionRest,
      tail.noCollectionRest]
  · simp [Pattern.hasCanonicalBinderMetadataList, head.canonicalBinders,
      tail.canonicalBinders]

protected theorem SchemaPatternsAdmission.of_forall
    (patterns : List Pattern)
    (admission : ∀ pattern ∈ patterns, SchemaPatternAdmission pattern) :
    SchemaPatternsAdmission patterns := by
  induction patterns with
  | nil => exact .nil
  | cons pattern patterns inductionHypothesis =>
      exact .cons (admission pattern (by simp))
        (inductionHypothesis fun other membership =>
          admission other (by simp [membership]))

protected theorem SchemaPatternAdmission.fvar
    (name : String) (nonempty : name ≠ "") :
    SchemaPatternAdmission (.fvar name) := by
  refine
    { occurrenceNamesNonempty := ?_
      metavariablesAtTop := ?_
      wellScoped := ?_
      noCollectionRest := ?_
      canonicalBinders := ?_ }
  all_goals
    simp [patternMetavariableOccurrencesAt,
      Pattern.isWellScoped, Pattern.isWellScopedAt,
      patternHasNoCollectionRest, Pattern.hasCanonicalBinderMetadata,
      nonempty]

protected theorem SchemaPatternAdmission.apply
    (head : String) (arguments : List Pattern)
    (admission : ∀ pattern ∈ arguments, SchemaPatternAdmission pattern) :
    SchemaPatternAdmission (.apply head arguments) := by
  have argumentsAdmission :=
    SchemaPatternsAdmission.of_forall arguments admission
  exact
    { occurrenceNamesNonempty := by
        simpa [patternMetavariableOccurrencesAt] using
          argumentsAdmission.occurrenceNamesNonempty
      metavariablesAtTop := by
        simpa [patternMetavariableOccurrencesAt] using
          argumentsAdmission.metavariablesAtTop
      wellScoped := by
        simpa [Pattern.isWellScoped, Pattern.isWellScopedAt] using
          argumentsAdmission.wellScoped
      noCollectionRest := by
        simpa [patternHasNoCollectionRest] using
          argumentsAdmission.noCollectionRest
      canonicalBinders := by
        simpa [Pattern.hasCanonicalBinderMetadata] using
          argumentsAdmission.canonicalBinders }

/-- Occurrence-local renaming turns an admitted authored pattern into an
admitted generated schema pattern. -/
protected theorem SchemaPatternAdmission.authored
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    (pattern : Pattern) (admission : TopLevelPatternAdmission pattern) :
    SchemaPatternAdmission (authoredPattern demand slot pattern) := by
  exact
    { occurrenceNamesNonempty :=
        authoredPattern_occurrence_name_nonempty demand slot pattern
      metavariablesAtTop :=
        authoredPattern_occurrence_depth_zero demand slot pattern admission
      wellScoped :=
        authoredPattern_isWellScoped demand slot pattern admission
      noCollectionRest :=
        authoredPattern_hasNoCollectionRest demand slot pattern admission
      canonicalBinders :=
        authoredPattern_hasCanonicalBinderMetadata demand slot pattern admission }

/-- Encoding an ordered row of admitted formulas in front of a nonempty
context hole preserves schema admission. -/
protected theorem SchemaPatternAdmission.encodeContext_prepend
    (formulas : List Pattern) (tailName : String)
    (tailNonempty : tailName ≠ "")
    (admission : ∀ formula ∈ formulas, SchemaPatternAdmission formula) :
    SchemaPatternAdmission
      (ContextualInference.encodeContext
        (ContextSchema.prepend formulas (.hole tailName))) := by
  induction formulas with
  | nil =>
      simpa [ContextSchema.prepend, ContextualInference.encodeContext] using
        SchemaPatternAdmission.fvar tailName tailNonempty
  | cons formula formulas inductionHypothesis =>
      have headAdmission := admission formula (by simp)
      have tailAdmission := inductionHypothesis
        (fun other membership => admission other (by simp [membership]))
      have combined := SchemaPatternAdmission.apply
        ContextualInference.extendContextTerm.label
        [formula, ContextualInference.encodeContext
          (ContextSchema.prepend formulas (.hole tailName))]
        (by
          intro pattern membership
          simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
          rcases membership with rfl | rfl
          · exact headAdmission
          · exact tailAdmission)
      simpa [ContextSchema.prepend, ContextualInference.encodeContext] using
        combined

/-- Lowering an admitted contextual sequent produces an admitted ordinary
schema pattern. -/
protected theorem SchemaPatternAdmission.lowerSequent
    (sequent : Sequent)
    (variableContext : SchemaPatternAdmission
      (ContextualInference.encodeContext sequent.variableContext))
    (relationContext : SchemaPatternAdmission
      (ContextualInference.encodeContext sequent.relationContext))
    (conclusion : SchemaPatternAdmission sequent.conclusion) :
    SchemaPatternAdmission (ContextualInference.lowerSequent sequent) := by
  have combined := SchemaPatternAdmission.apply
    ContextualInference.contextualJudgment.head
    [ ContextualInference.encodeContext sequent.variableContext
    , ContextualInference.encodeContext sequent.relationContext
    , sequent.conclusion ]
    (by
      intro pattern membership
      simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
      rcases membership with rfl | rfl | rfl
      · exact variableContext
      · exact relationContext
      · exact conclusion)
  simpa [ContextualInference.lowerSequent] using combined

protected theorem SchemaPatternAdmission.variableClaim
    (carrier : String) (value : Pattern)
    (valueAdmission : SchemaPatternAdmission value) :
    SchemaPatternAdmission
      (ContextualCarrierClaims.variableClaim carrier value) := by
  apply SchemaPatternAdmission.apply
  intro pattern membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
  subst pattern
  exact valueAdmission

protected theorem SchemaPatternAdmission.typingClaim
    (carrier : String) (subject type : Pattern)
    (subjectAdmission : SchemaPatternAdmission subject)
    (typeAdmission : SchemaPatternAdmission type) :
    SchemaPatternAdmission
      (ContextualCarrierClaims.typingClaim carrier subject type) := by
  apply SchemaPatternAdmission.apply
  intro pattern membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl
  · exact subjectAdmission
  · exact typeAdmission

protected theorem SchemaPatternAdmission.reductionClaim
    (carrier : String) (source target : Pattern)
    (sourceAdmission : SchemaPatternAdmission source)
    (targetAdmission : SchemaPatternAdmission target) :
    SchemaPatternAdmission
      (ContextualCarrierClaims.reductionClaim carrier source target) := by
  apply SchemaPatternAdmission.apply
  intro pattern membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl
  · exact sourceAdmission
  · exact targetAdmission

/-- Finite executable evidence for `InferredRuleAdmission`.  The check covers
only structural input facts; it does not run proof search or consult a semantic
interpretation. -/
def inferredRuleAdmissionCheck (rule : ContextualInference.Rule) : Bool :=
  let lowered := ContextualInference.lowerRule rule
  let occurrences := RuleSchema.occurrences lowered
  let names := occurrences.eraseDups.map Prod.fst
  let patterns := RuleSchema.patterns lowered
  (rule.id.value != "") &&
    occurrences.all (fun occurrence => occurrence.1 != "") &&
    (names.eraseDups.length == names.length) &&
    patterns.all Pattern.isWellScoped &&
    patterns.all patternHasNoCollectionRest &&
    patterns.all Pattern.hasCanonicalBinderMetadata

/-- The finite structural check reconstructs every proof-relevant admission
field.  Concrete generators may therefore compute the check while downstream
validity theorems depend only on `InferredRuleAdmission`. -/
theorem inferredRuleAdmission_of_check
    (rule : ContextualInference.Rule)
    (checked : inferredRuleAdmissionCheck rule = true) :
    InferredRuleAdmission rule := by
  unfold inferredRuleAdmissionCheck at checked
  rcases Bool.and_eq_true_iff.mp checked with
    ⟨checked, canonicalBinders⟩
  rcases Bool.and_eq_true_iff.mp checked with
    ⟨checked, noCollectionRest⟩
  rcases Bool.and_eq_true_iff.mp checked with ⟨checked, patternsScoped⟩
  rcases Bool.and_eq_true_iff.mp checked with
    ⟨checked, occurrenceNamesUnique⟩
  rcases Bool.and_eq_true_iff.mp checked with
    ⟨identifier, occurrenceNames⟩
  refine
    { identifierNonempty := bne_iff_ne.mp identifier
      occurrenceNamesNonempty := ?_
      occurrenceNamesNodup := ?_
      patternsWellScoped := ?_
      patternsHaveNoCollectionRest := ?_
      patternsHaveCanonicalBinders := ?_ }
  · intro occurrence membership
    exact bne_iff_ne.mp
      (List.all_eq_true.mp occurrenceNames occurrence membership)
  · exact
      (Mettapedia.Util.LinearHash.eraseDupsLength_eq_true_iff_nodup _).mp
        occurrenceNamesUnique
  · exact List.all_eq_true.mp patternsScoped
  · exact List.all_eq_true.mp noCollectionRest
  · exact List.all_eq_true.mp canonicalBinders

private theorem eraseDups_nodup
    {α : Type*} [BEq α] [LawfulBEq α] :
    ∀ values : List α, values.eraseDups.Nodup
  | [] => by simp
  | value :: values => by
      rw [List.eraseDups_cons]
      refine List.nodup_cons.mpr
        ⟨?_, eraseDups_nodup
          (values.filter fun other => !other == value)⟩
      intro member
      rw [List.mem_eraseDups, List.mem_filter] at member
      simp at member
termination_by values => values.length
decreasing_by
  have shorter :=
    List.length_filter_le (fun other => !other == value) values
  simp only [List.length_cons]
  omega

/-- If every metavariable occurrence lies at one binder depth, deduplicating
full occurrence coordinates and then forgetting the depth cannot reintroduce
a duplicate name. -/
private theorem occurrenceNames_nodup_of_same_depth
    (occurrences : List (String × Nat)) (depth : Nat)
    (sameDepth : ∀ occurrence ∈ occurrences, occurrence.2 = depth) :
    ((occurrences.eraseDups).map Prod.fst).Nodup := by
  apply (eraseDups_nodup occurrences).map_on
  intro first firstMembership second secondMembership sameName
  apply Prod.ext sameName
  rw [sameDepth first (List.mem_eraseDups.mp firstMembership),
    sameDepth second (List.mem_eraseDups.mp secondMembership)]

/-- Compositional pattern evidence supplies an inferred-rule admission.  The
same-depth invariant is exactly what makes name-only formal parameters
unambiguous after occurrence-coordinate deduplication. -/
theorem inferredRuleAdmission_of_schemaPatterns
    (rule : ContextualInference.Rule)
    (identifierNonempty : rule.id.value ≠ "")
    (admission : ∀ pattern ∈
      RuleSchema.patterns (ContextualInference.lowerRule rule),
      SchemaPatternAdmission pattern) :
    InferredRuleAdmission rule := by
  let patterns := RuleSchema.patterns (ContextualInference.lowerRule rule)
  have patternsAdmission : SchemaPatternsAdmission patterns :=
    SchemaPatternsAdmission.of_forall patterns admission
  refine
    { identifierNonempty := identifierNonempty
      occurrenceNamesNonempty := ?_
      occurrenceNamesNodup := ?_
      patternsWellScoped := ?_
      patternsHaveNoCollectionRest := ?_
      patternsHaveCanonicalBinders := ?_ }
  · exact patternsAdmission.occurrenceNamesNonempty
  · exact occurrenceNames_nodup_of_same_depth _ 0
      patternsAdmission.metavariablesAtTop
  · intro pattern membership
    exact (admission pattern membership).wellScoped
  · intro pattern membership
    exact (admission pattern membership).noCollectionRest
  · intro pattern membership
    exact (admission pattern membership).canonicalBinders

private theorem eraseDups_eq_self_of_nodup
    {α : Type*} [BEq α] [LawfulBEq α] :
    ∀ {values : List α}, values.Nodup → values.eraseDups = values
  | [], _ => by simp
  | value :: values, nodup => by
      rw [List.eraseDups_cons]
      obtain ⟨absent, tailNodup⟩ := List.nodup_cons.mp nodup
      have retained :
          values.filter (fun other => !other == value) = values := by
        rw [List.filter_eq_self]
        intro other membership
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true,
          beq_eq_false_iff_ne]
        exact fun equality => absent (equality ▸ membership)
      rw [retained, eraseDups_eq_self_of_nodup tailNodup]

/-- Inferring the formal row discharges both directions of the checker's
declaration/occurrence agreement.  Only honest identifier, binder-depth, and
pattern-shape obligations remain. -/
theorem inferMetavariables_locallyValid
    (rule : ContextualInference.Rule)
    (admission : InferredRuleAdmission rule) :
    RuleSchema.isLocallyValid
      (ContextualInference.lowerRule (inferMetavariables rule)) = true := by
  let occurrences :=
    RuleSchema.occurrences (ContextualInference.lowerRule rule)
  have namesNonempty :
      ((occurrences.eraseDups).map Prod.fst).all
          (fun name => name != "") = true := by
    apply List.all_eq_true.mpr
    intro name membership
    obtain ⟨occurrence, occurrenceMembership, rfl⟩ :=
      List.mem_map.mp membership
    rw [bne_iff_ne]
    exact admission.occurrenceNamesNonempty occurrence
      (List.mem_eraseDups.mp occurrenceMembership)
  have namesUnique :
      ((((occurrences.eraseDups).map Prod.fst).eraseDups.length ==
        ((occurrences.eraseDups).map Prod.fst).length) = true) := by
    rw [beq_iff_eq]
    rw [eraseDups_eq_self_of_nodup admission.occurrenceNamesNodup]
  have occurrencesDeclared :
      occurrences.all (fun occurrence =>
        occurrences.eraseDups.contains occurrence) = true := by
    apply List.all_eq_true.mpr
    intro occurrence membership
    exact List.contains_iff_mem.mpr (List.mem_eraseDups.mpr membership)
  have declarationsUsed :
      occurrences.eraseDups.all (fun formal =>
        occurrences.contains formal) = true := by
    apply List.all_eq_true.mpr
    intro formal membership
    exact List.contains_iff_mem.mpr (List.mem_eraseDups.mp membership)
  unfold RuleSchema.isLocallyValid
  simp only [inferMetavariables, ContextualInference.lowerRule,
    RuleSchema.metavariableNames, RuleSchema.occurrences,
    RuleSchema.patterns, bne_iff_ne, Bool.and_eq_true]
  exact
    ⟨⟨⟨⟨⟨⟨⟨admission.identifierNonempty, namesNonempty⟩, namesUnique⟩,
      occurrencesDeclared⟩, declarationsUsed⟩,
      List.all_eq_true.mpr admission.patternsWellScoped⟩,
      List.all_eq_true.mpr admission.patternsHaveNoCollectionRest⟩,
      List.all_eq_true.mpr admission.patternsHaveCanonicalBinders⟩

/-- Carrier resolver for literal authored syntax.  It preserves every modal
carrier name and appends only endpoint carriers absent from that signature. -/
def sourceCarrierAt {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (object : TypeExpr) : String :=
  SelectedNativeTypeSourceIndexedCarrierSupport.resolve demand object

/-- The augmented resolver is definitionally conservative on each selected
rewrite carrier. -/
@[simp] theorem sourceCarrierAt_rewriteType
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    sourceCarrierAt demand (typingAt demand slot).rewriteType =
      carrierAt demand (typingAt demand slot).rewriteType := by
  change
    SelectedNativeTypeSourceIndexedCarrierSupport.resolve demand
        (demand.occurrences.get slot).typing.rewriteType =
      ContextualModalExtension.compiledCarrierName demand.foundation
        (demand.occurrences.get slot).typing.rewriteType
  apply SelectedNativeTypeSourceIndexedCarrierSupport.resolve_eq_modal_of_required
    demand slot
  simp [SelectedNativeTypeFoundation.requiredCarrierRoots]

/-- The augmented resolver is likewise conservative on the selected focus
carrier used by formation and introduction conclusions. -/
@[simp] theorem sourceCarrierAt_focusType
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    sourceCarrierAt demand (typingAt demand slot).focusType =
      carrierAt demand (typingAt demand slot).focusType := by
  change
    SelectedNativeTypeSourceIndexedCarrierSupport.resolve demand
        (demand.occurrences.get slot).typing.focusType =
      ContextualModalExtension.compiledCarrierName demand.foundation
        (demand.occurrences.get slot).typing.focusType
  apply SelectedNativeTypeSourceIndexedCarrierSupport.resolve_eq_modal_of_required
    demand slot
  simp [SelectedNativeTypeFoundation.requiredCarrierRoots]

/-! ## Covered source fragment -/

/-- The source-variable supports covered by the manuscript's `V`/`W`
partition.  A source-indexed extension cannot be constructed until every
selected occurrence has no context/focus overlap. -/
def SupportSeparatedDemand {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) : Prop :=
  ∀ slot : Occurrence demand,
    DisplayedRewriteVariableProfile.sharedNames
      (typingAt demand slot).site = []

/-! ## Exact authored environments -/

/-- Every endpoint variable paired with its authored carrier type, in first
endpoint-occurrence order. -/
def authoredBindings {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    List (String × TypeExpr) :=
  DisplayedRewriteVariableProfile.typedBindings (typingAt demand slot)
    (endpointVariableNames demand slot)

/-- When every endpoint variable is genuinely bound by the authored source,
the typed variable context retains the complete endpoint row in exactly its
first-occurrence order. -/
theorem authoredBindingNames_of_endpointSourceBound
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    (sourceBound : ∀ name ∈ endpointVariableNames demand slot,
      name ∈ (typingAt demand slot).site.rewrite.left.freeFvarNames) :
    (authoredBindings demand slot).map Prod.fst =
      endpointVariableNames demand slot := by
  unfold authoredBindings
  exact DisplayedRewriteVariableProfile.typedBindingNames_of_supported
    (typingAt demand slot) (endpointVariableNames demand slot) sourceBound

/-- Variable-context claims for every occurrence-local authored variable. -/
def authoredVariableClaims {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    List Pattern :=
  (authoredBindings demand slot).map fun binding =>
    ContextualCarrierClaims.variableClaim (sourceCarrierAt demand binding.2)
      (.fvar (renameVariable demand slot binding.1))

/-- The exact authored fixed-context variables, retaining the displayed
telescope order. -/
def authoredRelyValues {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    List Pattern :=
  List.ofFn fun index : Fin (bindingsAt demand slot).length =>
    .fvar (renameVariable demand slot
      ((bindingsAt demand slot).get index).1)

def authoredRelyVariableClaims {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    List Pattern :=
  List.ofFn fun index : Fin (bindingsAt demand slot).length =>
    let binding := (bindingsAt demand slot).get index
    ContextualCarrierClaims.variableClaim (sourceCarrierAt demand binding.2)
      (.fvar (renameVariable demand slot binding.1))

def authoredRelyTypingClaims {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    List Pattern :=
  List.ofFn fun index : Fin (bindingsAt demand slot).length =>
    let binding := (bindingsAt demand slot).get index
    ContextualCarrierClaims.typingClaim (sourceCarrierAt demand binding.2)
      (.fvar (renameVariable demand slot binding.1))
      (.fvar (relyTypeName index.val))

/-- Apply the generated result-family constructor to the exact authored rely
row, rather than to a second row of proxy values. -/
def authoredFamilyApplication {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    (family : Pattern) : Pattern :=
  ContextualFamilyApplication.applyFamily
    (auxiliaryLabel .familyApplication slot.val) family
    (authoredRelyValues demand slot)

def authoredResultSortPremise {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    Sequent :=
  let carrier := sourceCarrierAt demand (typingAt demand slot).rewriteType
  { variableContext := ContextSchema.prepend
      (authoredRelyVariableClaims demand slot) gamma
    relationContext := ContextSchema.prepend
      (authoredRelyTypingClaims demand slot) delta
    conclusion := ContextualCarrierClaims.typingClaim carrier
      (authoredFamilyApplication demand slot (.fvar "result-family"))
      (sortCode carrier (ContextualModalProfile.resultCode
        (occurrenceAt demand slot).profile)) }

/-- Inventory of the generic rely-type names.  The final formal row is
inferred from the complete rule syntax, so this list is proof-facing
provenance rather than a second declaration authority. -/
def relyTypeMetavariables {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    List (String × Nat) :=
  List.ofFn fun index : Fin (bindingsAt demand slot).length =>
    (relyTypeName index.val, 0)

/-- Universe premises for the rely-type row, using this extension's explicit
ambient contexts.  Keeping the tiny constructor local makes rule validation
compositional instead of depending on private implementation constants of an
earlier generator. -/
def relySortPremises {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    List Sequent :=
  List.ofFn fun index : Fin (bindingsAt demand slot).length =>
    let binding := (bindingsAt demand slot).get index
    let carrier := sourceCarrierAt demand binding.2
    { variableContext := gamma
      relationContext := delta
      conclusion := ContextualCarrierClaims.typingClaim carrier
        (.fvar (relyTypeName index.val))
        (sortCode carrier
          ((occurrenceAt demand slot).profile
            (ContextualModalProfile.relySlot (typingAt demand slot) index))) }

/-! ## Paper-faithful rule fragment -/

/-- Open formation syntax before its formal row is inferred. -/
def formationRuleCore {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    ContextualInference.Rule where
  id := ⟨ruleName .formation slot.val⟩
  metavariables := []
  premises :=
    SelectedNativeTypeSourceIndexedIntroduction.relySortPremises demand slot ++
      [authoredResultSortPremise demand slot]
  conclusion :=
    let carrier := sourceCarrierAt demand (typingAt demand slot).focusType
    { variableContext := gamma
      relationContext := delta
      conclusion := ContextualCarrierClaims.typingClaim carrier
        (modalType demand slot (.fvar "result-family"))
        (sortCode carrier (ContextualModalProfile.resultCode
          (occurrenceAt demand slot).profile)) }

/-- A root-like occurrence with no fixed-context bindings has a valid open
formation schema.  The proof is uniform in the authored occurrence and its
universe profile; it checks the generator family rather than enumerating
emitted rows. -/
theorem formationRuleCore_admission_of_bindingsAt_eq_nil
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    (emptyBindings : bindingsAt demand slot = []) :
    InferredRuleAdmission (formationRuleCore demand slot) := by
  refine
    { identifierNonempty := ?_
      occurrenceNamesNonempty := ?_
      occurrenceNamesNodup := ?_
      patternsWellScoped := ?_
      patternsHaveNoCollectionRest := ?_
      patternsHaveCanonicalBinders := ?_ }
  all_goals
    simp [formationRuleCore,
      SelectedNativeTypeSourceIndexedIntroduction.relySortPremises,
      authoredResultSortPremise, authoredRelyValues,
      authoredRelyVariableClaims, authoredRelyTypingClaims,
      authoredFamilyApplication,
      SelectedNativeTypeContextualCalculus.modalType,
      SelectedNativeTypeContextualCalculus.relyTypes,
      SelectedNativeTypeContextualCalculus.sortCode,
      emptyBindings,
      ruleName, RuleKind.tag,
      auxiliaryLabel, AuxiliaryKind.tag,
      ContextualFamilyApplication.applyFamily,
      ContextualCarrierClaims.typingClaim,
      ContextualCarrierClaims.claimLabel,
      ContextualCarrierClaims.ClaimKind.tag,
      ContextualInference.lowerRule, ContextualInference.lowerSequent,
      ContextualInference.encodeContext,
      gamma, delta,
      CarrierUniverseSignature.label, CarrierUniverseSignature.Code.tag,
      RuleSchema.occurrences, RuleSchema.patterns,
      patternMetavariableOccurrencesAt,
      patternsMetavariableOccurrencesAt,
      patternHasNoCollectionRest,
      patternsHaveNoCollectionRest,
      Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt,
      Pattern.hasCanonicalBinderMetadata,
      Pattern.hasCanonicalBinderMetadataList] <;>
    decide

/-- Formation is source-occurrence indexed through its modal label, rely
telescope, and local universe profile.  Its formal row is compiled from those
actual occurrences. -/
def formationRule {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    ContextualInference.Rule :=
  inferMetavariables (formationRuleCore demand slot)

/-- Source-side structural evidence consumed by the binder-free introduction
generator.  These are facts about the independently authored rewrite and
focus, not about the generated rule. -/
structure IntroductionSourceAdmission {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (slot : Occurrence demand) : Prop where
  source : TopLevelPatternAdmission
    (typingAt demand slot).site.rewrite.left
  target : TopLevelPatternAdmission
    (typingAt demand slot).site.rewrite.right
  focus : TopLevelPatternAdmission (typingAt demand slot).site.focus

/-- The body premise of source-indexed introduction, retained separately so
both generation and validity proofs consume the same authored object. -/
def introductionBodyPremise {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (slot : Occurrence demand) : Sequent :=
  { variableContext := ContextSchema.prepend
      (authoredVariableClaims demand slot) gamma
    relationContext := ContextSchema.prepend
      (SelectedNativeTypeOccurrenceStepClaim.claim slot
        (authoredSource demand slot) (authoredTarget demand slot) ::
          authoredRelyTypingClaims demand slot) delta
    conclusion := ContextualCarrierClaims.typingClaim
      (sourceCarrierAt demand (typingAt demand slot).rewriteType)
      (authoredTarget demand slot)
      (authoredFamilyApplication demand slot (.fvar "result-family")) }

/-- Exact source-indexed conclusion of introduction. -/
def introductionConclusion {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (slot : Occurrence demand) : Sequent :=
  { variableContext := gamma
    relationContext := delta
    conclusion := ContextualCarrierClaims.typingClaim
      (sourceCarrierAt demand (typingAt demand slot).focusType)
      (authoredFocus demand slot)
      (modalType demand slot (.fvar "result-family")) }

/-- Open introduction syntax for one exact authored rewrite occurrence.  The
occurrence-step assumption contains the literal authored source and
right-hand side; the body types that right-hand side; the conclusion types
the literal selected focus. -/
def introductionRuleCore {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    ContextualInference.Rule where
  id := ⟨ruleName .introduction slot.val⟩
  metavariables := []
  premises :=
    SelectedNativeTypeSourceIndexedIntroduction.relySortPremises demand slot ++
    [ authoredResultSortPremise demand slot
    , introductionBodyPremise demand slot ]
  conclusion := introductionConclusion demand slot

/-- Root-like, binder-free authored occurrences generate admissible open
introduction schemas.  The proof composes source-pattern, context, claim, and
sequent admissions; it never normalizes the finished rule wholesale. -/
theorem introductionRuleCore_admission_of_source
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    (emptyBindings : bindingsAt demand slot = [])
    (sourceAdmission : IntroductionSourceAdmission demand slot) :
    InferredRuleAdmission (introductionRuleCore demand slot) := by
  have gammaAdmission : SchemaPatternAdmission
      (ContextualInference.encodeContext gamma) := by
    simpa [gamma, ContextualInference.encodeContext] using
      SchemaPatternAdmission.fvar "Gamma" (by decide)
  have deltaAdmission : SchemaPatternAdmission
      (ContextualInference.encodeContext delta) := by
    simpa [delta, ContextualInference.encodeContext] using
      SchemaPatternAdmission.fvar "Delta" (by decide)
  have resultFamilyAdmission :
      SchemaPatternAdmission (.fvar "result-family") :=
    SchemaPatternAdmission.fvar _ (by decide)
  have sortAdmission (carrier : String)
      (code : CarrierUniverseSignature.Code) :
      SchemaPatternAdmission (sortCode carrier code) := by
    apply SchemaPatternAdmission.apply
    simp
  have modalAdmission :
      SchemaPatternAdmission
        (modalType demand slot (.fvar "result-family")) := by
    have applied := SchemaPatternAdmission.apply
      (SelectedModalNaming.label slot.val) [.fvar "result-family"]
      (by
        intro pattern membership
        simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
        subst pattern
        exact resultFamilyAdmission)
    simpa [modalType, relyTypes, emptyBindings] using applied
  have familyAdmission :
      SchemaPatternAdmission
        (authoredFamilyApplication demand slot (.fvar "result-family")) := by
    have applied := SchemaPatternAdmission.apply
      (auxiliaryLabel .familyApplication slot.val) [.fvar "result-family"]
      (by
        intro pattern membership
        simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
        subst pattern
        exact resultFamilyAdmission)
    simpa [authoredFamilyApplication, authoredRelyValues, emptyBindings,
      ContextualFamilyApplication.applyFamily] using applied
  have resultSortVariableContextAdmission : SchemaPatternAdmission
      (ContextualInference.encodeContext
        (authoredResultSortPremise demand slot).variableContext) := by
    simpa [authoredResultSortPremise, authoredRelyVariableClaims,
      emptyBindings] using gammaAdmission
  have resultSortRelationContextAdmission : SchemaPatternAdmission
      (ContextualInference.encodeContext
        (authoredResultSortPremise demand slot).relationContext) := by
    simpa [authoredResultSortPremise, authoredRelyTypingClaims,
      emptyBindings] using deltaAdmission
  have resultSortConclusionAdmission : SchemaPatternAdmission
      (authoredResultSortPremise demand slot).conclusion := by
    apply SchemaPatternAdmission.typingClaim
    · exact familyAdmission
    · exact sortAdmission _ _
  have resultSortAdmission : SchemaPatternAdmission
      (ContextualInference.lowerSequent
        (authoredResultSortPremise demand slot)) :=
    SchemaPatternAdmission.lowerSequent _
      resultSortVariableContextAdmission resultSortRelationContextAdmission
      resultSortConclusionAdmission
  have authoredSourceAdmission : SchemaPatternAdmission
      (authoredSource demand slot) := by
    simpa [authoredSource] using SchemaPatternAdmission.authored demand slot
      (typingAt demand slot).site.rewrite.left sourceAdmission.source
  have authoredTargetAdmission : SchemaPatternAdmission
      (authoredTarget demand slot) := by
    simpa [authoredTarget] using SchemaPatternAdmission.authored demand slot
      (typingAt demand slot).site.rewrite.right sourceAdmission.target
  have authoredFocusAdmission : SchemaPatternAdmission
      (authoredFocus demand slot) := by
    simpa [authoredFocus] using SchemaPatternAdmission.authored demand slot
      (typingAt demand slot).site.focus sourceAdmission.focus
  have variableClaimsAdmission :
      ∀ formula ∈ authoredVariableClaims demand slot,
        SchemaPatternAdmission formula := by
    intro formula membership
    unfold authoredVariableClaims at membership
    obtain ⟨binding, _bindingMembership, rfl⟩ := List.mem_map.mp membership
    apply SchemaPatternAdmission.variableClaim
    exact SchemaPatternAdmission.fvar _
      (renameVariable_ne_empty demand slot binding.1)
  have bodyVariableContextAdmission : SchemaPatternAdmission
      (ContextualInference.encodeContext
        (introductionBodyPremise demand slot).variableContext) := by
    simpa [introductionBodyPremise, gamma] using
      SchemaPatternAdmission.encodeContext_prepend
        (authoredVariableClaims demand slot) "Gamma" (by decide)
        variableClaimsAdmission
  have occurrenceStepAdmission : SchemaPatternAdmission
      (SelectedNativeTypeOccurrenceStepClaim.claim slot
        (authoredSource demand slot) (authoredTarget demand slot)) := by
    apply SchemaPatternAdmission.apply
    intro pattern membership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl
    · exact authoredSourceAdmission
    · exact authoredTargetAdmission
  have bodyRelationContextAdmission : SchemaPatternAdmission
      (ContextualInference.encodeContext
        (introductionBodyPremise demand slot).relationContext) := by
    have combined := SchemaPatternAdmission.encodeContext_prepend
      [SelectedNativeTypeOccurrenceStepClaim.claim slot
        (authoredSource demand slot) (authoredTarget demand slot)]
      "Delta" (by decide)
      (by
        intro pattern membership
        simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
        subst pattern
        exact occurrenceStepAdmission)
    simpa [introductionBodyPremise, authoredRelyTypingClaims,
      emptyBindings, delta] using combined
  have bodyConclusionAdmission : SchemaPatternAdmission
      (introductionBodyPremise demand slot).conclusion :=
    SchemaPatternAdmission.typingClaim _ _ _ authoredTargetAdmission
      familyAdmission
  have bodyAdmission : SchemaPatternAdmission
      (ContextualInference.lowerSequent
        (introductionBodyPremise demand slot)) :=
    SchemaPatternAdmission.lowerSequent _ bodyVariableContextAdmission
      bodyRelationContextAdmission bodyConclusionAdmission
  have finalConclusionAdmission : SchemaPatternAdmission
      (introductionConclusion demand slot).conclusion :=
    SchemaPatternAdmission.typingClaim _ _ _ authoredFocusAdmission
      modalAdmission
  have finalAdmission : SchemaPatternAdmission
      (ContextualInference.lowerSequent
        (introductionConclusion demand slot)) :=
    SchemaPatternAdmission.lowerSequent _ gammaAdmission deltaAdmission
      finalConclusionAdmission
  apply inferredRuleAdmission_of_schemaPatterns
  · simp [introductionRuleCore, ruleName, RuleKind.tag]
  · intro pattern membership
    have normalized : pattern ∈
        [ ContextualInference.lowerSequent
            (authoredResultSortPremise demand slot)
        , ContextualInference.lowerSequent
            (introductionBodyPremise demand slot)
        , ContextualInference.lowerSequent
            (introductionConclusion demand slot) ] := by
      simpa [RuleSchema.patterns, ContextualInference.lowerRule,
        introductionRuleCore,
        SelectedNativeTypeSourceIndexedIntroduction.relySortPremises,
        emptyBindings] using membership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at normalized
    rcases normalized with rfl | rfl | rfl
    · exact resultSortAdmission
    · exact bodyAdmission
    · exact finalAdmission

/-- Closed introduction rule.  The formal arguments are derived from the
paper-faithful literal syntax above, so they cannot drift from the selected
source occurrence. -/
def introductionRule {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    ContextualInference.Rule :=
  inferMetavariables (introductionRuleCore demand slot)

/-- Generator-family admission for one selected source occurrence.  Concrete
profiles prove this once per occurrence; all emitted local-validity results
then follow through the two shared rule constructors. -/
structure OccurrenceAdmission {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (slot : Occurrence demand) : Prop where
  formation : InferredRuleAdmission (formationRuleCore demand slot)
  introduction : InferredRuleAdmission (introductionRuleCore demand slot)

/-- Uniform admission theorem for a binder-free root occurrence.  Concrete
languages need prove only facts about their authored source patterns and the
absence of a fixed rely telescope; validity of both generated rule families
then follows from the shared constructors. -/
theorem occurrenceAdmission_of_root_source
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    (emptyBindings : bindingsAt demand slot = [])
    (sourceAdmission : IntroductionSourceAdmission demand slot) :
    OccurrenceAdmission demand slot :=
  { formation := formationRuleCore_admission_of_bindingsAt_eq_nil
      demand slot emptyBindings
    introduction := introductionRuleCore_admission_of_source
      demand slot emptyBindings sourceAdmission }

/-- Finite input check for both rule families emitted at one selected source
occurrence. -/
def occurrenceAdmissionCheck {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (slot : Occurrence demand) : Bool :=
  inferredRuleAdmissionCheck (formationRuleCore demand slot) &&
    inferredRuleAdmissionCheck (introductionRuleCore demand slot)

/-- Reconstruct generator-family admission from its two finite structural
checks. -/
theorem occurrenceAdmission_of_check {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    (checked : occurrenceAdmissionCheck demand slot = true) :
    OccurrenceAdmission demand slot := by
  simp only [occurrenceAdmissionCheck, Bool.and_eq_true] at checked
  exact
    ⟨inferredRuleAdmission_of_check _ checked.1,
      inferredRuleAdmission_of_check _ checked.2⟩

/-- A successful whole-profile structural check supplies admission for every
selected occurrence without enumerating generated output rules. -/
theorem occurrenceAdmission_of_profile_check
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (checked : (List.ofFn fun slot : Occurrence demand =>
      occurrenceAdmissionCheck demand slot).all id = true) :
    ∀ slot, OccurrenceAdmission demand slot := by
  intro slot
  apply occurrenceAdmission_of_check
  exact List.all_eq_true.mp checked _
    (List.mem_ofFn.mpr ⟨slot, rfl⟩)

/-- Formation local validity is inherited from the shared constructor and its
occurrence admission, rather than recomputed for each generated row. -/
theorem formationRule_locallyValid {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    (admission : InferredRuleAdmission (formationRuleCore demand slot)) :
    RuleSchema.isLocallyValid (lowerRule (formationRule demand slot)) = true := by
  exact inferMetavariables_locallyValid _ admission

/-- Introduction local validity is inherited from the shared constructor and
its occurrence admission, rather than recomputed for each generated row. -/
theorem introductionRule_locallyValid {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    (admission : InferredRuleAdmission (introductionRuleCore demand slot)) :
    RuleSchema.isLocallyValid
      (lowerRule (introductionRule demand slot)) = true := by
  exact inferMetavariables_locallyValid _ admission

def rulesAt {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    List RuleSchema :=
  [lowerRule (formationRule demand slot),
    lowerRule (introductionRule demand slot)]

/-- Both emitted rules at an occurrence pass the local checker from the same
generator-family evidence. -/
theorem rulesAt_locallyValid {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    (admission : OccurrenceAdmission demand slot) :
    (rulesAt demand slot).all RuleSchema.isLocallyValid = true := by
  simp [rulesAt,
    formationRule_locallyValid demand slot admission.formation,
    introductionRule_locallyValid demand slot admission.introduction]

def profiledRules {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) : List RuleSchema :=
  (List.ofFn fun slot : Occurrence demand => rulesAt demand slot).flatten

/-- A profile whose selected occurrences all satisfy the shared admission
generates only locally valid rules.  This theorem is stable under profile
regeneration: it quantifies over occurrences instead of enumerating output
rows. -/
theorem profiledRules_locallyValid {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (admission : ∀ slot, OccurrenceAdmission demand slot) :
    (profiledRules demand).all RuleSchema.isLocallyValid = true := by
  rw [profiledRules, List.all_flatten]
  apply List.all_eq_true.mpr
  intro row rowMembership
  obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp rowMembership
  exact rulesAt_locallyValid demand slot (admission slot)

/-- Elimination is absent, so only result-family application is needed from
the former three-constructor support surface. -/
def familyApplicationTerms {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) : List GrammarRule :=
  List.ofFn fun slot : Occurrence demand =>
    familyApplicationTerm demand slot

/-- Source-dependent delta.  The proof argument makes the covered support
fragment an admission condition rather than an informal side remark. -/
def profileExtension {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (_separated : SupportSeparatedDemand demand) :
    CalculusLanguageExtension where
  newTerms := familyApplicationTerms demand
  newRules := profiledRules demand

/-! ## Structural canaries -/

namespace Canary

open ContextualModalSignature.Canary
open SelectedNativeTypeContextualCalculus.Canary
open SelectedNativeTypeAuthoredOccurrenceSyntax.Canary

private abbrev middleSlot : Occurrence (middleDemand .star) :=
  ⟨0, by simp [middleDemand]⟩

private abbrev middleCarrier : String :=
  sourceCarrierAt (middleDemand .star)
    (.base ContextualModalSignature.Canary.termType.name)

theorem middle_supportSeparated :
    SupportSeparatedDemand (middleDemand .star) := by
  intro slot
  rw [middle_slot_eq_zero .star slot, middle_typingAt]
  apply List.eq_nil_iff_forall_not_mem.mpr
  exact DisplayedRewriteVariableProfile.Canary.middle_has_no_shared_role

theorem middle_authored_metavariables_exact :
    authoredMetavariables (middleDemand .star) middleSlot =
      [(authoredVariableName 0 0, 0), (authoredVariableName 0 1, 0),
        (authoredVariableName 0 2, 0)] := by
  rw [authoredMetavariables, middle_endpointVariableNames]
  rfl

theorem middle_authored_bindings_exact :
    authoredBindings (middleDemand .star) middleSlot =
      [("left", .base ContextualModalSignature.Canary.termType.name),
        ("focus", .base ContextualModalSignature.Canary.termType.name),
        ("right", .base ContextualModalSignature.Canary.termType.name)] := by
  unfold authoredBindings
  rw [middle_endpointVariableNames]
  simp [DisplayedRewriteVariableProfile.typedBindings,
    DisplayedRewriteVariableProfile.variableType?,
    DisplayedRewriteSite.rewrite, ContextualModalSignature.Canary.source,
    ContextualModalSignature.Canary.sourceLanguage,
    ContextualModalSignature.Canary.contextualRewrite,
    WellSorted.FreeTypeContext.ofList]

theorem middle_authored_variable_claims_exact :
    authoredVariableClaims (middleDemand .star) middleSlot =
      [ ContextualCarrierClaims.variableClaim middleCarrier
          (.fvar (authoredVariableName 0 0))
      , ContextualCarrierClaims.variableClaim middleCarrier
          (.fvar (authoredVariableName 0 1))
      , ContextualCarrierClaims.variableClaim middleCarrier
          (.fvar (authoredVariableName 0 2)) ] := by
  rw [authoredVariableClaims, middle_authored_bindings_exact]
  simp only [List.map_cons, List.map_nil]
  unfold renameVariable
  rw [middle_endpointVariableNames]
  rfl

theorem middle_authored_rely_values_exact :
    authoredRelyValues (middleDemand .star) middleSlot =
      [.fvar (authoredVariableName 0 0),
        .fvar (authoredVariableName 0 2)] := by
  simp [authoredRelyValues, middle_bindingsAt, renameVariable,
    middle_endpointVariableNames]

theorem middle_authored_rely_variable_claims_exact :
    authoredRelyVariableClaims (middleDemand .star) middleSlot =
      [ ContextualCarrierClaims.variableClaim middleCarrier
          (.fvar (authoredVariableName 0 0))
      , ContextualCarrierClaims.variableClaim middleCarrier
          (.fvar (authoredVariableName 0 2)) ] := by
  simp [authoredRelyVariableClaims, middle_bindingsAt, renameVariable,
    middle_endpointVariableNames]

theorem middle_authored_rely_typing_claims_exact :
    authoredRelyTypingClaims (middleDemand .star) middleSlot =
      [ ContextualCarrierClaims.typingClaim middleCarrier
          (.fvar (authoredVariableName 0 0)) (.fvar (relyTypeName 0))
      , ContextualCarrierClaims.typingClaim middleCarrier
          (.fvar (authoredVariableName 0 2)) (.fvar (relyTypeName 1)) ] := by
  simp [authoredRelyTypingClaims, middle_bindingsAt, renameVariable,
    middle_endpointVariableNames]

theorem middle_rely_type_metavariables_exact :
    relyTypeMetavariables (middleDemand .star) middleSlot =
      [(relyTypeName 0, 0), (relyTypeName 1, 0)] := by
  simp [relyTypeMetavariables, middle_bindingsAt]

/-- The repaired rule concludes with the exact selected source component. -/
theorem middle_conclusion_subject_exact :
    (introductionRule (middleDemand .star) middleSlot).conclusion.conclusion =
      ContextualCarrierClaims.typingClaim
        (sourceCarrierAt (middleDemand .star)
          (typingAt (middleDemand .star) middleSlot).focusType)
        (authoredFocus (middleDemand .star) middleSlot)
        (modalType (middleDemand .star) middleSlot
          (.fvar "result-family")) := by
  rfl

/-- The repaired body checks the exact authored right-hand side. -/
theorem middle_body_subject_exact :
    (introductionRule (middleDemand .star) middleSlot).premises.getLast?.map
        Sequent.conclusion =
      some (ContextualCarrierClaims.typingClaim
        (sourceCarrierAt (middleDemand .star)
          (typingAt (middleDemand .star) middleSlot).rewriteType)
        (authoredTarget (middleDemand .star) middleSlot)
        (authoredFamilyApplication (middleDemand .star) middleSlot
          (.fvar "result-family"))) := by
  simp [introductionRule, introductionRuleCore, introductionBodyPremise]

/-- The exact-occurrence step assumption names both authored endpoints and
cannot collapse to an unindexed reduction claim. -/
theorem middle_body_occurrence_step_head_exact :
    (introductionRule (middleDemand .star) middleSlot).premises.getLast?.map
        (fun premise => premise.relationContext) =
      some (ContextSchema.prepend
        (SelectedNativeTypeOccurrenceStepClaim.claim middleSlot
          (authoredSource (middleDemand .star) middleSlot)
          (authoredTarget (middleDemand .star) middleSlot) ::
            authoredRelyTypingClaims (middleDemand .star) middleSlot)
        delta) := by
  simp [introductionRule, introductionRuleCore, introductionBodyPremise]

private theorem middle_introduction_core_admission :
    InferredRuleAdmission
      (introductionRuleCore (middleDemand .star) middleSlot) := by
  refine
    { identifierNonempty := ?_
      occurrenceNamesNonempty := ?_
      occurrenceNamesNodup := ?_
      patternsWellScoped := ?_
      patternsHaveNoCollectionRest := ?_
      patternsHaveCanonicalBinders := ?_ }
  all_goals
    simp [introductionRuleCore, introductionBodyPremise,
      introductionConclusion, middle_authored_variable_claims_exact,
      middle_authored_rely_values_exact,
      middle_authored_rely_variable_claims_exact,
      middle_authored_rely_typing_claims_exact,
      authoredResultSortPremise,
      SelectedNativeTypeSourceIndexedIntroduction.relySortPremises,
      authoredFamilyApplication, modalType, relyTypes, sortCode,
      middle_authoredSource_exact, middle_authoredTarget_exact,
      middle_authoredFocus_exact, middle_typingAt, middle_bindingsAt,
      sourceCarrierAt, SelectedNativeTypeSourceIndexedCarrierSupport.resolve,
      auxiliaryLabel, AuxiliaryKind.tag, ruleName,
      RuleKind.tag, relyTypeName, indexedMetavariable,
      ContextualFamilyApplication.applyFamily,
      ContextualCarrierClaims.variableClaim,
      ContextualCarrierClaims.typingClaim,
      SelectedNativeTypeOccurrenceStepClaim.claim,
      SelectedNativeTypeOccurrenceStepClaim.Naming.label,
      ContextualCarrierClaims.claimLabel,
      ContextualCarrierClaims.ClaimKind.tag,
      ContextualInference.lowerRule, ContextualInference.lowerSequent,
      ContextualInference.encodeContext, ContextSchema.prepend, gamma, delta,
      CarrierUniverseSignature.label, CarrierUniverseSignature.Code.tag,
      RuleSchema.occurrences, RuleSchema.patterns,
      patternMetavariableOccurrencesAt,
      patternsMetavariableOccurrencesAt, patternHasNoCollectionRest,
      patternsHaveNoCollectionRest, Pattern.isWellScoped,
      Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
      Pattern.hasCanonicalBinderMetadata,
      Pattern.hasCanonicalBinderMetadataList,
      authoredVariableName, Nat.pair] <;>
    decide

/-- The harder non-root witness passes the ordinary local schema gate without
resource overrides. -/
theorem middle_introduction_locallyValid :
    RuleSchema.isLocallyValid
      (lowerRule (introductionRule (middleDemand .star) middleSlot)) = true := by
  exact inferMetavariables_locallyValid _
    middle_introduction_core_admission

/-- The repaired introduction is observably different from the earlier proxy
rule even before a semantic interpretation is chosen. -/
theorem middle_introduction_ne_proxy :
    introductionRule (middleDemand .star) middleSlot ≠
      SelectedNativeTypeContextualCalculus.introductionRule
        (middleDemand .star) middleSlot := by
  intro equality
  have conclusions := congrArg
    (fun rule : ContextualInference.Rule => rule.conclusion.conclusion) equality
  have subjectEquality :
      authoredFocus (middleDemand .star) middleSlot = .fvar "focus" := by
    simpa [introductionRule, introductionRuleCore, introductionConclusion,
      SelectedNativeTypeContextualCalculus.introductionRule,
      ContextualCarrierClaims.typingClaim] using conclusions
  exact middle_authoredFocus_ne_private_focus subjectEquality

/-- Universe level remains a separate, load-bearing profile coordinate in
formation. -/
theorem middle_formation_conclusions_distinct :
    (formationRule (middleDemand .star) middleSlot).conclusion ≠
      (formationRule (middleDemand .box)
        ⟨0, by simp [middleDemand]⟩).conclusion := by
  intro equality
  have conclusionEquality := congrArg Sequent.conclusion equality
  injection conclusionEquality with _ argumentsEquality
  injection argumentsEquality with _ tailEquality
  injection tailEquality with typeEquality _
  change
    sortCode
        (sourceCarrierAt (middleDemand .star)
          (typingAt (middleDemand .star) middleSlot).focusType)
        .star =
      sortCode
        (sourceCarrierAt (middleDemand .box)
          (typingAt (middleDemand .box)
            ⟨0, by simp [middleDemand]⟩).focusType)
        .box at typeEquality
  unfold sortCode at typeEquality
  injection typeEquality with labels _
  exact CarrierUniverseSignature.star_label_ne_box_label _ _ labels

/-- The covered fragment emits exactly formation and introduction; the
unrepaired eliminator is not hidden in the extension. -/
theorem middle_extension_inventory :
    (profileExtension (middleDemand .star) middle_supportSeparated).newTerms.length = 1 ∧
      (profileExtension (middleDemand .star) middle_supportSeparated).newRules.length = 2 := by
  exact ⟨rfl, rfl⟩

/-- The negative shared-variable witness lies outside the public extension's
admitted fragment. -/
theorem repeated_variable_site_not_separated :
    DisplayedRewriteVariableProfile.sharedNames
        DisplayedRewriteSite.Canary.firstOccurrence ≠ [] := by
  intro empty
  have membership :=
    (DisplayedRewriteVariableProfile.Canary.repeated_variable_is_shared
      "x").2 rfl
  simp [empty] at membership

end Canary

#print axioms Canary.middle_supportSeparated
#print axioms Canary.middle_conclusion_subject_exact
#print axioms Canary.middle_body_subject_exact
#print axioms Canary.middle_body_occurrence_step_head_exact
#print axioms Canary.middle_introduction_locallyValid
#print axioms Canary.middle_introduction_ne_proxy
#print axioms Canary.middle_formation_conclusions_distinct
#print axioms Canary.middle_extension_inventory
#print axioms Canary.repeated_variable_site_not_separated

end Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedIntroduction
