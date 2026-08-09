import Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLT
import Mettapedia.GSLT.LanguageDef.CalculusExtension
import Mettapedia.GSLT.LanguageDef.ExtensionGluing

/-!
# The PeTTa type system, composed out of four interacting layers

`TypeSystemGSLT` presents a term language and one proof calculus of twenty-one
rules over five judgment forms.  This module rebuilds that calculus from four
layers and recovers its admission from theirs, so the presentation is assembled
rather than asserted.

The dependency structure is a genuine directed graph, not a chain:

```
                union-membership
                 /            \
        consistency          value typing
   (Consistent, ConsistentList)     |
                                guard
```

* **union-membership** is self-contained.
* **consistency** and **value typing** are independent siblings: each uses
  union membership, neither uses the other.  `valueTyping_independent_of_consistency`
  proves the sibling claim rather than leaving it to the eye.
* **guard** uses value typing, and nothing else.

Two composition modes appear, and both are needed.  Siblings over a shared base
are the amalgamated case; guard-over-value-typing is the staged case, where a
later layer freely uses judgments an earlier one introduced.  `Compatible`
cannot describe the staged case — a layer that uses another's judgments is not
admitted alone — which is why admission here is *relative to an accumulated
base*.  The calculus-specific receipts below are also lifted to the generic
`ContextualAdmission` class, whose stacking theorem is driven by the
concatenation law of the authoring GSLT.

The negatives are what make the layering load-bearing rather than decorative:
`consistency_not_admitted_alone` and `guard_not_admitted_alone` show that two of
the four layers are genuinely inadmissible on their own, so the order of
assembly is carrying real weight.

Finally `assembledSource` concatenates the four authored calculus documents.
Its elaboration is exactly the live calculus, its admitted total object erases
to the unchanged PeTTa term language, and derivability in that calculus is
equivalent to reachability in its derived proof-search GSLT.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLTLayers

open Mettapedia.GSLT
open Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLT
open Mettapedia.GSLT.LanguageDef.InferenceExtension
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.ExtensionComposition
open Mettapedia.GSLT.LanguageDef.ExtensionGluing
open Mettapedia.GSLT.LanguageDef.CalculusExtension
open Mettapedia.GSLT.LanguageDef.CalculusAsLanguage
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## The four layers -/

/-- Membership in a union type.  Self-contained: its one recursive rule uses
only its own judgment. -/
def unionLayer : ProofCalculus where
  judgments := [{ head := "UnionMember", arity := 2 }]
  rules := [unionMemberHere, unionMemberThere]

/-- Static consistency, together with its componentwise list judgment.  The two
are mutually recursive, so they are one layer and not two. -/
def consistencyLayer : ProofCalculus where
  judgments :=
    [{ head := "Consistent", arity := 3 },
     { head := "ConsistentList", arity := 2 }]
  rules :=
    [consistentRefl, consistentDynLeft, consistentDynRight,
     consistentUnionRight, consistentUnionLeft, consistentBrand,
     consistentArrow, consistentListNil, consistentListCons]

/-- The dynamic judgment.  It uses union membership and nothing from the
consistency layer. -/
def valueTypingLayer : ProofCalculus where
  judgments := [{ head := "ValueHasType", arity := 2 }]
  rules :=
    [hasTypeNum, hasTypeStr, hasTypeTrue, hasTypeFalse,
     hasTypeWildcard, hasTypeUnion, hasTypeBrand,
     hasTypeNilList, hasTypeConsList]

/-- The transient cast, one rule over value typing. -/
def guardLayer : ProofCalculus where
  judgments := [{ head := "GuardPasses", arity := 2 }]
  rules := [guardPassesRule]

/-! ## Authored component GSLTs -/

/-- Canonical authored document for union membership. -/
def unionSource : CalculusSyntax := quote unionLayer

/-- Canonical authored document for consistency. -/
def consistencySource : CalculusSyntax := quote consistencyLayer

/-- Canonical authored document for value typing. -/
def valueTypingSource : CalculusSyntax := quote valueTypingLayer

/-- Canonical authored document for the guard judgment. -/
def guardSource : CalculusSyntax := quote guardLayer

/-- The four calculus GSLT documents composed by the term-former supplied by
`calculusSyntax`. -/
def assembledSource : CalculusSyntax :=
  calculusSyntax.append consistencySource
    (calculusSyntax.append unionSource
      (calculusSyntax.append valueTypingSource guardSource))

/-! ## Assembly -/

/-- Consistency, then union membership, then value typing, then guard. -/
def assembled : ProofCalculus :=
  mergeOf consistencyLayer (mergeOf unionLayer (mergeOf valueTypingLayer guardLayer))

/-- The accumulated form, in which each layer is added to everything before it. -/
def accumulated : ProofCalculus :=
  mergeOf (mergeOf (mergeOf consistencyLayer unionLayer) valueTypingLayer) guardLayer

/-- **The four layers are the authored calculus.**  Same declarations, same
order, nothing added and nothing dropped. -/
theorem layers_assemble : assembled = calculus := rfl

/-- Assembling and accumulating agree, which is merge associativity on this
instance. -/
theorem accumulated_eq_assembled : accumulated = assembled := by
  unfold accumulated assembled
  rw [← mergeOf_assoc, ← mergeOf_assoc]

/-! ## Admission, stage by stage

Each stage reuses the receipt recipe of the authored presentation; only the
calculus under test changes. -/

local macro "admissionSimp" : tactic =>
  `(tactic| simp [mergeOf, ProofCalculus.empty, AdmittedOver,
      unionLayer, consistencyLayer, valueTypingLayer, guardLayer,
      Presentation.ruleIds, Presentation.judgmentSignatureValid,
      Presentation.judgmentHeads, Presentation.conversionDeclarationValid,
      Presentation.lookupJudgment?, RuleSchema.isValidIn,
      RuleSchema.isValidV1,
      RuleSchema.metavariableNames, RuleSchema.occurrences, RuleSchema.patterns,
      patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
      patternHasNoCollectionRest, patternsHaveNoCollectionRest,
      Presentation.judgmentSchemaValid, fixedConstructorsValid,
      fixedConstructorListsValid, languageHasConstructorArity,
      Pattern.isWellScoped, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
      Pattern.hasCanonicalBinderMetadata,
      Pattern.hasCanonicalBinderMetadataList, Pattern.zipHead, Pattern.mapHead,
      Pattern.evalHead, language, termType, termConstructor,
      consistentRefl, consistentDynLeft, consistentDynRight,
      consistentUnionRight, consistentUnionLeft, consistentBrand,
      consistentArrow, consistentListNil, consistentListCons,
      unionMemberHere, unionMemberThere, hasTypeNum, hasTypeStr, hasTypeTrue,
      hasTypeFalse, hasTypeWildcard, hasTypeUnion, hasTypeBrand,
      hasTypeNilList, hasTypeConsList, guardPassesRule,
      consistent, consistentList, unionMember, valueHasType, guardPasses,
      tNum, tStr, tBool, tUndefined, tNil, tCons, tUnion, tArrow, tBrand,
      tList, edgeExact, edgeStructural,
      edgeDynamic, vNum, vStr, vTrue, vFalse, vNil, vCons,
      ruleId])

private theorem languageValidate : language.validate = [] := language_validate

/-- Union membership is admitted on its own. -/
theorem union_admitted :
    AdmittedOver language .empty unionLayer := by
  unfold AdmittedOver Presentation.isValidV2 Presentation.isValidV1
  rw [show (Presentation.mk language (mergeOf .empty unionLayer)).language.validate
      = [] from languageValidate]
  admissionSimp
  decide

/-- Consistency is admitted once union membership is present. -/
theorem consistency_admitted_over_union :
    AdmittedOver language unionLayer consistencyLayer := by
  unfold AdmittedOver Presentation.isValidV2 Presentation.isValidV1
  rw [show (Presentation.mk language (mergeOf unionLayer consistencyLayer)).language.validate
      = [] from languageValidate]
  admissionSimp
  decide

/-- **The sibling claim.**  Value typing is admitted over union membership
alone: it does not need the consistency layer.  This is the branch in the
dependency graph, proved rather than observed. -/
theorem valueTyping_independent_of_consistency :
    AdmittedOver language unionLayer valueTypingLayer := by
  unfold AdmittedOver Presentation.isValidV2 Presentation.isValidV1
  rw [show (Presentation.mk language (mergeOf unionLayer valueTypingLayer)).language.validate
      = [] from languageValidate]
  admissionSimp
  decide

/-- Stage one: consistency and union membership together. -/
theorem stageOne :
    AdmittedOver language .empty (mergeOf consistencyLayer unionLayer) := by
  unfold AdmittedOver Presentation.isValidV2 Presentation.isValidV1
  rw [show (Presentation.mk language
      (mergeOf .empty (mergeOf consistencyLayer unionLayer))).language.validate
      = [] from languageValidate]
  admissionSimp
  decide

/-- Stage two: value typing over what stage one accumulated. -/
theorem stageTwo :
    AdmittedOver language (mergeOf consistencyLayer unionLayer) valueTypingLayer := by
  unfold AdmittedOver Presentation.isValidV2 Presentation.isValidV1
  rw [show (Presentation.mk language
      (mergeOf (mergeOf consistencyLayer unionLayer) valueTypingLayer)).language.validate
      = [] from languageValidate]
  admissionSimp
  decide

/-- Stage three: the guard over what stage two accumulated. -/
theorem stageThree :
    AdmittedOver language
      (mergeOf (mergeOf consistencyLayer unionLayer) valueTypingLayer) guardLayer := by
  unfold AdmittedOver Presentation.isValidV2 Presentation.isValidV1
  rw [show (Presentation.mk language accumulated).language.validate
      = [] from languageValidate]
  admissionSimp
  decide

/-! ## The same stages through generic contextual admission

The preceding propositions use the established total `mergeOf` notation.  The
generic class retains the stronger authored fact that the partial merge
actually succeeds.  For these concrete layers the declarations are fresh and
none claims rooted conversion authority, so the two readings coincide. -/

private theorem stageOne_compatible :
    Compatible .empty (mergeOf consistencyLayer unionLayer) := by
  constructor <;>
    simp [ProofCalculus.empty, mergeOf, consistencyLayer, unionLayer]

private theorem stageTwo_compatible :
    Compatible (mergeOf consistencyLayer unionLayer) valueTypingLayer := by
  constructor <;>
    simp [mergeOf, consistencyLayer, unionLayer, valueTypingLayer,
      consistentRefl, consistentDynLeft, consistentDynRight,
      consistentUnionRight, consistentUnionLeft, consistentBrand,
      consistentArrow, consistentListNil, consistentListCons,
      unionMemberHere, unionMemberThere, hasTypeNum, hasTypeStr,
      hasTypeTrue, hasTypeFalse, hasTypeWildcard, hasTypeUnion,
      hasTypeBrand, hasTypeNilList, hasTypeConsList, ruleId]

private theorem stageThree_compatible :
    Compatible
      (mergeOf (mergeOf consistencyLayer unionLayer) valueTypingLayer)
      guardLayer := by
  constructor <;>
    simp [mergeOf, consistencyLayer, unionLayer, valueTypingLayer, guardLayer,
      consistentRefl, consistentDynLeft, consistentDynRight,
      consistentUnionRight, consistentUnionLeft, consistentBrand,
      consistentArrow, consistentListNil, consistentListCons,
      unionMemberHere, unionMemberThere, hasTypeNum, hasTypeStr,
      hasTypeTrue, hasTypeFalse, hasTypeWildcard, hasTypeUnion,
      hasTypeBrand, hasTypeNilList, hasTypeConsList, guardPassesRule, ruleId]

/-- The first accumulated stage is accepted by the generic, partial-merge
admission class. -/
theorem stageOne_compositional :
    CompositionalAdmittedOver language .empty
      (mergeOf consistencyLayer unionLayer) :=
  (compositionalAdmittedOver_iff language stageOne_compatible).2 stageOne

/-- Value typing is admitted over the first accumulated stage through the
same generic class. -/
theorem stageTwo_compositional :
    CompositionalAdmittedOver language
      (mergeOf consistencyLayer unionLayer) valueTypingLayer :=
  (compositionalAdmittedOver_iff language stageTwo_compatible).2 stageTwo

/-- The guard is admitted over the second accumulated stage through the same
generic class. -/
theorem stageThree_compositional :
    CompositionalAdmittedOver language
      (mergeOf (mergeOf consistencyLayer unionLayer) valueTypingLayer)
      guardLayer :=
  (compositionalAdmittedOver_iff language stageThree_compatible).2 stageThree

/-- **Generic stacking has the expected concrete result.**  The reusable
`ContextualAdmission` theorem combines the last stage with the empty authored
base; uniqueness of `Option.some` identifies its payload with `accumulated`.
This is a use of the general class, not a restatement of the PeTTa validator. -/
theorem accumulated_compositional :
    CompositionalAdmittedOver language .empty accumulated := by
  have baseMerge :
      calculusAuthoringGSLT.merge .empty
          (mergeOf (mergeOf consistencyLayer unionLayer) valueTypingLayer) =
        some (mergeOf (mergeOf consistencyLayer unionLayer) valueTypingLayer) :=
    calculusAuthoringGSLT.toPartialMonoid.unit_op _
  obtain ⟨combined, combinedMerge, admitted⟩ :=
    GSLT.ContextualAdmission.admittedOver_stack
      (calculusAdmission language) baseMerge stageThree_compositional
  have canonical := append_eq_mergeOf stageThree_compatible
  change proofCalculusMonoid.op
      (mergeOf (mergeOf consistencyLayer unionLayer) valueTypingLayer)
      guardLayer = some combined at combinedMerge
  rw [canonical] at combinedMerge
  cases combinedMerge
  exact admitted

/-! ## Negatives: the layering carries weight

Two of the four layers are inadmissible on their own, because each uses a
judgment another layer introduces.  So the staged reading is not a convenience
over an already-valid partition. -/

/-- Consistency alone is rejected: its union rules use a judgment it does not
declare. -/
theorem consistency_not_admitted_alone :
    ¬ AdmittedOver language .empty consistencyLayer := by
  intro admitted
  unfold AdmittedOver Presentation.isValidV2 at admitted
  simp only [Bool.and_eq_true] at admitted
  have rulesAdmitted := admitted.1.2
  have rulesFail :
      (Presentation.mk language (mergeOf .empty consistencyLayer)).rules.all
        (RuleSchema.isValidIn (Presentation.mk language (mergeOf .empty consistencyLayer)))
        = false := by
    admissionSimp
  rw [rulesFail] at rulesAdmitted
  exact Bool.noConfusion rulesAdmitted

/-- The guard alone is rejected: it uses the dynamic judgment it does not
declare. -/
theorem guard_not_admitted_alone :
    ¬ AdmittedOver language .empty guardLayer := by
  intro admitted
  unfold AdmittedOver Presentation.isValidV2 at admitted
  simp only [Bool.and_eq_true] at admitted
  have rulesAdmitted := admitted.1.2
  have rulesFail :
      (Presentation.mk language (mergeOf .empty guardLayer)).rules.all
        (RuleSchema.isValidIn (Presentation.mk language (mergeOf .empty guardLayer)))
        = false := by
    admissionSimp
  rw [rulesFail] at rulesAdmitted
  exact Bool.noConfusion rulesAdmitted

/-! ## The authored receipt, recovered from the layers -/

/-- **The presentation's admission follows from the staged one.**  The original
receipt is not assumed here; it is rebuilt from four layers that were each
admitted against what came before. -/
theorem presentation_valid_from_layers : presentation.isValidV2 = true := by
  have staged := stageThree
  unfold AdmittedOver at staged
  rwa [show mergeOf (mergeOf (mergeOf consistencyLayer unionLayer) valueTypingLayer)
      guardLayer = calculus from
    (accumulated_eq_assembled.trans layers_assemble)] at staged

/-! ## The live calculus through the generic realization contract -/

/-- The staged admission receipt as a point of the canonical contextual
calculus fibre. -/
def admittedTypeSystem : AdmittedCalculusAt language :=
  ⟨calculus, presentation_valid_from_layers⟩

/-- Recovering a validated presentation from the admitted fibre gives the
existing PeTTa presentation exactly. -/
theorem admittedTypeSystem_checked :
    admittedTypeSystem.checked language = checked := by
  apply Subtype.ext
  rfl

/-- The generic certified realization is the live PeTTa proof-search engine:
it accepts exactly the goal lists inhabited by the staged calculus. -/
theorem proofSearchRealization_live (goals : GoalState) :
    proofSearchRealization.compile language admittedTypeSystem goals ↔
      Nonempty (DerivationList checked goals) := by
  simpa [admittedTypeSystem_checked] using
    proofSearchRealization_adequate language admittedTypeSystem goals

/-! ## The conservative-extension square for the real calculus -/

/-- Concatenating the four authored documents elaborates to exactly the live
twenty-one-rule calculus. -/
theorem assembledSource_elaborates :
    elaborate assembledSource = some calculus := by
  change elaborate
    (consistencySource ++
      (unionSource ++ (valueTypingSource ++ guardSource))) = some calculus
  rw [elaborate_append, elaborate_append, elaborate_append]
  simp [consistencySource, unionSource, valueTypingSource, guardSource,
    ProofCalculus.append?, consistencyLayer, unionLayer, valueTypingLayer,
    guardLayer, calculus]

/-- The authored document builds the exact live checker `Presentation`. -/
theorem assembledSource_definition :
    elaborateDefinition? language assembledSource = some presentation := by
  simp [elaborateDefinition?, assembledSource_elaborates, presentation]

/-- The authored document passes admission as the live checked definition. -/
theorem assembledSource_admitted :
    admit? language assembledSource = some checked := by
  unfold admit?
  rw [assembledSource_definition]
  simp [Presentation.validateV2?, checked, presentation_valid]

/-- **Flagship conservative-extension theorem.**  The composed authored GSLT
preserves the exact PeTTa term language, elaborates to the exact live calculus,
and reduces every derivability question to reachability in a genuine GSLT. -/
theorem typeSystem_conservativeExtension (goals : GoalState) :
    checked.1.erase = language ∧
      elaborate assembledSource = some checked.1.calculus ∧
      (Nonempty (DerivationList checked goals) ↔
        (proofSearchGSLT checked).MultiStep goals []) :=
  admitted_source_adequacy assembledSource_admitted goals

/-- Positive operational witness: the existing checked PeTTa proof of
`VNum : TNum` becomes a proof-search reduction to no obligations. -/
theorem value_num_proofSearch :
    (proofSearchGSLT checked).MultiStep
      [valueHasType vNum tNum] [] :=
  (derivation_nonempty_iff_proofSearch checked
    (valueHasType vNum tNum)).mp
      (checkRaw_soundness value_num_has_type_number)

/-- The same nontrivial PeTTa theorem passes through the common realization
interface used by staged backends. -/
theorem value_num_realization :
    proofSearchRealization.compile language admittedTypeSystem
      [valueHasType vNum tNum] := by
  apply (proofSearchRealization_live _).2
  obtain ⟨derivation⟩ := checkRaw_soundness value_num_has_type_number
  exact ⟨.cons derivation .nil⟩

/-- The composed source really carries all twenty-one rule declarations. -/
theorem assembled_rule_count :
    (Option.get (elaborate assembledSource)
      (by simp [assembledSource_elaborates])).rules.length = 21 := by
  rw [show Option.get (elaborate assembledSource)
      (by simp [assembledSource_elaborates]) = calculus by
    simp [assembledSource_elaborates]]
  rfl

end Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLTLayers
