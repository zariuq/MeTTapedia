import Mettapedia.GSLT.LanguageDef.ProofGSLTInterpretation

/-!
# Proof-relevant, judgment-translating interpretations

`ProofGSLT.Interpretation` realizes one source rule by a target open
derivation with exactly the same premise and conclusion judgments.  This file
adds the non-functional layer needed when elaboration changes judgments or
when the target chosen for a conclusion depends on retained translations of
the premises.

The relation between source and target judgments is `Type`-valued.  Mapping a
derivation therefore returns the translated target judgment, the retained
relation witness, and the target derivation.  Composition retains the
intermediate judgment and both witnesses.  Its relation fibers associate by
a canonical equivalence rather than by erasing the intermediate evidence.

This is a rule-generated translation: the action on derivations is derived
recursively from `onRule`; it is not an opaque preservation callback.
-/

namespace Mettapedia.GSLT.LanguageDef.ProofGSLT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker

universe u

/-- Ordered target judgments together with a retained translation witness
for every source judgment occurrence. -/
inductive RelatedContext
    (Related : Pattern → Pattern → Type u) : List Pattern → Type u where
  | nil : RelatedContext Related []
  | cons {source : Pattern} {sources : List Pattern}
      (target : Pattern) (head : Related source target)
      (tail : RelatedContext Related sources) :
      RelatedContext Related (source :: sources)

namespace RelatedContext

/-- The ordered target context selected by the retained witnesses. -/
def targets {Related : Pattern → Pattern → Type u} :
    {sources : List Pattern} → RelatedContext Related sources → List Pattern
  | _, .nil => []
  | _, .cons target _ tail => target :: tail.targets

/-- The target occurrence corresponding to one source occurrence. -/
def targetIndex {Related : Pattern → Pattern → Type u}
    {sources : List Pattern} (context : RelatedContext Related sources)
    (index : Fin sources.length) : Fin context.targets.length :=
  match context with
  | .nil => Fin.elim0 index
  | .cons _ _ tail =>
      Fin.cases ⟨0, by simp [targets]⟩
        (fun tailIndex => (tail.targetIndex tailIndex).succ) index

/-- Recover the relation witness at an ordered premise occurrence. -/
def relatedAt {Related : Pattern → Pattern → Type u}
    {sources : List Pattern} (context : RelatedContext Related sources)
    (index : Fin sources.length) :
    Related (sources.get index)
      (context.targets.get (context.targetIndex index)) :=
  by
    cases context with
    | nil => exact Fin.elim0 index
    | cons target head tail =>
        exact Fin.cases head (fun tailIndex => tail.relatedAt tailIndex) index

end RelatedContext

/-- A proof-relevant interpretation may change a judgment.  For each source
rule application and each ordered choice of related target premises it builds
a target conclusion, a witness relating the conclusions, and an open target
derivation from those selected premises. -/
structure RelationalInterpretation (source target : Object) where
  Related : Pattern → Pattern → Type u
  onRule :
    ∀ (ruleInstance : RuleInstance) {premises : List Pattern}
      {conclusion : Pattern},
      RuleApplication source.presentation ruleInstance premises conclusion →
      (premiseTargets : RelatedContext Related premises) →
      Σ targetConclusion,
        Related conclusion targetConclusion ×
          OpenDerivation target.presentation premiseTargets.targets
            targetConclusion

namespace RelationalInterpretation

/-- Result of translating one open source derivation into a fixed selected
target premise context. -/
structure OpenResult {source target : Object}
    (interpretation : RelationalInterpretation.{u} source target)
    (targetContext : List Pattern) (sourceGoal : Pattern) where
  targetGoal : Pattern
  related : interpretation.Related sourceGoal targetGoal
  derivation : OpenDerivation target.presentation targetContext targetGoal

/-- Result of translating one closed source derivation. -/
structure ClosedResult {source target : Object}
    (interpretation : RelationalInterpretation.{u} source target)
    (sourceGoal : Pattern) where
  targetGoal : Pattern
  related : interpretation.Related sourceGoal targetGoal
  derivation : Derivation target.presentation targetGoal

/-- Ordered translation results for rule premises. -/
inductive OpenResultList {source target : Object}
    (interpretation : RelationalInterpretation.{u} source target)
    (targetContext : List Pattern) : List Pattern → Type u where
  | nil : OpenResultList interpretation targetContext []
  | cons {sourceGoal : Pattern} {sourceGoals : List Pattern}
      (head : OpenResult interpretation targetContext sourceGoal)
      (tail : OpenResultList interpretation targetContext sourceGoals) :
      OpenResultList interpretation targetContext (sourceGoal :: sourceGoals)

namespace OpenResultList

/-- The ordered target goals selected while translating the source vector. -/
def targetGoals {source target : Object}
    {interpretation : RelationalInterpretation.{u} source target}
    {targetContext : List Pattern} :
    {sourceGoals : List Pattern} →
      OpenResultList interpretation targetContext sourceGoals → List Pattern
  | _, .nil => []
  | _, .cons head tail => head.targetGoal :: tail.targetGoals

/-- Package all pointwise relation witnesses as one related context. -/
def relatedContext {source target : Object}
    {interpretation : RelationalInterpretation.{u} source target}
    {targetContext : List Pattern} :
    {sourceGoals : List Pattern} →
      (results : OpenResultList interpretation targetContext sourceGoals) →
      RelatedContext interpretation.Related sourceGoals
  | _, .nil => .nil
  | _, .cons head tail =>
      .cons head.targetGoal head.related tail.relatedContext

@[simp] theorem relatedContext_targets {source target : Object}
    {interpretation : RelationalInterpretation.{u} source target}
    {targetContext sourceGoals}
    (results : OpenResultList interpretation targetContext sourceGoals) :
    results.relatedContext.targets = results.targetGoals := by
  induction results with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [relatedContext, RelatedContext.targets, targetGoals,
        inductionHypothesis]

/-- Forget the relation witnesses while retaining the ordered target proofs. -/
def derivations {source target : Object}
    {interpretation : RelationalInterpretation.{u} source target}
    {targetContext : List Pattern} :
    {sourceGoals : List Pattern} →
      (results : OpenResultList interpretation targetContext sourceGoals) →
      OpenDerivationList target.presentation targetContext results.targetGoals
  | _, .nil => .nil
  | _, .cons head tail => .cons head.derivation tail.derivations

end OpenResultList

mutual

/-- Translate an open derivation after selecting a related target judgment for
each source premise occurrence. -/
def mapOpen {source target : Object}
    (interpretation : RelationalInterpretation.{u} source target)
    {sourceContext : List Pattern} {goal : Pattern}
    (context : RelatedContext interpretation.Related sourceContext) :
    OpenDerivation source.presentation sourceContext goal →
      OpenResult interpretation context.targets goal
  | .assumption index =>
      { targetGoal := context.targets.get (context.targetIndex index)
        related := context.relatedAt index
        derivation := .assumption (context.targetIndex index) }
  | .byRule ruleInstance application children =>
      let translated := mapOpenList interpretation context children
      let realized := interpretation.onRule ruleInstance application
        translated.relatedContext
      let targetDerivations : OpenDerivationList target.presentation
          context.targets translated.relatedContext.targets := by
        simpa only [OpenResultList.relatedContext_targets] using
          translated.derivations
      { targetGoal := realized.1
        related := realized.2.1
        derivation := realized.2.2.bind targetDerivations }

/-- Translate an ordered vector of open derivations pointwise. -/
def mapOpenList {source target : Object}
    (interpretation : RelationalInterpretation.{u} source target)
    {sourceContext goals : List Pattern}
    (context : RelatedContext interpretation.Related sourceContext) :
    OpenDerivationList source.presentation sourceContext goals →
      OpenResultList interpretation context.targets goals
  | .nil => .nil
  | .cons head tail =>
      .cons (mapOpen interpretation context head)
        (mapOpenList interpretation context tail)

end

/-- Translate a closed derivation.  The target judgment and its relation
witness remain data rather than being existentially truncated. -/
def mapDerivation {source target : Object}
    (interpretation : RelationalInterpretation.{u} source target)
    {goal : Pattern} (derivation : Derivation source.presentation goal) :
    ClosedResult interpretation goal :=
  let translated := interpretation.mapOpen (.nil)
    (OpenDerivation.ofClosed (context := []) derivation)
  { targetGoal := translated.targetGoal
    related := translated.related
    derivation := translated.derivation.close }

/-! ## The judgment-preserving fragment embeds -/

/-- Equality-related target premises can be used as the ordered assumptions
expected by an ordinary judgment-preserving interpretation. -/
private def equalityAssumptions
    {presentation : ValidatedPresentation} {premises : List Pattern}
    (context : RelatedContext (fun source target => PLift (source = target))
      premises) :
    OpenDerivationList presentation context.targets premises :=
  OpenDerivationList.ofFn premises fun index => by
    rw [(context.relatedAt index).down]
    exact .assumption (context.targetIndex index)

/-- Every ordinary judgment-preserving interpretation embeds in the
proof-relevant relational notion.  Equality is retained in `PLift` so the
relation lives in `Type`. -/
def ofInterpretation {source target : Object}
    (interpretation : Interpretation source target) :
    RelationalInterpretation source target where
  Related := fun sourceGoal targetGoal => PLift (sourceGoal = targetGoal)
  onRule := by
    intro ruleInstance premises conclusion application premiseTargets
    exact ⟨conclusion, ⟨rfl⟩,
      (interpretation.onRule ruleInstance application).bind
        (equalityAssumptions premiseTargets)⟩

/-- The identity relational interpretation is the embedded ordinary identity.
Its relation witnesses retain exact judgment equality. -/
def id (object : Object) : RelationalInterpretation object object :=
  ofInterpretation (Interpretation.id object)

/-! ## Proof-relevant composition -/

namespace CompositeContext

variable {first middle last : Object}
  (earlier : RelationalInterpretation.{u} first middle)
  (later : RelationalInterpretation.{u} middle last)

/-- Retain the intermediate target selected at every premise occurrence. -/
def left : {sources : List Pattern} →
    RelatedContext
      (fun source target =>
        Σ middleGoal,
          earlier.Related source middleGoal ×
            later.Related middleGoal target)
      sources →
    RelatedContext earlier.Related sources
  | _, .nil => .nil
  | _, .cons _target ⟨middleGoal, firstRelated, _⟩ tail =>
      .cons middleGoal firstRelated (left tail)

/-- The second half of every retained composite premise witness. -/
def right : {sources : List Pattern} →
    (context : RelatedContext
      (fun source target =>
        Σ middleGoal,
          earlier.Related source middleGoal ×
            later.Related middleGoal target)
      sources) →
    RelatedContext later.Related (left earlier later context).targets
  | _, .nil => .nil
  | _, .cons target ⟨_middleGoal, _, secondRelated⟩ tail =>
      .cons target secondRelated (right tail)

/-- Splitting composite witnesses preserves the final target context. -/
theorem right_targets : ∀ {sources : List Pattern}
    (context : RelatedContext
      (fun source target =>
        Σ middleGoal,
          earlier.Related source middleGoal ×
            later.Related middleGoal target)
      sources),
    (right earlier later context).targets = context.targets := by
  intro sources context
  induction context with
  | nil => rfl
  | cons target witness tail inductionHypothesis =>
      rcases witness with ⟨middleGoal, firstRelated, secondRelated⟩
      simp [right, RelatedContext.targets, inductionHypothesis]

end CompositeContext

/-- Change only the premise context of an open derivation along an equality. -/
private def castContext {presentation : ValidatedPresentation}
    {first second : List Pattern} {goal : Pattern}
    (same : first = second)
    (derivation : OpenDerivation presentation first goal) :
    OpenDerivation presentation second goal :=
  same ▸ derivation

/-- Compose proof-relevant translations.  The intermediate judgment and both
relation witnesses are retained in the composite relation fiber. -/
def comp {first middle last : Object}
    (earlier : RelationalInterpretation.{u} first middle)
    (later : RelationalInterpretation.{u} middle last) :
    RelationalInterpretation first last where
  Related := fun sourceGoal targetGoal =>
    Σ middleGoal,
      earlier.Related sourceGoal middleGoal ×
        later.Related middleGoal targetGoal
  onRule := by
    intro ruleInstance premises conclusion application premiseTargets
    let firstContext := CompositeContext.left earlier later premiseTargets
    let secondContext := CompositeContext.right earlier later premiseTargets
    let firstResult := earlier.onRule ruleInstance application firstContext
    let secondResult := later.mapOpen secondContext firstResult.2.2
    exact ⟨secondResult.targetGoal,
      ⟨firstResult.1, firstResult.2.1, secondResult.related⟩,
      castContext (CompositeContext.right_targets earlier later premiseTargets)
        secondResult.derivation⟩

/-- The two associations of three composite relation fibers are canonically
equivalent.  This is the retained associator data at the judgment-relation
layer; no strict equality or full bicategory is claimed. -/
def compRelatedAssoc {first second third fourth : Object}
    (one : RelationalInterpretation.{u} first second)
    (two : RelationalInterpretation.{u} second third)
    (three : RelationalInterpretation.{u} third fourth)
    (sourceGoal targetGoal : Pattern) :
    (comp (comp one two) three).Related sourceGoal targetGoal ≃
      (comp one (comp two three)).Related sourceGoal targetGoal where
  toFun := fun witness =>
    match witness with
    | ⟨thirdGoal, ⟨secondGoal, firstRelated, secondRelated⟩,
        thirdRelated⟩ =>
      ⟨secondGoal, firstRelated,
        ⟨thirdGoal, secondRelated, thirdRelated⟩⟩
  invFun := fun witness =>
    match witness with
    | ⟨secondGoal, firstRelated,
        ⟨thirdGoal, secondRelated, thirdRelated⟩⟩ =>
      ⟨thirdGoal, ⟨secondGoal, firstRelated, secondRelated⟩,
        thirdRelated⟩
  left_inv := by intro witness; rcases witness with ⟨_, ⟨_, _, _⟩, _⟩; rfl
  right_inv := by intro witness; rcases witness with ⟨_, _, ⟨_, _, _⟩⟩; rfl

end RelationalInterpretation

end Mettapedia.GSLT.LanguageDef.ProofGSLT
