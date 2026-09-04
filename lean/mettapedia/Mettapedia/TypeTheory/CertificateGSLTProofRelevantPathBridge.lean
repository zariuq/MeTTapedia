import Mettapedia.TypeTheory.ProofRelevantTranslationDependentAction
import Mettapedia.GSLT.LanguageDef.CalculusAsLanguage

/-!
# Checked calculus derivations as proof-relevant GSLT histories

Every validated calculus language already induces a proposition-valued
proof-search GSLT whose states are ordered obligation lists.  This module
retains the exact occurrence behind each search step: the selected rule
instance, its ordered premises and conclusion, and the untouched obligation
suffix.

Those occurrences form a `ProofRelevantGSLT`.  Checked derivation trees map to
finite evidence paths, evidence paths reconstruct checked derivations, and
the sequential path length is exactly the number of primitive rule nodes.
The construction is calculus-generic: it assumes neither Horn clauses nor a
particular object logic.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.CertificateGSLTProofRelevantPathBridge

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CalculusAsLanguage
open Mettapedia.GSLT.ProofRelevant
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.TypeTheory.CategoryIndexedFamilyCwf
open Mettapedia.TypeTheory.ProofRelevantRouteFamilyBridge

/-! ## Exact occurrences for the proof-search GSLT -/

/-- One authored proof-search occurrence.  Unlike the proposition-valued
`Resolves` relation, this carrier retains the selected rule instance and the
ordered local decomposition of the obligation state. -/
structure ProofSearchOccurrence
    (definition : ValidatedCalculusLanguageDef)
    (source target : GoalState) where
  ruleInstance : RuleInstance
  premises : List Pattern
  conclusion : Pattern
  suffix : GoalState
  application :
    RuleApplication definition ruleInstance premises conclusion
  source_eq : source = conclusion :: suffix
  target_eq : target = premises ++ suffix

namespace ProofSearchOccurrence

/-- Forget occurrence identity to the established semantic proof-search
step. -/
theorem erase {definition : ValidatedCalculusLanguageDef}
    {source target : GoalState}
    (occurrence : ProofSearchOccurrence definition source target) :
    (proofSearchGSLT definition).Step source target := by
  apply (proofSearchGSLT_step_iff_application
    definition source target).2
  exact ⟨occurrence.ruleInstance, occurrence.premises,
    occurrence.conclusion, occurrence.suffix, occurrence.application,
    occurrence.source_eq, occurrence.target_eq⟩

/-- A declaratively admitted rule application is a one-step occurrence on a
singleton obligation list. -/
def singleton {definition : ValidatedCalculusLanguageDef}
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {conclusion : Pattern}
    (application :
      RuleApplication definition ruleInstance premises conclusion) :
    ProofSearchOccurrence definition [conclusion] premises where
  ruleInstance := ruleInstance
  premises := premises
  conclusion := conclusion
  suffix := []
  application := application
  source_eq := rfl
  target_eq := by simp

/-- The same declarative rule application at the head of an explicit
untouched obligation suffix.  Stating this constructor directly avoids
introducing any representational casts into the retained occurrence. -/
def atHead {definition : ValidatedCalculusLanguageDef}
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {conclusion : Pattern}
    (application :
      RuleApplication definition ruleInstance premises conclusion)
    (suffix : GoalState) :
    ProofSearchOccurrence definition
      (conclusion :: suffix) (premises ++ suffix) where
  ruleInstance := ruleInstance
  premises := premises
  conclusion := conclusion
  suffix := suffix
  application := application
  source_eq := rfl
  target_eq := rfl

/-- Resolving the same first obligation while preserving an additional
right-hand suffix retains the same rule occurrence. -/
def appendRight {definition : ValidatedCalculusLanguageDef}
    {source target : GoalState}
    (occurrence : ProofSearchOccurrence definition source target)
    (extension : GoalState) :
    ProofSearchOccurrence definition
      (source ++ extension) (target ++ extension) := by
  rcases occurrence with
    ⟨ruleInstance, premises, conclusion, suffix, application,
      source_eq, target_eq⟩
  subst source
  subst target
  refine
    { ruleInstance := ruleInstance
      premises := premises
      conclusion := conclusion
      suffix := suffix ++ extension
      application := application
      source_eq := ?_
      target_eq := ?_ }
  · rfl
  · simp [List.append_assoc]

end ProofSearchOccurrence

/-- The exact evidence family of the proof-search GSLT. -/
def proofSearchStepEvidence (definition : ValidatedCalculusLanguageDef) :
    StepEvidence (proofSearchGSLT definition) where
  Evidence := ProofSearchOccurrence definition
  erases_iff source target := by
    constructor
    · rintro ⟨occurrence⟩
      exact occurrence.erase
    · intro step
      rcases (proofSearchGSLT_step_iff_application
          definition source target).1 step with
        ⟨ruleInstance, premises, conclusion, suffix, application,
          source_eq, target_eq⟩
      exact ⟨
        { ruleInstance := ruleInstance
          premises := premises
          conclusion := conclusion
          suffix := suffix
          application := application
          source_eq := source_eq
          target_eq := target_eq }⟩

/-- The proof-search dynamics of any validated calculus, now retaining exact
rule occurrences as Type-valued evidence. -/
def proofRelevantProofSearchGSLT
    (definition : ValidatedCalculusLanguageDef) : ProofRelevantGSLT :=
  ⟨proofSearchGSLT definition, proofSearchStepEvidence definition⟩

/-- Complete sequential proof-search histories. -/
abbrev ProofSearchPath (definition : ValidatedCalculusLanguageDef)
    (source target : GoalState) :=
  Route (ProofSearchOccurrence definition) source target

/-- The free proof-search path category is the proof-relevant dependent
context generated by the authored calculus. -/
abbrev proofSearchContext (definition : ValidatedCalculusLanguageDef) :
    Context.{0} :=
  evidenceContext (proofRelevantProofSearchGSLT definition)

/-- Histories from a selected obligation state form its representable
dependent family. -/
def proofSearchHistoryFamily (definition : ValidatedCalculusLanguageDef)
    (start : GoalState) : IndexedFamily (proofSearchContext definition) :=
  evidencePathFamily (proofRelevantProofSearchGSLT definition) start

/-! ## Structural operations on evidence paths -/

/-- Preserve a fixed suffix throughout every occurrence of a proof-search
history. -/
def pathAppendRight {definition : ValidatedCalculusLanguageDef}
    {source target : GoalState}
    (path : ProofSearchPath definition source target)
    (suffix : GoalState) :
    ProofSearchPath definition (source ++ suffix) (target ++ suffix) :=
  match path with
  | .refl _ => .refl _
  | .cons occurrence rest =>
      .cons (occurrence.appendRight suffix)
        (pathAppendRight rest suffix)

@[simp] theorem pathAppendRight_length
    {definition : ValidatedCalculusLanguageDef}
    {source target : GoalState}
    (path : ProofSearchPath definition source target)
    (suffix : GoalState) :
    (pathAppendRight path suffix).length = path.length := by
  induction path with
  | refl => rfl
  | cons occurrence rest inductionHypothesis =>
      simp [pathAppendRight, Route.length, inductionHypothesis]

/-- Suffix preservation is functorial over concatenation of proof-search
histories. -/
@[simp] theorem pathAppendRight_append
    {definition : ValidatedCalculusLanguageDef}
    {source middle target : GoalState}
    (first : ProofSearchPath definition source middle)
    (second : ProofSearchPath definition middle target)
    (suffix : GoalState) :
    pathAppendRight (first.append second) suffix =
      (pathAppendRight first suffix).append
        (pathAppendRight second suffix) := by
  induction first with
  | refl => rfl
  | cons occurrence rest inductionHypothesis =>
      simp [Route.append, pathAppendRight, inductionHypothesis]

/-- Splitting a derivation forest that was assembled at the same authored
boundary recovers both components exactly. -/
@[simp] theorem derivationListSplitAppend_append
    {definition : ValidatedCalculusLanguageDef}
    {first second : List Pattern}
    (left : DerivationList definition first)
    (right : DerivationList definition second) :
    derivationListSplitAppend first second
        (derivationListAppend left right) =
      (left, right) := by
  cases left with
  | nil => rfl
  | cons head tail =>
      simp only [derivationListAppend, derivationListSplitAppend]
      rw [derivationListSplitAppend_append tail right]

/-- Splitting any derivation forest at its indexed authored boundary and
then reassembling it loses no derivation occurrence. -/
theorem derivationListAppend_split
    {definition : ValidatedCalculusLanguageDef}
    (first second : List Pattern)
    (derivations : DerivationList definition (first ++ second)) :
    let divided := derivationListSplitAppend first second derivations
    derivationListAppend divided.1 divided.2 = derivations := by
  induction first with
  | nil => rfl
  | cons premise rest inductionHypothesis =>
      cases derivations with
      | cons head tail =>
          simp [derivationListSplitAppend, derivationListAppend,
            inductionHypothesis tail]

/-- Erase a Type-valued occurrence path to the original proposition-valued
multi-step proof-search reachability witness. -/
def erasePath {definition : ValidatedCalculusLanguageDef}
    {source target : GoalState} :
    ProofSearchPath definition source target →
      (proofSearchGSLT definition).MultiStep source target
  | .refl state =>
      @GSLT.MultiStep.refl (proofSearchGSLT definition) state
  | .cons occurrence rest =>
      .step occurrence.erase (erasePath rest)

/-! ## Checked derivation trees to sequential occurrence histories -/

mutual

/-- Serialize a checked derivation while retaining an arbitrary ordered
suffix of obligations.  This is the structural core of leftmost search: the
derivation discharges its own goal and leaves the suffix untouched. -/
def derivationToPathWithSuffix
    {definition : ValidatedCalculusLanguageDef}
    {goal : Pattern} (suffix : GoalState) :
    Derivation definition goal →
      ProofSearchPath definition (goal :: suffix) suffix
  | .byRule _ application children =>
      .cons (ProofSearchOccurrence.atHead application suffix)
        (derivationListToPathWithSuffix suffix children)

/-- Serialize an ordered derivation forest while retaining an arbitrary
right-hand obligation suffix. -/
def derivationListToPathWithSuffix
    {definition : ValidatedCalculusLanguageDef}
    {goals : List Pattern} (suffix : GoalState) :
    DerivationList definition goals →
      ProofSearchPath definition (goals ++ suffix) suffix
  | .nil => .refl suffix
  | @DerivationList.cons _ premise premises head tail =>
      (derivationToPathWithSuffix (premises ++ suffix) head).append
        (derivationListToPathWithSuffix suffix tail)

end

/-- Serialize a checked derivation tree as the deterministic leftmost
proof-search history that discharges its singleton goal. -/
def derivationToPath {definition : ValidatedCalculusLanguageDef}
    {goal : Pattern} (derivation : Derivation definition goal) :
    ProofSearchPath definition [goal] [] :=
  derivationToPathWithSuffix [] derivation

/-- Serialize an ordered derivation forest as one left-to-right proof-search
history. -/
def derivationListToPath {definition : ValidatedCalculusLanguageDef}
    {goals : List Pattern} :
    DerivationList definition goals → ProofSearchPath definition goals []
  | .nil => .refl []
  | @DerivationList.cons _ premise premises head tail =>
      (derivationToPathWithSuffix premises head).append
        (derivationListToPath tail)

/-- Sequentializing an assembled derivation forest preserves its authored
boundary: the first component runs with the second as obligations, then the
second component runs to completion. -/
theorem derivationListToPath_append
    {definition : ValidatedCalculusLanguageDef}
    {first second : List Pattern}
    (left : DerivationList definition first)
    (right : DerivationList definition second) :
    derivationListToPath (derivationListAppend left right) =
      (derivationListToPathWithSuffix second left).append
        (derivationListToPath right) := by
  cases left with
  | nil => rfl
  | cons head tail =>
      simp only [derivationListAppend, derivationListToPath,
        derivationListToPathWithSuffix]
      rw [derivationListToPath_append tail right]
      exact (Route.append_assoc _ _ _).symm

/-- A checked derivation forest is directly an inhabitant of the dependent
history family at the discharged endpoint. -/
def derivationListHistoryValue
    {definition : ValidatedCalculusLanguageDef}
    {goals : List Pattern}
    (derivations : DerivationList definition goals) :
    (proofSearchHistoryFamily definition goals).obj [] :=
  derivationListToPath derivations

/-! ## Sequential histories reconstruct checked derivations -/

/-- One exact occurrence reconstructs the derivation node at the head of the
source obligations, given derivations for the target obligations. -/
def ProofSearchOccurrence.prependDerivations
    {definition : ValidatedCalculusLanguageDef}
    {source target : GoalState}
    (occurrence : ProofSearchOccurrence definition source target)
    (targetDerivations : DerivationList definition target) :
    DerivationList definition source := by
  rcases occurrence with
    ⟨ruleInstance, premises, conclusion, suffix, application,
      source_eq, target_eq⟩
  subst source
  subst target
  let divided :=
    derivationListSplitAppend premises suffix targetDerivations
  exact .cons (.byRule ruleInstance application divided.1) divided.2

/-- One-step backwards replay and forward sequentialization are exact
inverses around the retained occurrence. -/
theorem derivationListToPath_prependDerivations
    {definition : ValidatedCalculusLanguageDef}
    {source target : GoalState}
    (occurrence : ProofSearchOccurrence definition source target)
    (targetDerivations : DerivationList definition target) :
    derivationListToPath
        (occurrence.prependDerivations targetDerivations) =
      .cons occurrence (derivationListToPath targetDerivations) := by
  rcases occurrence with
    ⟨ruleInstance, premises, conclusion, suffix, application,
      source_eq, target_eq⟩
  subst source
  subst target
  simp only [ProofSearchOccurrence.prependDerivations,
    derivationListToPath, derivationToPathWithSuffix, Route.append]
  rw [← derivationListToPath_append]
  rw [derivationListAppend_split]
  congr

/-- Replay a whole occurrence history backwards over derivations of its final
obligations. -/
def pathPrependDerivations
    {definition : ValidatedCalculusLanguageDef}
    {source target : GoalState}
    (path : ProofSearchPath definition source target)
    (targetDerivations : DerivationList definition target) :
    DerivationList definition source :=
  match path with
  | .refl _ => targetDerivations
  | .cons occurrence rest =>
      occurrence.prependDerivations
        (pathPrependDerivations rest targetDerivations)

/-- Backwards replay turns sequential path composition into ordinary
function composition on checked derivation forests. -/
theorem pathPrependDerivations_append
    {definition : ValidatedCalculusLanguageDef}
    {source middle target : GoalState}
    (first : ProofSearchPath definition source middle)
    (second : ProofSearchPath definition middle target)
    (targetDerivations : DerivationList definition target) :
    pathPrependDerivations (first.append second) targetDerivations =
      pathPrependDerivations first
        (pathPrependDerivations second targetDerivations) := by
  induction first with
  | refl => rfl
  | cons occurrence rest inductionHypothesis =>
      simp [Route.append, pathPrependDerivations, inductionHypothesis]

mutual

/-- Replaying the suffix-parametric serialization of one checked derivation
recovers that derivation in front of the untouched suffix exactly. -/
theorem pathPrependDerivations_derivationToPathWithSuffix
    {definition : ValidatedCalculusLanguageDef}
    {goal : Pattern} {suffix : GoalState}
    (derivation : Derivation definition goal)
    (suffixDerivations : DerivationList definition suffix) :
    pathPrependDerivations
        (derivationToPathWithSuffix suffix derivation)
        suffixDerivations =
      .cons derivation suffixDerivations := by
  cases derivation with
  | byRule ruleInstance application children =>
      simp [derivationToPathWithSuffix, pathPrependDerivations,
        ProofSearchOccurrence.prependDerivations,
        ProofSearchOccurrence.atHead,
        pathPrependDerivations_derivationListToPathWithSuffix
          children suffixDerivations,
        derivationListSplitAppend_append]

/-- Replaying the suffix-parametric serialization of an ordered checked
forest recovers the forest followed by that untouched suffix exactly. -/
theorem pathPrependDerivations_derivationListToPathWithSuffix
    {definition : ValidatedCalculusLanguageDef}
    {goals suffix : GoalState}
    (derivations : DerivationList definition goals)
    (suffixDerivations : DerivationList definition suffix) :
    pathPrependDerivations
        (derivationListToPathWithSuffix suffix derivations)
        suffixDerivations =
      derivationListAppend derivations suffixDerivations := by
  cases derivations with
  | nil => rfl
  | cons head tail =>
      simp [derivationListToPathWithSuffix,
        pathPrependDerivations_append,
        pathPrependDerivations_derivationToPathWithSuffix,
        pathPrependDerivations_derivationListToPathWithSuffix,
        derivationListAppend]

end

/-- A complete proof-search occurrence history ending at no obligations
reconstructs a checked derivation forest. -/
def pathToDerivationList
    {definition : ValidatedCalculusLanguageDef}
    {goals : GoalState}
    (path : ProofSearchPath definition goals []) :
    DerivationList definition goals :=
  pathPrependDerivations path .nil

/-- The checked derivation forest survives sequentialization and backwards
replay exactly; no rule instance, child order, or application evidence is
lost. -/
theorem pathToDerivationList_derivationListToPath
    {definition : ValidatedCalculusLanguageDef}
    {goals : GoalState}
    (derivations : DerivationList definition goals) :
    pathToDerivationList (derivationListToPath derivations) =
      derivations := by
  cases derivations with
  | nil => rfl
  | cons head tail =>
      simp [pathToDerivationList, derivationListToPath,
        pathPrependDerivations_append,
        pathPrependDerivations_derivationToPathWithSuffix]
      simpa only [pathToDerivationList] using
        pathToDerivationList_derivationListToPath tail

/-- Forward sequentialization after replaying an arbitrary path is that
path followed by the forward history of the supplied terminal derivations.
This is the suffix-general right-inverse law. -/
theorem derivationListToPath_pathPrependDerivations
    {definition : ValidatedCalculusLanguageDef}
    {source target : GoalState}
    (path : ProofSearchPath definition source target)
    (targetDerivations : DerivationList definition target) :
    derivationListToPath
        (pathPrependDerivations path targetDerivations) =
      path.append (derivationListToPath targetDerivations) := by
  induction path with
  | refl => rfl
  | cons occurrence rest inductionHypothesis =>
      simp only [pathPrependDerivations, Route.append]
      rw [derivationListToPath_prependDerivations,
        inductionHypothesis]

/-- Conversely, sequentializing a complete history after backwards replay
recovers the exact history, including every retained rule occurrence. -/
theorem derivationListToPath_pathToDerivationList
    {definition : ValidatedCalculusLanguageDef}
    {goals : GoalState}
    (path : ProofSearchPath definition goals []) :
    derivationListToPath (pathToDerivationList path) = path := by
  change derivationListToPath
      (pathPrependDerivations path .nil) = path
  rw [derivationListToPath_pathPrependDerivations]
  exact Route.append_refl path

/-- Complete checked derivation forests and complete proof-relevant
leftmost histories are equivalent data, not merely equi-inhabited
propositions. -/
def derivationListEquivProofSearchPath
    (definition : ValidatedCalculusLanguageDef) (goals : GoalState) :
    DerivationList definition goals ≃
      ProofSearchPath definition goals [] where
  toFun := derivationListToPath
  invFun := pathToDerivationList
  left_inv := pathToDerivationList_derivationListToPath
  right_inv := derivationListToPath_pathToDerivationList

/-- Type-valued adequacy: checked derivations and complete proof-relevant
search histories are inhabited under exactly the same conditions.  Both
directions are witnessed by explicit functions above, not by choice from the
proposition-valued reachability theorem. -/
theorem derivationList_nonempty_iff_evidencePath
    (definition : ValidatedCalculusLanguageDef) (goals : GoalState) :
    Nonempty (DerivationList definition goals) ↔
      Nonempty (ProofSearchPath definition goals []) := by
  constructor
  · rintro ⟨derivations⟩
    exact ⟨derivationListToPath derivations⟩
  · rintro ⟨path⟩
    exact ⟨pathToDerivationList path⟩

/-! ## Exact quantitative agreement -/

mutual

/-- Number of primitive rule nodes in a closed checked derivation. -/
def derivationRuleCount {definition : ValidatedCalculusLanguageDef}
    {goal : Pattern} : Derivation definition goal → Nat
  | .byRule _ _ children => derivationListRuleCount children + 1

/-- Total primitive rule nodes in an ordered checked derivation forest. -/
def derivationListRuleCount
    {definition : ValidatedCalculusLanguageDef}
    {goals : List Pattern} : DerivationList definition goals → Nat
  | .nil => 0
  | .cons head tail =>
      derivationRuleCount head + derivationListRuleCount tail

end

mutual

/-- Suffix-parametric tree sequentialization neither invents nor discards
primitive rule nodes. -/
theorem derivationToPathWithSuffix_length
    {definition : ValidatedCalculusLanguageDef}
    {goal : Pattern} (suffix : GoalState)
    (derivation : Derivation definition goal) :
    (derivationToPathWithSuffix suffix derivation).length =
      derivationRuleCount derivation := by
  cases derivation with
  | byRule _ application children =>
      simp [derivationToPathWithSuffix, derivationRuleCount, Route.length,
        derivationListToPathWithSuffix_length suffix children]

/-- The same exact count agreement holds for suffix-parametric ordered
derivation forests. -/
theorem derivationListToPathWithSuffix_length
    {definition : ValidatedCalculusLanguageDef}
    {goals : List Pattern} (suffix : GoalState)
    (derivations : DerivationList definition goals) :
    (derivationListToPathWithSuffix suffix derivations).length =
      derivationListRuleCount derivations := by
  cases derivations with
  | nil => rfl
  | cons head tail =>
      calc
        (derivationListToPathWithSuffix suffix (.cons head tail)).length =
            (derivationToPathWithSuffix (_ ++ suffix) head).length +
              (derivationListToPathWithSuffix suffix tail).length :=
          Route.length_append _ _
        _ = derivationRuleCount head + derivationListRuleCount tail := by
          rw [derivationToPathWithSuffix_length,
            derivationListToPathWithSuffix_length]

end

/-- Sequentialization of a closed tree has exactly one occurrence per
primitive rule node. -/
theorem derivationToPath_length
    {definition : ValidatedCalculusLanguageDef}
    {goal : Pattern} (derivation : Derivation definition goal) :
    (derivationToPath derivation).length =
      derivationRuleCount derivation :=
  derivationToPathWithSuffix_length [] derivation

/-- Sequentialization of a closed ordered forest has exactly one occurrence
per primitive rule node. -/
theorem derivationListToPath_length
    {definition : ValidatedCalculusLanguageDef}
    {goals : List Pattern}
    (derivations : DerivationList definition goals) :
    (derivationListToPath derivations).length =
      derivationListRuleCount derivations := by
  cases derivations with
  | nil => rfl
  | cons head tail =>
      simp [derivationListToPath, derivationListRuleCount,
        Route.length_append, derivationToPathWithSuffix_length,
        derivationListToPath_length tail]

/-! ## Positive and negative controls -/

/-- One admitted rule application produces a one-occurrence history and its
erasure is the established semantic proof-search step. -/
def singletonRulePath {definition : ValidatedCalculusLanguageDef}
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {conclusion : Pattern}
    (application :
      RuleApplication definition ruleInstance premises conclusion) :
    ProofSearchPath definition [conclusion] premises :=
  .cons (ProofSearchOccurrence.singleton application) (.refl premises)

@[simp] theorem singletonRulePath_length
    {definition : ValidatedCalculusLanguageDef}
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {conclusion : Pattern}
    (application :
      RuleApplication definition ruleInstance premises conclusion) :
    (singletonRulePath application).length = 1 :=
  rfl

/-- If a state has no semantic outgoing proof-search step and differs from
the target, no proof-relevant path can be fabricated between them. -/
theorem no_path_of_no_outgoing_step
    {definition : ValidatedCalculusLanguageDef}
    {source target : GoalState}
    (different : source ≠ target)
    (noStep : ∀ next, ¬ (proofSearchGSLT definition).Step source next) :
    IsEmpty (ProofSearchPath definition source target) := by
  constructor
  intro path
  cases path with
  | refl => exact different rfl
  | cons occurrence rest => exact noStep _ occurrence.erase

#print axioms ProofSearchOccurrence.erase
#print axioms proofSearchStepEvidence
#print axioms pathAppendRight_length
#print axioms erasePath
#print axioms derivationListToPath_prependDerivations
#print axioms pathToDerivationList_derivationListToPath
#print axioms derivationListToPath_pathToDerivationList
#print axioms derivationListEquivProofSearchPath
#print axioms derivationList_nonempty_iff_evidencePath
#print axioms derivationToPath_length
#print axioms derivationListToPath_length
#print axioms singletonRulePath_length
#print axioms no_path_of_no_outgoing_step

end Mettapedia.TypeTheory.CertificateGSLTProofRelevantPathBridge
