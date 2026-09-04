import Mettapedia.TypeTheory.CertificateGSLTProofRelevantPathBridge

/-!
# Scheduled proof-search histories and their justification quotient

The ordinary calculus-as-language construction always rewrites the first
outstanding obligation.  That deterministic convention is useful for a
canonical encoding, but it should not be confused with the operational
history of a concurrent, heuristic, or agent-directed prover.

This module permits a rule application at any explicitly retained occurrence
of the obligation list.  A scheduled occurrence records the untouched prefix
and suffix as well as the rule instance, premises, conclusion, and independent
`RuleApplication` evidence.  Complete scheduled histories replay backwards to
the same checked `DerivationList` objects used by the certificate GSLT.

The central result identifies the quotient of complete schedules by equal
reconstructed justification with checked derivation forests.  Thus three
layers remain distinct:

* a checked derivation forest is the justification;
* a scheduled path is an operational linearization of that justification;
* an observer may forget the schedule exactly when it factors through the
  justification map.

This is independent of premise exchange.  Reordering premises inside a rule
node requires a separate `PremisePermutationInvariant` theorem for that rule
interface.  Here the ordered proof tree stays fixed while independent rule
occurrences may be visited in different orders.

The construction is generic in a validated calculus.  In particular it does
not assume Horn clauses, first-order terms, a fixed search algorithm, or a
specific object logic.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.CertificateGSLTScheduledHistory

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CalculusAsLanguage
open Mettapedia.GSLT.ProofRelevant
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.TypeTheory.CertificateGSLTProofRelevantPathBridge

/-! ## Any-occurrence proof search -/

/-- One scheduled backward-search step.  The selected conclusion may occur
anywhere in the ordered obligation list; `before` and `suffix` retain its
occurrence rather than locating it merely by judgment equality. -/
def ScheduledResolves (definition : ValidatedCalculusLanguageDef) :
    GoalState → GoalState → Prop :=
  fun source target =>
    ∃ before ruleInstance premises conclusion suffix,
      RuleApplication definition ruleInstance premises conclusion ∧
      source = before ++ conclusion :: suffix ∧
      target = before ++ (premises ++ suffix)

/-- The GSLT of proof search with an explicit scheduler-selected obligation. -/
def scheduledProofSearchGSLT
    (definition : ValidatedCalculusLanguageDef) : GSLT where
  Term := GoalState
  equations :=
    { r := Eq
      iseqv := ⟨Eq.refl, Eq.symm, Eq.trans⟩ }
  rewrites := ScheduledResolves definition
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

/-- The scheduled GSLT step is exactly one independently admitted rule
application together with an occurrence-sensitive focus decomposition. -/
theorem scheduledProofSearchGSLT_step_iff_application
    (definition : ValidatedCalculusLanguageDef)
    (source target : GoalState) :
    (scheduledProofSearchGSLT definition).Step source target ↔
      ∃ before ruleInstance premises conclusion suffix,
        RuleApplication definition ruleInstance premises conclusion ∧
        source = before ++ conclusion :: suffix ∧
        target = before ++ (premises ++ suffix) :=
  Iff.rfl

/-- Exact Type-valued evidence for one scheduled rule occurrence. -/
structure ScheduledProofSearchOccurrence
    (definition : ValidatedCalculusLanguageDef)
    (source target : GoalState) where
  before : GoalState
  ruleInstance : RuleInstance
  premises : List Pattern
  conclusion : Pattern
  suffix : GoalState
  application :
    RuleApplication definition ruleInstance premises conclusion
  source_eq : source = before ++ conclusion :: suffix
  target_eq : target = before ++ (premises ++ suffix)

namespace ScheduledProofSearchOccurrence

/-- Forget retained occurrence identity to the proposition-valued scheduled
step relation. -/
theorem erase {definition : ValidatedCalculusLanguageDef}
    {source target : GoalState}
    (occurrence : ScheduledProofSearchOccurrence definition source target) :
    (scheduledProofSearchGSLT definition).Step source target := by
  exact ⟨occurrence.before, occurrence.ruleInstance,
    occurrence.premises, occurrence.conclusion, occurrence.suffix,
    occurrence.application, occurrence.source_eq, occurrence.target_eq⟩

/-- The canonical leftmost occurrence is a scheduled occurrence with empty
prefix. -/
def ofLeftmost {definition : ValidatedCalculusLanguageDef}
    {source target : GoalState}
    (occurrence : ProofSearchOccurrence definition source target) :
    ScheduledProofSearchOccurrence definition source target where
  before := []
  ruleInstance := occurrence.ruleInstance
  premises := occurrence.premises
  conclusion := occurrence.conclusion
  suffix := occurrence.suffix
  application := occurrence.application
  source_eq := by simpa using occurrence.source_eq
  target_eq := by simpa using occurrence.target_eq

/-- Place one admitted rule application at an explicitly chosen occurrence
between an untouched prefix and suffix. -/
def placed {definition : ValidatedCalculusLanguageDef}
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {conclusion : Pattern}
    (before : GoalState)
    (application :
      RuleApplication definition ruleInstance premises conclusion)
    (suffix : GoalState) :
    ScheduledProofSearchOccurrence definition
      (before ++ conclusion :: suffix)
      (before ++ (premises ++ suffix)) where
  before := before
  ruleInstance := ruleInstance
  premises := premises
  conclusion := conclusion
  suffix := suffix
  application := application
  source_eq := rfl
  target_eq := rfl

/-- Numeric position of the selected obligation in the current ordered state. -/
def focusIndex {definition : ValidatedCalculusLanguageDef}
    {source target : GoalState}
    (occurrence : ScheduledProofSearchOccurrence definition source target) : Nat :=
  occurrence.before.length

/-- The selected conclusion is present at the exact retained occurrence in
the source obligation state. -/
theorem conclusion_mem_source
    {definition : ValidatedCalculusLanguageDef}
    {source target : GoalState}
    (occurrence : ScheduledProofSearchOccurrence definition source target) :
    occurrence.conclusion ∈ source := by
  rcases occurrence with
    ⟨before, ruleInstance, premises, conclusion, suffix, application,
      source_eq, target_eq⟩
  subst source
  simp

end ScheduledProofSearchOccurrence

/-- Every semantic scheduled step has exact occurrence evidence and vice
versa. -/
def scheduledProofSearchStepEvidence
    (definition : ValidatedCalculusLanguageDef) :
    StepEvidence (scheduledProofSearchGSLT definition) where
  Evidence := ScheduledProofSearchOccurrence definition
  erases_iff source target := by
    constructor
    · rintro ⟨occurrence⟩
      exact occurrence.erase
    · rintro ⟨before, ruleInstance, premises, conclusion, suffix,
          application, source_eq, target_eq⟩
      exact ⟨
        { before := before
          ruleInstance := ruleInstance
          premises := premises
          conclusion := conclusion
          suffix := suffix
          application := application
          source_eq := source_eq
          target_eq := target_eq }⟩

/-- The proof-relevant scheduled proof-search dynamics. -/
def proofRelevantScheduledProofSearchGSLT
    (definition : ValidatedCalculusLanguageDef) : ProofRelevantGSLT :=
  ⟨scheduledProofSearchGSLT definition,
    scheduledProofSearchStepEvidence definition⟩

/-- An operational history whose scheduler may select any outstanding
obligation occurrence. -/
abbrev ScheduledProofSearchPath
    (definition : ValidatedCalculusLanguageDef)
    (source target : GoalState) :=
  Route (ScheduledProofSearchOccurrence definition) source target

/-! ## The canonical leftmost schedule embeds faithfully -/

/-- Regard a leftmost occurrence history as a scheduled history. -/
def leftmostPathToScheduled
    {definition : ValidatedCalculusLanguageDef}
    {source target : GoalState} :
    ProofSearchPath definition source target →
      ScheduledProofSearchPath definition source target
  | .refl state => .refl state
  | .cons occurrence rest =>
      .cons (ScheduledProofSearchOccurrence.ofLeftmost occurrence)
        (leftmostPathToScheduled rest)

@[simp] theorem leftmostPathToScheduled_length
    {definition : ValidatedCalculusLanguageDef}
    {source target : GoalState}
    (path : ProofSearchPath definition source target) :
    (leftmostPathToScheduled path).length = path.length := by
  induction path with
  | refl => rfl
  | cons occurrence rest inductionHypothesis =>
      simp [leftmostPathToScheduled, Route.length, inductionHypothesis]

/-- The canonical schedule of a checked derivation forest. -/
def derivationListToScheduledPath
    {definition : ValidatedCalculusLanguageDef}
    {goals : GoalState}
    (derivations : DerivationList definition goals) :
    ScheduledProofSearchPath definition goals [] :=
  leftmostPathToScheduled (derivationListToPath derivations)

/-! ## Backwards replay: schedules to justifications -/

/-- Splitting before an empty authored prefix returns the untouched forest. -/
@[simp] theorem derivationListSplitAppend_nil
    {definition : ValidatedCalculusLanguageDef}
    (goals : GoalState)
    (derivations : DerivationList definition goals) :
    derivationListSplitAppend [] goals derivations = (.nil, derivations) :=
  rfl

/-- Concatenating no derivations on the left returns the right forest. -/
@[simp] theorem derivationListAppend_nil_left
    {definition : ValidatedCalculusLanguageDef}
    {goals : GoalState}
    (derivations : DerivationList definition goals) :
    derivationListAppend (.nil : DerivationList definition []) derivations =
      derivations :=
  rfl

/-- Concatenation preserves the first derivation occurrence. -/
@[simp] theorem derivationListAppend_cons
    {definition : ValidatedCalculusLanguageDef}
    {goal : Pattern} {first second : GoalState}
    (head : Derivation definition goal)
    (tail : DerivationList definition first)
    (right : DerivationList definition second) :
    derivationListAppend (.cons head tail) right =
      .cons head (derivationListAppend tail right) :=
  rfl

/-- Splitting a visibly consed derivation forest after its first occurrence
recovers that occurrence and the untouched tail. -/
@[simp] theorem derivationListSplitAppend_singleton
    {definition : ValidatedCalculusLanguageDef}
    {goal : Pattern} {goals : GoalState}
    (head : Derivation definition goal)
    (tail : DerivationList definition goals) :
    derivationListSplitAppend [goal] goals (.cons head tail) =
      (.cons head .nil, tail) :=
  rfl

/-- Rebuild the source derivation forest of one arbitrary-focus occurrence
from checked derivations of all target obligations. -/
def ScheduledProofSearchOccurrence.prependDerivations
    {definition : ValidatedCalculusLanguageDef}
    {source target : GoalState}
    (occurrence : ScheduledProofSearchOccurrence definition source target)
    (targetDerivations : DerivationList definition target) :
    DerivationList definition source := by
  rcases occurrence with
    ⟨before, ruleInstance, premises, conclusion, suffix, application,
      source_eq, target_eq⟩
  subst source
  subst target
  let prefixAndRest :=
    derivationListSplitAppend before (premises ++ suffix) targetDerivations
  let premisesAndSuffix :=
    derivationListSplitAppend premises suffix prefixAndRest.2
  exact derivationListAppend prefixAndRest.1
    (.cons (.byRule ruleInstance application premisesAndSuffix.1)
      premisesAndSuffix.2)

/-- Backwards replay at an explicitly assembled occurrence is exact on the
three authored derivation-forest pieces. -/
@[simp] theorem ScheduledProofSearchOccurrence.placed_prependDerivations
    {definition : ValidatedCalculusLanguageDef}
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {conclusion : Pattern}
    (before : GoalState)
    (application :
      RuleApplication definition ruleInstance premises conclusion)
    (suffix : GoalState)
    (beforeDerivations : DerivationList definition before)
    (premiseDerivations : DerivationList definition premises)
    (suffixDerivations : DerivationList definition suffix) :
    (ScheduledProofSearchOccurrence.placed before application suffix).prependDerivations
        (derivationListAppend beforeDerivations
          (derivationListAppend premiseDerivations suffixDerivations)) =
      derivationListAppend beforeDerivations
        (.cons (.byRule ruleInstance application premiseDerivations)
          suffixDerivations) := by
  simp [ScheduledProofSearchOccurrence.placed,
    ScheduledProofSearchOccurrence.prependDerivations,
    derivationListSplitAppend_append]

/-- On an empty prefix, arbitrary-focus backwards replay is definitionally
the established leftmost backwards replay. -/
@[simp] theorem ScheduledProofSearchOccurrence.ofLeftmost_prependDerivations
    {definition : ValidatedCalculusLanguageDef}
    {source target : GoalState}
    (occurrence : ProofSearchOccurrence definition source target)
    (targetDerivations : DerivationList definition target) :
    (ScheduledProofSearchOccurrence.ofLeftmost occurrence).prependDerivations
        targetDerivations =
      occurrence.prependDerivations targetDerivations := by
  rcases occurrence with
    ⟨ruleInstance, premises, conclusion, suffix, application,
      source_eq, target_eq⟩
  subst source
  subst target
  simp [ScheduledProofSearchOccurrence.ofLeftmost,
    ScheduledProofSearchOccurrence.prependDerivations,
    ProofSearchOccurrence.prependDerivations]

/-- Replay a scheduled history backwards over derivations of its terminal
obligations. -/
def scheduledPathPrependDerivations
    {definition : ValidatedCalculusLanguageDef}
    {source target : GoalState}
    (path : ScheduledProofSearchPath definition source target)
    (targetDerivations : DerivationList definition target) :
    DerivationList definition source :=
  match path with
  | .refl _ => targetDerivations
  | .cons occurrence rest =>
      occurrence.prependDerivations
        (scheduledPathPrependDerivations rest targetDerivations)

/-- Complete scheduled histories reconstruct checked derivation forests. -/
def scheduledPathToDerivationList
    {definition : ValidatedCalculusLanguageDef}
    {goals : GoalState}
    (path : ScheduledProofSearchPath definition goals []) :
    DerivationList definition goals :=
  scheduledPathPrependDerivations path .nil

/-- Embedding and replay commute for every leftmost path, including paths
whose final obligations are not empty. -/
theorem scheduledPathPrependDerivations_leftmostPathToScheduled
    {definition : ValidatedCalculusLanguageDef}
    {source target : GoalState}
    (path : ProofSearchPath definition source target)
    (targetDerivations : DerivationList definition target) :
    scheduledPathPrependDerivations
        (leftmostPathToScheduled path) targetDerivations =
      pathPrependDerivations path targetDerivations := by
  induction path with
  | refl => rfl
  | cons occurrence rest inductionHypothesis =>
      simp [leftmostPathToScheduled, scheduledPathPrependDerivations,
        pathPrependDerivations, inductionHypothesis]

/-- Canonical leftmost scheduling followed by arbitrary-schedule replay loses
no part of the checked justification. -/
@[simp] theorem scheduledPathToDerivationList_derivationListToScheduledPath
    {definition : ValidatedCalculusLanguageDef}
    {goals : GoalState}
    (derivations : DerivationList definition goals) :
    scheduledPathToDerivationList
        (derivationListToScheduledPath derivations) = derivations := by
  rw [scheduledPathToDerivationList, derivationListToScheduledPath,
    scheduledPathPrependDerivations_leftmostPathToScheduled]
  exact pathToDerivationList_derivationListToPath derivations

/-! ## Schedule quotient and observer discipline -/

/-- Two complete schedules have the same justification when backwards replay
reconstructs the same ordered checked derivation forest. -/
def SameJustification
    {definition : ValidatedCalculusLanguageDef}
    {goals : GoalState}
    (left right : ScheduledProofSearchPath definition goals []) : Prop :=
  scheduledPathToDerivationList left =
    scheduledPathToDerivationList right

theorem sameJustification_equivalence
    (definition : ValidatedCalculusLanguageDef) (goals : GoalState) :
    Equivalence (@SameJustification definition goals) := by
  constructor
  · intro path
    rfl
  · intro left right equal
    exact equal.symm
  · intro first second third firstSecond secondThird
    exact firstSecond.trans secondThird

/-- The principled quotient identifies exactly operational schedules that
reconstruct the same justification. -/
def scheduleJustificationSetoid
    (definition : ValidatedCalculusLanguageDef) (goals : GoalState) :
    Setoid (ScheduledProofSearchPath definition goals []) where
  r := SameJustification
  iseqv := sameJustification_equivalence definition goals

/-- A complete schedule modulo equality of reconstructed justification. -/
abbrev ScheduleJustificationQuotient
    (definition : ValidatedCalculusLanguageDef) (goals : GoalState) :=
  Quotient (scheduleJustificationSetoid definition goals)

/-- Reconstruct a checked forest from a schedule quotient. -/
def scheduleQuotientToDerivationList
    (definition : ValidatedCalculusLanguageDef) (goals : GoalState) :
    ScheduleJustificationQuotient definition goals →
      DerivationList definition goals :=
  Quotient.lift scheduledPathToDerivationList (by
    intro left right equal
    exact equal)

/-- Checked derivation forests are exactly complete operational schedules
modulo equality of justification. -/
def derivationListEquivScheduleJustificationQuotient
    (definition : ValidatedCalculusLanguageDef) (goals : GoalState) :
    DerivationList definition goals ≃
      ScheduleJustificationQuotient definition goals where
  toFun derivations :=
    Quotient.mk _ (derivationListToScheduledPath derivations)
  invFun := scheduleQuotientToDerivationList definition goals
  left_inv derivations := by
    exact scheduledPathToDerivationList_derivationListToScheduledPath derivations
  right_inv quotient := by
    refine Quotient.inductionOn quotient ?_
    intro path
    apply Quotient.sound
    exact scheduledPathToDerivationList_derivationListToScheduledPath
      (scheduledPathToDerivationList path)

/-- An observation factors through justification when some function on
checked derivation forests computes it for every complete schedule. -/
def FactorsThroughJustification
    {definition : ValidatedCalculusLanguageDef}
    {goals : GoalState} {Output : Type*}
    (observer : ScheduledProofSearchPath definition goals [] → Output) : Prop :=
  ∃ onJustification : DerivationList definition goals → Output,
    ∀ path, observer path = onJustification (scheduledPathToDerivationList path)

/-- Every observer licensed to forget schedules is constant on schedules with
the same justification. -/
theorem observer_eq_of_factorsThroughJustification
    {definition : ValidatedCalculusLanguageDef}
    {goals : GoalState} {Output : Type*}
    {observer : ScheduledProofSearchPath definition goals [] → Output}
    (factors : FactorsThroughJustification observer)
    {left right : ScheduledProofSearchPath definition goals []}
    (same : SameJustification left right) :
    observer left = observer right := by
  rcases factors with ⟨onJustification, agreement⟩
  rw [agreement left, agreement right, same]

/-! ## Exact work accounting -/

/-- Primitive rule-node count is additive over ordered derivation-forest
concatenation. -/
theorem derivationListRuleCount_append
    {definition : ValidatedCalculusLanguageDef}
    {first second : GoalState}
    (left : DerivationList definition first)
    (right : DerivationList definition second) :
    derivationListRuleCount (derivationListAppend left right) =
      derivationListRuleCount left + derivationListRuleCount right := by
  cases left with
  | nil =>
      simp [derivationListAppend, derivationListRuleCount]
  | cons head tail =>
      change
        derivationRuleCount head +
            derivationListRuleCount (derivationListAppend tail right) =
          derivationRuleCount head + derivationListRuleCount tail +
            derivationListRuleCount right
      rw [derivationListRuleCount_append tail right]
      omega

/-- Splitting a derivation forest at an authored boundary partitions its
primitive rule nodes exactly. -/
theorem derivationListRuleCount_split
    {definition : ValidatedCalculusLanguageDef}
    (first second : GoalState)
    (derivations : DerivationList definition (first ++ second)) :
    let divided := derivationListSplitAppend first second derivations
    derivationListRuleCount derivations =
      derivationListRuleCount divided.1 +
        derivationListRuleCount divided.2 := by
  induction first with
  | nil =>
      simp [derivationListSplitAppend, derivationListRuleCount]
  | cons premise rest inductionHypothesis =>
      cases derivations with
      | cons head tail =>
          change
            derivationRuleCount head + derivationListRuleCount tail =
              derivationRuleCount head +
                derivationListRuleCount
                  (derivationListSplitAppend rest second tail).1 +
                derivationListRuleCount
                  (derivationListSplitAppend rest second tail).2
          rw [inductionHypothesis tail]
          omega

/-- Replaying one scheduled occurrence adds exactly its one retained rule
node, regardless of where the scheduler focused. -/
theorem ScheduledProofSearchOccurrence.prependDerivations_ruleCount
    {definition : ValidatedCalculusLanguageDef}
    {source target : GoalState}
    (occurrence : ScheduledProofSearchOccurrence definition source target)
    (targetDerivations : DerivationList definition target) :
    derivationListRuleCount
        (occurrence.prependDerivations targetDerivations) =
      derivationListRuleCount targetDerivations + 1 := by
  rcases occurrence with
    ⟨before, ruleInstance, premises, conclusion, suffix, application,
      source_eq, target_eq⟩
  subst source
  subst target
  have firstSplit :=
    derivationListRuleCount_split before (premises ++ suffix) targetDerivations
  have secondSplit :=
    derivationListRuleCount_split premises suffix
      (derivationListSplitAppend before (premises ++ suffix)
        targetDerivations).2
  dsimp [ScheduledProofSearchOccurrence.prependDerivations]
  rw [derivationListRuleCount_append]
  simp only [derivationListRuleCount, derivationRuleCount]
  dsimp only at firstSplit secondSplit
  omega

/-- Backwards replay of a scheduled path accounts for every occurrence and
every supplied terminal derivation exactly once. -/
theorem scheduledPathPrependDerivations_ruleCount
    {definition : ValidatedCalculusLanguageDef}
    {source target : GoalState}
    (path : ScheduledProofSearchPath definition source target)
    (targetDerivations : DerivationList definition target) :
    derivationListRuleCount
        (scheduledPathPrependDerivations path targetDerivations) =
      path.length + derivationListRuleCount targetDerivations := by
  induction path with
  | refl => simp [scheduledPathPrependDerivations, Route.length]
  | cons occurrence rest inductionHypothesis =>
      rw [scheduledPathPrependDerivations,
        occurrence.prependDerivations_ruleCount,
        inductionHypothesis]
      simp only [Route.length]
      omega

/-- Every complete operational schedule has exactly one step per primitive
rule node in its reconstructed justification. -/
theorem scheduledPathToDerivationList_ruleCount
    {definition : ValidatedCalculusLanguageDef}
    {goals : GoalState}
    (path : ScheduledProofSearchPath definition goals []) :
    derivationListRuleCount (scheduledPathToDerivationList path) =
      path.length := by
  simpa only [scheduledPathToDerivationList, derivationListRuleCount,
    Nat.add_zero] using
    scheduledPathPrependDerivations_ruleCount path
      (DerivationList.nil : DerivationList definition [])

/-- Path length is a lawful justification-only observer. -/
theorem pathLength_factorsThroughJustification
    (definition : ValidatedCalculusLanguageDef) (goals : GoalState) :
    FactorsThroughJustification
      (fun path : ScheduledProofSearchPath definition goals [] => path.length) := by
  refine ⟨derivationListRuleCount, ?_⟩
  intro path
  exact (scheduledPathToDerivationList_ruleCount path).symm

/-! ## Schedule-sensitive observation and canaries -/

/-- Retain the sequence of scheduler-selected occurrence positions. -/
def focusTrace
    {definition : ValidatedCalculusLanguageDef}
    {source target : GoalState} :
    ScheduledProofSearchPath definition source target → List Nat
  | .refl _ => []
  | .cons occurrence rest => occurrence.focusIndex :: focusTrace rest

/-- Evidence that a scheduler can select an occurrence of `conclusion` in
the current state, with the successor state retained existentially. -/
def SelectableConclusion
    (definition : ValidatedCalculusLanguageDef)
    (state : GoalState) (conclusion : Pattern) : Type :=
  Σ next : GoalState,
    { occurrence : ScheduledProofSearchOccurrence definition state next //
      occurrence.conclusion = conclusion }

/-- A rule conclusion that is absent from the current obligation state
cannot be scheduled.  This is the basic causal fence against moving a
dependent child step before the parent step that exposes it. -/
theorem not_selectableConclusion_of_not_mem
    {definition : ValidatedCalculusLanguageDef}
    {state : GoalState} {conclusion : Pattern}
    (absent : conclusion ∉ state) :
    IsEmpty (SelectableConclusion definition state conclusion) := by
  constructor
  rintro ⟨next, ⟨occurrence, selected⟩⟩
  apply absent
  rw [← selected]
  exact occurrence.conclusion_mem_source

namespace Canary

variable {definition : ValidatedCalculusLanguageDef}
variable {goal : Pattern} {ruleInstance : RuleInstance}

/-! The controls are parametric in one independently admitted zero-premise
rule.  Consequently they apply to every calculus with an axiom-like rule,
without making the fixture's object logic part of the schedule theory. -/

/-- Resolve the first of two equal but occurrence-distinct obligations. -/
def firstOfTwo :
    RuleApplication definition ruleInstance [] goal →
      ScheduledProofSearchOccurrence definition [goal, goal] [goal] :=
  fun application =>
    ScheduledProofSearchOccurrence.placed [] application [goal]

/-- Resolve the second of two equal but occurrence-distinct obligations. -/
def secondOfTwo :
    RuleApplication definition ruleInstance [] goal →
      ScheduledProofSearchOccurrence definition [goal, goal] [goal] :=
  fun application => by
    simpa using ScheduledProofSearchOccurrence.placed [goal] application []

/-- Resolve the sole remaining occurrence. -/
def sole (application : RuleApplication definition ruleInstance [] goal) :
    ScheduledProofSearchOccurrence definition [goal] [] :=
  ScheduledProofSearchOccurrence.placed [] application []

/-- The checked leaf reconstructed by the admitted zero-premise rule. -/
def axiomDerivation
    (application : RuleApplication definition ruleInstance [] goal) :
    Derivation definition goal :=
  .byRule ruleInstance application .nil

@[simp] theorem sole_prepend_nil
    (application : RuleApplication definition ruleInstance [] goal) :
    (sole application).prependDerivations .nil =
      .cons (axiomDerivation application) .nil := by
  simpa [sole, axiomDerivation] using
    ScheduledProofSearchOccurrence.placed_prependDerivations
      ([] : GoalState) application ([] : GoalState)
      (DerivationList.nil : DerivationList definition [])
      (DerivationList.nil : DerivationList definition [])
      (DerivationList.nil : DerivationList definition [])

@[simp] theorem firstOfTwo_prepend_singleton
    (application : RuleApplication definition ruleInstance [] goal) :
    (firstOfTwo application).prependDerivations
        (.cons (axiomDerivation application) .nil) =
      .cons (axiomDerivation application)
        (.cons (axiomDerivation application) .nil) := by
  simpa [firstOfTwo, axiomDerivation] using
    ScheduledProofSearchOccurrence.placed_prependDerivations
      ([] : GoalState) application [goal]
      (DerivationList.nil : DerivationList definition [])
      (DerivationList.nil : DerivationList definition [])
      (.cons (axiomDerivation application) .nil)

@[simp] theorem secondOfTwo_prepend_singleton
    (application : RuleApplication definition ruleInstance [] goal) :
    (secondOfTwo application).prependDerivations
        (.cons (axiomDerivation application) .nil) =
      .cons (axiomDerivation application)
        (.cons (axiomDerivation application) .nil) := by
  simpa [secondOfTwo, axiomDerivation] using
    ScheduledProofSearchOccurrence.placed_prependDerivations
      [goal] application ([] : GoalState)
      (.cons (axiomDerivation application) .nil)
      (DerivationList.nil : DerivationList definition [])
      (DerivationList.nil : DerivationList definition [])

/-- The canonical left-to-right schedule. -/
def leftFirst (application : RuleApplication definition ruleInstance [] goal) :
    ScheduledProofSearchPath definition [goal, goal] [] :=
  .cons (firstOfTwo application) (.cons (sole application) (.refl []))

/-- A distinct schedule that resolves the second authored occurrence first. -/
def rightFirst (application : RuleApplication definition ruleInstance [] goal) :
    ScheduledProofSearchPath definition [goal, goal] [] :=
  .cons (secondOfTwo application) (.cons (sole application) (.refl []))

theorem leftFirst_focusTrace
    (application : RuleApplication definition ruleInstance [] goal) :
    focusTrace (leftFirst application) = [0, 0] := rfl

theorem rightFirst_focusTrace
    (application : RuleApplication definition ruleInstance [] goal) :
    focusTrace (rightFirst application) = [1, 0] := rfl

/-- The two raw operational histories are genuinely different. -/
theorem leftFirst_ne_rightFirst
    (application : RuleApplication definition ruleInstance [] goal) :
    leftFirst application ≠ rightFirst application := by
  intro equal
  have traceEqual := congrArg focusTrace equal
  rw [leftFirst_focusTrace application,
    rightFirst_focusTrace application] at traceEqual
  cases traceEqual

/-- Positive independence control: the two schedules reconstruct the exact
same ordered proof justification, including both duplicated occurrences. -/
theorem leftFirst_sameJustification_rightFirst :
    ∀ application : RuleApplication definition ruleInstance [] goal,
      SameJustification (leftFirst application) (rightFirst application) := by
  intro application
  simp [SameJustification, leftFirst, rightFirst,
    scheduledPathToDerivationList, scheduledPathPrependDerivations,
    sole_prepend_nil, firstOfTwo_prepend_singleton,
    secondOfTwo_prepend_singleton]

/-- Both schedules perform the same amount of primitive work. -/
theorem leftFirst_length_eq_rightFirst_length :
    ∀ application : RuleApplication definition ruleInstance [] goal,
      (leftFirst application).length = (rightFirst application).length := by
  intro application
  exact observer_eq_of_factorsThroughJustification
    (pathLength_factorsThroughJustification definition [goal, goal])
    (leftFirst_sameJustification_rightFirst application)

/-- Negative observer control: the focus trace cannot factor through proof
justification, because it distinguishes two schedules of the same proof. -/
theorem focusTrace_does_not_factorThroughJustification :
    RuleApplication definition ruleInstance [] goal →
      ¬ FactorsThroughJustification
        (fun path : ScheduledProofSearchPath definition [goal, goal] [] =>
          focusTrace path) := by
  intro application factors
  have equal := observer_eq_of_factorsThroughJustification factors
    (leftFirst_sameJustification_rightFirst application)
  rw [leftFirst_focusTrace application,
    rightFirst_focusTrace application] at equal
  cases equal

/-! ### A dependent pair does not commute -/

variable {parent child : Pattern}
variable {parentRule childRule : RuleInstance}

/-- The checked justification in which a parent rule exposes one child
obligation and the child rule then closes it. -/
def dependentDerivation
    (parentApplication :
      RuleApplication definition parentRule [child] parent)
    (childApplication :
      RuleApplication definition childRule [] child) :
    Derivation definition parent :=
  .byRule parentRule parentApplication
    (.cons (.byRule childRule childApplication .nil) .nil)

/-- The only causally sensible two-step schedule: expose the child, then
discharge it. -/
def dependentParentThenChild
    (parentApplication :
      RuleApplication definition parentRule [child] parent)
    (childApplication :
      RuleApplication definition childRule [] child) :
    ScheduledProofSearchPath definition [parent] [] :=
  .cons (ScheduledProofSearchOccurrence.placed [] parentApplication [])
    (.cons (ScheduledProofSearchOccurrence.placed [] childApplication [])
      (.refl []))

/-- Positive dependent control: replay reconstructs the nested proof tree,
not two unrelated leaves. -/
theorem dependentParentThenChild_reconstructs
    (parentApplication :
      RuleApplication definition parentRule [child] parent)
    (childApplication :
      RuleApplication definition childRule [] child) :
    scheduledPathToDerivationList
        (dependentParentThenChild parentApplication childApplication) =
      .cons (dependentDerivation parentApplication childApplication) .nil := by
  let childDerivation : Derivation definition child :=
    .byRule childRule childApplication .nil
  have childReplay :
      (ScheduledProofSearchOccurrence.placed [] childApplication []).prependDerivations
          .nil = .cons childDerivation .nil := by
    simpa [childDerivation] using
      ScheduledProofSearchOccurrence.placed_prependDerivations
        ([] : GoalState) childApplication ([] : GoalState)
        (DerivationList.nil : DerivationList definition [])
        (DerivationList.nil : DerivationList definition [])
        (DerivationList.nil : DerivationList definition [])
  have parentReplay :
      (ScheduledProofSearchOccurrence.placed [] parentApplication []).prependDerivations
          (.cons childDerivation .nil) =
        .cons
          (.byRule parentRule parentApplication
            (.cons childDerivation .nil)) .nil := by
    simpa using
      ScheduledProofSearchOccurrence.placed_prependDerivations
        ([] : GoalState) parentApplication ([] : GoalState)
        (DerivationList.nil : DerivationList definition [])
        (.cons childDerivation .nil)
        (DerivationList.nil : DerivationList definition [])
  change
    (ScheduledProofSearchOccurrence.placed [] parentApplication []).prependDerivations
        ((ScheduledProofSearchOccurrence.placed [] childApplication []).prependDerivations
          .nil) =
      .cons
        (.byRule parentRule parentApplication
          (.cons (.byRule childRule childApplication .nil) .nil)) .nil
  rw [childReplay]
  exact parentReplay

/-- Negative dependent control: when parent and child judgments differ, the
child rule cannot run first because its conclusion is not yet an obligation. -/
theorem child_not_selectable_before_parent
    (different : child ≠ parent) :
    IsEmpty (SelectableConclusion definition [parent] child) :=
  not_selectableConclusion_of_not_mem (by simpa using different)

end Canary

#print axioms scheduledProofSearchGSLT_step_iff_application
#print axioms ScheduledProofSearchOccurrence.erase
#print axioms scheduledPathPrependDerivations_leftmostPathToScheduled
#print axioms scheduledPathToDerivationList_derivationListToScheduledPath
#print axioms derivationListEquivScheduleJustificationQuotient
#print axioms observer_eq_of_factorsThroughJustification
#print axioms scheduledPathToDerivationList_ruleCount
#print axioms pathLength_factorsThroughJustification
#print axioms not_selectableConclusion_of_not_mem
#print axioms Canary.leftFirst_ne_rightFirst
#print axioms Canary.leftFirst_sameJustification_rightFirst
#print axioms Canary.focusTrace_does_not_factorThroughJustification
#print axioms Canary.dependentParentThenChild_reconstructs
#print axioms Canary.child_not_selectable_before_parent

end Mettapedia.TypeTheory.CertificateGSLTScheduledHistory
