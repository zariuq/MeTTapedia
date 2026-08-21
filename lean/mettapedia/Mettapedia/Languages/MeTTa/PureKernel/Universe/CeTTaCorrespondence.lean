import Mettapedia.Languages.MeTTa.PureKernel.Universe.OutcomeContract

/-!
# Native authority correspondence and run gates

This module is the proof interface between an independent Prime authority and
a native implementation.  Native execution does not define the theory.  It
returns a receipt whose semantic outcome is evidence-bearing, whose authority
identity is stable, and whose resource refinement obeys the budget order.

Only checked refutation may remove a candidate occurrence from learning.
Only checked establishment may authorize execution.  Operational faults stay
outside the semantic outcome and authorize neither action.
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation

namespace CeTTaCorrespondence

open OutcomeContract
open Mettapedia.TypeTheory.AuthorityTheory

universe u v w x y

/-! ## The display quotient loses operational distinctions -/

inductive FlatCheckingStatus where
  | established
  | refuted
  | undetermined
  | incomplete
deriving DecidableEq, Repr

/-- A deliberately lossy display for a complete native run. -/
def flatStatus : NativeRunTag → FlatCheckingStatus
  | .ok .established => .established
  | .ok .refuted => .refuted
  | .ok .incomplete => .incomplete
  | .ok .outsideFragment => .undetermined
  | .fault => .undetermined

def outsideRunTag : NativeRunTag := .ok .outsideFragment
def engineFailureRunTag : NativeRunTag := .fault

@[simp] theorem outside_flatStatus :
    flatStatus outsideRunTag = .undetermined :=
  rfl

@[simp] theorem engineFailure_flatStatus :
    flatStatus engineFailureRunTag = .undetermined :=
  rfl

/-- Flattening loses semantic abstention versus operational failure even
though the canonical run type keeps them in different layers. -/
theorem flatStatus_not_injective : ¬ Function.Injective flatStatus := by
  intro injective
  have equality : outsideRunTag = engineFailureRunTag := injective rfl
  exact (by decide : outsideRunTag ≠ engineFailureRunTag) equality

theorem outside_and_engine_have_distinct_meanings :
    outsideRunTag.publicObservation = .status .undetermined ∧
      engineFailureRunTag.publicObservation = .operationalFault () :=
  ⟨rfl, rfl⟩

/-! ## Explicit budgets -/

inductive BudgetRequest where
  | bounded (steps : Nat)
  | unbounded
deriving DecidableEq, Repr

def BudgetRequest.le : BudgetRequest → BudgetRequest → Prop
  | .bounded smaller, .bounded larger => smaller ≤ larger
  | .bounded _, .unbounded => True
  | .unbounded, .unbounded => True
  | .unbounded, .bounded _ => False

instance : LE BudgetRequest := ⟨BudgetRequest.le⟩

@[simp] theorem BudgetRequest.bounded_le_bounded (smaller larger : Nat) :
    BudgetRequest.bounded smaller ≤ .bounded larger ↔ smaller ≤ larger :=
  Iff.rfl

@[simp] theorem BudgetRequest.bounded_le_unbounded (steps : Nat) :
    BudgetRequest.bounded steps ≤ .unbounded :=
  trivial

@[simp] theorem BudgetRequest.unbounded_not_le_bounded (steps : Nat) :
    ¬ (BudgetRequest.unbounded ≤ .bounded steps) := by
  intro impossible
  exact impossible

theorem BudgetRequest.le_refl (budget : BudgetRequest) : budget ≤ budget := by
  cases budget with
  | bounded steps => exact Nat.le_refl steps
  | unbounded => trivial

theorem BudgetRequest.le_trans {first second third : BudgetRequest}
    (firstSecond : first ≤ second) (secondThird : second ≤ third) :
    first ≤ third := by
  cases first with
  | bounded firstSteps =>
      cases second with
      | bounded secondSteps =>
          cases third with
          | bounded thirdSteps =>
              exact Nat.le_trans firstSecond secondThird
          | unbounded => trivial
      | unbounded =>
          cases third with
          | bounded thirdSteps => exact False.elim secondThird
          | unbounded => trivial
  | unbounded =>
      cases second with
      | bounded secondSteps => exact False.elim firstSecond
      | unbounded =>
          cases third with
          | bounded thirdSteps => exact False.elim secondThird
          | unbounded => trivial

/-! ## The native checker obligation record -/

def RunDecided {Failure : Type u} {Established : Sort v} {Refuted : Sort w}
    {Boundary : Type x} {Incomplete : Type y} :
    RunResult Failure (Outcome Established Refuted Boundary Incomplete) → Prop
  | .ok outcome => Outcome.Decided outcome
  | .fault _ => False

/-- Obligations for reading one native procedure as an implementation of a
named authority.  Faults are constrained at the transport layer; budget
monotonicity compares semantic outcomes only when both runs returned one. -/
structure NativeCheckerObligations
    (Input : Type u) (Judgment : Type v)
    (authority : Authority.{v, w, x} Judgment)
    (profile : Profile) (Provenance : Type y) where
  key : AuthorityKey
  keyProfile : key.profile = profile
  denote : Input → Judgment
  classOf : Input → JudgmentClass
  run : (budget : BudgetRequest) → (input : Input) →
    Receipt authority BoundaryReason ResourceReceipt FaultReason BudgetRequest
      Provenance key budget (denote input)
  unboundedInClass : ∀ input,
    classify profile (classOf input) = .inClass →
      RunDecided (run .unbounded input).result
  unboundedOutside : ∀ input reason,
    classify profile (classOf input) = .outOfClass reason →
      (run .unbounded input).result = .ok (.outsideFragment reason)
  unboundedFault : ∀ input reason,
    classify profile (classOf input) = .fault reason →
      (run .unbounded input).result = .fault reason
  monotone : ∀ input {smaller larger}, smaller ≤ larger →
    ∀ smallerOutcome largerOutcome,
      (run smaller input).result = .ok smallerOutcome →
      (run larger input).result = .ok largerOutcome →
      Outcome.BudgetRefines smallerOutcome largerOutcome

namespace NativeCheckerObligations

variable {Input : Type u} {Judgment : Type v}
variable {authority : Authority.{v, w, x} Judgment}
variable {profile : Profile} {Provenance : Type y}

theorem inClass_unbounded_decides
    (checker : NativeCheckerObligations Input Judgment authority profile
      Provenance)
    (input : Input)
    (inClass : classify profile (checker.classOf input) = .inClass) :
    RunDecided (checker.run .unbounded input).result :=
  checker.unboundedInClass input inClass

/-- A declared in-class unbounded run cannot be an operational fault. -/
theorem inClass_unbounded_not_fault
    (checker : NativeCheckerObligations Input Judgment authority profile
      Provenance)
    (input : Input)
    (inClass : classify profile (checker.classOf input) = .inClass) :
    ∀ failure, (checker.run .unbounded input).result ≠ .fault failure := by
  intro failure equality
  have decided := checker.inClass_unbounded_decides input inClass
  rw [equality] at decided
  exact decided

/-- The Boolean view is justified exactly where an outcome is decided. -/
theorem inClass_unbounded_has_boolean
    (checker : NativeCheckerObligations Input Judgment authority profile
      Provenance)
    (input : Input)
    (inClass : classify profile (checker.classOf input) = .inClass) :
    ∃ outcome value,
      (checker.run .unbounded input).result = .ok outcome ∧
        outcome.asBool = some value := by
  have decided := checker.inClass_unbounded_decides input inClass
  generalize resultEquality : (checker.run .unbounded input).result = result at decided ⊢
  cases result with
  | fault failure => exact False.elim decided
  | ok outcome =>
      cases decided with
      | established evidence => exact ⟨_, true, rfl, rfl⟩
      | refuted obstruction => exact ⟨_, false, rfl, rfl⟩

theorem no_budget_flip_established_to_refuted
    (checker : NativeCheckerObligations Input Judgment authority profile
      Provenance)
    (input : Input) {smaller larger : BudgetRequest}
    (budgetOrder : smaller ≤ larger)
    {evidence : authority.Evidence (checker.denote input)}
    {obstruction : authority.Obstruction (checker.denote input)}
    (smallResult : (checker.run smaller input).result =
      .ok (.established evidence))
    (largeResult : (checker.run larger input).result =
      .ok (.refuted obstruction)) : False := by
  have refinement := checker.monotone input budgetOrder
    (.established evidence) (.refuted obstruction) smallResult largeResult
  exact Outcome.not_budget_flip_established_refuted evidence obstruction
    refinement

theorem no_budget_flip_refuted_to_established
    (checker : NativeCheckerObligations Input Judgment authority profile
      Provenance)
    (input : Input) {smaller larger : BudgetRequest}
    (budgetOrder : smaller ≤ larger)
    {obstruction : authority.Obstruction (checker.denote input)}
    {evidence : authority.Evidence (checker.denote input)}
    (smallResult : (checker.run smaller input).result =
      .ok (.refuted obstruction))
    (largeResult : (checker.run larger input).result =
      .ok (.established evidence)) : False := by
  have refinement := checker.monotone input budgetOrder
    (.refuted obstruction) (.established evidence) smallResult largeResult
  exact Outcome.not_budget_flip_refuted_established obstruction evidence
    refinement

/-- More fuel cannot turn a fixed authority's fragment abstention into a
decision. -/
theorem budget_preserves_outside_fragment
    (checker : NativeCheckerObligations Input Judgment authority profile
      Provenance)
    (input : Input) {smaller larger : BudgetRequest}
    (budgetOrder : smaller ≤ larger) (reason : BoundaryReason)
    {later : AuthorizedOutcome authority BoundaryReason ResourceReceipt
      (checker.denote input)}
    (smallResult : (checker.run smaller input).result =
      .ok (.outsideFragment reason))
    (largeResult : (checker.run larger input).result = .ok later) :
    later = .outsideFragment reason := by
  exact Outcome.budget_does_not_resolve_outside reason later
    (checker.monotone input budgetOrder (.outsideFragment reason) later
      smallResult largeResult)

end NativeCheckerObligations

/-! ## Safe learning versus executable admission -/

def safeRetain : NativeRunTag → Bool
  | .ok .refuted => false
  | _ => true

def executable : NativeRunTag → Bool
  | .ok .established => true
  | _ => false

theorem safeRetain_false_iff (tag : NativeRunTag) :
    safeRetain tag = false ↔ tag = .ok .refuted := by
  cases tag with
  | ok outcome => cases outcome <;> decide
  | fault => decide

theorem executable_true_iff (tag : NativeRunTag) :
    executable tag = true ↔ tag = .ok .established := by
  cases tag with
  | ok outcome => cases outcome <;> decide
  | fault => decide

theorem abstention_retained_not_executable :
    safeRetain outsideRunTag = true ∧ executable outsideRunTag = false :=
  ⟨rfl, rfl⟩

theorem incomplete_retained_not_executable :
    safeRetain (.ok .incomplete) = true ∧
      executable (.ok .incomplete) = false :=
  ⟨rfl, rfl⟩

theorem fault_retained_not_executable :
    safeRetain engineFailureRunTag = true ∧
      executable engineFailureRunTag = false :=
  ⟨rfl, rfl⟩

/-! ## Occurrence bags preserve multiplicity -/

structure TaggedOccurrence (Candidate : Type) where
  candidate : Candidate
  result : NativeRunTag

def observeAll {Candidate : Type} (observe : Candidate → NativeRunTag)
    (candidates : List Candidate) : List (TaggedOccurrence Candidate) :=
  candidates.map fun candidate => ⟨candidate, observe candidate⟩

def eraseAll {Candidate : Type}
    (occurrences : List (TaggedOccurrence Candidate)) : List Candidate :=
  occurrences.map TaggedOccurrence.candidate

@[simp] theorem erase_observeAll {Candidate : Type}
    (observe : Candidate → NativeRunTag) (candidates : List Candidate) :
    eraseAll (observeAll observe candidates) = candidates := by
  simp [eraseAll, observeAll, List.map_map, Function.comp_def]

def safeFrontier {Candidate : Type}
    (occurrences : List (TaggedOccurrence Candidate)) : List Candidate :=
  (occurrences.filter fun occurrence => safeRetain occurrence.result).map
    TaggedOccurrence.candidate

def executableFrontier {Candidate : Type}
    (occurrences : List (TaggedOccurrence Candidate)) : List Candidate :=
  (occurrences.filter fun occurrence => executable occurrence.result).map
    TaggedOccurrence.candidate

@[simp] theorem duplicate_abstention_preserved {Candidate : Type}
    (candidate : Candidate) :
    safeFrontier
      [⟨candidate, outsideRunTag⟩, ⟨candidate, outsideRunTag⟩] =
        [candidate, candidate] := by
  simp [safeFrontier, safeRetain, outsideRunTag]

@[simp] theorem duplicate_refutation_removed {Candidate : Type}
    (candidate : Candidate) :
    safeFrontier
      [⟨candidate, .ok .refuted⟩, ⟨candidate, .ok .refuted⟩] = [] := by
  simp [safeFrontier, safeRetain]

theorem safe_and_executable_frontiers_differ_on_abstention
    {Candidate : Type} (candidate : Candidate) :
    safeFrontier [⟨candidate, outsideRunTag⟩] = [candidate] ∧
      executableFrontier [⟨candidate, outsideRunTag⟩] = [] := by
  simp [safeFrontier, executableFrontier, safeRetain, executable,
    outsideRunTag]

/-! ## Axiom audit -/

#print axioms flatStatus_not_injective
#print axioms NativeCheckerObligations.no_budget_flip_established_to_refuted
#print axioms duplicate_abstention_preserved

end CeTTaCorrespondence

end Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation
