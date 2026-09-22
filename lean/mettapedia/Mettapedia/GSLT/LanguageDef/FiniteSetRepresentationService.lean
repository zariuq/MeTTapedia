import Mettapedia.GSLT.Dynamics.AnswerEffect
import Mettapedia.GSLT.LanguageDef.NIKServiceInvocation
import Mettapedia.GSLT.LanguageDef.NIKPropositionBranching

/-!
# Finite representations and native set-operation services

The executable objects here are ordinary lists. Their representation relation
is membership in an independently supplied abstract set, not equality of list
code and not a reduction rule. Append implements union at this relation while
retaining the original order and duplicate occurrences in its actual result.

The NIK operation has a real source-admission premise: the two input lists
must represent the caller's two declared sets. Execution does not inspect that
proof. A membership decision is complete only for a supplied finite
representation, with decidable equality on its elements. Neither construction
decides arbitrary sets or propositions, extends trusted conversion, or proves
textual-language/backend hosting.

This is the native-operation/decision route to a representation contract.
`BiformTheory` separately requires meanings of retained algorithmic events to
be theorems of a supplied declarative theory; no such theory or event syntax is
manufactured here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.FiniteSetRepresentationService

open Mettapedia.GSLT.Dynamics.AnswerEffects
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.NIKServiceInvocation

universe u

variable {α : Type u}

/-- An external extensional contract. Order and duplicates remain in `code`. -/
def Represents (code : List α) (set : Set α) : Prop :=
  ∀ value, value ∈ code ↔ value ∈ set

/-- This relation agrees with the existing list-to-finite-support projection;
the projection is not the stored or returned executable object. -/
theorem represents_iff_support (code : List α) (set : Set α) :
    Represents code set ↔ Finset.coeEmb (listToSupport.map code) = set := by
  classical
  have membership (value : α) :
      value ∈ Finset.coeEmb (listToSupport.map code) ↔ value ∈ code := by
    change value ∈ (code : Multiset α).toFinset ↔ value ∈ code
    simp
  constructor
  · intro represents
    ext value
    exact (membership value).trans (represents value)
  · intro same value
    rw [← same]
    exact (membership value).symm

theorem represents_append {left right : List α} {first second : Set α}
    (leftRepresents : Represents left first)
    (rightRepresents : Represents right second) :
    Represents (left ++ right) (first ∪ second) := by
  intro value
  exact List.mem_append.trans
    (or_congr (leftRepresents value) (rightRepresents value))

/-- The abstract set is a caller parameter, not defined as the algorithm's
image. The executable carrier remains a list. -/
def representedSet (set : Set α) : AdmissionObject.{u} where
  Carrier := List α
  Meaning := fun code => Represents code set

def unionSource (first second : Set α) : AdmissionObject.{u} where
  Carrier := List α × List α
  Meaning := fun input => Represents input.1 first ∧ Represents input.2 second

/-- Only the actual list append runs. Its semantic qualification is supplied
by the independent membership theorem. -/
def unionOperation (first second : Set α) :
    AdmissionHom (unionSource first second) (representedSet (first ∪ second)) where
  run input := input.1 ++ input.2
  preserves _ meaningful := represents_append meaningful.1 meaningful.2

def unionService (first second : Set α) :
    NIK.Service.{u, 0} (representedSet (first ∪ second)) :=
  .nativeOperation (unionSource first second) (unionOperation first second)

def unionRequest (first second : Set α) (input : List α × List α) :
    Request (unionService first second) :=
  .nativeOperation input

theorem union_input_admission_iff (first second : Set α)
    (input : List α × List α) :
    InputAdmission (unionRequest first second input) ↔
      Represents input.1 first ∧ Represents input.2 second :=
  native_operation_input_admission_iff (unionOperation first second) input

/-- Exact ordered output is an execution fact even on unadmitted inputs. -/
theorem union_returns_append (first second : Set α) (input : List α × List α) :
    (invoke (unionRequest first second input)).acceptedValue =
      some (input.1 ++ input.2) :=
  rfl

theorem union_accepted_iff (first second : Set α) (input : List α × List α)
    (output : List α) :
    (invoke (unionRequest first second input)).acceptedValue = some output ↔
      output = input.1 ++ input.2 := by
  change (some (input.1 ++ input.2) : Option (List α)) = some output ↔ _
  rw [Option.some.injEq, eq_comm]

/-- The semantic statement, unlike execution, requires the original source
admission. It uses the existing four-face invocation soundness theorem. -/
theorem accepted_union_represents (first second : Set α)
    (input : List α × List α)
    (admitted : InputAdmission (unionRequest first second input))
    {output : List α}
    (accepted : (invoke (unionRequest first second input)).acceptedValue = some output) :
    Represents output (first ∪ second) :=
  accepted_meaning (unionRequest first second input) admitted accepted

def membershipTarget (set : Set α) : AdmissionObject.{u} where
  Carrier := α
  Meaning := fun value => value ∈ set

/-- Equality testing plus a supplied representation licenses a complete
membership decision for this set only. The function is `List.contains`. -/
def membershipKernel [DecidableEq α] (code : List α) (set : Set α)
    (represents : Represents code set) :
    Checker.DecisionKernel α (fun value => value ∈ set) where
  decide value := code.contains value
  correct value := by
    simpa only [List.contains_iff_mem] using represents value

def membershipService [DecidableEq α] (code : List α) (set : Set α)
    (represents : Represents code set) : NIK.Service.{u, 0} (membershipTarget set) :=
  .directDecision (membershipKernel code set represents)

def membershipRequest [DecidableEq α] (code : List α) (set : Set α)
    (represents : Represents code set) (value : α) :
    Request (membershipService code set represents) :=
  .directDecision value

theorem membership_request_admitted [DecidableEq α] (code : List α) (set : Set α)
    (represents : Represents code set) (value : α) :
    InputAdmission (membershipRequest code set represents value) :=
  .directDecision

theorem membership_service_true_iff [DecidableEq α]
    (code : List α) (set : Set α) (represents : Represents code set) (value : α) :
    invoke (membershipRequest code set represents value) = .decided true ↔ value ∈ set :=
  direct_decision_true_iff (target := membershipTarget set)
    (membershipKernel code set represents) value

/-- Here a negative answer really does refute membership, because this
particular service is a complete decision, not incomplete evidence search. -/
theorem membership_service_false_iff [DecidableEq α]
    (code : List α) (set : Set α) (represents : Represents code set) (value : α) :
    invoke (membershipRequest code set represents value) = .decided false ↔ value ∉ set :=
  direct_decision_false_iff (target := membershipTarget set)
    (membershipKernel code set represents) value

theorem membership_accepted_iff [DecidableEq α]
    (code : List α) (set : Set α) (represents : Represents code set) (value : α) :
    (invoke (membershipRequest code set represents value)).acceptedValue = some value ↔
      value ∈ set := by
  change (if code.contains value = true then some value else none) =
    (some value : Option α) ↔ value ∈ set
  rw [← (membershipKernel code set represents).correct value]
  change _ ↔ code.contains value = true
  cases code.contains value <;> simp

/-- The operation's exact result becomes the next decision service's actual
finite representation. Both services retain their existing invocation types. -/
theorem union_then_membership [DecidableEq α] (first second : Set α)
    (input : List α × List α)
    (admitted : InputAdmission (unionRequest first second input))
    {output : List α}
    (accepted : (invoke (unionRequest first second input)).acceptedValue = some output) :
    output = input.1 ++ input.2 ∧
      ∃ represents : Represents output (first ∪ second), ∀ value,
        (invoke (membershipRequest output (first ∪ second) represents value)).acceptedValue =
          some value ↔ value ∈ first ∨ value ∈ second := by
  refine ⟨(union_accepted_iff first second input output).mp accepted,
    accepted_union_represents first second input admitted accepted, ?_⟩
  intro value
  exact membership_accepted_iff output (first ∪ second) _ value

section Branching

open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open NIKPropositionBranching

universe uState uAnswer uIntent

variable {State : Type uState} {Answer : Type uAnswer} {Intent : Type uIntent}

/-- A successfully returned, independently admitted append supplies the finite
membership decision consumed by the existing proposition brancher. For both
polarities, the complete ordered worlds are exactly those of the selected
evidence-dependent body. State, choice traces and deferred intents are not
erased or supplied by a second evaluator. -/
theorem accepted_union_branch_worlds [DecidableEq α] (first second : Set α)
    (input : List α × List α)
    (admitted : InputAdmission (unionRequest first second input))
    {output : List α}
    (accepted : (invoke (unionRequest first second input)).acceptedValue = some output)
    (value : α) (state : State) (branch : BranchTrace) :
    let kernel := membershipKernel output (first ∪ second)
      (accepted_union_represents first second input admitted accepted)
    let meaning := fun (set : Set α) (element : α) => element ∈ set
    let outcome := decideOutcome meaning (first ∪ second) kernel value
    ∀ (thenBody : (decisionAuthority meaning (first ∪ second) kernel).Evidence value →
        Program State Answer Intent)
      (elseBody : (decisionAuthority meaning (first ∪ second) kernel).Obstruction value →
        Program State Answer Intent),
      output = input.1 ++ input.2 ∧
      ((value ∈ first ∨ value ∈ second) → ∃ evidence,
        runWorldsAt (branchProgram outcome thenBody elseBody) state branch =
          (runWorldsAt (thenBody evidence) state branch).map
            (Mettapedia.TypeTheory.ContextualDependentSequencing.WorldResult.mapAnswer
              (fun answer => .established (evidence, answer)))) ∧
      ((value ∉ first ∧ value ∉ second) → ∃ evidence,
        runWorldsAt (branchProgram outcome thenBody elseBody) state branch =
          (runWorldsAt (elseBody evidence) state branch).map
            (Mettapedia.TypeTheory.ContextualDependentSequencing.WorldResult.mapAnswer
              (fun answer => .refuted (evidence, answer)))) := by
  dsimp only
  intro thenBody elseBody
  let kernel := membershipKernel output (first ∪ second)
    (accepted_union_represents first second input admitted accepted)
  let meaning := fun (set : Set α) (element : α) => element ∈ set
  let outcome := decideOutcome meaning (first ∪ second) kernel value
  refine ⟨(union_accepted_iff first second input output).mp accepted, ?_, ?_⟩
  · intro present
    have positive : outcome.asBool = some true :=
      (decideOutcome_true_iff meaning (first ∪ second) kernel value).mpr present
    obtain ⟨evidence, selected⟩ := outcome.asBool_eq_true_iff.mp positive
    refine ⟨evidence, ?_⟩
    change runWorldsAt (branchProgram outcome thenBody elseBody) state branch = _
    rw [selected]
    exact established_worlds evidence thenBody elseBody state branch
  · intro absent
    have negative : outcome.asBool = some false :=
      (decideOutcome_false_iff meaning (first ∪ second) kernel value).mpr
        (fun present => present.elim absent.1 absent.2)
    obtain ⟨evidence, selected⟩ := outcome.asBool_eq_false_iff.mp negative
    refine ⟨evidence, ?_⟩
    change runWorldsAt (branchProgram outcome thenBody elseBody) state branch = _
    rw [selected]
    exact refuted_worlds evidence thenBody elseBody state branch

end Branching

/-- A deficient executable operation cannot acquire the same union contract.
The witness input is independently admitted, so this is not an empty-fibre
argument. A right-only element refutes the result of dropping the right list. -/
theorem no_left_only_union_admission (first second : Set α)
    (input : List α × List α)
    (admitted : (unionSource first second).Meaning input)
    (value : α) (rightOnly : value ∈ second) (notLeft : value ∉ first) :
    ¬ ∃ operation : AdmissionHom (unionSource first second)
        (representedSet (first ∪ second)), operation.run = Prod.fst := by
  rintro ⟨operation, sameRun⟩
  have outputMeaning := operation.preserves input admitted
  rw [sameRun] at outputMeaning
  have inOutput := (outputMeaning value).mpr (Or.inr rightOnly)
  exact notLeft ((admitted.1 value).mp inOutput)

namespace Controls

/-- These predicates are fixed independently of both executable unions. -/
def first : Set Nat := { value | value = 1 ∨ value = 2 }

def second : Set Nat := { value | value = 3 ∨ value = 1 }

def input : List Nat × List Nat := ([2, 1, 2], [3, 1])

theorem input_represents :
    Represents input.1 first ∧ Represents input.2 second := by
  constructor <;> intro value <;>
    simp [input, first, second, or_comm, or_left_comm]

theorem input_admitted : InputAdmission (unionRequest first second input) :=
  (union_input_admission_iff first second input).mpr input_represents

theorem actual_union :
    (invoke (unionRequest first second input)).acceptedValue = some [2, 1, 2, 3, 1] :=
  union_returns_append first second input

theorem actual_union_represents : Represents [2, 1, 2, 3, 1] (first ∪ second) :=
  accepted_union_represents first second input input_admitted actual_union

theorem actual_membership :
    invoke (membershipRequest [2, 1, 2, 3, 1] (first ∪ second)
      actual_union_represents 3) = .decided true ∧
    invoke (membershipRequest [2, 1, 2, 3, 1] (first ∪ second)
      actual_union_represents 4) = .decided false := by
  constructor <;> rfl

theorem actual_result_retains_order_and_duplicates :
    ([2, 1, 2, 3, 1] : List Nat).head? = some 2 ∧
      ([2, 1, 2, 3, 1] : List Nat).count 2 = 2 ∧
      ([2, 1, 2, 3, 1] : List Nat).count 1 = 2 := by
  decide

theorem reordered_represents : Represents [3, 1, 2, 1, 2] (first ∪ second) := by
  intro value
  simp [first, second, or_comm, or_left_comm, or_assoc]

theorem deduplicated_represents : Represents [1, 2, 3] (first ∪ second) := by
  intro value
  simp [first, second, or_comm, or_left_comm, or_assoc]

/-- Extensional agreement neither sorts nor deduplicates the retained code. -/
theorem same_set_distinct_codes :
    Represents [2, 1, 2, 3, 1] (first ∪ second) ∧
      Represents [3, 1, 2, 1, 2] (first ∪ second) ∧
      Represents [1, 2, 3] (first ∪ second) ∧
      ([2, 1, 2, 3, 1] : List Nat) ≠ [3, 1, 2, 1, 2] ∧
      ([2, 1, 2, 3, 1] : List Nat) ≠ [1, 2, 3] := by
  exact ⟨actual_union_represents, reordered_represents, deduplicated_represents,
    by decide, by decide⟩

theorem set_meaning_cannot_recover_all_codes :
    ¬ ∃ recover : Set Nat → List Nat, ∀ code,
      Represents code (first ∪ second) → recover (first ∪ second) = code := by
  rintro ⟨recover, recovers⟩
  have impossible := (recovers _ actual_union_represents).symm.trans
    (recovers _ deduplicated_represents)
  exact same_set_distinct_codes.2.2.2.2 impossible

/-- Deliberately incorrect union: its runtime silently drops the right list. -/
def leftOnly (lists : List Nat × List Nat) : List Nat := lists.1

theorem wrong_union_fails_same_relation :
    (unionSource first second).Meaning input ∧
      leftOnly input = [2, 1, 2] ∧
      ¬ Represents (leftOnly input) (first ∪ second) := by
  refine ⟨input_represents, rfl, ?_⟩
  intro represents
  have missing := (represents 3).mpr (Or.inr (Or.inl rfl))
  simp [leftOnly, input] at missing

theorem wrong_union_not_admitted :
    ¬ ∃ operation : AdmissionHom (unionSource first second)
        (representedSet (first ∪ second)), operation.run = leftOnly :=
  no_left_only_union_admission first second input input_represents 3
    (Or.inl rfl) (by simp [first])

/-- The admission proof is not a hidden runtime gate: an invalid source still
computes, but its successful-looking response has no promised set meaning. -/
theorem unadmitted_input_still_computes :
    ¬ InputAdmission (unionRequest first second ([0], [3, 1])) ∧
      (invoke (unionRequest first second ([0], [3, 1]))).acceptedValue =
        some [0, 3, 1] ∧
      ¬ Represents [0, 3, 1] (first ∪ second) := by
  refine ⟨?_, union_returns_append first second ([0], [3, 1]), ?_⟩
  · intro admitted
    have represents := (union_input_admission_iff first second _).mp admitted
    have extra := (represents.1 0).mp (by simp)
    simp [first] at extra
  · intro represents
    have extra := (represents 0).mp (by simp)
    simp [first, second] at extra

open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open NIKPropositionBranching

/-- The brancher's input code is the actual admitted union's result. Its two
bodies are the existing state-and-intent controls, now driven by membership
in these externally declared sets rather than their original SAT workload. -/
def branchAfterUnion (value : Nat) :=
  branchProgram
    (decideOutcome (fun (set : Set Nat) element => element ∈ set) (first ∪ second)
      (membershipKernel ((unionOperation first second).run input) (first ∪ second)
        (accepted_union_represents first second input input_admitted
          (union_returns_append first second input))) value)
    NIKPropositionBranching.Controls.thenEffect
    NIKPropositionBranching.Controls.elseEffect

theorem present_selects_only_then :
    (runWorldsAt (branchAfterUnion 3) 7 [true]).map
      (fun world => (world.answer.asBool, world.branch, world.state, world.intents)) =
        [(some true, [true], 8, ["then"])] :=
  rfl

theorem absent_selects_only_else :
    (runWorldsAt (branchAfterUnion 4) 7 [true]).map
      (fun world => (world.answer.asBool, world.branch, world.state, world.intents)) =
        [(some false, [true], 107, ["else"])] :=
  rfl

theorem admitted_union_decides_and_branches :
    InputAdmission (unionRequest first second input) ∧
      (invoke (unionRequest first second input)).acceptedValue = some [2, 1, 2, 3, 1] ∧
      Represents [2, 1, 2, 3, 1] (first ∪ second) ∧
      (runWorldsAt (branchAfterUnion 3) 7 [true]).map
        (fun world => (world.answer.asBool, world.branch, world.state, world.intents)) =
          [(some true, [true], 8, ["then"])] ∧
      (runWorldsAt (branchAfterUnion 4) 7 [true]).map
        (fun world => (world.answer.asBool, world.branch, world.state, world.intents)) =
          [(some false, [true], 107, ["else"])] :=
  ⟨input_admitted, actual_union, actual_union_represents,
    present_selects_only_then, absent_selects_only_else⟩

end Controls

end Mettapedia.GSLT.LanguageDef.FiniteSetRepresentationService
