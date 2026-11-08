import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualParkedContinuations
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualStandingCodeControls

/-!
# Two source arms compete for one pending continuation

Both source arms are independently admitted. One consumes request 1 and
the shared continuation; the other would consume request 2 and that same
continuation. The actual first compiled firing removes the claim, retains
both reusable code rows and leaves the second request untouched. No source
arm can subsequently select the consumed logical continuation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualParkedContinuations.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualRuleCode
open ContextualRuleCode.Controls (DataOp dataSignature base locals captures origin raw Tm symbol request result
  declaration before rows queryValue rowValue sourceDeclaration)
open ContextualConditionalRows ContextualConditionalSourceProblem
open ContextualStandingEvents ContextualStandingScheduler

local instance : DecidableEq dataSignature.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : dataSignature.Srt) : DecidableEq (dataSignature.Op sort) := inferInstanceAs (DecidableEq DataOp)

def code : Declaration (Tm raw) := arm (symbol 99) declaration
def store (occurrence : Nat) : Row locals captures [] () :=
  if occurrence = 3 then ofStored locals captures (.shared (symbol 99))
  else if occurrence = 7 ∨ occurrence = 8 then ofStored locals captures (.schema (encodeDeclaration code))
  else rows occurrence
def sourceWorld : ContextualConditionalExecution.State locals Nat [] () :=
  {before with present := {0, 1, 3, 7, 8}, rows := store}
def world : World dataSignature () Nat [] :=
  ⟨Nat, locals, inferInstance, sourceWorld, sourceWorld.present, []⟩
def queued : State dataSignature () Nat [] := ⟨world, {7, 8}⟩
def first : Selection Nat := ⟨[0], [], [90]⟩
def second : Selection Nat := ⟨[1], [], [91]⟩
def firstProblem := problem locals locals captures (ContextualStandingEntry.selected 7 (selected 3 first))
  (ContextualStandingEntry.activation locals captures code).rule store []
def secondProblem := problem locals locals captures (ContextualStandingEntry.selected 8 (selected 3 second))
  (ContextualStandingEntry.activation locals captures code).rule store []
def sourceCode (value : Tm origin) := arm (symbol 99) (sourceDeclaration value)

theorem first_problem_explicit : firstProblem =
    [(observe (symbol 99), observe (symbol 99)),
     (observe (request (queryValue 0)), observe (request (symbol 1))),
     (observe (encodeDeclaration (sourceCode (queryValue 0))),
      observe (encodeDeclaration (sourceCode (rowValue 4))))] := by
  with_unfolding_all rfl

theorem second_problem_explicit : secondProblem =
    [(observe (symbol 99), observe (symbol 99)),
     (observe (request (queryValue 0)), observe (request (symbol 2))),
     (observe (encodeDeclaration (sourceCode (queryValue 0))),
      observe (encodeDeclaration (sourceCode (rowValue 4))))] := by
  with_unfolding_all rfl

def model (value : Nat) : Assignment origin captures
  | .inl _ => symbol value
  | .inr (.inl _) => symbol value
  | .inr (.inr _) => symbol 0

theorem first_source : SourceReady world 7 3 (symbol 99) declaration first := by
  refine ⟨⟨rfl, ?_⟩, by decide +kernel⟩
  refine ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    ⟨Nat, captures, model 1, ?_⟩, ?_⟩
  · change ContextualResidual.Models (model 1) firstProblem
    rw [first_problem_explicit]
    intro equation member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl
  · intro check member
    cases member

theorem second_source : SourceReady world 8 3 (symbol 99) declaration second := by
  refine ⟨⟨rfl, ?_⟩, by decide +kernel⟩
  refine ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    ⟨Nat, captures, model 2, ?_⟩, ?_⟩
  · change ContextualResidual.Models (model 2) secondProblem
    rw [second_problem_explicit]
    intro equation member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl
  · intro check member
    cases member

theorem one_compiled_arm_removes_the_shared_claim :
    ∃ invocation : Invocation world, invocation.installation = 7 ∧ invocation.Admissible ∧
      Allowed queued (.commit world (.invoke invocation)) ∧
      invocation.target.current.present = {1, 7, 8, 90} ∧
      (∀ held body picked, ¬ SourceReady invocation.target 8 3 held body picked) := by
  obtain ⟨invocation, installation, _, shape, admissible, _⟩ := realize_source_arm first_source 0
  refine ⟨invocation, installation, admissible, ⟨rfl, admissible, ?_⟩, ?_, ?_⟩
  · change invocation.installation ∈ ({7, 8} : Set Nat)
    rw [installation]
    exact Or.inl rfl
  · have physical := (Action.invoke invocation).physical_result
    change invocation.target.current.present = _ at physical
    rw [physical]
    simp only [Action.taken, Action.made, shape]
    decide +kernel
  · intro held body picked source
    exact an_executed_arm_consumes_the_continuation invocation 3 first shape
      (source_needs_the_continuation source)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualParkedContinuations.Controls
