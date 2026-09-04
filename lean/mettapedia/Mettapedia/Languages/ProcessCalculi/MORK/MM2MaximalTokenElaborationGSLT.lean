import Mettapedia.GSLT.Core.ClosureCriteria
import Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenElaborationPlan
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-!
# Deterministic CST-to-Atom GSLT for MM2

The generated parser and MM2 execution are separated by one pure elaboration
stage.  Its source is an occurrence-preserving CST; its result is either the
exact ordered MM2 atom program or an explicit malformed-tree outcome.  This
module exposes that stage as a deterministic GSLT and through OSLF, without
introducing a second parser or a second execution semantics.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenElaborationGSLT

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.ClosureCriteria
open Mettapedia.GSLT.Parsing.PresentationExprSemantics
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenElaborationPlan
open Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenSemantics

inductive Control where
  | request (tree : CST)
  | halted (outcome : ElaborationOutcome)
  deriving Repr, DecidableEq

def step? : Control → Option Control
  | .request tree => some (.halted (compileRoot tree))
  | .halted _ => none

def theory : GSLT where
  Term := Control
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target => step? source = some target
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

@[simp] theorem theory_step_iff (source target : Control) :
    theory.Step source target ↔ step? source = some target :=
  Iff.rfl

theorem theory_step_deterministic
    {source first second : Control}
    (firstStep : theory.Step source first)
    (secondStep : theory.Step source second) :
    first = second := by
  exact Option.some.inj (firstStep.symm.trans secondStep)

theorem halted_is_normal (outcome : ElaborationOutcome) :
    theory.IsNormalForm (.halted outcome) := by
  rintro ⟨target, step⟩
  change step? (.halted outcome) = some target at step
  simp [step?] at step

/-- A deterministic driver exposes the same single transition to generic
bounded execution without carrying hidden private state. -/
def driver : HostedDriver theory where
  State := Unit
  step := fun source _ => (step? source).map fun target => (target, ())
  sound := by
    intro source state target state' moved
    cases state
    simp only [Option.map_eq_some_iff] at moved
    rcases moved with ⟨next, stepExact, pairExact⟩
    cases pairExact
    exact stepExact

abbrev exactOutcomeNativeType (outcome : ElaborationOutcome) :
    GSLTNativeType theory :=
  exactTargetNativeType theory (.halted outcome)

theorem satisfies_exactOutcomeNativeType_iff
    (tree : CST) (outcome : ElaborationOutcome) :
    (gsltOSLF theory).satisfies (.request tree)
        (exactOutcomeNativeType outcome).pred ↔
      compileRoot tree = outcome := by
  exact (satisfies_exactTargetNativeType_iff_step theory
    (.request tree) (.halted outcome)).trans (by
      change step? (.request tree) = some (.halted outcome) ↔ _
      simp [step?])

/-- A successfully planned parse takes the exact source-derived elaboration
step.  The result is reconstructed from the finite plan rather than stored in
the GSLT definition. -/
theorem parsed_program_inhabits_exact_outcome
    {input : List Nat} (parsed : PlannedProgram input) :
    (gsltOSLF theory).satisfies (.request parsed.tree)
      (exactOutcomeNativeType (.program parsed.atoms)).pred := by
  rw [satisfies_exactOutcomeNativeType_iff]
  exact parsed.compiledLowering

/-- Any claimed successful target reconstructs the finite-plan lowering
equation. -/
theorem successful_target_reflects_compiled_lowering
    {tree : CST} {atoms : List
      Mettapedia.Languages.MeTTa.OSLFCore.Atom}
    (step : theory.Step (.request tree) (.halted (.program atoms))) :
    compileRoot tree = .program atoms := by
  change step? (.request tree) = some (.halted (.program atoms)) at step
  simpa [step?] using step

/-! ## Positive and negative controls -/

private def emptyTree : CST :=
  .node "mm2:program-empty" 0 0 []

private def malformedTree : CST :=
  .node "mm2:program-open" 0 1 []

theorem empty_tree_steps_to_empty_program :
    theory.Step (.request emptyTree) (.halted (.program [])) := by
  change step? (.request emptyTree) = some (.halted (.program []))
  decide +kernel

theorem malformed_tree_steps_to_explicit_rejection :
    theory.Step (.request malformedTree) (.halted .malformedCST) := by
  change step? (.request malformedTree) = some (.halted .malformedCST)
  decide +kernel

theorem malformed_tree_cannot_step_to_empty_program :
    ¬ theory.Step (.request malformedTree) (.halted (.program [])) := by
  change ¬ (step? (.request malformedTree) = some (.halted (.program [])))
  decide +kernel

#print axioms theory_step_deterministic
#print axioms halted_is_normal
#print axioms satisfies_exactOutcomeNativeType_iff
#print axioms parsed_program_inhabits_exact_outcome
#print axioms successful_target_reflects_compiled_lowering
#print axioms empty_tree_steps_to_empty_program
#print axioms malformed_tree_steps_to_explicit_rejection
#print axioms malformed_tree_cannot_step_to_empty_program

end Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenElaborationGSLT
