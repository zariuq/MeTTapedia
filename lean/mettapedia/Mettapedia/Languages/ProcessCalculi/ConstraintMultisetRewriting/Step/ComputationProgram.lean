import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationReplay
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Spaces

/-!
# A fixed table-and-descriptor program restricting the actual full step

The program value contains a finite equation table and its checked relation
to the qualified source package. The existing finite code grammar supplies
primitive reductions and constructor paths. Neither the program value nor
its table depends on the term being run.

A proposal contains syntax, a decoded event and literal source alignment;
it contains no source reduction or target admission assumption. The actual
full step checks its resource operation. Program permission restricts that
step to compilations of these proposals.

This backend validates a path and substitution descriptor before matching
the complete represented row. It does not implement higher-order context
matching in the native unifier, or claim to be a compiler to ordinary
context-free transform rule syntax.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProgram

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull
open AlgebraicSchema AlgebraicParallel NativeTypesOnTheStep.Computing

structure Program {Head : Type} (rules : Rules Head) where
  table : SchemaTable Head
  presentation : SchemaPresentation rules
  same : ∀ {arity : Nat} (left right : Tm Head arity),
    presentation.schema left right ↔ table.family left right

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
  (program : Program S.R) [DecidableRel S.R.headEq]

structure Proposal (state : State S.R Nat) where
  source : Nat
  target : Nat
  code : ComputationReplay.Code (Head := Head) state.frame.arity
  event : ComputationSyntax.Event program.presentation state.frame.arity
  parsed : ComputationReplaySyntax.decodeEvent program.presentation program.table program.same code = some event
  aligned : event.source = (state.label source).2.code

variable {program}

theorem Proposal.reduction {state : State S.R Nat} (proposal : Proposal program state) :
    StepCore S.R.computation S.R.headEq (state.label proposal.source).2.code proposal.event.target := by
  have source := proposal.event.sound
  rwa [proposal.aligned] at source

def Proposal.output (qualified : Qualified S) {state : State S.R Nat} (proposal : Proposal program state) :
    TotalTerm state.frame :=
  ⟨(state.label proposal.source).1, ⟨proposal.event.target,
    (qualified.subjectReduction state.frame.formed (.single proposal.reduction)
      (state.label proposal.source).2.typed).1⟩⟩

def Proposal.compile (qualified : Qualified S) {state : State S.R Nat} (proposal : Proposal program state) :
    Firing S.levels state :=
  ComputationResources.firing S.levels state proposal.source proposal.target (proposal.output qualified)

theorem Proposal.admitted_iff (qualified : Qualified S) {state : State S.R Nat}
    (proposal : Proposal program state) :
    (step S.levels Nat).Admits (proposal.compile qualified) ↔
      proposal.source ∈ state.present ∧ proposal.target ∉ state.present ∧
        (frames S.levels).Solvable state.knowledge :=
  ComputationResources.admitted_iff S.levels _ _ _ _

def Proposal.instruction {state : State S.R Nat} (proposal : Proposal program state)
    (present : proposal.source ∈ state.present) (consistent : (frames S.levels).Solvable state.knowledge) :
    ComputationProfile.Instruction program.presentation
      (⟨state, proposal.source, present, consistent⟩ : ComputationProfile.Configuration (S := S)) :=
  ⟨proposal.event, proposal.aligned⟩

theorem Proposal.compile_instruction (qualified : Qualified S) {state : State S.R Nat}
    (proposal : Proposal program state) (present : proposal.source ∈ state.present)
    (consistent : (frames S.levels).Solvable state.knowledge) :
    (proposal.instruction present consistent).compile qualified proposal.target = proposal.compile qualified := rfl

variable (program)

def permits (qualified : Qualified S) {state : State S.R Nat} (firing : Firing S.levels state) : Prop :=
  ∃ proposal : Proposal program state, proposal.compile qualified = firing

def restricted (qualified : Qualified S) :=
  Spaces.restrict (step S.levels Nat).toStep (permits program qualified)

theorem admission_is_native (qualified : Qualified S) {state : State S.R Nat}
    (firing : Firing S.levels state) :
    (restricted program qualified).Admits firing ↔
      (step S.levels Nat).Admits firing ∧ permits program qualified firing := Iff.rfl

theorem proposal_is_permitted (qualified : Qualified S) {state : State S.R Nat}
    (proposal : Proposal program state) : permits program qualified (proposal.compile qualified) :=
  ⟨proposal, rfl⟩

theorem every_admitted_firing_computes (qualified : Qualified S) {state : State S.R Nat}
    {firing : Firing S.levels state} (accepted : (restricted program qualified).Admits firing) :
    ∃ proposal : Proposal program state,
      proposal.compile qualified = firing ∧
      proposal.source ∈ state.present ∧ proposal.target ∉ state.present ∧
      StepCore S.R.computation S.R.headEq (state.label proposal.source).2.code proposal.event.target := by
  obtain ⟨proposal, same⟩ := accepted.2
  have native : (step S.levels Nat).Admits (proposal.compile qualified) := same.symm ▸ accepted.1
  have shape := (proposal.admitted_iff qualified).mp native
  exact ⟨proposal, same, shape.1, shape.2.1, proposal.reduction⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProgram

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProgram.every_admitted_firing_computes
