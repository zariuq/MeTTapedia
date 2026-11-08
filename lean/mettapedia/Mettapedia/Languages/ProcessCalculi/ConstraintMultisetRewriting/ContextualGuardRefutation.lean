import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardSemantics
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameWorklist

/-!
# Certified absence from the existing contextual equation worklist

Each observed occurrence contributes one ordinary joint equation problem.
Only a certified refutation of every such problem establishes the absence
ask. A residual, including a solved compatible instance or fuel exhaustion,
does not certify absence. The checker exports no local binding or answer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardRefutation

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualGuardMatching

universe u
variable {S : Signature} {Local Shared Next Future : Type} {O : Type u}
  (locals : Local → MetaArity S) (captures : Shared → MetaArity S)
  {next : Next → MetaArity S} {future : Future → MetaArity S}

def joint {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S captures) Γ sort))
    (row : ContextualStoredRows.Row locals captures Γ sort) (pattern : Term (signature S captures) Γ sort) :
    EquationStore (Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort) :=
  ContextualFrameUnifier.mapProblem (ContextualSelectionViews.capturedSource locals captures) problem ++
    [(ContextualStoredRows.asTemplate locals captures row,
      instantiate (ContextualSelectionViews.capturedSource locals captures) pattern)]

def observedJoint {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S captures) Γ sort))
    (row : ContextualStoredRows.Row locals captures Γ sort) (pattern : Term (signature S captures) Γ sort) :
    ContextualResidual.Problem (ContextualSelectionViews.source locals captures) :=
  (joint locals captures problem row pattern).map fun equation => (observe equation.1, observe equation.2)

theorem instance_preserves_models (localBodies : Assignment locals future)
    (embedding : Assignment next future) (candidate : Assignment captures next)
    {Γ : Ctx S} {sort : S.Srt} (problem : EquationStore (Term (signature S captures) Γ sort))
    (solved : ContextualFrameUnifier.Models candidate problem) :
    ContextualFrameUnifier.Models (instanceAssignment locals localBodies embedding candidate)
      (ContextualFrameUnifier.mapProblem (ContextualSelectionViews.capturedSource locals captures) problem) := by
  intro equation member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  exact (instance_on_shared_value locals localBodies embedding candidate original.1).trans
    ((congrArg (instantiate embedding) (solved original present)).trans
      (instance_on_shared_value locals localBodies embedding candidate original.2).symm)

theorem match_gives_joint_model (candidate : Assignment captures next)
    {Γ : Ctx S} {sort : S.Srt} (problem : EquationStore (Term (signature S captures) Γ sort))
    (row : ContextualStoredRows.Row locals captures Γ sort) (pattern : Term (signature S captures) Γ sort)
    (solved : ContextualFrameUnifier.Models candidate problem)
    (matched : Matches locals candidate (instantiate candidate pattern) row) :
    ∃ (Later : Type) (later : Later → MetaArity S)
      (combined : Assignment (ContextualSelectionViews.source locals captures) later),
        ContextualFrameUnifier.Models combined (joint locals captures problem row pattern) := by
  cases row with
  | schema body =>
      obtain ⟨extension, localBodies, same⟩ := matched
      refine ⟨extension.Names, extension.declarations,
        instanceAssignment locals localBodies extension.assignment candidate,
        (ContextualFrameUnifier.models_append _ _ _).mpr ⟨?_, ?_⟩⟩
      · exact instance_preserves_models locals captures localBodies extension.assignment candidate problem solved
      · intro equation member
        have only := List.mem_singleton.mp member
        subst equation
        exact same.trans (instance_on_shared_value locals localBodies extension.assignment candidate pattern).symm
  | shared value =>
      let extension := Extension.withLocals locals next
      let localBodies : Assignment locals extension.declarations :=
        fun identity => generator extension.declarations (.inl identity)
      refine ⟨extension.Names, extension.declarations,
        instanceAssignment locals localBodies extension.assignment candidate,
        (ContextualFrameUnifier.models_append _ _ _).mpr ⟨?_, ?_⟩⟩
      · exact instance_preserves_models locals captures localBodies extension.assignment candidate problem solved
      · intro equation member
        have only := List.mem_singleton.mp member
        subst equation
        exact (instance_on_shared_value locals localBodies extension.assignment candidate value).trans
          ((congrArg (instantiate extension.assignment) matched.symm).trans
            (instance_on_shared_value locals localBodies extension.assignment candidate pattern).symm)

theorem observed_joint_models {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S captures) Γ sort))
    (row : ContextualStoredRows.Row locals captures Γ sort) (pattern : Term (signature S captures) Γ sort)
    (candidate : Assignment (ContextualSelectionViews.source locals captures) next)
    (solved : ContextualFrameUnifier.Models candidate (joint locals captures problem row pattern)) :
    ContextualResidual.Models candidate (observedJoint locals captures problem row pattern) := by
  intro equation member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  exact congrArg observe (solved original present)

variable [DecidableEq Local] [DecidableEq Shared] [DecidableEq S.Srt]
  [∀ sort, DecidableEq (S.Op sort)]

def certifiesRowAbsence (fuel : Nat) {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S captures) Γ sort))
    (row : ContextualStoredRows.Row locals captures Γ sort) (pattern : Term (signature S captures) Γ sort) : Bool :=
  match ContextualFrameWorklist.run fuel (ContextualSelectionViews.source locals captures)
      (observedJoint locals captures problem row pattern) with
  | .refuted _ => true
  | .residual _ => false

theorem certifiesRowAbsence_sound (fuel : Nat) {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S captures) Γ sort))
    (row : ContextualStoredRows.Row locals captures Γ sort) (pattern : Term (signature S captures) Γ sort)
    (accepted : certifiesRowAbsence locals captures fuel problem row pattern = true)
    (candidate : Assignment captures next) (solved : ContextualFrameUnifier.Models candidate problem) :
    ¬ Matches locals candidate (instantiate candidate pattern) row := by
  intro matched
  cases computed : ContextualFrameWorklist.run fuel (ContextualSelectionViews.source locals captures)
      (observedJoint locals captures problem row pattern) with
  | residual update => simp only [certifiesRowAbsence, computed, Bool.false_eq_true] at accepted
  | refuted impossible =>
      obtain ⟨Later, later, combined, jointSolved⟩ :=
        match_gives_joint_model locals captures candidate problem row pattern solved matched
      exact impossible later combined (observed_joint_models locals captures problem row pattern combined jointSolved)

def certifiesAbsence [DecidableEq O] (fuel : Nat) {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S captures) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (world : Finset O)
    (pattern : Term (signature S captures) Γ sort) : Bool :=
  decide (∀ occurrence ∈ world, certifiesRowAbsence locals captures fuel problem (rows occurrence) pattern = true)

theorem certifiesAbsence_sound [DecidableEq O] (fuel : Nat) {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S captures) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (world : Finset O)
    (pattern : Term (signature S captures) Γ sort)
    (accepted : certifiesAbsence locals captures fuel problem rows world pattern = true) :
    ContextualGuardSemantics.Ask locals problem rows world (.absent pattern) := by
  intro Later later candidate solved occurrence present
  have all := of_decide_eq_true accepted
  exact certifiesRowAbsence_sound locals captures fuel problem (rows occurrence) pattern
    (all occurrence present) candidate solved

theorem zero_fuel_never_certifies_a_row {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S captures) Γ sort))
    (row : ContextualStoredRows.Row locals captures Γ sort) (pattern : Term (signature S captures) Γ sort) :
    certifiesRowAbsence locals captures 0 problem row pattern = false := rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardRefutation
