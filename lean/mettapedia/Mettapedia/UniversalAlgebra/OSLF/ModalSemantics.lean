import Mettapedia.OSLF.Framework.DerivedModalities
import Mettapedia.UniversalAlgebra.GSLT.ContextualRewriting

/-!
# OSLF modalities for oriented equation systems

The reduction span and its adjoint modalities belong to an oriented contextual
rewrite system.  They are deliberately not attached to the underlying
equations alone: opposite orientations have the same convertibility but can
have different one-step modal observations.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAlgebra

open Mettapedia.OSLF.Framework.DerivedModalities

universe u

variable {S : Signature.{u}} {equations : EquationSystem S}

/-- The proof-relevant reduction span of an oriented contextual rewrite
system. -/
def contextualReductionSpan (orientation : Orientation equations) :
    ReductionSpan (Term S) where
  Edge := { pair : Term S × Term S //
    ContextualStep orientation pair.1 pair.2 }
  source edge := edge.1.1
  target edge := edge.1.2

/-- Every oriented equation system carries the change-of-base adjunction
between its step-future and predecessor-universal modalities. -/
theorem contextual_modal_galois (orientation : Orientation equations) :
    GaloisConnection
      (derivedDiamond (contextualReductionSpan orientation))
      (derivedBox (contextualReductionSpan orientation)) :=
  derived_galois (contextualReductionSpan orientation)

/-! ## Direction is observable before equivalence closure -/

namespace DirectionCanary

inductive Operation where
  | leftConstant
  | rightConstant
deriving DecidableEq, Repr

def signature : Signature where
  Operation := Operation
  arity _ := 0

def left : Term signature :=
  .op .leftConstant (fun position => Fin.elim0 position)

def right : Term signature :=
  .op .rightConstant (fun position => Fin.elim0 position)

def system : EquationSystem signature where
  equations := [(left, right)]

def forward : Orientation system where
  direction _ := .forward

def reverse : Orientation system where
  direction _ := .reverse

theorem forward_step : ContextualStep forward left right := by
  have step := ContextualStep.root (orientation := forward)
    (⟨0, by decide⟩ : Fin system.equations.length) Term.var
  simpa [forward, system, Orientation.source, Orientation.target,
    left, right, Term.subst] using step

theorem reverse_step : ContextualStep reverse right left := by
  have step := ContextualStep.root (orientation := reverse)
    (⟨0, by decide⟩ : Fin system.equations.length) Term.var
  simpa [reverse, system, Orientation.source, Orientation.target,
    left, right, Term.subst] using step

theorem forward_step_source {source target : Term signature}
    (step : ContextualStep forward source target) : source = left := by
  induction step with
  | root occurrence substitution =>
      have bound := occurrence.isLt
      change occurrence.val < 1 at bound
      have occurrenceEq : occurrence =
          (⟨0, by decide⟩ : Fin system.equations.length) :=
        Fin.eq_of_val_eq (Nat.lt_one_iff.mp bound)
      subst occurrence
      change left.subst substitution = left
      unfold left
      simp only [Term.subst_op]
      congr 1
      funext position
      exact Fin.elim0 position
  | congrArg operation arguments position inner ih =>
      exact Fin.elim0 position

theorem reverse_step_source {source target : Term signature}
    (step : ContextualStep reverse source target) : source = right := by
  induction step with
  | root occurrence substitution =>
      have bound := occurrence.isLt
      change occurrence.val < 1 at bound
      have occurrenceEq : occurrence =
          (⟨0, by decide⟩ : Fin system.equations.length) :=
        Fin.eq_of_val_eq (Nat.lt_one_iff.mp bound)
      subst occurrence
      change right.subst substitution = right
      unfold right
      simp only [Term.subst_op]
      congr 1
      funext position
      exact Fin.elim0 position
  | congrArg operation arguments position inner ih =>
      exact Fin.elim0 position

theorem not_forward_step_reverse : ¬ ContextualStep forward right left := by
  intro step
  have distinct : right ≠ left := by simp [right, left]
  exact distinct (forward_step_source step)

theorem not_reverse_step_forward : ¬ ContextualStep reverse left right := by
  intro step
  have distinct : left ≠ right := by simp [left, right]
  exact distinct (reverse_step_source step)

/-- The forward orientation can reach `right` from `left` in one step. -/
theorem forward_diamond :
    derivedDiamond (contextualReductionSpan forward)
      (fun term => term = right) left := by
  exact ⟨⟨(left, right), forward_step⟩, rfl, rfl⟩

/-- The reverse orientation cannot make the same observation. -/
theorem not_reverse_diamond :
    ¬ derivedDiamond (contextualReductionSpan reverse)
      (fun term => term = right) left := by
  rintro ⟨edge, sourceEq, targetEq⟩
  change edge.1.1 = left at sourceEq
  change edge.1.2 = right at targetEq
  have step := edge.2
  rw [sourceEq, targetEq] at step
  exact not_reverse_step_forward step

/-- Despite their different modalities, both orientations generate the same
equational consequence relation after equivalence closure. -/
theorem both_orientations_same_convertibility (first second : Term signature) :
    Relation.EqvGen (ContextualStep forward) first second ↔
      Relation.EqvGen (ContextualStep reverse) first second := by
  rw [← consequence_iff_convertibility system forward,
    ← consequence_iff_convertibility system reverse]

end DirectionCanary

end Mettapedia.UniversalAlgebra
