import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameWorklist
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternOccursControls

/-!
# Executed refusals distinguish scope, finite trees and erasable arguments

The same bounded driver accepts declared ambient variables and local binder
variables, refuses undeclared capture and rigid self-containment, and keeps
solvable non-pattern applications. Every refusal ranges over later frames.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameRefutationControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualFrameWorklist

abbrev base := ContextualFrame.Controls.signature
local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq ContextualFrame.Controls.Operator)
abbrev declaration := ContextualPatternOccurs.Controls.declaration
abbrev extended := signature base declaration

def hole {Γ : Ctx base} : Term extended Γ () := .op (.inr (.mk false)) .nil
def unary {Γ : Ctx base} (argument : Term extended Γ ()) : Term extended Γ () :=
  .op (.inr (.mk true)) (.cons argument .nil)
def constant {Γ : Ctx base} : Term extended Γ () := .op (.inl .constant) .nil
def pair {Γ : Ctx base} (left right : Term extended Γ ()) : Term extended Γ () :=
  .op (.inl .pair) (.cons left (.cons right .nil))
def abstracted {Γ : Ctx base} (body : Term extended (() :: Γ) ()) : Term extended Γ () :=
  .op (.inl .lam) (.cons body .nil)

def capture : Problem declaration :=
  [(observe (hole (Γ := [()])), observe (Term.var (Γ := [()]) (s := ()) .zero))]
def ambient : Problem declaration :=
  [(observe (unary (Γ := [()]) (.var .zero)), observe (Term.var (Γ := [()]) (s := ()) .zero))]
def ownBinder : Problem declaration :=
  [(observe (hole (Γ := [])), observe (abstracted (Γ := []) (.var .zero)))]
def cyclic : Problem declaration :=
  [(observe (hole (Γ := [])), observe (pair (Γ := []) hole constant))]
def reversedCyclic : Problem declaration :=
  [(observe (pair (Γ := []) hole constant), observe (hole (Γ := [])))]
def binderCyclic : Problem declaration :=
  [(observe (hole (Γ := [])), observe (abstracted (Γ := []) hole))]
def erasable : Problem declaration :=
  [(observe (hole (Γ := [])), observe (unary (Γ := []) hole))]
def rigidErasable : Problem declaration :=
  [(observe (hole (Γ := [])), observe (pair (Γ := []) (unary hole) constant))]

def variableModel : Assignment declaration declaration
  | false => constant
  | true => .var .zero

theorem variableModel_models_ambient : Models variableModel ambient := by
  apply (models_observed_iff variableModel _ _).mpr
  rfl

def binderModel : Assignment declaration declaration
  | false => abstracted (.var .zero)
  | true => constant

theorem binderModel_models_ownBinder : Models binderModel ownBinder := by
  apply (models_observed_iff binderModel _ _).mpr
  rfl

def isRefuted {problem : Problem declaration} : Result problem → Bool
  | .refuted _ => true
  | .residual _ => false

def pendingCount {problem : Problem declaration} : Result problem → Option Nat
  | .refuted _ => none
  | .residual update => some update.remaining.length

theorem declared_ambient_application_is_accepted : pendingCount (run 1 declaration ambient) = some 0 := by
  rw [run_eq_local_on_model 1 ambient declaration variableModel variableModel_models_ambient]
  decide +kernel

theorem undeclared_ambient_capture_is_refused : isRefuted (run 1 declaration capture) = true := by
  decide +kernel

theorem a_local_binder_is_available_inside_its_own_body : pendingCount (run 1 declaration ownBinder) = some 0 := by
  rw [run_eq_local_on_model 1 ownBinder declaration binderModel binderModel_models_ownBinder]
  decide +kernel

theorem rigid_self_containment_is_refused : isRefuted (run 1 declaration cyclic) = true := by
  decide +kernel

theorem the_reverse_rigid_equation_is_also_refused : isRefuted (run 1 declaration reversedCyclic) = true := by
  decide +kernel

theorem rigid_self_containment_under_a_binder_is_refused : isRefuted (run 1 declaration binderCyclic) = true := by
  decide +kernel

theorem an_erasable_argument_is_kept_as_a_residual : pendingCount (run 3 declaration erasable) = some 1 := by
  decide +kernel

theorem a_later_impossible_constraint_is_found : isRefuted (run 1 declaration (erasable ++ cyclic)) = true := by
  decide +kernel

def eraseRigid : Assignment declaration declaration
  | false => pair constant constant
  | true => constant

theorem the_non_pattern_rigid_equation_has_an_actual_solution : Models eraseRigid rigidErasable := by
  apply (models_observed_iff eraseRigid (hole (Γ := [])) (pair (unary hole) constant)).mpr
  rfl

theorem no_amount_of_fuel_can_refute_that_solution (fuel : Nat) :
    ∃ update, run fuel declaration rigidErasable = .residual update := by
  obtain ⟨update, computed, _⟩ := preserves_every_solution fuel rigidErasable declaration eraseRigid
    the_non_pattern_rigid_equation_has_an_actual_solution
  exact ⟨update, computed⟩

theorem the_computed_capture_refusal_excludes_every_later_frame
    {Next : Type} (next : Next → MetaArity base) (candidate : Assignment declaration next) :
    ¬ Models candidate capture := by
  have refused := undeclared_ambient_capture_is_refused
  generalize computed : run 1 declaration capture = result at refused
  cases result with
  | residual _ => cases refused
  | refuted impossible => exact impossible next candidate

def repeatedDeclaration (_ : Unit) : MetaArity base := ([(), ()], ())
abbrev repeatedSignature := signature base repeatedDeclaration
def repeatedLeft : Term repeatedSignature [(), ()] () :=
  .op (.inr (.mk ())) (.cons (.var .zero) (.cons (.var .zero) .nil))
def repeatedOutside : Problem repeatedDeclaration :=
  [(observe repeatedLeft, observe (Term.var (Γ := [(), ()]) (s := ()) (.succ .zero)))]

theorem even_a_repeated_spine_cannot_reach_a_missing_variable :
    (match run 1 repeatedDeclaration repeatedOutside with
      | .refuted _ => true
      | .residual _ => false) = true := by
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameRefutationControls
