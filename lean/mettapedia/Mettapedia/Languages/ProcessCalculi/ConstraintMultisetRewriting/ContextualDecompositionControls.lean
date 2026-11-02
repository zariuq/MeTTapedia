import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDecomposition
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingControls

/-!
# Decomposition controls for binders, metadata and rigid clashes

The lambda equation generates a child equation in its extended context.
Declared unary dependence is accepted; a nullary hole cannot capture that
binder. Closed-looking physical trees at different context tags remain
different observations. Heterogeneous fields retain both their sorts.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDecomposition.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualBinding.Controls (base declaration extended nullaryId)

abbrev A := ContextualObservationAction.action declaration
def unaryId : Nat × Nat := (1, 0)

def unaryBody : Term extended [()] () := .op (.inr (.mk unaryId)) (.cons (.var .zero) .nil)
def nullaryBody : Term extended [()] () := .op (.inr (.mk nullaryId)) .nil
def variableBody : Term extended [()] () := .var .zero

def lambda (body : Term extended [()] ()) : Term extended [] () := .op (.inl .lam) (.cons body .nil)

def unaryProblem : EquationStore (Observation base declaration) :=
  [(observe (lambda unaryBody), observe (lambda variableBody))]

def nullaryProblem : EquationStore (Observation base declaration) :=
  [(observe (lambda nullaryBody), observe (lambda variableBody))]

theorem the_child_retains_its_extended_context :
    argumentEquations (Args.cons (S := extended) (bs := [()]) (Γ := []) unaryBody Args.nil)
      (Args.cons (S := extended) (bs := [()]) (Γ := []) variableBody Args.nil) =
      [(observe unaryBody, observe variableBody)] := rfl

theorem declared_binder_dependence_is_consistent : A.Consistent unaryProblem := by
  refine ⟨ContextualBinding.answer unaryId variableBody, ?_⟩
  intro equation member
  have same := List.mem_singleton.mp member
  subst equation
  apply (ContextualObservationAction.solves_observed_iff declaration _ _ _).mpr
  rfl

theorem undeclared_binder_capture_is_inconsistent : ¬ A.Consistent nullaryProblem := by
  rintro ⟨assignment, solved⟩
  have children := (rigid_node_iff assignment ContextualFrame.Controls.Operator.lam
    (Args.cons nullaryBody Args.nil) (Args.cons variableBody Args.nil)).mp solved
  apply ContextualBinding.Controls.nullary_binding_cannot_capture_the_surrounding_binder
  refine ⟨assignment, ?_⟩
  intro equation member
  have same := List.mem_singleton.mp member
  subst equation
  exact (ContextualObservationAction.solves_observed_iff declaration assignment nullaryBody variableBody).mp
    (children _ (List.mem_singleton_self _))

def constant {Γ : Ctx base} : Term extended Γ () := .op (.inl .constant) .nil

theorem identical_closed_trees_do_not_erase_their_context_tags :
    ¬ A.Consistent [(observe (constant (Γ := [])), observe (constant (Γ := [()]))) ] := by
  rintro ⟨assignment, solved⟩
  have same := solved _ (List.mem_singleton_self _)
  change (⟨[], (), constant⟩ : Observation base declaration) = ⟨[()], (), constant⟩ at same
  have contexts := congrArg Sigma.fst same
  cases contexts

theorem distinct_rigid_heads_are_inconsistent :
    ¬ A.Consistent
      [(observe (Term.op (S := extended) (Γ := []) (s := ()) (.inl .pair) (.cons constant (.cons constant .nil))),
        observe (lambda variableBody))] :=
  rigid_clash (S := base) (declaration := declaration) (Γ := []) (sort := ())
    ContextualFrame.Controls.Operator.pair ContextualFrame.Controls.Operator.lam
    (by intro same; cases same) _ _

inductive MixedOperator : Bool → Type where
  | constant (sort : Bool) : MixedOperator sort
  | combine : MixedOperator true

def mixedSignature : Signature where
  Srt := Bool
  Op := MixedOperator
  arity operator := match operator with
    | .constant _ => []
    | .combine => [([], false), ([false], true)]

abbrev mixedDeclarations (sort : Bool) : MetaArity mixedSignature := ([], sort)
abbrev mixed := signature mixedSignature mixedDeclarations

def firstArgs : Args mixed [([], false), ([false], true)] [] :=
  .cons (.op (.inr (.mk false)) .nil) (.cons (.op (.inr (.mk true)) .nil) .nil)

def secondArgs : Args mixed [([], false), ([false], true)] [] :=
  .cons (.op (.inl (.constant false)) .nil) (.cons (.op (.inl (.constant true)) .nil) .nil)

theorem heterogeneous_fields_keep_their_sort_and_context_tags :
    (argumentEquations firstArgs secondArgs).map (fun equation => (equation.1.1, equation.1.2.1)) =
      [([], false), ([false], true)] := rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDecomposition.Controls
