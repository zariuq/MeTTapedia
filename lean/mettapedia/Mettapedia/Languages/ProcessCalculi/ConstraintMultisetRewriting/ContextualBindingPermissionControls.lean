import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingPermissionFirings
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingAuthority
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProcessInterference

/-!
# Granted sharing, transitive protection and hidden guard dependencies

These controls permit refinement of an intentionally granted capture while
retaining a different joint caller interface. They reject changes through
compound dependency chains and keep the distinction between marginal and
joint possibilities. Negative and count guards include variables in watched
shared rows even when their query has no variables.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingPermissionControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualBindingPermissions ContextualBindingPermissionGuards
open ContextualSelectionViews.Controls (base locals captures atom p pair)

abbrev Value := Term (signature base captures) [] ()
def x : Value := generator captures 0
def y : Value := generator captures 1
def z : Value := generator captures 2
def setX : EquationStore Value := [(x, atom captures)]
def protectY : List (Observation base captures) := [observe y, observe (p y)]
def grantX : Set Nat := {0}

theorem protected_y_roots (name : Nat) : name ∈ observationRoots protectY ↔ name = 1 := by
  change (∃ observation ∈ protectY, name ∈ support observation.2.2) ↔ name = 1
  simp [protectY, observe, y, p, pair, atom, support, supportArgs, support_generator]

theorem granted_capture_is_permitted : Permitted grantX ([] : EquationStore Value) setX protectY := by
  constructor
  · intro equation present name member
    obtain rfl := List.mem_singleton.mp present
    change name ∈ equationNames (x, atom captures) at member
    have atZero : name = 0 := by
      simpa [equationNames, x, atom, support, supportArgs, support_generator] using member
    simpa [grantX] using atZero
  · intro name granted reached
    have atZero : name = 0 := by simpa [grantX] using granted
    have component : name ∈ ({1} : Set Nat) :=
      dependencyClosure_least (fun root member => (protected_y_roots root).mp member)
        (fun _ member => False.elim (List.not_mem_nil member)) name reached
    have atOne : name = 1 := component
    omega

theorem setX_consistent : (ContextualFamilies.action captures [] ()).Consistent setX := by
  refine ⟨fun _ => atom captures, ?_⟩
  intro equation member
  obtain rfl := List.mem_singleton.mp member
  rfl

theorem the_joint_ungranted_view_is_preserved {Future : Type} (future : Future → MetaArity base)
    (question : List (Observation base future) → Prop) :
    (∃ candidate : Assignment captures future,
      ContextualFrameUnifier.Models candidate setX ∧ question (jointView candidate protectY)) ↔
    ∃ candidate : Assignment captures future,
      ContextualFrameUnifier.Models candidate ([] : EquationStore Value) ∧ question (jointView candidate protectY) :=
  granted_capture_is_permitted.joint_possible_iff setX_consistent question

def chained : EquationStore Value := [(x, p y), (y, p z)]
def protectX : List (Observation base captures) := [observe x]

theorem root_reaches_dependency_under_a_constructor :
    DependencyClosure chained (observationRoots protectX) 1 := by
  apply DependencyClosure.equation (known := 0)
    (DependencyClosure.root (by
      refine ⟨observe x, List.mem_singleton_self _, ?_⟩
      exact (support_generator 0).symm ▸ List.mem_singleton_self 0))
    (x, p y) (by simp [chained])
  · decide +kernel
  · decide +kernel

theorem dependency_closure_is_transitive_through_constructors :
    DependencyClosure chained (observationRoots protectX) 2 := by
  apply DependencyClosure.equation root_reaches_dependency_under_a_constructor
    (y, p z) (by simp [chained])
  · decide +kernel
  · decide +kernel

theorem a_grant_cannot_cross_the_transitive_protected_component (granted : Set Nat) :
    ¬ Permitted granted chained [(z, atom captures)] protectX := by
  intro permission
  have grantedZ : 2 ∈ granted := permission.additions (z, atom captures)
    (List.mem_singleton_self _) 2 (by decide +kernel)
  exact permission.separated 2 grantedZ dependency_closure_is_transitive_through_constructors

def resolvedChain : Assignment captures captures
  | 0 => p (p z)
  | 1 => p z
  | name + 2 => generator captures (name + 2)

def changeZ : Assignment captures captures :=
  fun name => if name = 2 then atom captures else generator captures name

theorem resolved_chain_models_the_old_equations : ContextualFrameUnifier.Models resolvedChain chained := by
  intro equation member
  rcases List.mem_cons.mp member with rfl | later
  · rfl
  · obtain rfl := List.mem_singleton.mp later
    rfl

theorem fixing_the_root_does_not_fix_its_resolved_value :
    changeZ 0 = generator captures 0 ∧
      instantiate (Assignment.compose changeZ resolvedChain) x ≠ instantiate resolvedChain x := by
  refine ⟨rfl, ?_⟩
  intro same
  have impossible := congrArg support same
  change ([] : List Nat) = [2] at impossible
  cases impossible

def equate : EquationStore Value := [(x, y)]

theorem every_single_marginal_can_survive_equating :
    (∀ caller : Assignment captures captures, ∃ extended : Assignment captures captures,
      ContextualFrameUnifier.Models extended equate ∧ extended 0 = caller 0) ∧
    (∀ caller : Assignment captures captures, ∃ extended : Assignment captures captures,
      ContextualFrameUnifier.Models extended equate ∧ extended 1 = caller 1) := by
  constructor
  · intro caller
    refine ⟨fun _ => caller 0, ?_, rfl⟩
    intro equation member
    obtain rfl := List.mem_singleton.mp member
    rfl
  · intro caller
    refine ⟨fun _ => caller 1, ?_, rfl⟩
    intro equation member
    obtain rfl := List.mem_singleton.mp member
    rfl

theorem the_unequal_joint_pair_cannot_survive_equating :
    ¬ ∃ extended : Assignment captures captures,
      ContextualFrameUnifier.Models extended equate ∧
        extended 0 = atom captures ∧ extended 1 = p (atom captures) := by
  rintro ⟨extended, model, first, second⟩
  have equal := model (x, y) (List.mem_singleton_self _)
  simp only [x, y, instantiate_generator] at equal
  rw [first, second] at equal
  have heads := (Term.op.inj equal).1
  cases heads

theorem the_unequal_joint_pair_was_previously_possible :
    ∃ candidate : Assignment captures captures,
      ContextualFrameUnifier.Models candidate ([] : EquationStore Value) ∧
        candidate 0 = atom captures ∧ candidate 1 = p (atom captures) := by
  refine ⟨fun name => if name = 1 then p (atom captures) else atom captures, ?_, rfl, rfl⟩
  intro _ member
  cases member

open ContextualGuardSemantics.Controls (query sharedRows world)

theorem closed_negative_and_count_queries_retain_hidden_row_names :
    support query = [] ∧
      0 ∈ guardNames locals sharedRows world (.absent query) ∧
      0 ∈ guardNames locals sharedRows world (.count query 1) := by
  refine ⟨rfl, ?_, ?_⟩ <;>
    simp [guardNames, world, sharedRows, rowNames, p, pair, atom,
      ContextualSelectionViews.Controls.sharedValue, support, supportArgs, support_generator]

theorem granting_the_hidden_row_variable_is_rejected :
    ¬ Permitted grantX ([] : EquationStore Value) setX
      (guardObservations locals sharedRows world (.count query 1)) := by
  intro permission
  have granted : 0 ∈ grantX := by simp [grantX]
  apply permission.separated 0 granted
  apply DependencyClosure.root
  simpa using guard_name_is_observation_root locals sharedRows world (.count query 1) []
    closed_negative_and_count_queries_retain_hidden_row_names.2.2

theorem the_unprotected_hidden_binding_really_changes_the_count :
    ¬ ContextualGuardSemantics.Ask locals ([] : EquationStore Value) sharedRows world (.count query 1) ∧
      ContextualGuardSemantics.Ask locals setX sharedRows world (.count query 1) :=
  ContextualProcessInterference.same_world_different_information_changes_the_guard

theorem the_hidden_binding_changes_pointwise_absence :
    ContextualGuardSemantics.Holds locals (generator captures) sharedRows world (.absent query) ∧
      ¬ ContextualGuardSemantics.Holds locals ContextualGuardSemantics.Controls.assignedA
        sharedRows world (.absent query) := by
  refine ⟨ContextualGuardSemantics.Controls.identity_absence_of_a_shared_unknown_is_only_pointwise, ?_⟩
  intro absent
  exact absent 7 (by decide +kernel)
    ContextualGuardSemantics.Controls.later_binding_makes_the_shared_row_match

def mixedSchema : Term (signature base (ContextualSelectionViews.source locals captures)) [] () :=
  pair (generator _ (Sum.inl 0)) (generator _ (Sum.inr 1))

theorem schema_locals_are_private_but_schema_captures_are_dependencies :
    rowNames locals (ContextualStoredRows.Row.schema mixedSchema) = [1] := rfl

def auxiliaryAlias : Assignment captures captures :=
  fun name => if name = 2 then x else generator captures name

theorem the_granted_auxiliary_alias_solves_the_actual_equation :
    ContextualFrameUnifier.Models auxiliaryAlias [(z, x)] := by
  intro equation member
  obtain rfl := List.mem_singleton.mp member
  rfl

theorem the_auxiliary_alias_preserves_protected_support :
    AnswerPermitted ({2} : Set Nat) auxiliaryAlias protectX := by
  constructor
  · intro name outside
    have different : name ≠ 2 := outside
    simp [auxiliaryAlias, different]
  · intro name member
    change (∃ observation ∈ [observe x], name ∈ support observation.2.2) at member
    obtain ⟨observation, atRoot, named⟩ := member
    obtain rfl := List.mem_singleton.mp atRoot
    have atZero : name = 0 := by simpa [x, observe, support_generator] using named
    simp [atZero]

/-- Disjoint syntactic equation support is intentionally only sufficient.
The checked-answer criterion accepts this harmless granted auxiliary alias. -/
theorem the_support_only_criterion_is_not_complete :
    ¬ Permitted ({2} : Set Nat) ([] : EquationStore Value) [(z, x)] protectX := by
  intro permission
  have impossible := permission.additions (z, x) (List.mem_singleton_self _) 0 (by decide +kernel)
  exact (by decide +kernel : (0 : Nat) ≠ 2) impossible

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingPermissionControls
