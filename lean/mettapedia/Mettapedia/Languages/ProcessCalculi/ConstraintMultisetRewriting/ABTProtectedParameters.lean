import Mettapedia.GSLT.LanguageDef.ScopedABTProtectedSubstitution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FixedMatching

/-!
# Protected ambient ABT parameters in a two-sided equation action

The declared ambient prefix is rigid, and loose indices outside it remain
mobile. Both sides of every equation use the same capture-avoiding action.
This is a profile over the existing signature-indexed ABT, with no claim
that arbitrary object indices are guest proof variables or that this profile
implements higher-order pattern search.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ABTProtectedParameters

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT

variable {Head : Type}

abbrev Assignment (Head : Type) (width : Nat) := ProtectedSubstitution.Assignment Head width

def action (width : Nat) : SubstitutionAction (Term Head) (Assignment Head width) where
  E := Eq
  equivalence := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  apply := fun assignment => Term.substituteMany assignment.val
  identity := ProtectedSubstitution.identity width
  compose := ProtectedSubstitution.compose width
  apply_identity := Term.substituteMany_ids
  apply_compose := ProtectedSubstitution.compose_apply width
  preserves := fun assignment {_ _} same => congrArg (Term.substituteMany assignment.val) same

theorem parameter_fixed (width : Nat) (assignment : Assignment Head width)
    (index : Nat) (inside : index < width) :
    (action width).apply assignment (.idx index) = .idx index :=
  ProtectedSubstitution.parameter_fixed width assignment index inside

theorem supported_term_fixed (width : Nat) (assignment : Assignment Head width)
    (term : Term Head) (supported : Term.supportedAt width term = true) :
    (action width).apply assignment term = term :=
  ProtectedSubstitution.supported_term_fixed width assignment term supported

theorem fixed_of_supported (width : Nat) (term : Term Head)
    (supported : Term.supportedAt width term = true) :
    FixedMatching.Fixed (action width) term :=
  fun assignment => supported_term_fixed width assignment term supported

theorem the_boundary_index_is_not_fixed (width : Nat) :
    ¬FixedMatching.Fixed (action width) (Term.idx (Head := Head) width) := by
  intro fixed
  exact ProtectedSubstitution.boundary_can_change width
    (fixed (ProtectedSubstitution.atBoundary width (.idx (width + 1))))

/-- The action can bind either side of an equation while preserving every
declared parameter. The replacement is already scoped in that interface. -/
theorem loose_against_parameterized_value (width : Nat) (value : Term Head)
    (supported : Term.supportedAt width value = true) :
    (action width).Solves (ProtectedSubstitution.atBoundary width value) (.idx width, value) ∧
      (action width).Solves (ProtectedSubstitution.atBoundary width value) (value, .idx width) := by
  have bound := ProtectedSubstitution.atBoundary_apply width value
  have unchanged := ProtectedSubstitution.supported_term_fixed width
    (ProtectedSubstitution.atBoundary width value) value supported
  constructor
  · change Term.substituteMany _ _ = Term.substituteMany _ _
    exact bound.trans unchanged.symm
  · change Term.substituteMany _ _ = Term.substituteMany _ _
    exact unchanged.trans bound.symm

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ABTProtectedParameters
