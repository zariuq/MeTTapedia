import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternPreservation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameSelectionControls

/-!
# Structural-fragment controls keep application more general than recovery

Permuted mixed-sort arguments and a binder's own variable are recognized.
Repeated and compound arguments still graft correctly but lie outside the
distinct-variable fragment. Noninjective renaming and unrestricted hole
images provide two concrete failures of fragment preservation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternFragment.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualFrameSelection.Controls (base repeatedMap)

def declaration : Nat → MetaArity base
  | 0 => ([true, false], false)
  | 1 => ([false, false], false)
  | 2 => ([false], false)
  | _ + 3 => ([false], true)

abbrev extended := signature base declaration

def swapped : Term extended [false, true] false :=
  .op (.inr (.mk 0)) (.cons (.var (.succ .zero)) (.cons (.var .zero) .nil))

def repeated : Term extended [false] false :=
  .op (.inr (.mk 1)) (.cons (.var .zero) (.cons (.var .zero) .nil))

def compound : Term extended [] false :=
  .op (.inr (.mk 2)) (.cons (Term.op (S := extended) (Γ := []) (.inl (.constant false)) .nil) .nil)

def underBinder : Term extended [] true :=
  .op (.inl .combine) (.cons (.op (.inl (.constant false)) .nil)
    (.cons (.op (.inr (.mk 3)) (.cons (.var .zero) .nil)) .nil))

def images : Assignment declaration declaration
  | 0 => .var (.succ .zero)
  | 1 => .var .zero
  | 2 => .var .zero
  | _ + 3 => .op (.inl (.constant true)) .nil

theorem all_images_are_structural_patterns : ∀ identity, Pattern base declaration (images identity)
  | 0 => .object _
  | 1 => .object _
  | 2 => .object _
  | _ + 3 => Pattern.rigid (S := base) (declaration := declaration) (.constant true) .nil .nil

theorem reordered_mixed_sort_arguments_are_recognized : check swapped = true := by cbv

theorem the_field_may_use_its_own_binder : check underBinder = true := by cbv

theorem permitted_instantiation_preserves_the_binding_field :
    Pattern base declaration (instantiate images underBinder) :=
  instantiate_preserves images all_images_are_structural_patterns underBinder
    (check_sound underBinder the_field_may_use_its_own_binder)

theorem the_binder_field_is_actually_instantiated :
    instantiate images underBinder =
      Term.op (S := extended) (Γ := []) (.inl .combine)
        (.cons (.op (.inl (.constant false)) .nil) (.cons (.op (.inl (.constant true)) .nil) .nil)) :=
  rfl

theorem repeated_arguments_are_outside_the_distinct_fragment : check repeated = false := by cbv

theorem repeated_arguments_still_graft_an_ordinary_body : instantiate images repeated = .var .zero := rfl

theorem compound_arguments_are_outside_the_distinct_fragment : check compound = false := rfl

theorem compound_arguments_still_graft_an_ordinary_body :
    instantiate images compound = Term.op (S := extended) (Γ := []) (.inl (.constant false)) .nil := rfl

theorem a_noninjective_renaming_is_not_licensed : RenamingSlots.check repeatedMap = false := by cbv

theorem a_noninjective_renaming_can_leave_the_fragment :
    check (rename (S := extended) repeatedMap (generator declaration 1)) = false := by cbv

def unrestrictedImages : Assignment declaration declaration
  | 0 => .op (.inr (.mk 1)) (.cons (.var (.succ .zero)) (.cons (.var (.succ .zero)) .nil))
  | 1 => images 1
  | 2 => images 2
  | identity + 3 => images (identity + 3)

theorem the_generator_is_a_pattern : Pattern base declaration (generator declaration 0) := generator_pattern 0

theorem unrestricted_instantiation_can_leave_the_fragment :
    check (instantiate unrestrictedImages (generator declaration 0)) = false := by cbv

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternFragment.Controls
