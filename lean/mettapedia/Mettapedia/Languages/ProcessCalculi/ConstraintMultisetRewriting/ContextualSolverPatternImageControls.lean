import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverPatternImages
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualImitationRepeatedControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFlexPairControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelfPairControls
import Mettapedia.OSLF.Syntax.BindingScopePullbackFinite
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FiniteScopeControls

/-!
# Solver-image controls preserve binding and delimit the structural fragment

Actual lambda synthesis, same-hole pruning, and an overlapping flexible pair
produce pattern images. A repeated occurrence map provides a counterexample
to dropping the projection-injectivity hypothesis: its valid general answer
contains a repeated helper spine and falls outside this solver fragment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverPatternImages.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualPatternFragment
open ScopePullback.Controls (base leftMap rightMap pullback)

namespace Lambda
open ContextualImitation.Controls

theorem imitation_uses_a_pattern_image_with_its_own_binder : Pattern base target (first original) :=
  imitation_images (S := base) [] ContextualFrame.Controls.Operator.lam others original

theorem the_synthesized_identity_is_still_in_the_structural_fragment : Pattern base target (combined original) := by
  have secondImages : ∀ identity, Pattern base target (second identity) :=
    ordinary_binding_images helper (Term.var (S := signature base target) (Γ := [()]) .zero)
      (Pattern.object (S := base) (declaration := target) .zero)
  exact instantiate_preserves second secondImages (first original)
    imitation_uses_a_pattern_image_with_its_own_binder

end Lambda

namespace SameHole
open ContextualSelfPair.Controls

theorem pruning_swapped_parameters_has_a_pattern_image : Pattern base target (frameAnswer (.inl ())) :=
  same_hole_images swapped () others (.inl ())

end SameHole

namespace DifferentHoles
open ContextualFlexPair.Controls

private theorem left_injective : ∀ sort, Function.Injective (leftMap sort) :=
  (RenamingSlots.check_iff (S := base) leftMap).mp (by cbv)

private theorem right_injective : ∀ sort, Function.Injective (rightMap sort) :=
  (RenamingSlots.check_iff (S := base) rightMap).mp (by cbv)

theorem both_flexible_images_remain_patterns :
    Pattern base target (ContextualFlexPair.answer pullback () others (.inl false)) ∧
      Pattern base target (ContextualFlexPair.answer pullback () others (.inl true)) :=
  ⟨different_hole_images pullback () others left_injective right_injective (.inl false),
    different_hole_images pullback () others left_injective right_injective (.inl true)⟩

end DifferentHoles

namespace Repeated

abbrev overlap := FiniteScope.Controls.repeated
def others (_ : Nat) : MetaArity base := ([], ())
abbrev source := ContextualFlexPair.sourceDeclarations [(), ()] [()] () others
abbrev target := ContextualFlexPair.targetDeclarations overlap.context () others
def answer : Assignment source target := ContextualFlexPair.answer overlap () others

theorem the_helper_projection_is_not_injective : ¬ ∀ sort, Function.Injective (overlap.toRight sort) := by
  intro unique
  have same := unique () FiniteScope.Controls.right_projection_can_share_a_variable
  exact FiniteScope.Controls.left_projection_still_distinguishes_the_slots
    (congrArg (overlap.toLeft ()) same)

theorem general_factoring_can_produce_a_repeated_helper_spine :
    check (answer (.inl true)) = false := by
  cases observed : check (answer (.inl true)) with
  | false => rfl
  | true =>
      have structured := check_sound (answer (.inl true)) observed
      exact False.elim (the_helper_projection_is_not_injective
        ((renamed_generator_pattern_iff (S := base) (declaration := target) (.inl ()) overlap.toRight).mp structured))

theorem this_general_answer_still_solves_its_application_equation :
    instantiate answer (rename (S := signature base source) FiniteScope.Controls.repeatedLeft (generator source (.inl false))) =
      instantiate answer (rename (S := signature base source) FiniteScope.Controls.singleRight (generator source (.inl true))) :=
  ContextualFlexPair.sound overlap () others

end Repeated

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverPatternImages.Controls
