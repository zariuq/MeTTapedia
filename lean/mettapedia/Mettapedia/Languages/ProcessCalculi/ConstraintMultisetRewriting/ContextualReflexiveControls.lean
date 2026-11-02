import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualReflexiveProgress
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameWorklistControls

/-!
# Reflexivity accepts arbitrary identical applications and respects metadata

Compound and repeated arguments need no unique hole recovery to discharge
an identical equation. Different formal spines are not reflexive. Matching
constructor shapes at different context or sort indices are refused before
any comparison across their dependent types.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualReflexiveControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualReflexive

abbrev base := ContextualFrameWorklist.Controls.base
abbrev source := ContextualFrameWorklist.Controls.declaration
abbrev extended := signature base source
local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq ContextualFrame.Controls.Operator)

def repeated : Term extended [()] () := ContextualFrameWorklist.Controls.call (.var .zero) (.var .zero)

theorem a_repeated_application_can_be_reflexive_without_a_unique_body :
    (tryTerms repeated repeated).isSome = true := by
  decide +kernel

theorem different_spines_are_not_mistaken_for_reflexivity :
    (tryTerms ContextualFrameWorklist.Controls.formal ContextualFrameWorklist.Controls.swapped).isSome = false := by
  decide +kernel

theorem a_solved_compound_equation_does_not_shrink_the_original_interface :
    ContextualFrameWorklist.Controls.originalImageArity
      (ContextualFrameWorklist.run 1 source ContextualFrameWorklist.Controls.compoundProblem) false = some 2 := by
  decide +kernel

def sorted : Signature where
  Srt := Bool
  Op _ := Unit
  arity _ := []
def declarations (_ : Nat) : MetaArity sorted := ([], false)
abbrev sortedExtended := signature sorted declarations
local instance : DecidableEq sorted.Srt := inferInstanceAs (DecidableEq Bool)
local instance (sort : sorted.Srt) : DecidableEq (sorted.Op sort) := inferInstanceAs (DecidableEq Unit)
def constant (Γ : Ctx sorted) (sort : sorted.Srt) : Term sortedExtended Γ sort :=
  .op (.inl ()) .nil

theorem identical_constructor_shapes_at_different_sorts_are_not_reflexive :
    (tryEquation (observe (constant [] false), observe (constant [] true))).isSome = false := by
  decide +kernel

theorem identical_closed_shapes_at_different_contexts_are_not_reflexive :
    (tryEquation (observe (constant [] false), observe (constant [false] false))).isSome = false := by
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualReflexiveControls
