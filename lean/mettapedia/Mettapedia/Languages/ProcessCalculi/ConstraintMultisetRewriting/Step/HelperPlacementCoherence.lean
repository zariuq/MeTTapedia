import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperPlacementIso

/-!
# Declaration-swap coherence of contextual placements

After one candidate on each side, both placement orders have the same local
endpoints. Their native declaration frames differ by the canonical coproduct
swap. Both source assignments commute with it, so the complete joint stores
are transported exactly and physical occurrence identities are preserved.
These are effect laws; admission of either execution is a separate condition.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers.ContextPlacement

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {O : Type} [DecidableEq O]
  {left right : Helpers.State S O} (placed : ContextPlacement left right)

abbrev afterLeftRight (f : Helpers.Firing left) (g : Helpers.Firing right) : ContextPlacement f.after g.after :=
  ((placed.afterLeft f).swap.afterLeft g).swap

abbrev afterRightLeft (f : Helpers.Firing left) (g : Helpers.Firing right) : ContextPlacement f.after g.after :=
  (placed.swap.afterLeft g).swap.afterLeft f

theorem after_both_left_map (f : Helpers.Firing left) (g : Helpers.Firing right) :
    Assignment.compose (Helpers.swap placed.frame f.helper g.helper) (placed.afterLeftRight f g).leftMap =
      (placed.afterRightLeft f g).leftMap := by
  funext name
  cases name with
  | inl name =>
      change instantiate (Helpers.swap placed.frame f.helper g.helper)
        (instantiate (incl (extend placed.frame f.helper) g.helper)
          (instantiate (incl placed.frame f.helper) (placed.leftMap name))) =
            instantiate (incl (extend placed.frame g.helper) f.helper)
              (instantiate (incl placed.frame g.helper) (placed.leftMap name))
      exact swap_value placed.frame f.helper g.helper (placed.leftMap name)
  | inr freshName =>
      cases freshName
      change instantiate (Helpers.swap placed.frame f.helper g.helper)
        (instantiate (incl (extend placed.frame f.helper) g.helper) (fresh placed.frame f.helper)) =
          fresh (extend placed.frame g.helper) f.helper
      exact swap_incl_fresh placed.frame f.helper g.helper

theorem after_both_right_map (f : Helpers.Firing left) (g : Helpers.Firing right) :
    Assignment.compose (Helpers.swap placed.frame f.helper g.helper) (placed.afterLeftRight f g).rightMap =
      (placed.afterRightLeft f g).rightMap := by
  funext name
  cases name with
  | inl name =>
      change instantiate (Helpers.swap placed.frame f.helper g.helper)
        (instantiate (incl (extend placed.frame f.helper) g.helper)
          (instantiate (incl placed.frame f.helper) (placed.rightMap name))) =
            instantiate (incl (extend placed.frame g.helper) f.helper)
              (instantiate (incl placed.frame g.helper) (placed.rightMap name))
      exact swap_value placed.frame f.helper g.helper (placed.rightMap name)
  | inr freshName =>
      cases freshName
      change instantiate (Helpers.swap placed.frame f.helper g.helper) (fresh (extend placed.frame f.helper) g.helper) =
        instantiate (incl (extend placed.frame g.helper) f.helper) (fresh placed.frame g.helper)
      exact swap_fresh placed.frame f.helper g.helper

def afterBothIso (f : Helpers.Firing left) (g : Helpers.Firing right) :
    PlacementIso (placed.afterLeftRight f g) (placed.afterRightLeft f g) where
  frame := Helpers.swapIso placed.frame f.helper g.helper
  left_map := placed.after_both_left_map f g
  right_map := placed.after_both_right_map f g

def afterBothSwap (f : Helpers.Firing left) (g : Helpers.Firing right) :
    helperStep.StateIso (placed.afterLeftRight f g).state (placed.afterRightLeft f g).state :=
  (placed.afterBothIso f g).toStateIso

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers.ContextPlacement
