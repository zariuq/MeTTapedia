import Mettapedia.Logic.LP.Core

/-!
# Executable structural equality of first-order terms

Function arguments are compared at every declared finite position. This is
equality of the existing term type, including its variable identities and
function arities, rather than unifiability or equality after substitution.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.LP

variable {σ : LPSignature} [DecidableEq σ.vars] [DecidableEq σ.constants]
  [DecidableEq σ.functionSymbols]

def Term.structuralEqual : Term σ → Term σ → Bool
  | .var first, .var second => decide (first = second)
  | .const first, .const second => decide (first = second)
  | .app first left, .app second right =>
      if same : second = first then
        (List.finRange (σ.functionArity first)).all fun position =>
          structuralEqual (left position) ((same ▸ right) position)
      else false
  | _, _ => false
termination_by first _second => first.size
decreasing_by exact Term.size_subterm _

theorem Term.structuralEqual_iff : ∀ (first second : Term σ),
    first.structuralEqual second = true ↔ first = second
  | .var _, .var _ => by simp [structuralEqual]
  | .const _, .const _ => by simp [structuralEqual]
  | .var _, .const _ => by simp [structuralEqual]
  | .var _, .app _ _ => by simp [structuralEqual]
  | .const _, .var _ => by simp [structuralEqual]
  | .const _, .app _ _ => by simp [structuralEqual]
  | .app _ _, .var _ => by simp [structuralEqual]
  | .app _ _, .const _ => by simp [structuralEqual]
  | .app first left, .app second right => by
      simp only [structuralEqual]
      split_ifs with same
      · subst second
        rw [List.all_eq_true]
        constructor
        · intro equal
          apply congrArg (Term.app first)
          funext position
          exact (structuralEqual_iff (left position) (right position)).mp
            (equal position (by simp))
        · intro equal position _
          have fields := eq_of_heq (Term.app.inj equal).2
          exact (structuralEqual_iff (left position) (right position)).mpr (congrFun fields position)
      · simp only [false_iff]
        intro equal
        exact same (Term.app.inj equal).1.symm
termination_by first _second => first.size
decreasing_by all_goals exact Term.size_subterm _

instance : DecidableEq (Term σ) := fun first second =>
  decidable_of_iff (first.structuralEqual second = true) (Term.structuralEqual_iff first second)

end Mettapedia.Logic.LP
