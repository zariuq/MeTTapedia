import Mettapedia.OSLF.Syntax.PartialRenaming
import Mettapedia.GSLT.LanguageDef.ScopedMatcherDependencyBoundary

/-!
# Typed dependency inverse-renaming controls

The signature is derived from the same authored language as the scoped-matcher
boundary controls. These examples recover actual bodies using existing
strengtheners; they neither infer permissions nor modify the matcher.
-/

namespace Mettapedia.GSLT.LanguageDef.PartialRenamingControls

open Mettapedia.OSLF.Binding Mettapedia.OSLF.MeTTaIL.Syntax
open MetaDependencyControls ScopedMatcherDependencyBoundary
open WellSorted.OccurrenceControls (a)

set_option autoImplicit false

/-- The existing weakening inverse supplies the variable recognition algorithm. -/
def selectOld : Strengthener oldArgument where
  un := (Strengthener.ofWeaken signature (Γ := [a]) a).un
  un_rho := by
    intro s v
    cases v with
    | zero => rfl
    | succ impossible => exact nomatch impossible
  rho_un := by
    intro s v w found
    cases v with
    | zero => cases found
    | succ inner =>
        cases inner with
        | zero => cases found; rfl
        | succ impossible => exact nomatch impossible

theorem swap_involutive : ∀ s (v : Var [a, a] s),
    swapArguments s (swapArguments s v) = v := by
  intro s v
  cases v with
  | zero => rfl
  | succ inner =>
      cases inner with
      | zero => rfl
      | succ impossible => exact nomatch impossible

def inverseSwap : Strengthener swapArguments where
  un := fun s v => some (swapArguments s v)
  un_rho := fun s v => congrArg some (swap_involutive s v)
  rho_un := by
    intro s v w found
    cases found
    exact swap_involutive s v

/-- An enclosing parameter is referenced below a newly introduced binder. -/
def nestedBody : Term signature [a] (.arrow a a) :=
  .op (.lambda a a) (.cons (.var (.succ .zero)) .nil)

/-- The target retains the older ambient variable, not its unsupported neighbor. -/
def nestedSelected : Term signature [a, a] (.arrow a a) :=
  .op (.lambda a a) (.cons (.var (.succ (.succ .zero))) .nil)

def nestedUnsupported : Term signature [a, a] (.arrow a a) :=
  .op (.lambda a a) (.cons (.var (.succ .zero)) .nil)

def locallyBoundSource : Term signature [a, a] (.arrow a a) :=
  .op (.lambda a a) (.cons (.var .zero) .nil)

def locallyBoundResult : Term signature [a] (.arrow a a) :=
  .op (.lambda a a) (.cons (.var .zero) .nil)

theorem subset_variable_recovered :
    strengthenT selectOld (.var (.succ .zero) : Term signature [a, a] a) =
      some (.var .zero) := rfl

theorem permutation_variable_recovered :
    strengthenT inverseSwap (.var (.succ .zero) : Term signature [a, a] a) =
      some (.var .zero) := rfl

theorem subset_nested_recovered : strengthenT selectOld nestedSelected = some nestedBody := rfl

theorem subset_nested_reconstructs : rename oldArgument nestedBody = nestedSelected :=
  rename_strengthenT selectOld
    nestedSelected nestedBody subset_nested_recovered

theorem new_local_binder_preserved :
    strengthenT selectOld locallyBoundSource = some locallyBoundResult := rfl

theorem unsupported_reference_declined :
    strengthenT selectOld (.var .zero : Term signature [a, a] a) = none := rfl

theorem unsupported_nested_reference_declined :
    strengthenT selectOld nestedUnsupported = none := rfl

/-- Rejection reflects a real dependency obstruction, not merely a failed search. -/
theorem unsupported_nested_has_no_body :
    ¬ ∃ body : Term signature [a] (.arrow a a), rename oldArgument body = nestedUnsupported :=
  (strengthenT_eq_none_iff selectOld
    nestedUnsupported).mp unsupported_nested_reference_declined

theorem every_selected_body_recovered {s : signature.Srt} (body : Term signature [a] s) :
    strengthenT selectOld (rename oldArgument body) = some body :=
  strengthenT_rename selectOld body

theorem every_permuted_body_recovered {s : signature.Srt} (body : Term signature [a, a] s) :
    strengthenT inverseSwap (rename swapArguments body) = some body :=
  strengthenT_rename inverseSwap body

/-- Primitive recovery cannot be claimed for a map that substitutes the new
ambient variable for the selected old one. -/
theorem newest_argument_is_not_inverse :
    selectOld.un a (newestArgument a (.zero : Var [a] a)) ≠ some (.zero : Var [a] a) := by
  intro equality
  cases equality

end Mettapedia.GSLT.LanguageDef.PartialRenamingControls
