import Mettapedia.OSLF.Syntax.BindingScopePullback
import Mettapedia.OSLF.Syntax.BindingScopeEqualizer

/-!
# Injective parameter interfaces for contextual solver cases

An equalizer's inclusion is injective by its recovery law. A pullback's
left projection is injective when the right occurrence map is, and conversely
for its right projection. These are statements about the actual typed
variable interfaces, including permutations; no sort enumeration is needed.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding

variable {S : Signature} {L R Γ : Ctx S}

theorem ScopeEqualizer.inclusion_injective {left right : Ren S L Γ}
    (equalizer : ScopeEqualizer left right) : ∀ sort, Function.Injective (equalizer.inclusion sort) := by
  intro sort first second same
  have firstRecovered := equalizer.strengthener.un_rho sort first
  have secondRecovered := equalizer.strengthener.un_rho sort second
  rw [same] at firstRecovered
  exact Option.some.inj (firstRecovered.symm.trans secondRecovered)

theorem ScopePullback.toLeft_injective {left : Ren S L Γ} {right : Ren S R Γ}
    (pullback : ScopePullback left right) (rightInjective : ∀ sort, Function.Injective (right sort)) :
    ∀ sort, Function.Injective (pullback.toLeft sort) := by
  intro sort first second same
  apply pullback.jointly_injective_variables same
  apply rightInjective sort
  exact (pullback.commutes sort first).symm.trans
    ((congrArg (left sort) same).trans (pullback.commutes sort second))

theorem ScopePullback.toRight_injective {left : Ren S L Γ} {right : Ren S R Γ}
    (pullback : ScopePullback left right) (leftInjective : ∀ sort, Function.Injective (left sort)) :
    ∀ sort, Function.Injective (pullback.toRight sort) := by
  intro sort first second same
  apply pullback.jointly_injective_variables ?_ same
  apply leftInjective sort
  exact (pullback.commutes sort first).trans
    ((congrArg (right sort) same).trans (pullback.commutes sort second).symm)

end Mettapedia.OSLF.Binding
