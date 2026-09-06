import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.SimpleFragmentSubstitutionTranslation

/-!
# Type information lost by the simple-fragment erasure

The intrinsic simple syntax records the intermediate type of each application.
The cumulative presentation records an unannotated lambda/application term and
proves its typing separately. Consequently two closed intrinsic terms of the
same type can erase to the same presentation term.

The collision below uses two beta redexes that return their enclosing variable.
Their discarded arguments are identities at different types. Their extensional
meaning agrees, but their intrinsic syntax differs. Therefore the raw erasure
has no left inverse recovering intrinsic terms, even at a fixed closed type.
This is a boundary for retaining typing information; it is not a failure of
type preservation or an obstruction to comparisons modulo conversion.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace SimpleFragmentErasureBoundary

open FourFaceBetaExperiment
open FourFaceBetaExperiment.IntrinsicSTT

universe u

/-- The closed identity at the atomic type. -/
def identityTerm : Term [] (.arr .atom .atom) :=
  .lam (.var .zero)

/-- An identity at the atomic type is evaluated and discarded. -/
def discardAtomicIdentity : Term [] (.arr .atom .atom) :=
  .lam (.app (.lam (.var (.succ .zero)))
    (show Term [.atom] (.arr .atom .atom) from .lam (.var .zero)))

/-- An identity at a function type is evaluated and discarded instead. -/
def discardFunctionIdentity : Term [] (.arr .atom .atom) :=
  .lam (.app (.lam (.var (.succ .zero)))
    (show Term [.atom] (.arr (.arr .atom .atom) (.arr .atom .atom)) from
      .lam (.var .zero)))

/-- Observe the first application domain below leading lambda binders. -/
def firstApplicationDomain : {context : List Ty} → {type : Ty} →
    Term context type → Option Ty
  | _, _, .var _ => none
  | _, _, .lam body => firstApplicationDomain body
  | _, _, @Term.app _ domain _ _ _ => some domain

/-- The erased type annotations distinguish the two intrinsic terms. -/
theorem discardIdentities_ne : discardAtomicIdentity ≠ discardFunctionIdentity := by
  intro equal
  have domains := congrArg firstApplicationDomain equal
  change some (Ty.arr .atom .atom) =
    some (Ty.arr (.arr .atom .atom) (.arr .atom .atom)) at domains
  cases domains

/-- The cumulative raw syntax forgets those application-domain annotations. -/
theorem erase_discardIdentities_eq :
    TowerDTT.eraseTerm discardAtomicIdentity =
      TowerDTT.eraseTerm discardFunctionIdentity := rfl

/-- Positive control: erasure still distinguishes an identity from its redex. -/
theorem erase_identity_ne_discard :
    TowerDTT.eraseTerm identityTerm ≠
      TowerDTT.eraseTerm discardAtomicIdentity := by
  intro equal
  cases equal

/-- The two intrinsic terms have the same function meaning in every carrier. -/
theorem denote_discardIdentities_eq {Ground : Type u}
    (environment : Environment Ground []) :
    discardAtomicIdentity.denote environment =
      discardFunctionIdentity.denote environment := rfl

/-- Both erased terms remain well typed at their declared common type. -/
theorem discardIdentities_wellTyped :
    Presentation.Tower.HasType .nil
      (TowerDTT.eraseTerm discardAtomicIdentity)
      (TowerDTT.eraseTypeAt 0 (.arr .atom .atom)) ∧
    Presentation.Tower.HasType .nil
      (TowerDTT.eraseTerm discardFunctionIdentity)
      (TowerDTT.eraseTypeAt 0 (.arr .atom .atom)) :=
  ⟨TowerDTT.eraseTerm_hasType discardAtomicIdentity,
    TowerDTT.eraseTerm_hasType discardFunctionIdentity⟩

/-- At a fixed closed type, erasure does not retain intrinsic term identity. -/
theorem eraseTerm_not_injective :
    ¬ Function.Injective
      (TowerDTT.eraseTerm : Term [] (.arr .atom .atom) → Presentation.Tower.Tm 0) := by
  intro injective
  exact discardIdentities_ne (injective erase_discardIdentities_eq)

/-- No decoder from raw tower terms can recover every intrinsic source term. -/
theorem no_left_inverse :
    ¬ ∃ restore : Presentation.Tower.Tm 0 → Term [] (.arr .atom .atom),
      Function.LeftInverse restore TowerDTT.eraseTerm := by
  rintro ⟨restore, inverse⟩
  exact eraseTerm_not_injective inverse.injective

#print axioms discardIdentities_ne
#print axioms erase_discardIdentities_eq
#print axioms erase_identity_ne_discard
#print axioms denote_discardIdentities_eq
#print axioms discardIdentities_wellTyped
#print axioms eraseTerm_not_injective
#print axioms no_left_inverse

end SimpleFragmentErasureBoundary
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
