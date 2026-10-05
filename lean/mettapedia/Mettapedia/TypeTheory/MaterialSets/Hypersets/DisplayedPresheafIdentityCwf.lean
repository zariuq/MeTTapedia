import Mettapedia.TypeTheory.MaterialSets.Hypersets.DisplayedPresheafIdentity

/-!
# The actual displayed presheaf identity CwF

The existing displayed presheaf comprehension operations are bundled with
explicit substitution proofs. The identity formation, reflexivity and full
dependent J already constructed with actual small material witness graphs
then instantiate the contextual identity contracts. No elimination operator
or substitution law is supplied as a hypothesis.

The CwF contains every small displayed family, with its actual restriction
maps and natural sections. The discrete identity interpretation and its local
reflection properties do not impose identity rules on a native syntax.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.DisplayedPresheafIdentityCwf

open CategoryTheory
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.TypeTheory.DisplayedPresheafComprehension
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualIdentityTypes
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent (compose identity)
open PowerClassPresheafProducts

universe u
variable (C : Type u) [Category.{u} C]

/-- Actual w12 displayed comprehension, with explicit natural-transformation
substitution and no default functor-category composition proofs. -/
abbrev cwf : Cwf.{u + 1, u, u + 1, u} where
  Ctx := Cᵒᵖ ⥤ Type u
  Sub := NatTrans
  idS := identity
  compS later earlier := compose earlier later
  id_comp _ := rfl
  comp_id _ := rfl
  comp_assoc _ _ _ := rfl
  Ty base := DisplayedFamily.{u, u, u, u} base
  tySub family change := PowerClassPresheafProducts.reindex change family
  tySub_id _ := rfl
  tySub_comp _ _ _ := rfl
  Tm _ family := family.sections
  tmSub term change := reindexSection change _ term
  tmSub_id _ := rfl
  tmSub_comp _ _ _ := rfl
  ext _ family := totalSpace family
  wk := PowerClassPresheafProducts.projection
  vz := lastVariable
  pair change family term :=
    compose (sectionMap (PowerClassPresheafProducts.reindex change family) term)
      (DisplayedPresheafIdentity.totalReindex change family)
  wk_pair _ _ _ := rfl
  vz_pair _ _ _ := rfl
  pair_eta _ _ := rfl

def formation : IdentityFormation (cwf C) where
  idTy := DisplayedPresheafIdentity.identityFamily
  idTy_sub := DisplayedPresheafIdentity.identityFamily_reindex

def introduction : IdentityReflexivity (cwf C) (formation C) where
  refl := fun term => DisplayedPresheafIdentity.reflexivity _ term
  refl_sub := by
    intro source target change family term
    exact DisplayedPresheafIdentity.reflexivity_reindex change family term

/-- The contextual contracts are satisfied by the constructed operations on
the actual nested presheaf comprehensions and arbitrary natural motives. -/
def elimination : IdentityEliminationBeta (cwf C) (formation C) (introduction C) where
  reflexivitySubstitution := DisplayedPresheafIdentity.diagonal
  over_diagonal _ := rfl
  witness_is_refl _ := HEq.rfl
  j motive method := DisplayedPresheafIdentity.J _ motive method
  beta motive method := DisplayedPresheafIdentity.J_beta _ motive method

theorem identityContext_eq {base : Cᵒᵖ ⥤ Type u} (family : DisplayedFamily.{u, u, u, u} base) :
    ContextualIdentityTypes.identityContext (cwf C) (formation C) family =
      DisplayedPresheafIdentity.identityContext family := rfl

theorem discreteEndpointReflection : IdentityEndpointReflection (cwf C) (formation C) := by
  intro base family left right witness
  exact DisplayedPresheafIdentity.identitySection_endpoints family witness

theorem discreteProofIrrelevance : IdentityProofIrrelevance (cwf C) (formation C) := by
  intro base family left right
  exact DisplayedPresheafIdentity.identitySections_subsingleton family left right

end Mettapedia.TypeTheory.MaterialSets.Hypersets.DisplayedPresheafIdentityCwf
