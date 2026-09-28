import Mettapedia.Languages.Agda.Adequacy.AdministrativeReflection
import Mettapedia.Languages.Agda.Structural.AdministrativeAdmission

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.StaticAdequacy.ComponentTransport

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Structural
open Structural.Statics (RawTm RawTy RawContext TypeParameter TypeBody)
open Structural.AdministrativeStatics

abbrev IdentityReturn {n : Nat} (source : StaticSpecification.RawContext n) (target : RawContext n) :=
  Statics.TypedSubstitution CoreDerivation (embedContext source) target
    (Telescope.identity (S := sig) .term n)

noncomputable def forwardTypeEqualityAt {n : Nat} {source : StaticSpecification.RawContext n}
    {target : RawContext n} (back : IdentityReturn source target)
    {A B : StaticSpecification.Ty n} (equal : StaticSpecification.TypeEq source A B) :
    CoreDerivation (Statics.typeEqual target (embedTy A) (embedTy B)) := by
  have moved := (includeCanonical (typeEqualityForward equal)).substitution target
    (Telescope.identity (S := sig) .term n) back
  exact (congrArg₂ (fun A B => CoreDerivation (Statics.typeEqual target A B))
    (Telescope.bind_identity (embedTy A)) (Telescope.bind_identity (embedTy B))).mp moved

noncomputable def bridgeTypeEquality {n : Nat} {source : StaticSpecification.RawContext n}
    {target : RawContext n} (back : IdentityReturn source target)
    {A B : StaticSpecification.Ty n} {rawA rawB : RawTy n}
    (left : CoreDerivation (Statics.typeEqual target rawA (embedTy A)))
    (right : CoreDerivation (Statics.typeEqual target rawB (embedTy B)))
    (equal : StaticSpecification.TypeEq source A B) :
    CoreDerivation (Statics.typeEqual target rawA rawB) :=
  left.typeTransitivity ((forwardTypeEqualityAt back equal).typeTransitivity right.typeSymmetry)

noncomputable def transportPiComponentEqualities {n : Nat}
    {source : StaticSpecification.RawContext n} {target : RawContext n}
    {a a' : StaticSpecification.Ty n} {b b' : StaticSpecification.TyAbs n}
    {A A' : TypeParameter n} {B B' : TypeBody n}
    (base : IdentityReturn source target)
    (extended : IdentityReturn (source.snoc a) (target.snoc A.code))
    (firstDomain : CoreDerivation (Statics.typeEqual target A.code (embedTy a)))
    (secondDomain : CoreDerivation (Statics.typeEqual target A'.code (embedTy a')))
    (firstCodomain : CoreDerivation (Statics.typeEqual (target.snoc A.code) B.open.code (embedTy b.open)))
    (secondCodomain : CoreDerivation (Statics.typeEqual (target.snoc A.code) B'.open.code (embedTy b'.open)))
    (domain : StaticSpecification.TypeEq source a a')
    (codomain : StaticSpecification.TypeEq (source.snoc a) b.open b'.open) :
    CoreDerivation (Statics.typeEqual target A.code A'.code) ×
      CoreDerivation (Statics.typeEqual (target.snoc A.code) B.open.code B'.open.code) :=
  ⟨bridgeTypeEquality base firstDomain secondDomain domain,
    bridgeTypeEquality extended firstCodomain secondCodomain codomain⟩

end Mettapedia.Languages.Agda.StaticAdequacy.ComponentTransport
