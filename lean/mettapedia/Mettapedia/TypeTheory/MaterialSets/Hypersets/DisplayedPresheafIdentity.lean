import Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassPresheafProducts
import Mettapedia.TypeTheory.MaterialSets.Hypersets.PresheafIdentityWitness
import Mettapedia.TypeTheory.ContextualIdentityTypes

/-!
# Discrete identity elimination in actual displayed presheaf contexts

The endpoint and witness contexts are constructed with existing displayed
comprehension. Restriction maps carry endpoint equality, and reflexivity is
a natural section. An explicitly proved natural inverse to the reflexivity
diagonal extends every displayed natural motive's reflexive method to a
full dependent J term. Its computation and base-substitution laws concern
actual natural sections and context maps.

This is the discrete interpretation in set-valued presheaves. Its local
proof irrelevance does not impose UIP, equality reflection, or an identity
interpretation on another calculus.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.DisplayedPresheafIdentity

open CategoryTheory
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.TypeTheory.DisplayedPresheafComprehension
open PowerClassPresheafProducts
open Mettapedia.GSLT.Topos.ConstructivePresheaf
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent (compose identity)

universe u
variable {C : Type u} [Category.{u} C]
variable {P Q : Cᵒᵖ ⥤ Type u}

def identityFamily (domain : DisplayedFamily.{u, u, u, u} P) (left right : domain.sections) :
    DisplayedFamily.{u, u, u, u} P where
  obj point := PresheafIdentityWitness.Witness (left.val point) (right.val point)
  map {first second} step := TypeCat.ofHom fun witness =>
    PresheafIdentityWitness.encode ((left.property step).symm.trans
      ((congrArg (fun value => domain.map step value) (PresheafIdentityWitness.decode witness)).trans (right.property step)))
  map_id _ := by apply ConcreteCategory.hom_ext; intro _; exact Subsingleton.elim _ _
  map_comp _ _ := by apply ConcreteCategory.hom_ext; intro _; exact Subsingleton.elim _ _

def reflexivity (domain : DisplayedFamily.{u, u, u, u} P) (term : domain.sections) :
  (identityFamily domain term term).sections :=
  ⟨fun _ => PresheafIdentityWitness.encode rfl, by intro _ _ _; rfl⟩

theorem identityFamily_reindex (change : NatTrans Q P)
    (domain : DisplayedFamily.{u, u, u, u} P) (left right : domain.sections) :
    PowerClassPresheafProducts.reindex change (identityFamily domain left right) =
      identityFamily (PowerClassPresheafProducts.reindex change domain) (reindexSection change domain left) (reindexSection change domain right) := rfl

theorem reflexivity_reindex (change : NatTrans Q P)
    (domain : DisplayedFamily.{u, u, u, u} P) (term : domain.sections) :
    HEq (reindexSection change (identityFamily domain term term) (reflexivity domain term))
      (reflexivity (PowerClassPresheafProducts.reindex change domain) (reindexSection change domain term)) := HEq.rfl

def secondFamily (domain : DisplayedFamily.{u, u, u, u} P) :
    DisplayedFamily.{u, u, u, u} (totalSpace domain) := PowerClassPresheafProducts.reindex (PowerClassPresheafProducts.projection domain) domain

def endpoints (domain : DisplayedFamily.{u, u, u, u} P) : Cᵒᵖ ⥤ Type u := totalSpace (secondFamily domain)

def endpointFamily (domain : DisplayedFamily.{u, u, u, u} P) :
    DisplayedFamily.{u, u, u, u} (endpoints domain) := PowerClassPresheafProducts.reindex (PowerClassPresheafProducts.projection (secondFamily domain)) (secondFamily domain)

def leftEndpoint (domain : DisplayedFamily.{u, u, u, u} P) : (endpointFamily domain).sections :=
  reindexSection (PowerClassPresheafProducts.projection (secondFamily domain)) (secondFamily domain) (lastVariable domain)

def rightEndpoint (domain : DisplayedFamily.{u, u, u, u} P) : (endpointFamily domain).sections :=
  lastVariable (secondFamily domain)

def witnessFamily (domain : DisplayedFamily.{u, u, u, u} P) :
    DisplayedFamily.{u, u, u, u} (endpoints domain) :=
  identityFamily (endpointFamily domain) (leftEndpoint domain) (rightEndpoint domain)

def identityContext (domain : DisplayedFamily.{u, u, u, u} P) : Cᵒᵖ ⥤ Type u := totalSpace (witnessFamily domain)

def diagonal (domain : DisplayedFamily.{u, u, u, u} P) : NatTrans (totalSpace domain) (identityContext domain) where
  app _ := TypeCat.ofHom fun receipt => ⟨⟨receipt, receipt.2⟩, PresheafIdentityWitness.encode rfl⟩
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro receipt
    rfl

def readLeft (domain : DisplayedFamily.{u, u, u, u} P) : NatTrans (identityContext domain) (totalSpace domain) where
  app _ := TypeCat.ofHom fun receipt => receipt.1.1
  naturality _ _ _ := by apply ConcreteCategory.hom_ext; intro _; rfl

theorem readLeft_diagonal (domain : DisplayedFamily.{u, u, u, u} P) :
    compose (diagonal domain) (readLeft domain) = identity (totalSpace domain) := rfl

theorem diagonal_readLeft_value (domain : DisplayedFamily.{u, u, u, u} P)
    (point : Cᵒᵖ) (receipt : (identityContext domain).obj point) :
    (diagonal domain).app point ((readLeft domain).app point receipt) = receipt := by
  rcases receipt with ⟨⟨⟨value, left⟩, right⟩, witness⟩
  cases PresheafIdentityWitness.decode witness
  exact congrArg (fun proof =>
    (⟨⟨⟨value, left⟩, left⟩, proof⟩ : (identityContext domain).obj point))
      (PresheafIdentityWitness.encode_decode witness)

theorem diagonal_readLeft (domain : DisplayedFamily.{u, u, u, u} P) :
    compose (readLeft domain) (diagonal domain) = identity (identityContext domain) := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  exact diagonal_readLeft_value domain point

private theorem diagonal_readLeft_point (domain : DisplayedFamily.{u, u, u, u} P)
    (point : (identityContext domain).Elements) :
    (elementMap (diagonal domain)).obj ((elementMap (readLeft domain)).obj point) = point :=
  congrArg (fun receipt => (⟨point.1, receipt⟩ : (identityContext domain).Elements))
    (diagonal_readLeft_value domain point.1 point.2)

private theorem mapFunctions_heq {base : Cᵒᵖ ⥤ Type u} (family : DisplayedFamily.{u, u, u, u} base)
    {first second otherFirst otherSecond : base.Elements}
    (sourceEq : first = otherFirst) (targetEq : second = otherSecond)
    (left : first ⟶ second) (right : otherFirst ⟶ otherSecond)
    (sameArrow : HEq left.val right.val) : HEq (family.map left) (family.map right) := by
  cases sourceEq
  cases targetEq
  have same : left = right := Subtype.ext (eq_of_heq sameArrow)
  cases same
  rfl

private theorem mapValues_heq {base : Cᵒᵖ ⥤ Type u} (family : DisplayedFamily.{u, u, u, u} base)
    {first second otherSecond : base.Elements} (targetEq : second = otherSecond)
    (left : first ⟶ second) (right : first ⟶ otherSecond)
    (sameArrow : HEq left.val right.val) (member : family.obj first) :
    HEq (family.map left member) (family.map right member) := by
  cases targetEq
  have same : left = right := Subtype.ext (eq_of_heq sameArrow)
  cases same
  rfl

/-- The cancellation includes displayed restriction maps, not just their
objectwise types. It follows from the actual contextual diagonal inverse. -/
theorem motiveCancellation (domain : DisplayedFamily.{u, u, u, u} P)
    (motive : DisplayedFamily.{u, u, u, u} (identityContext domain)) :
    PowerClassPresheafProducts.reindex (readLeft domain) (PowerClassPresheafProducts.reindex (diagonal domain) motive) = motive := by
  refine Functor.hext (fun point => congrArg motive.obj (diagonal_readLeft_point domain point)) ?_
  intro first second step
  exact mapFunctions_heq motive (diagonal_readLeft_point domain first) (diagonal_readLeft_point domain second)
    ((elementMap (diagonal domain)).map ((elementMap (readLeft domain)).map step)) step HEq.rfl

def J (domain : DisplayedFamily.{u, u, u, u} P)
    (motive : DisplayedFamily.{u, u, u, u} (identityContext domain))
    (method : (PowerClassPresheafProducts.reindex (diagonal domain) motive).sections) : motive.sections :=
  CP.castSection (motiveCancellation domain motive)
    (reindexSection (readLeft domain) (PowerClassPresheafProducts.reindex (diagonal domain) motive) method)

theorem J_value_heq (domain : DisplayedFamily.{u, u, u, u} P)
    (motive : DisplayedFamily.{u, u, u, u} (identityContext domain))
    (method : (PowerClassPresheafProducts.reindex (diagonal domain) motive).sections) (point : (identityContext domain).Elements) :
    HEq ((J domain motive method).val point) (method.val ((elementMap (readLeft domain)).obj point)) :=
  CP.castSection_value _ _ point

theorem J_beta (domain : DisplayedFamily.{u, u, u, u} P)
    (motive : DisplayedFamily.{u, u, u, u} (identityContext domain))
    (method : (PowerClassPresheafProducts.reindex (diagonal domain) motive).sections) :
    reindexSection (diagonal domain) motive (J domain motive method) = method := by
  apply Subtype.ext
  funext point
  exact eq_of_heq (J_value_heq domain motive method ((elementMap (diagonal domain)).obj point))

section Substitution

theorem reindex_comp {R : Cᵒᵖ ⥤ Type u} (first : NatTrans Q P) (second : NatTrans R Q)
    (family : DisplayedFamily.{u, u, u, u} P) :
    PowerClassPresheafProducts.reindex second (PowerClassPresheafProducts.reindex first family) =
      PowerClassPresheafProducts.reindex (compose second first) family := rfl

theorem reindex_id (family : DisplayedFamily.{u, u, u, u} P) :
    PowerClassPresheafProducts.reindex (identity P) family = family := rfl

/-- The actual comprehension map retains its dependent member. Its laws
are explicit and do not invoke default functor composition proofs. -/
def totalReindex (change : NatTrans Q P) (domain : DisplayedFamily.{u, u, u, u} P) :
    NatTrans (totalSpace (PowerClassPresheafProducts.reindex change domain)) (totalSpace domain) where
  app _ := TypeCat.ofHom fun receipt => ⟨change.app _ receipt.1, receipt.2⟩
  naturality X Y step := by
    apply ConcreteCategory.hom_ext
    rintro ⟨value, member⟩
    have same := congrArg (fun map => map value) (change.naturality step)
    apply Sigma.ext same
    exact mapValues_heq domain (congrArg (fun value => (⟨Y, value⟩ : P.Elements)) same)
      ((elementMap change).map (CategoryOfElements.homMk (F := Q)
        ⟨X, value⟩ ⟨Y, Q.map step value⟩ step rfl))
      (CategoryOfElements.homMk (F := P)
        ⟨X, change.app X value⟩ ⟨Y, P.map step (change.app X value)⟩ step rfl) HEq.rfl member

theorem secondFamily_reindex (change : NatTrans Q P) (domain : DisplayedFamily.{u, u, u, u} P) :
    PowerClassPresheafProducts.reindex (totalReindex change domain) (secondFamily domain) =
      secondFamily (PowerClassPresheafProducts.reindex change domain) := rfl

def endpointReindex (change : NatTrans Q P) (domain : DisplayedFamily.{u, u, u, u} P) :
    NatTrans (endpoints (PowerClassPresheafProducts.reindex change domain)) (endpoints domain) :=
  totalReindex (totalReindex change domain) (secondFamily domain)

theorem witnessFamily_reindex (change : NatTrans Q P) (domain : DisplayedFamily.{u, u, u, u} P) :
    PowerClassPresheafProducts.reindex (endpointReindex change domain) (witnessFamily domain) =
      witnessFamily (PowerClassPresheafProducts.reindex change domain) := rfl

def identityReindex (change : NatTrans Q P) (domain : DisplayedFamily.{u, u, u, u} P) :
    NatTrans (identityContext (PowerClassPresheafProducts.reindex change domain)) (identityContext domain) :=
  totalReindex (endpointReindex change domain) (witnessFamily domain)

theorem totalReindex_id (domain : DisplayedFamily.{u, u, u, u} P) :
    totalReindex (identity P) domain = identity (totalSpace domain) := rfl

theorem totalReindex_comp {R : Cᵒᵖ ⥤ Type u} (first : NatTrans Q P) (second : NatTrans R Q)
    (domain : DisplayedFamily.{u, u, u, u} P) :
    totalReindex (compose second first) domain =
      compose (totalReindex second (PowerClassPresheafProducts.reindex first domain))
        (totalReindex first domain) := rfl

theorem identityReindex_id (domain : DisplayedFamily.{u, u, u, u} P) :
    identityReindex (identity P) domain = identity (identityContext domain) := rfl

theorem identityReindex_comp {R : Cᵒᵖ ⥤ Type u} (first : NatTrans Q P) (second : NatTrans R Q)
    (domain : DisplayedFamily.{u, u, u, u} P) :
    identityReindex (compose second first) domain =
      compose (identityReindex second (PowerClassPresheafProducts.reindex first domain))
        (identityReindex first domain) := rfl

theorem diagonal_square (change : NatTrans Q P) (domain : DisplayedFamily.{u, u, u, u} P) :
    compose (diagonal (PowerClassPresheafProducts.reindex change domain)) (identityReindex change domain) =
      compose (totalReindex change domain) (diagonal domain) := rfl

theorem readLeft_square (change : NatTrans Q P) (domain : DisplayedFamily.{u, u, u, u} P) :
    compose (identityReindex change domain) (readLeft domain) =
      compose (readLeft (PowerClassPresheafProducts.reindex change domain)) (totalReindex change domain) := rfl

theorem reflexiveMotive_reindex (change : NatTrans Q P) (domain : DisplayedFamily.{u, u, u, u} P)
    (motive : DisplayedFamily.{u, u, u, u} (identityContext domain)) :
    PowerClassPresheafProducts.reindex (totalReindex change domain)
      (PowerClassPresheafProducts.reindex (diagonal domain) motive) =
      PowerClassPresheafProducts.reindex (diagonal (PowerClassPresheafProducts.reindex change domain))
        (PowerClassPresheafProducts.reindex (identityReindex change domain) motive) := by
  rw [reindex_comp, reindex_comp, diagonal_square]

def reindexMethod (change : NatTrans Q P) (domain : DisplayedFamily.{u, u, u, u} P)
    (motive : DisplayedFamily.{u, u, u, u} (identityContext domain))
    (method : (PowerClassPresheafProducts.reindex (diagonal domain) motive).sections) :
    (PowerClassPresheafProducts.reindex (diagonal (PowerClassPresheafProducts.reindex change domain))
      (PowerClassPresheafProducts.reindex (identityReindex change domain) motive)).sections :=
  CP.castSection (reflexiveMotive_reindex change domain motive)
    (reindexSection (totalReindex change domain) (PowerClassPresheafProducts.reindex (diagonal domain) motive) method)

/-- Full dependent J is stable under every natural base substitution. The
motive ranges over both endpoints and the actual material witness carrier. -/
theorem J_substitution (change : NatTrans Q P) (domain : DisplayedFamily.{u, u, u, u} P)
    (motive : DisplayedFamily.{u, u, u, u} (identityContext domain))
    (method : (PowerClassPresheafProducts.reindex (diagonal domain) motive).sections) :
    reindexSection (identityReindex change domain) motive (J domain motive method) =
      J (PowerClassPresheafProducts.reindex change domain)
        (PowerClassPresheafProducts.reindex (identityReindex change domain) motive)
        (reindexMethod change domain motive method) := by
  apply Subtype.ext
  funext point
  apply eq_of_heq
  have first := J_value_heq domain motive method ((elementMap (identityReindex change domain)).obj point)
  have second := J_value_heq (PowerClassPresheafProducts.reindex change domain)
    (PowerClassPresheafProducts.reindex (identityReindex change domain) motive)
    (reindexMethod change domain motive method) point
  have methodCast := CP.castSection_value (reflexiveMotive_reindex change domain motive)
    (reindexSection (totalReindex change domain) (PowerClassPresheafProducts.reindex (diagonal domain) motive) method)
    ((elementMap (readLeft (PowerClassPresheafProducts.reindex change domain))).obj point)
  exact first.trans (second.trans methodCast).symm

theorem J_beta_substitution (change : NatTrans Q P) (domain : DisplayedFamily.{u, u, u, u} P)
    (motive : DisplayedFamily.{u, u, u, u} (identityContext domain))
    (method : (PowerClassPresheafProducts.reindex (diagonal domain) motive).sections) :
    reindexSection (diagonal (PowerClassPresheafProducts.reindex change domain))
      (PowerClassPresheafProducts.reindex (identityReindex change domain) motive)
      (reindexSection (identityReindex change domain) motive (J domain motive method)) =
      reindexMethod change domain motive method := by
  rw [J_substitution]
  exact J_beta _ _ _

/-- A composite base substitution and successive substitutions agree at
the full dependent J term, including its reflexive method. -/
theorem J_substitution_comp {R : Cᵒᵖ ⥤ Type u}
    (first : NatTrans Q P) (second : NatTrans R Q)
    (domain : DisplayedFamily.{u, u, u, u} P)
    (motive : DisplayedFamily.{u, u, u, u} (identityContext domain))
    (method : (PowerClassPresheafProducts.reindex (diagonal domain) motive).sections) :
    J (PowerClassPresheafProducts.reindex (compose second first) domain)
        (PowerClassPresheafProducts.reindex (identityReindex (compose second first) domain) motive)
        (reindexMethod (compose second first) domain motive method) =
      reindexSection (identityReindex second (PowerClassPresheafProducts.reindex first domain))
        (PowerClassPresheafProducts.reindex (identityReindex first domain) motive)
        (J (PowerClassPresheafProducts.reindex first domain)
          (PowerClassPresheafProducts.reindex (identityReindex first domain) motive)
          (reindexMethod first domain motive method)) := by
  rw [← J_substitution, ← J_substitution]
  rfl

end Substitution

/-! The following laws are local controls for this discrete interpretation.
The positive motive retains the actual endpoint family. A distinct endpoint
pair has no material witness, and identity terms reflect equality only here. -/

def endpointMotive (domain : DisplayedFamily.{u, u, u, u} P) :
    DisplayedFamily.{u, u, u, u} (identityContext domain) :=
  PowerClassPresheafProducts.reindex (readLeft domain) (secondFamily domain)

def endpointMethod (domain : DisplayedFamily.{u, u, u, u} P) :
    (PowerClassPresheafProducts.reindex (diagonal domain) (endpointMotive domain)).sections :=
  lastVariable domain

theorem J_endpoint_value (domain : DisplayedFamily.{u, u, u, u} P)
    (point : (identityContext domain).Elements) :
    (J domain (endpointMotive domain) (endpointMethod domain)).val point = point.2.1.1.2 :=
  eq_of_heq (J_value_heq domain (endpointMotive domain) (endpointMethod domain) point)

theorem offDiagonal_empty (domain : DisplayedFamily.{u, u, u, u} P)
    (point : P.Elements) (left right : domain.obj point) (different : left ≠ right) :
    ¬ Nonempty ((witnessFamily domain).obj ⟨point.1, ⟨⟨point.2, left⟩, right⟩⟩) :=
  PresheafIdentityWitness.witness_empty_of_distinct different

theorem identitySection_endpoints (domain : DisplayedFamily.{u, u, u, u} P)
    {left right : domain.sections} (witness : (identityFamily domain left right).sections) : left = right := by
  apply Subtype.ext
  funext point
  exact PresheafIdentityWitness.decode (witness.val point)

theorem identitySections_subsingleton (domain : DisplayedFamily.{u, u, u, u} P)
    (left right : domain.sections) : Subsingleton ((identityFamily domain left right).sections) :=
  ⟨fun first second => Subtype.ext (funext fun point =>
    @Subsingleton.elim (PresheafIdentityWitness.Witness (left.val point) (right.val point))
      inferInstance (first.val point) (second.val point))⟩

end Mettapedia.TypeTheory.MaterialSets.Hypersets.DisplayedPresheafIdentity
