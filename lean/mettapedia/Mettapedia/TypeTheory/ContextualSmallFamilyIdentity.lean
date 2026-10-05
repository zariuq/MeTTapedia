import Mettapedia.TypeTheory.ContextualSmallFamilyComprehension
import Mettapedia.TypeTheory.MaterialSets.Hypersets.PresheafIdentityWitness

/-!
# Small material discrete identity over wider contextual parameters

Actual nested comprehension retains both endpoints and the small material
singleton witness. An explicitly inverse reflexivity diagonal constructs
dependent J for arbitrary natural motives, including motives in a larger
universe than the identity fibre. Base substitution retains every endpoint,
witness and motive value.

This is the discrete interpretation in set-valued contextual families.
Its local equality and witness irrelevance do not impose native UIP or
reflection, or identify it with a proof-relevant groupoid interpretation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSmallFamilyIdentity

open CategoryTheory ContextualWitnessCover
open ContextualImageFactorization
open ContextualSmallFamilyTypeFormers ContextualSmallFamilyComprehension
open MaterialSets.Hypersets

universe u v w z t
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type v}


def reindex {other : D ⥤ Type w} (family : base.Elements ⥤ Type z)
    (change : NaturalHom other base) : other.Elements ⥤ Type z :=
  ContextualSmallFamilyUniverse.restrict (ContextualSmallFamilyUniverse.elementMap change) family

def identityFamily (domain : base.Elements ⥤ Type u) (left right : domain.sections) : base.Elements ⥤ Type u where
  obj point := PresheafIdentityWitness.Witness (left.val point) (right.val point)
  map {first second} step := TypeCat.ofHom fun witness =>
    PresheafIdentityWitness.encode ((left.property step).symm.trans
      ((congrArg (fun value => domain.map step value) (PresheafIdentityWitness.decode witness)).trans
        (right.property step)))
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro _
    exact Subsingleton.elim _ _
  map_comp _ _ := by
    apply ConcreteCategory.hom_ext
    intro _
    exact Subsingleton.elim _ _

def reflexivity (domain : base.Elements ⥤ Type u) (term : domain.sections) :
    (identityFamily domain term term).sections :=
  ⟨fun _ => PresheafIdentityWitness.encode rfl, by intro _ _ _; rfl⟩

def reindexSection {other : D ⥤ Type w} (change : NaturalHom other base)
    (family : base.Elements ⥤ Type z) (term : family.sections) :
    (reindex family change).sections :=
  sectionPull (ContextualSmallFamilyUniverse.elementMap change) family term

theorem identityFamily_substitution {other : D ⥤ Type w} (change : NaturalHom other base)
    (domain : base.Elements ⥤ Type u) (left right : domain.sections) :
    reindex (identityFamily domain left right) change =
      identityFamily (reindex domain change)
        (reindexSection change domain left) (reindexSection change domain right) := rfl

theorem reflexivity_substitution {other : D ⥤ Type w} (change : NaturalHom other base)
    (domain : base.Elements ⥤ Type u) (term : domain.sections) :
    HEq (reindexSection change (identityFamily domain term term) (reflexivity domain term))
      (reflexivity (reindex domain change)
        (reindexSection change domain term)) := HEq.rfl

def secondFamily (domain : base.Elements ⥤ Type u) :
    (ContextualSmallFamilyUniverse.total domain).Elements ⥤ Type u :=
  reindex domain (ContextualSmallFamilyUniverse.projection domain)

def lastVariable (domain : base.Elements ⥤ Type u) : (secondFamily domain).sections :=
  ⟨fun point => point.2.2, fun {_ _} step => ((unflatten domain).map step).2⟩

def endpoints (domain : base.Elements ⥤ Type u) : D ⥤ Type (max u v) :=
  ContextualSmallFamilyUniverse.total (secondFamily domain)

def endpointFamily (domain : base.Elements ⥤ Type u) : (endpoints domain).Elements ⥤ Type u :=
  reindex (secondFamily domain)
    (ContextualSmallFamilyUniverse.projection (secondFamily domain))

def leftEndpoint (domain : base.Elements ⥤ Type u) : (endpointFamily domain).sections :=
  reindexSection (ContextualSmallFamilyUniverse.projection (secondFamily domain))
    (secondFamily domain) (lastVariable domain)

def rightEndpoint (domain : base.Elements ⥤ Type u) : (endpointFamily domain).sections :=
  lastVariable (secondFamily domain)

def witnessFamily (domain : base.Elements ⥤ Type u) : (endpoints domain).Elements ⥤ Type u :=
  identityFamily (endpointFamily domain) (leftEndpoint domain) (rightEndpoint domain)

def identityContext (domain : base.Elements ⥤ Type u) : D ⥤ Type (max u v) :=
  ContextualSmallFamilyUniverse.total (witnessFamily domain)

def diagonal (domain : base.Elements ⥤ Type u) :
    NaturalHom (ContextualSmallFamilyUniverse.total domain) (identityContext domain) where
  app _ receipt := ⟨⟨receipt, receipt.2⟩, PresheafIdentityWitness.encode rfl⟩
  naturality _ _ := rfl

def readLeft (domain : base.Elements ⥤ Type u) :
    NaturalHom (identityContext domain) (ContextualSmallFamilyUniverse.total domain) where
  app _ receipt := receipt.1.1
  naturality _ _ := rfl

theorem readLeft_diagonal (domain : base.Elements ⥤ Type u) :
    (diagonal domain).comp (readLeft domain) = ContextualSmallMapConstructions.identity (ContextualSmallFamilyUniverse.total domain) := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem diagonal_readLeft_value (domain : base.Elements ⥤ Type u)
    (point : D) (receipt : (identityContext domain).obj point) :
    (diagonal domain).app point ((readLeft domain).app point receipt) = receipt := by
  rcases receipt with ⟨⟨⟨parameter, left⟩, right⟩, witness⟩
  cases PresheafIdentityWitness.decode witness
  exact congrArg (fun proof =>
    (⟨⟨⟨parameter, left⟩, left⟩, proof⟩ : (identityContext domain).obj point))
      (PresheafIdentityWitness.encode_decode witness)

theorem diagonal_readLeft (domain : base.Elements ⥤ Type u) :
    (readLeft domain).comp (diagonal domain) = ContextualSmallMapConstructions.identity (identityContext domain) := by
  apply NaturalHom.ext
  exact diagonal_readLeft_value domain

theorem diagonal_readLeft_point (domain : base.Elements ⥤ Type u)
    (point : (identityContext domain).Elements) :
    (ContextualSmallFamilyUniverse.elementMap (diagonal domain)).obj
        ((ContextualSmallFamilyUniverse.elementMap (readLeft domain)).obj point) = point :=
  congrArg (fun receipt => (⟨point.1, receipt⟩ : (identityContext domain).Elements))
    (diagonal_readLeft_value domain point.1 point.2)

theorem motiveCancellation (domain : base.Elements ⥤ Type u)
    (motive : (identityContext domain).Elements ⥤ Type z) :
    reindex
      (reindex motive (diagonal domain)) (readLeft domain) = motive := by
  refine Functor.hext (fun point => congrArg motive.obj (diagonal_readLeft_point domain point)) ?_
  intro first second step
  exact ContextualSmallFamilyUniverse.familyArrow_heq motive
    (diagonal_readLeft_point domain first) (diagonal_readLeft_point domain second) _ _
    (ContextualSmallFamilyUniverse.elementsArrow_heq
      (diagonal_readLeft_point domain first) (diagonal_readLeft_point domain second) _ _ HEq.rfl)

def J (domain : base.Elements ⥤ Type u) (motive : (identityContext domain).Elements ⥤ Type z)
    (method : (reindex motive (diagonal domain)).sections) : motive.sections :=
  sectionCast (motiveCancellation domain motive)
    (reindexSection (readLeft domain)
      (reindex motive (diagonal domain)) method)

theorem J_value_heq (domain : base.Elements ⥤ Type u) (motive : (identityContext domain).Elements ⥤ Type z)
    (method : (reindex motive (diagonal domain)).sections)
    (point : (identityContext domain).Elements) :
    HEq ((J domain motive method).val point)
      (method.val ((ContextualSmallFamilyUniverse.elementMap (readLeft domain)).obj point)) :=
  sectionCast_value _ _ point

theorem J_beta (domain : base.Elements ⥤ Type u) (motive : (identityContext domain).Elements ⥤ Type z)
    (method : (reindex motive (diagonal domain)).sections) :
    reindexSection (diagonal domain) motive (J domain motive method) = method := by
  apply Subtype.ext
  funext point
  exact eq_of_heq (J_value_heq domain motive method
    ((ContextualSmallFamilyUniverse.elementMap (diagonal domain)).obj point))

section Substitution

variable {other : D ⥤ Type w} (change : NaturalHom other base)

theorem reindex_comp {third : D ⥤ Type z} (first : NaturalHom other base)
    (second : NaturalHom third other) (family : base.Elements ⥤ Type u) :
    reindex (reindex family first) second = reindex family (second.comp first) := rfl

theorem reindex_id (family : base.Elements ⥤ Type u) : reindex family (ContextualSmallMapConstructions.identity base) = family := rfl

def totalReindex (domain : base.Elements ⥤ Type u) :
    NaturalHom (ContextualSmallFamilyUniverse.total (reindex domain change))
      (ContextualSmallFamilyUniverse.total domain) := totalChange domain change

theorem secondFamily_reindex (domain : base.Elements ⥤ Type u) :
    reindex (secondFamily domain) (totalReindex change domain) = secondFamily (reindex domain change) := rfl

def endpointReindex (domain : base.Elements ⥤ Type u) :
    NaturalHom (endpoints (reindex domain change)) (endpoints domain) :=
  totalReindex (totalReindex change domain) (secondFamily domain)

theorem witnessFamily_reindex (domain : base.Elements ⥤ Type u) :
    reindex (witnessFamily domain) (endpointReindex change domain) = witnessFamily (reindex domain change) := rfl

def identityReindex (domain : base.Elements ⥤ Type u) :
    NaturalHom (identityContext (reindex domain change)) (identityContext domain) :=
  totalReindex (endpointReindex change domain) (witnessFamily domain)

theorem totalReindex_id (domain : base.Elements ⥤ Type u) :
    totalReindex (ContextualSmallMapConstructions.identity base) domain = ContextualSmallMapConstructions.identity (ContextualSmallFamilyUniverse.total domain) := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem totalReindex_comp {third : D ⥤ Type z} (first : NaturalHom other base)
    (second : NaturalHom third other) (domain : base.Elements ⥤ Type u) :
    totalReindex (second.comp first) domain =
      (totalReindex second (reindex domain first)).comp (totalReindex first domain) := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem identityReindex_id (domain : base.Elements ⥤ Type u) :
    identityReindex (ContextualSmallMapConstructions.identity base) domain = ContextualSmallMapConstructions.identity (identityContext domain) := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem identityReindex_comp {third : D ⥤ Type z} (first : NaturalHom other base)
    (second : NaturalHom third other) (domain : base.Elements ⥤ Type u) :
    identityReindex (second.comp first) domain =
      (identityReindex second (reindex domain first)).comp (identityReindex first domain) := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem diagonal_square (domain : base.Elements ⥤ Type u) :
    (diagonal (reindex domain change)).comp (identityReindex change domain) =
      (totalReindex change domain).comp (diagonal domain) := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem readLeft_square (domain : base.Elements ⥤ Type u) :
    (identityReindex change domain).comp (readLeft domain) =
      (readLeft (reindex domain change)).comp (totalReindex change domain) := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem reflexiveMotive_reindex (domain : base.Elements ⥤ Type u)
    (motive : (identityContext domain).Elements ⥤ Type z) :
    reindex (reindex motive (diagonal domain)) (totalReindex change domain) =
      reindex (reindex motive (identityReindex change domain)) (diagonal (reindex domain change)) := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

def reindexMethod (domain : base.Elements ⥤ Type u) (motive : (identityContext domain).Elements ⥤ Type z)
    (method : (reindex motive (diagonal domain)).sections) :
    (reindex (reindex motive (identityReindex change domain)) (diagonal (reindex domain change))).sections :=
  sectionCast (reflexiveMotive_reindex change domain motive)
    (reindexSection (totalReindex change domain) (reindex motive (diagonal domain)) method)

theorem J_substitution (domain : base.Elements ⥤ Type u) (motive : (identityContext domain).Elements ⥤ Type z)
    (method : (reindex motive (diagonal domain)).sections) :
    reindexSection (identityReindex change domain) motive (J domain motive method) =
      J (reindex domain change) (reindex motive (identityReindex change domain))
        (reindexMethod change domain motive method) := by
  apply Subtype.ext
  funext point
  apply eq_of_heq
  have first := J_value_heq domain motive method
    ((ContextualSmallFamilyUniverse.elementMap (identityReindex change domain)).obj point)
  have second := J_value_heq (reindex domain change) (reindex motive (identityReindex change domain))
    (reindexMethod change domain motive method) point
  have castValue := sectionCast_value (reflexiveMotive_reindex change domain motive)
    (reindexSection (totalReindex change domain) (reindex motive (diagonal domain)) method)
    ((ContextualSmallFamilyUniverse.elementMap (readLeft (reindex domain change))).obj point)
  exact first.trans (second.trans castValue).symm

theorem J_beta_substitution (domain : base.Elements ⥤ Type u) (motive : (identityContext domain).Elements ⥤ Type z)
    (method : (reindex motive (diagonal domain)).sections) :
    reindexSection (diagonal (reindex domain change)) (reindex motive (identityReindex change domain))
      (reindexSection (identityReindex change domain) motive (J domain motive method)) =
        reindexMethod change domain motive method := by
  rw [J_substitution]
  exact J_beta _ _ _

end Substitution

theorem J_substitution_comp {other : D ⥤ Type w} {third : D ⥤ Type z}
    (first : NaturalHom other base) (second : NaturalHom third other)
    (domain : base.Elements ⥤ Type u) (motive : (identityContext domain).Elements ⥤ Type t)
    (method : (reindex motive (diagonal domain)).sections) :
    J (reindex domain (second.comp first)) (reindex motive (identityReindex (second.comp first) domain))
        (reindexMethod (second.comp first) domain motive method) =
      reindexSection (identityReindex second (reindex domain first))
        (reindex motive (identityReindex first domain))
        (J (reindex domain first) (reindex motive (identityReindex first domain))
          (reindexMethod first domain motive method)) := by
  rw [← J_substitution, ← J_substitution]
  rfl

def endpointMotive (domain : base.Elements ⥤ Type u) : (identityContext domain).Elements ⥤ Type u :=
  reindex (secondFamily domain) (readLeft domain)

def endpointMethod (domain : base.Elements ⥤ Type u) :
    (reindex (endpointMotive domain) (diagonal domain)).sections := lastVariable domain

theorem J_endpoint_value (domain : base.Elements ⥤ Type u) (point : (identityContext domain).Elements) :
    (J domain (endpointMotive domain) (endpointMethod domain)).val point = point.2.1.1.2 :=
  eq_of_heq (J_value_heq domain (endpointMotive domain) (endpointMethod domain) point)

theorem offDiagonal_empty (domain : base.Elements ⥤ Type u) (point : base.Elements)
    (left right : domain.obj point) (different : left ≠ right) :
    ¬ Nonempty ((witnessFamily domain).obj ⟨point.1, ⟨⟨point.2, left⟩, right⟩⟩) :=
  PresheafIdentityWitness.witness_empty_of_distinct different

theorem identitySection_endpoints (domain : base.Elements ⥤ Type u)
    {left right : domain.sections} (witness : (identityFamily domain left right).sections) : left = right := by
  apply Subtype.ext
  funext point
  exact PresheafIdentityWitness.decode (witness.val point)

theorem identitySections_subsingleton (domain : base.Elements ⥤ Type u) (left right : domain.sections) :
    Subsingleton ((identityFamily domain left right).sections) :=
  ⟨fun first second => Subtype.ext (funext fun point =>
    @Subsingleton.elim (PresheafIdentityWitness.Witness (left.val point) (right.val point))
      inferInstance (first.val point) (second.val point))⟩

theorem identity_decoder (domain : base.Elements ⥤ Type u) (left right : domain.sections) :
    ContextualSmallFamilyUniverse.decodedFamily
      (ContextualSmallFamilyUniverse.classifier (identityFamily domain left right)) =
        identityFamily domain left right := ContextualSmallFamilyUniverse.decoded_classifier_eq _

end Mettapedia.TypeTheory.ContextualSmallFamilyIdentity
