import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Types.Basic

/-!
# A constructed small contextual witness cover

Over a small category, the free fibre at a point consists of every generator
and an actual arrow from that generator to the point. Restriction postcomposes
this arrow. These fibres inhabit the category's original small universe.

Authored witness data in a possibly wider functor determines a natural map
from this actual small cover. Its universal property compares all such
natural maps with witness data at the generators. Pointwise nonemptiness
alone does not select these data in this module, and the diagonal local
inhabitants of the cover are not asserted to form a compatible section.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualWitnessCover

open CategoryTheory

universe u v w t

variable {E : Type u} [Category.{u} E]

/-- Natural pointwise maps between type-valued functors whose value
universes need not coincide. No change to either carrier is made. -/
structure NaturalHom (source : E ⥤ Type v) (target : E ⥤ Type w) where
  app : ∀ point, source.obj point → target.obj point
  naturality : ∀ {first second} (arrow : first ⟶ second) (value : source.obj first),
    target.map arrow (app first value) = app second (source.map arrow value)

namespace NaturalHom

variable {source : E ⥤ Type v} {target : E ⥤ Type w} {later : E ⥤ Type t}

theorem ext (first second : NaturalHom source target)
    (same : ∀ point value, first.app point value = second.app point value) : first = second := by
  cases first with
  | mk first first_law =>
    cases second with
    | mk second second_law =>
      have maps : first = second := funext fun point => funext fun value => same point value
      cases maps
      rfl

def comp (first : NaturalHom source target) (second : NaturalHom target later) :
    NaturalHom source later where
  app point value := second.app point (first.app point value)
  naturality arrow value :=
    (second.naturality arrow (first.app _ value)).trans
      (congrArg (second.app _) (first.naturality arrow value))

/-- Compatible sections are transported using the actual naturality law,
even from an original small source into a wider target. -/
def mapSection (operation : NaturalHom source target) (term : source.sections) : target.sections :=
  ⟨fun point => operation.app point (term.val point), by
    intro first second arrow
    exact (operation.naturality arrow (term.val first)).trans
      (congrArg (operation.app second) (term.property arrow))⟩

theorem mapSection_comp (first : NaturalHom source target) (second : NaturalHom target later)
    (term : source.sections) : (first.comp second).mapSection term =
      second.mapSection (first.mapSection term) := rfl

def toNatTrans {first second : E ⥤ Type v} (operation : NaturalHom first second) :
    NatTrans first second where
  app point := TypeCat.ofHom (operation.app point)
  naturality _ _ arrow := by
    apply ConcreteCategory.hom_ext
    intro value
    exact (operation.naturality arrow value).symm

def ofNatTrans {first second : E ⥤ Type v} (operation : NatTrans first second) :
    NaturalHom first second where
  app point := operation.app point
  naturality arrow value := (congrArg (fun map => map value) (operation.naturality arrow)).symm

end NaturalHom

/-- Each fibre contains all small generators and all actual arrows to its
point. It is a constructed `Type u`, independently of a witness functor. -/
def free : E ⥤ Type u where
  obj point := Σ generator : E, generator ⟶ point
  map arrow := TypeCat.ofHom (fun receipt => ⟨receipt.1, receipt.2 ≫ arrow⟩)
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro receipt
    exact congrArg (Sigma.mk receipt.1) (Category.comp_id receipt.2)
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro receipt
    exact congrArg (Sigma.mk receipt.1) (Category.assoc receipt.2 first second).symm

def seed (point : E) : (free (E := E)).obj point := ⟨point, 𝟙 point⟩

def terminal : E ⥤ Type u where
  obj _ := PUnit.{u + 1}
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def projection : NatTrans (free (E := E)) terminal where
  app _ := TypeCat.ofHom (fun _ => PUnit.unit)
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro _
    rfl

theorem projection_surjective (point : E) : Function.Surjective (projection.app point) := by
  intro value
  cases value
  exact ⟨seed point, rfl⟩

theorem fibre_inhabited (point : E) : Nonempty ((free (E := E)).obj point) := ⟨seed point⟩

def terminalSection : (terminal (E := E)).sections :=
  ⟨fun _ => PUnit.unit, fun _ => rfl⟩

/-- A natural splitting would give a compatible section. The local diagonal
inhabitants used in the surjectivity proof do not supply this map. -/
def sectionOfTerminalMap (operation : NatTrans terminal (free (E := E))) :
    (free (E := E)).sections := (NaturalHom.ofNatTrans operation).mapSection terminalSection

/-- Witnesses are input data, not selected from pointwise existence. They
need not be compatible; actual arrows provide the natural transported map. -/
def fromWitness (R : E ⥤ Type v) (witness : ∀ generator, R.obj generator) :
    NaturalHom (free (E := E)) R where
  app _ receipt := R.map receipt.2 (witness receipt.1)
  naturality arrow receipt :=
    (congrArg (fun map => map (witness receipt.1)) (R.map_comp receipt.2 arrow)).symm

theorem fromWitness_seed (R : E ⥤ Type v) (witness : ∀ generator, R.obj generator)
    (point : E) : (fromWitness R witness).app point (seed point) = witness point :=
  R.map_id_apply point (witness point)

theorem free_map_seed {first second : E} (arrow : first ⟶ second) :
    (free (E := E)).map arrow (seed first) = ⟨first, arrow⟩ :=
  congrArg (Sigma.mk first) (Category.id_comp arrow)

def witnessOfHom (R : E ⥤ Type v) (operation : NaturalHom (free (E := E)) R) :
    ∀ point, R.obj point := fun point => operation.app point (seed point)

theorem fromWitness_witnessOfHom (R : E ⥤ Type v) (operation : NaturalHom (free (E := E)) R) :
    fromWitness R (witnessOfHom R operation) = operation := by
  apply NaturalHom.ext
  rintro point ⟨generator, arrow⟩
  change R.map arrow (operation.app generator (seed generator)) =
    operation.app point ⟨generator, arrow⟩
  exact (operation.naturality arrow (seed generator)).trans
    (congrArg (operation.app point) (free_map_seed arrow))

theorem witnessOfHom_fromWitness (R : E ⥤ Type v) (witness : ∀ generator, R.obj generator) :
    witnessOfHom R (fromWitness R witness) = witness := funext (fromWitness_seed R witness)

/-- The actual free-cover universal property has explicit inverses and is
valid across the small-source / wide-target universe boundary. -/
def witnessHomEquiv (R : E ⥤ Type v) :
    (∀ point, R.obj point) ≃ NaturalHom (free (E := E)) R where
  toFun := fromWitness R
  invFun := witnessOfHom R
  left_inv := witnessOfHom_fromWitness R
  right_inv := fromWitness_witnessOfHom R

theorem nonempty_hom_iff_witness_data (R : E ⥤ Type v) :
    Nonempty (NaturalHom (free (E := E)) R) ↔ Nonempty (∀ point, R.obj point) :=
  ⟨fun ⟨operation⟩ => ⟨witnessOfHom R operation⟩,
    fun ⟨witness⟩ => ⟨fromWitness R witness⟩⟩

theorem free_no_section_of_target_no_section (R : E ⥤ Type v)
    (witness : ∀ generator, R.obj generator) (absent : ¬ Nonempty R.sections) :
    ¬ Nonempty (free (E := E)).sections :=
  fun ⟨term⟩ => absent ⟨(fromWitness R witness).mapSection term⟩

/-- Naturality of the local diagonal inhabitants would amount to requiring
every contextual arrow to fix that chosen receipt. This is not automatic. -/
theorem seed_compatible_iff :
    (∀ {first second : E} (arrow : first ⟶ second),
      (free (E := E)).map arrow (seed first) = seed second) ↔
      ∀ {first second : E} (arrow : first ⟶ second),
        (⟨first, arrow⟩ : (free (E := E)).obj second) = seed second := by
  constructor
  · intro compatible first second arrow
    exact (free_map_seed arrow).symm.trans (compatible arrow)
  · intro compatible first second arrow
    exact (free_map_seed arrow).trans (compatible arrow)

end Mettapedia.TypeTheory.ContextualWitnessCover
