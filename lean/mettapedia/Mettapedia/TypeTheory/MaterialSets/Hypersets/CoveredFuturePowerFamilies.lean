import Mettapedia.TypeTheory.MaterialSets.Hypersets.FuturePowerFamilies

/-!
# Small-covered power families on larger argument objects

The context objects and arrows inhabit a fixed small universe; argument
fibres may inhabit a larger universe. A power element retains a stable
predicate on all future arrows together with propositional existence of a
uniform small enumeration of its truth at every future index. Restriction
constructs the new enumeration by precomposition, without selecting one
from its existence proof.

On an originally small argument family every stable future predicate has
such an enumeration, constructed from its actual truth subtype. On a larger
family the admitted predicates retain actual small covers. A cover is not
claimed to supply an inverse, a chosen representative, quotient closure,
collection, a universal small map or indexed finality.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerFamilies

open CategoryTheory
open PowerClassPresheafBaseChange

universe u v
variable {D : Type u} [Category.{u} D]

/-- The actual future category is small, independently of argument size. -/
def domain (A : D ⥤ Type v) (point : D) : Future.Objects point ⥤ Type v where
  obj future := A.obj future.1
  map step := A.map step.1
  map_id future := A.map_id future.1
  map_comp first second := A.map_comp first.1 second.1

abbrev Arguments (A : D ⥤ Type v) (point : D) := (domain A point).Elements

structure Predicate (A : D ⥤ Type v) (point : D) where
  holds : Arguments A point → Prop
  closed : ∀ {first second} (_step : first ⟶ second), holds first → holds second

namespace Predicate

variable {A : D ⥤ Type v} {point : D}

theorem ext (first second : Predicate A point)
    (same : ∀ argument, first.holds argument ↔ second.holds argument) : first = second := by
  cases first with
  | mk first firstLaw =>
    cases second with
    | mk second secondLaw =>
      have predicates : first = second := funext fun argument => propext (same argument)
      cases predicates
      rfl

end Predicate

/-- Each future has a displayed small carrier covering its actual true
arguments. Duplicate receipts are permitted; no inverse is asserted. -/
structure Enumeration {A : D ⥤ Type v} {point : D} (predicate : Predicate A point) where
  Carrier : Future.Objects point → Type u
  value : (future : Future.Objects point) → Carrier future → A.obj future.1
  covered : ∀ future argument,
    predicate.holds ⟨future, argument⟩ ↔ ∃ code, value future code = argument

abbrev Power (A : D ⥤ Type v) (point : D) :=
  {predicate : Predicate A point // Nonempty (Enumeration predicate)}

def futurePrecompose (A : D ⥤ Type v) {first second : D} (step : first ⟶ second) :
    Arguments A second ⥤ Arguments A first where
  obj argument := ⟨⟨argument.1.1, step ≫ argument.1.2⟩, argument.2⟩
  map move := ⟨⟨move.1.1, by rw [Category.assoc, move.1.2]⟩, move.2⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def restrict (A : D ⥤ Type v) {first second : D} (step : first ⟶ second)
    (predicate : Predicate A first) : Predicate A second where
  holds argument := predicate.holds ((futurePrecompose A step).obj argument)
  closed move available := predicate.closed ((futurePrecompose A step).map move) available

def restrictEnumeration {A : D ⥤ Type v} {first second : D}
    (step : first ⟶ second) {predicate : Predicate A first}
    (enumeration : Enumeration predicate) : Enumeration (restrict A step predicate) where
  Carrier future := enumeration.Carrier ⟨future.1, step ≫ future.2⟩
  value future := enumeration.value ⟨future.1, step ≫ future.2⟩
  covered future argument := enumeration.covered ⟨future.1, step ≫ future.2⟩ argument

def restrictPower (A : D ⥤ Type v) {first second : D} (step : first ⟶ second)
    (predicate : Power A first) : Power A second :=
  ⟨restrict A step predicate.val, by
    obtain ⟨enumeration⟩ := predicate.property
    exact ⟨restrictEnumeration step enumeration⟩⟩

theorem restrict_identity (A : D ⥤ Type v) (point : D) (predicate : Predicate A point) :
    restrict A (𝟙 point) predicate = predicate := by
  apply Predicate.ext
  intro argument
  change predicate.holds ⟨⟨argument.1.1, 𝟙 point ≫ argument.1.2⟩, argument.2⟩ ↔ _
  rw [Category.id_comp]
  rcases argument with ⟨⟨_, _⟩, _⟩
  exact Iff.rfl

theorem restrict_comp (A : D ⥤ Type v) {first middle last : D}
    (earlier : first ⟶ middle) (later : middle ⟶ last) (predicate : Predicate A first) :
    restrict A (earlier ≫ later) predicate = restrict A later (restrict A earlier predicate) := by
  apply Predicate.ext
  intro argument
  change predicate.holds ⟨⟨argument.1.1, (earlier ≫ later) ≫ argument.1.2⟩, argument.2⟩ ↔
    predicate.holds ⟨⟨argument.1.1, earlier ≫ (later ≫ argument.1.2)⟩, argument.2⟩
  rw [Category.assoc]

theorem restrictPower_identity (A : D ⥤ Type v) (point : D) (predicate : Power A point) :
    restrictPower A (𝟙 point) predicate = predicate :=
  Subtype.ext (restrict_identity A point predicate.val)

theorem restrictPower_comp (A : D ⥤ Type v) {first middle last : D}
    (earlier : first ⟶ middle) (later : middle ⟶ last) (predicate : Power A first) :
    restrictPower A (earlier ≫ later) predicate =
      restrictPower A later (restrictPower A earlier predicate) :=
  Subtype.ext (restrict_comp A earlier later predicate.val)

/-- The output size includes the small carrier-code universe even when the
argument universe is smaller. No host universe is identified with another. -/
def family (A : D ⥤ Type v) : D ⥤ Type (max u v) where
  obj point := Power A point
  map step := TypeCat.ofHom (restrictPower A step)
  map_id point := by
    apply ConcreteCategory.hom_ext
    exact restrictPower_identity A point
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    exact restrictPower_comp A earlier later

def current (A : D ⥤ Type v) (point : D) (argument : A.obj point) : Arguments A point :=
  ⟨⟨point, 𝟙 point⟩, argument⟩

/-- The actual truth subtype enumerates every predicate on small arguments. -/
def smallEnumeration {A : D ⥤ Type u} {point : D} (predicate : Predicate A point) :
    Enumeration predicate where
  Carrier future := {argument : A.obj future.1 // predicate.holds ⟨future, argument⟩}
  value _ code := code.val
  covered _ _ := ⟨fun available => ⟨⟨_, available⟩, rfl⟩,
    fun ⟨code, same⟩ => same ▸ code.property⟩

def toFull {A : D ⥤ Type u} {point : D} (predicate : Power A point) :
    FuturePowerFamilies.Predicate A point where
  holds := predicate.val.holds
  closed := predicate.val.closed

def ofFull {A : D ⥤ Type u} {point : D} (predicate : FuturePowerFamilies.Predicate A point) :
    Power A point :=
  ⟨⟨predicate.holds, predicate.closed⟩, ⟨smallEnumeration ⟨predicate.holds, predicate.closed⟩⟩⟩

theorem toFull_ofFull {A : D ⥤ Type u} {point : D}
    (predicate : FuturePowerFamilies.Predicate A point) : toFull (ofFull predicate) = predicate := by
  cases predicate
  rfl

theorem ofFull_toFull {A : D ⥤ Type u} {point : D}
    (predicate : Power A point) : ofFull (toFull predicate) = predicate := by
  apply Subtype.ext
  apply Predicate.ext
  intro argument
  exact Iff.rfl

/-- Small-covered and full future powers agree on every originally small
family, by constructed inverses rather than a chosen enumeration. -/
def smallEquiv (A : D ⥤ Type u) (point : D) : Power A point ≃ FuturePowerFamilies.Predicate A point where
  toFun := toFull
  invFun := ofFull
  left_inv := ofFull_toFull
  right_inv := toFull_ofFull

theorem smallEquiv_restrict (A : D ⥤ Type u) {first second : D}
    (step : first ⟶ second) (predicate : Power A first) :
    smallEquiv A second (restrictPower A step predicate) =
      FuturePowerFamilies.restrict A step (smallEquiv A first predicate) := rfl

end Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerFamilies
