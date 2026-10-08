import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualRealizedGraphs
import Mathlib.Data.Quot

/-!
# Constructive material readouts of contextual graph presentations

The material readout identifies exactly the existence of full future
matching data. Its context maps are constructed from the actual diagram
action. Current-picture bisimilarity is deliberately not used as the
kernel: agreement of current pictures can fail to match later children.

The quotient carrier is one universe above the small context category,
node fibres and matching realizers. Quotient equality forgets the particular
matching strategy; literal graph and occurrence data remain in the source.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles.ProfileGraphReadout

open CategoryTheory
open Mettapedia.TypeTheory.ContextualWitnessCover
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ContextualGraphDiagrams ContextualRealizedGraphs

universe u v
variable (D : Type u) [Category.{u} D]

def matchingSetoid (point : D) : Setoid (Value D point) where
  r first second := Nonempty (Equal first second)
  iseqv := {
    refl := fun value => ⟨Equal.refl value⟩
    symm := fun ⟨proof⟩ => ⟨proof.symm⟩
    trans := fun ⟨earlier⟩ ⟨later⟩ => ⟨earlier.trans later⟩ }

abbrev Material (point : D) : Type (u+1) := Quotient (matchingSetoid D point)

def readout {point : D} (value : Value D point) : Material D point :=
  Quotient.mk (matchingSetoid D point) value

theorem readout_kernel {point : D} (first second : Value D point) :
    readout D first = readout D second ↔ Nonempty (Equal first second) :=
  Quotient.eq_iff_equiv

def transport {first second : D} (arrival : first ⟶ second) :
    Material D first → Material D second :=
  Quotient.map (move D arrival) (fun {_ _} ⟨proof⟩ => ⟨Equal.restrict arrival proof⟩)

theorem transport_readout {first second : D} (arrival : first ⟶ second)
    (value : Value D first) :
    transport D arrival (readout D value) = readout D (move D arrival value) := rfl

theorem transport_identity (point : D) (value : Material D point) :
    transport D (𝟙 point) value = value := by
  induction value using Quotient.inductionOn with
  | h value => exact congrArg (readout D) (move_identity D point value)

theorem transport_composition {first middle last : D} (earlier : first ⟶ middle)
    (later : middle ⟶ last) (value : Material D first) :
    transport D (earlier ≫ later) value =
      transport D later (transport D earlier value) := by
  induction value using Quotient.inductionOn with
  | h value => exact congrArg (readout D) (move_composition D earlier later value)

def materialValues : D ⥤ Type (u+1) where
  obj := Material D
  map arrival := TypeCat.ofHom (transport D arrival)
  map_id point := by
    apply ConcreteCategory.hom_ext
    exact transport_identity D point
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    exact transport_composition D earlier later

def reading : NaturalHom (values D) (materialValues D) where
  app _ := readout D
  naturality _ _ := rfl

theorem member_invariant {point : D} {child otherChild parent otherParent : Value D point}
    (sameChild : Nonempty (Equal child otherChild))
    (sameParent : Nonempty (Equal parent otherParent)) :
    Nonempty (Member child parent) ↔ Nonempty (Member otherChild otherParent) := by
  obtain ⟨left⟩ := sameChild
  obtain ⟨right⟩ := sameParent
  exact ⟨fun ⟨proof⟩ => ⟨Member.transport left right proof⟩,
    fun ⟨proof⟩ => ⟨Member.transport left.symm right.symm proof⟩⟩

def member {point : D} (child parent : Material D point) : Prop :=
  Quotient.liftOn₂ child parent (fun child parent => Nonempty (Member child parent))
    (fun _ _ _ _ sameChild sameParent => propext (member_invariant D sameChild sameParent))

theorem member_readout {point : D} (child parent : Value D point) :
    member D (readout D child) (readout D parent) ↔ Nonempty (Member child parent) := Iff.rfl

theorem member_transport {first second : D} (arrival : first ⟶ second)
    {child parent : Material D first} (available : member D child parent) :
    member D (transport D arrival child) (transport D arrival parent) := by
  induction child using Quotient.inductionOn with
  | h child =>
    induction parent using Quotient.inductionOn with
    | h parent =>
      obtain ⟨proof⟩ := available
      exact ⟨Member.restrict arrival proof⟩

section Descent

variable {D} {point : D}

/-- Predicate descent uses precisely invariance under the material kernel. -/
theorem predicate_descends_iff (predicate : Value D point → Prop) :
    (∃ descended : Material D point → Prop,
      ∀ value, descended (readout D value) ↔ predicate value) ↔
    (∀ first second, Nonempty (Equal first second) →
      (predicate first ↔ predicate second)) := by
  constructor
  · rintro ⟨descended, computes⟩ first second matching
    exact (computes first).symm.trans
      (((readout_kernel D first second).mpr matching) ▸ computes second)
  · intro compatible
    exact ⟨Quotient.lift predicate (fun first second matching =>
      propext (compatible first second matching)), fun _ => Iff.rfl⟩

/-- A strict family descends exactly when its fibre type is invariant.
This criterion is stronger than an unstructured equivalence of fibres. -/
theorem family_descends_iff (family : Value D point → Type v) :
    (∃ descended : Material D point → Type v,
      ∀ value, descended (readout D value) = family value) ↔
    (∀ first second, Nonempty (Equal first second) → family first = family second) := by
  constructor
  · rintro ⟨descended, computes⟩ first second matching
    exact (computes first).symm.trans
      ((congrArg descended ((readout_kernel D first second).mpr matching)).trans (computes second))
  · intro compatible
    exact ⟨Quotient.lift family compatible, fun _ => rfl⟩

def descendFamily (family : Value D point → Type v)
    (compatible : ∀ first second, Nonempty (Equal first second) → family first = family second) :
    Material D point → Type v := Quotient.lift family compatible

theorem descendFamily_readout (family : Value D point → Type v)
    (compatible : ∀ first second, Nonempty (Equal first second) → family first = family second)
    (value : Value D point) : descendFamily family compatible (readout D value) = family value := rfl

/-- A section of an actual target family descends precisely when it has
compatible values, including their dependent types. -/
theorem term_descends_iff (family : Material D point → Type v)
    (term : ∀ value : Value D point, family (readout D value)) :
    (∃ descended : ∀ material, family material,
      ∀ value, descended (readout D value) = term value) ↔
    (∀ first second, Nonempty (Equal first second) → HEq (term first) (term second)) := by
  constructor
  · rintro ⟨descended, computes⟩ first second matching
    have same := (readout_kernel D first second).mpr matching
    have terms : HEq (descended (readout D first)) (descended (readout D second)) := by
      rw [same]
    simpa only [computes] using terms
  · intro compatible
    exact ⟨fun material => Quotient.hrecOn material term compatible, fun _ => rfl⟩

def descendTerm (family : Material D point → Type v)
    (term : ∀ value : Value D point, family (readout D value))
    (compatible : ∀ first second, Nonempty (Equal first second) → HEq (term first) (term second)) :
    ∀ material, family material := fun material => Quotient.hrecOn material term compatible

theorem descendTerm_readout (family : Material D point → Type v)
    (term : ∀ value : Value D point, family (readout D value))
    (compatible : ∀ first second, Nonempty (Equal first second) → HEq (term first) (term second))
    (value : Value D point) : descendTerm family term compatible (readout D value) = term value := rfl

end Descent

section NaturalDescent

variable {D} {target : D ⥤ Type v}

def descendNatural (operation : NaturalHom (values D) target)
    (compatible : ∀ point first second, Nonempty (Equal first second) →
      operation.app point first = operation.app point second) :
    NaturalHom (materialValues D) target where
  app point := Quotient.lift (operation.app point) (compatible point)
  naturality arrival material := by
    induction material using Quotient.inductionOn with
    | h value => exact operation.naturality arrival value

theorem descendNatural_reading (operation : NaturalHom (values D) target)
    (compatible : ∀ point first second, Nonempty (Equal first second) →
      operation.app point first = operation.app point second) :
    (reading D).comp (descendNatural operation compatible) = operation := by
  apply NaturalHom.ext
  intro point value
  rfl

/-- The context action creates no extra descent obligation: exact kernel
invariance and the original naturality law construct the target action. -/
theorem natural_descends_iff (operation : NaturalHom (values D) target) :
    (∃ descended : NaturalHom (materialValues D) target,
      (reading D).comp descended = operation) ↔
    (∀ point first second, Nonempty (Equal first second) →
      operation.app point first = operation.app point second) := by
  constructor
  · rintro ⟨descended, computes⟩ point first second matching
    rw [← computes]
    exact congrArg (descended.app point) ((readout_kernel D first second).mpr matching)
  · intro compatible
    exact ⟨descendNatural operation compatible, descendNatural_reading operation compatible⟩

end NaturalDescent

end Mettapedia.SetTheory.Profiles.ProfileGraphReadout
