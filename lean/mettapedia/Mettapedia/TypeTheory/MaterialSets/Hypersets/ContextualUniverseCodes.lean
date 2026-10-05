import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGeneratedUniverse

/-!
# Formation-preserving codes under base substitution

Raw codes retain the entire contextual material family and its actual
formation derivation. The code equations below identify only the explicit
identity and composition laws of base substitution, together with their
substitution congruence. Their semantic soundness is proved before the
quotient code action or its family interpretation is constructed.

This is a functor on labelled base-presheaf substitutions. It is distinct
from a coslice-local classifier or an internally small universe. The
pointwise material enclosure remains a readout: equality of present carrier
sets need not permit transport of a generated family.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualUniverseCodes

open CategoryTheory
open ContextualGeneratedUniverse
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent

universe u
variable {C : Type u} [Category.{u} C]

namespace MaterialFamily

theorem ext {context : LabelledContext C} {first second : MaterialFamily context}
    (families : first.family = second.family) (models : HEq first.model second.model) :
    first = second := by
  cases first
  cases second
  cases families
  cases eq_of_heq models
  rfl

theorem reindex_identity {context : LabelledContext C} (family : MaterialFamily context) :
    family.reindex (identity context.base) = family := by
  exact ext (PowerClassPresheafBaseChange.reindex_identity family.family) (heq_of_eq rfl)

theorem reindex_comp {context middle other : LabelledContext C}
    (family : MaterialFamily context)
    (earlier : NatTrans other.base middle.base) (later : NatTrans middle.base context.base) :
    (family.reindex later).reindex earlier = family.reindex (compose earlier later) := by
  exact ext (PowerClassPresheafBaseChange.reindex_comp earlier later family.family) (heq_of_eq rfl)

end MaterialFamily

variable (seeds : (context : LabelledContext C) → Type (u + 1))
variable (seedModel : (context : LabelledContext C) → seeds context → MaterialFamily context)
variable (arrows : (first second : Cᵒᵖ) → ArgumentCoding (first ⟶ second))

abbrev RawCode (context : LabelledContext C) :=
  ContextualGeneratedUniverse.Code seeds seedModel arrows context

def rawReindex {context other : LabelledContext C} (change : NatTrans other.base context.base)
    (code : RawCode seeds seedModel arrows context) : RawCode seeds seedModel arrows other :=
  ⟨code.1.reindex change, Generation.reindex code.2 change⟩

/-- Only substitution coherence is declared as a code equation. In particular,
equal present carriers do not identify codes or their formation derivations. -/
inductive Equation : {context : LabelledContext C} →
    RawCode seeds seedModel arrows context → RawCode seeds seedModel arrows context → Prop where
  | refl {context} (code : RawCode seeds seedModel arrows context) : Equation code code
  | symm {context} {first second : RawCode seeds seedModel arrows context}
      (related : Equation first second) : Equation second first
  | trans {context} {first middle last : RawCode seeds seedModel arrows context}
      (earlier : Equation first middle) (later : Equation middle last) : Equation first last
  | reindex_identity {context} (code : RawCode seeds seedModel arrows context) :
      Equation (rawReindex seeds seedModel arrows (identity context.base) code) code
  | reindex_comp {context middle other : LabelledContext C} (code : RawCode seeds seedModel arrows context)
      (earlier : NatTrans other.base middle.base) (later : NatTrans middle.base context.base) :
      Equation (rawReindex seeds seedModel arrows earlier (rawReindex seeds seedModel arrows later code))
        (rawReindex seeds seedModel arrows (compose earlier later) code)
  | reindex_cong {context other : LabelledContext C} {first second : RawCode seeds seedModel arrows context}
      (change : NatTrans other.base context.base) (related : Equation first second) :
      Equation (rawReindex seeds seedModel arrows change first) (rawReindex seeds seedModel arrows change second)

namespace Equation

theorem sound {context : LabelledContext C} {first second : RawCode seeds seedModel arrows context}
    (related : Equation seeds seedModel arrows first second) : first.1 = second.1 := by
  induction related with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ first second => exact first.trans second
  | reindex_identity code => exact MaterialFamily.reindex_identity code.1
  | reindex_comp code earlier later => exact MaterialFamily.reindex_comp code.1 earlier later
  | reindex_cong change _ ih => exact congrArg (fun family => family.reindex change) ih

end Equation

def codeSetoid (context : LabelledContext C) : Setoid (RawCode seeds seedModel arrows context) where
  r := Equation seeds seedModel arrows
  iseqv := ⟨Equation.refl, Equation.symm, Equation.trans⟩

def Code (context : LabelledContext C) : Type (u + 1) :=
  Quotient (codeSetoid seeds seedModel arrows context)

def ofRaw {context : LabelledContext C} (raw : RawCode seeds seedModel arrows context) :
    Code seeds seedModel arrows context :=
  Quotient.mk (codeSetoid seeds seedModel arrows context) raw

/-- The actual family and every material dictionary descend by the proved
soundness of substitution equations. No representative is selected. -/
def decodeFamily {context : LabelledContext C} : Code seeds seedModel arrows context → MaterialFamily context :=
  Quotient.lift Sigma.fst (fun _ _ related => Equation.sound seeds seedModel arrows related)

theorem decodeFamily_ofRaw {context : LabelledContext C} (raw : RawCode seeds seedModel arrows context) :
    decodeFamily seeds seedModel arrows (ofRaw seeds seedModel arrows raw) = raw.1 := rfl

theorem ofRaw_eq_iff {context : LabelledContext C}
    (first second : RawCode seeds seedModel arrows context) :
    ofRaw seeds seedModel arrows first = ofRaw seeds seedModel arrows second ↔
      Equation seeds seedModel arrows first second :=
  ⟨fun same => Quotient.exact same,
    fun related => @Quotient.sound _ (codeSetoid seeds seedModel arrows context)
      first second related⟩

theorem formed {context : LabelledContext C} (code : Code seeds seedModel arrows context) :
    Nonempty (Generation seeds seedModel arrows (decodeFamily seeds seedModel arrows code)) := by
  induction code using Quotient.inductionOn with
  | _ raw => exact ⟨raw.2⟩

def reindex {context other : LabelledContext C} (change : NatTrans other.base context.base) :
    Code seeds seedModel arrows context → Code seeds seedModel arrows other :=
  Quotient.map (rawReindex seeds seedModel arrows change)
    (fun _ _ related => Equation.reindex_cong change related)

theorem reindex_ofRaw {context other : LabelledContext C} (change : NatTrans other.base context.base)
    (raw : RawCode seeds seedModel arrows context) :
    reindex seeds seedModel arrows change (ofRaw seeds seedModel arrows raw) =
      ofRaw seeds seedModel arrows (rawReindex seeds seedModel arrows change raw) := rfl

theorem reindex_identity {context : LabelledContext C} (code : Code seeds seedModel arrows context) :
    reindex seeds seedModel arrows (identity context.base) code = code := by
  induction code using Quotient.inductionOn with
  | _ raw => exact Quotient.sound (Equation.reindex_identity raw)

theorem reindex_comp {context middle other : LabelledContext C}
    (earlier : NatTrans other.base middle.base) (later : NatTrans middle.base context.base)
    (code : Code seeds seedModel arrows context) :
    reindex seeds seedModel arrows earlier (reindex seeds seedModel arrows later code) =
      reindex seeds seedModel arrows (compose earlier later) code := by
  induction code using Quotient.inductionOn with
  | _ raw => exact Quotient.sound (Equation.reindex_comp raw earlier later)

theorem decodeFamily_reindex {context other : LabelledContext C}
    (change : NatTrans other.base context.base) (code : Code seeds seedModel arrows context) :
    decodeFamily seeds seedModel arrows (reindex seeds seedModel arrows change code) =
      (decodeFamily seeds seedModel arrows code).reindex change := by
  induction code using Quotient.inductionOn with
  | _ raw => rfl

/-- A context arrow is an actual base-presheaf substitution. This direction
makes the code action covariant without changing its underlying pullback. -/
instance substitutionCategory : Category.{u} (LabelledContext C) where
  Hom first second := NatTrans second.base first.base
  id context := identity context.base
  comp first second := compose second first
  id_comp _ := by apply NatTrans.ext; funext point; apply ConcreteCategory.hom_ext; intro value; rfl
  comp_id _ := by apply NatTrans.ext; funext point; apply ConcreteCategory.hom_ext; intro value; rfl
  assoc _ _ _ := by apply NatTrans.ext; funext point; apply ConcreteCategory.hom_ext; intro value; rfl

/-- Genuine code substitution pulls back the complete family and formation
data. It does not transport a code chosen from a carrier-only enclosure. -/
def baseSubstitutionCodeFunctor : LabelledContext C ⥤ Type (u + 1) where
  obj := Code seeds seedModel arrows
  map change := TypeCat.ofHom (reindex seeds seedModel arrows change)
  map_id _ := by apply ConcreteCategory.hom_ext; exact reindex_identity seeds seedModel arrows
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro code
    exact (reindex_comp seeds seedModel arrows second first code).symm

/-- The interpretation of codes lands in the actual family-and-dictionary
substitution functor. It retains every restriction map. -/
def baseSubstitutionFamilyFunctor : LabelledContext C ⥤ Type (u + 1) where
  obj := MaterialFamily
  map change := TypeCat.ofHom (fun family => family.reindex change)
  map_id _ := by apply ConcreteCategory.hom_ext; exact MaterialFamily.reindex_identity
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro family
    exact (MaterialFamily.reindex_comp family second first).symm

def interpretation : NatTrans (baseSubstitutionCodeFunctor seeds seedModel arrows)
    (baseSubstitutionFamilyFunctor (C := C)) where
  app _ := TypeCat.ofHom (decodeFamily seeds seedModel arrows)
  naturality _ _ change := by
    apply ConcreteCategory.hom_ext
    exact decodeFamily_reindex seeds seedModel arrows change

theorem interpreted_code_enclosed {context : LabelledContext C}
    (code : Code seeds seedModel arrows context) (point : context.base.Elements) :
    HSet.lift ((decodeFamily seeds seedModel arrows code).model point).carrier ∈
      ContextualGeneratedUniverse.enclosure seeds seedModel arrows context point := by
  induction code using Quotient.inductionOn with
  | _ raw => exact generated_mem_enclosure seeds seedModel arrows raw.2 point

theorem reindex_carrier {context other : LabelledContext C}
    (change : NatTrans other.base context.base) (code : Code seeds seedModel arrows context)
    (point : other.base.Elements) :
    ((decodeFamily seeds seedModel arrows (reindex seeds seedModel arrows change code)).model point).carrier =
      ((decodeFamily seeds seedModel arrows code).model
        ((PowerClassPresheafProducts.elementMap change).obj point)).carrier := by
  induction code using Quotient.inductionOn with
  | _ raw => rfl

def reindexMember {context other : LabelledContext C}
    (change : NatTrans other.base context.base) (code : Code seeds seedModel arrows context)
    (point : other.base.Elements)
    (member : {value : HSet.{u} // value ∈ ((decodeFamily seeds seedModel arrows code).model
      ((PowerClassPresheafProducts.elementMap change).obj point)).carrier}) :
    {value : HSet.{u} // value ∈
      ((decodeFamily seeds seedModel arrows (reindex seeds seedModel arrows change code)).model point).carrier} :=
  ⟨member.1, (reindex_carrier seeds seedModel arrows change code point).symm ▸ member.2⟩

theorem reindexMember_value {context other : LabelledContext C}
    (change : NatTrans other.base context.base) (code : Code seeds seedModel arrows context)
    (point : other.base.Elements)
    (member : {value : HSet.{u} // value ∈ ((decodeFamily seeds seedModel arrows code).model
      ((PowerClassPresheafProducts.elementMap change).obj point)).carrier}) :
    (reindexMember seeds seedModel arrows change code point member).1 = member.1 := rfl

theorem reindexMember_decode {context other : LabelledContext C}
    (change : NatTrans other.base context.base) (code : Code seeds seedModel arrows context)
    (point : other.base.Elements)
    (member : {value : HSet.{u} // value ∈ ((decodeFamily seeds seedModel arrows code).model
      ((PowerClassPresheafProducts.elementMap change).obj point)).carrier}) :
    HEq
      (((decodeFamily seeds seedModel arrows (reindex seeds seedModel arrows change code)).model point).decode
        (reindexMember seeds seedModel arrows change code point member))
      (((decodeFamily seeds seedModel arrows code).model
        ((PowerClassPresheafProducts.elementMap change).obj point)).decode member) := by
  induction code using Quotient.inductionOn with
  | _ raw => rfl

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualUniverseCodes
