import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualAuthoredGeneratedFamilies
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualFamilyEnlargement

/-!
# Constructed enclosures of authored generated families

Every recursive code retains its original-small native family and actual
material dictionaries, even over wider parameter presheaves. The collected
carrier is constructed from those graphs at the explicit code bound
`max (u+1) (v+1)`. Its members are exactly the enlarged decoded carriers.

Substitution compares the actual image of the source grammar with the
target grammar. Further cumulative enlargement commutes with collecting
these carriers. The complete native sections are decoded at every enlarged
bound. Neither present carrier equality nor membership in the enclosure
recovers a formation recipe.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualAuthoredGeneratedEnclosure

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover
open ContextualAuthoredMaterialFamilies ContextualAuthoredGeneratedFamilies

universe u v w
variable {D : Type u} [Category.{u} D]
variable (worlds : ArgumentCoding D) (arrows : (first second : D) → ArgumentCoding (first ⟶ second))
variable (seeds : (base : D ⥤ Type (max u v)) → Type (max (u + 1) v))
variable (seedModel : (base : D ⥤ Type (max u v)) → seeds base → Family base)
variable {base : D ⥤ Type (max u v)}

def enclosureGraph (point : base.Elements) : AccessiblePointedGraph.{max (u+1) (v+1)} :=
  AccessiblePointedGraph.sup fun code : Code worlds arrows seeds seedModel base =>
    (code.decode.models point).graph.enlarge.{u,max (u+1) (v+1)}

def enclosure (point : base.Elements) : HSet.{max (u+1) (v+1)} :=
  HSet.mk (enclosureGraph worlds arrows seeds seedModel point)

def reading (code : Code worlds arrows seeds seedModel base) (point : base.Elements) :
    HSet.{max (u+1) (v+1)} := HSet.enlarge.{u,max (u+1) (v+1)} (code.decode.models point).carrier

theorem mem_enclosure_iff (point : base.Elements) (value : HSet.{max (u+1) (v+1)}) :
    value ∈ enclosure worlds arrows seeds seedModel point ↔
      ∃ code : Code worlds arrows seeds seedModel base, reading worlds arrows seeds seedModel code point = value := by
  change value ∈ HSet.range _ ↔ _
  rw [HSet.mem_range]
  rfl

theorem code_enclosed (code : Code worlds arrows seeds seedModel base) (point : base.Elements) :
    reading worlds arrows seeds seedModel code point ∈ enclosure worlds arrows seeds seedModel point :=
  (mem_enclosure_iff worlds arrows seeds seedModel point _).mpr ⟨code, rfl⟩

theorem reading_eq_iff (first second : Code worlds arrows seeds seedModel base) (point : base.Elements) :
    reading worlds arrows seeds seedModel first point = reading worlds arrows seeds seedModel second point ↔
      (first.decode.models point).carrier = (second.decode.models point).carrier := by
  constructor
  · intro same
    exact HSet.enlarge_injective.{u,max (u+1) (v+1)} same
  · intro same
    exact congrArg HSet.enlarge.{u,max (u+1) (v+1)} same

theorem predicate_descends_iff (point : base.Elements)
    (predicate : Code worlds arrows seeds seedModel base → Prop) :
    (∃ observe : HSet.{max (u+1) (v+1)} → Prop,
      ∀ code, observe (reading worlds arrows seeds seedModel code point) ↔ predicate code) ↔
    (∀ first second : Code worlds arrows seeds seedModel base,
      (first.decode.models point).carrier = (second.decode.models point).carrier →
      (predicate first ↔ predicate second)) := by
  constructor
  · rintro ⟨observe, correct⟩ first second same
    have readings := (reading_eq_iff worlds arrows seeds seedModel first second point).mpr same
    exact (correct first).symm.trans ((congrArg observe readings).to_iff.trans (correct second))
  · intro respects
    refine ⟨fun value => ∃ code, reading worlds arrows seeds seedModel code point = value ∧ predicate code, ?_⟩
    intro code
    constructor
    · rintro ⟨original, same, holds⟩
      exact (respects original code
        ((reading_eq_iff worlds arrows seeds seedModel original code point).mp same)).mp holds
    · intro holds
      exact ⟨code, rfl, holds⟩

def fibreDecoder (code : Code worlds arrows seeds seedModel base) (point : base.Elements) :
    {value : HSet.{max (u+1) (v+1)} // value ∈ reading worlds arrows seeds seedModel code point} ≃
      code.decode.native.obj point :=
  (HSet.enlargedMembersEquiv.{u,max (u+1) (v+1)} (code.decode.models point).carrier).symm.trans
    (code.decode.models point).decode

theorem fibreDecoder_encode (code : Code worlds arrows seeds seedModel base) (point : base.Elements)
    (term : code.decode.native.obj point) :
    fibreDecoder worlds arrows seeds seedModel code point
      ((fibreDecoder worlds arrows seeds seedModel code point).symm term) = term :=
  (fibreDecoder worlds arrows seeds seedModel code point).apply_symm_apply term

theorem fibreDecoder_value (code : Code worlds arrows seeds seedModel base) (point : base.Elements)
    (term : code.decode.native.obj point) :
    ((fibreDecoder worlds arrows seeds seedModel code point).symm term).val =
      HSet.enlarge.{u,max (u+1) (v+1)} ((code.decode.models point).value term) := rfl

/-- This comparison retains the full decoded family, not only the existence
of an inhabitant of its current fibre. -/
def memberSections (code : Code worlds arrows seeds seedModel base) :
    code.decode.native.sections ≃
      (ContextualFamilyEnlargement.members.{u,max (u+1) (v+1)} code.decode.native code.decode.models).sections :=
  ContextualFamilyEnlargement.sectionEquiv code.decode.native code.decode.models

theorem memberSections_value (code : Code worlds arrows seeds seedModel base)
    (term : code.decode.native.sections) (point : base.Elements) :
    ((memberSections worlds arrows seeds seedModel code term).val point).val =
      HSet.enlarge.{u,max (u+1) (v+1)} ((code.decode.models point).value (term.val point)) := rfl

theorem memberSections_injective (code : Code worlds arrows seeds seedModel base) :
    Function.Injective (memberSections worlds arrows seeds seedModel code) :=
  (memberSections worlds arrows seeds seedModel code).injective

theorem all_formers_enclosed (domain : Code worlds arrows seeds seedModel base)
    (body : Code worlds arrows seeds seedModel domain.decode.extension)
    (left right : domain.decode.native.sections) (point : base.Elements) :
    reading worlds arrows seeds seedModel (domain.pi body) point ∈ enclosure worlds arrows seeds seedModel point ∧
      reading worlds arrows seeds seedModel (domain.sigma body) point ∈ enclosure worlds arrows seeds seedModel point ∧
      reading worlds arrows seeds seedModel (domain.identity left right) point ∈ enclosure worlds arrows seeds seedModel point ∧
      reading worlds arrows seeds seedModel (domain.w body) point ∈ enclosure worlds arrows seeds seedModel point :=
  ⟨code_enclosed worlds arrows seeds seedModel (domain.pi body) point,
    code_enclosed worlds arrows seeds seedModel (domain.sigma body) point,
    code_enclosed worlds arrows seeds seedModel (domain.identity left right) point,
    code_enclosed worlds arrows seeds seedModel (domain.w body) point⟩

section Substitution

variable {other middle : D ⥤ Type (max u v)}
variable (change : NaturalHom other base)

def substitutedEnclosure (point : other.Elements) : HSet.{max (u+1) (v+1)} :=
  HSet.range fun code : Code worlds arrows seeds seedModel base =>
    ((code.reindex change).decode.models point).graph.enlarge.{u,max (u+1) (v+1)}

theorem substitutedEnclosure_eq (point : other.Elements) :
    substitutedEnclosure worlds arrows seeds seedModel change point =
      enclosure worlds arrows seeds seedModel ((ContextualSmallFamilyUniverse.elementMap change).obj point) := rfl

theorem substitutedEnclosure_subset (point : other.Elements) :
    substitutedEnclosure worlds arrows seeds seedModel change point ⊆
      enclosure worlds arrows seeds seedModel point := by
  intro value member
  obtain ⟨code, same⟩ := HSet.mem_range.mp member
  exact (mem_enclosure_iff worlds arrows seeds seedModel point value).mpr ⟨code.reindex change, same⟩

theorem reindex_reading (code : Code worlds arrows seeds seedModel base) (point : other.Elements) :
    reading worlds arrows seeds seedModel (code.reindex change) point =
      reading worlds arrows seeds seedModel code ((ContextualSmallFamilyUniverse.elementMap change).obj point) := rfl

theorem reindex_reading_comp (earlier : NaturalHom middle other)
    (code : Code worlds arrows seeds seedModel base) (point : middle.Elements) :
    reading worlds arrows seeds seedModel ((code.reindex change).reindex earlier) point =
      reading worlds arrows seeds seedModel (code.reindex (earlier.comp change)) point := rfl

theorem enclosure_substitution_comp (earlier : NaturalHom middle other) (point : middle.Elements) :
    substitutedEnclosure worlds arrows seeds seedModel (earlier.comp change) point =
      substitutedEnclosure worlds arrows seeds seedModel change
        ((ContextualSmallFamilyUniverse.elementMap earlier).obj point) := rfl

/-- Pullback of a complete generated section keeps every member value at
the changed parameter, including all future arguments of a product. -/
def pulledSection (code : Code worlds arrows seeds seedModel base) (term : code.decode.native.sections) :
    (code.reindex change).decode.native.sections :=
  ⟨fun point => term.val ((ContextualSmallFamilyUniverse.elementMap change).obj point),
    fun step => term.property ((ContextualSmallFamilyUniverse.elementMap change).map step)⟩

theorem memberSections_substitution (code : Code worlds arrows seeds seedModel base)
    (term : code.decode.native.sections) (point : other.Elements) :
    (memberSections worlds arrows seeds seedModel (code.reindex change)
      (pulledSection worlds arrows seeds seedModel change code term)).val point =
      (memberSections worlds arrows seeds seedModel code term).val
        ((ContextualSmallFamilyUniverse.elementMap change).obj point) := rfl

end Substitution

section Cumulativity

/-- The separately built range uses the original code index and embeds
each original graph directly at the larger mixed bound. -/
def enlargedEnclosure (point : base.Elements) : HSet.{max (max (u+1) (v+1)) w} :=
  HSet.range fun code : ULift.{w} (Code worlds arrows seeds seedModel base) =>
    (code.down.decode.models point).graph.enlarge.{u,max (max (u+1) (v+1)) w}

theorem enlargedEnclosure_eq (point : base.Elements) :
    enlargedEnclosure.{u,v,w} worlds arrows seeds seedModel point =
      HSet.enlarge.{max (u+1) (v+1),w} (enclosure worlds arrows seeds seedModel point) := by
  apply HSet.ext
  intro value
  rw [enlargedEnclosure, HSet.mem_range, HSet.mem_enlarge_iff]
  constructor
  · rintro ⟨code, same⟩
    refine ⟨reading worlds arrows seeds seedModel code.down point,
      code_enclosed worlds arrows seeds seedModel code.down point, ?_⟩
    exact (HSet.enlarge_comp.{u,max (u+1) (v+1),w} (code.down.decode.models point).carrier).trans same
  · rintro ⟨old, belongs, same⟩
    obtain ⟨code, represented⟩ := (mem_enclosure_iff worlds arrows seeds seedModel point old).mp belongs
    refine ⟨ULift.up code, ?_⟩
    exact (HSet.enlarge_comp.{u,max (u+1) (v+1),w} (code.decode.models point).carrier).symm.trans
      ((congrArg HSet.enlarge.{max (u+1) (v+1),w} represented).trans same)

theorem enlarged_reading_enclosed (code : Code worlds arrows seeds seedModel base) (point : base.Elements) :
    HSet.enlarge.{u,max (max (u+1) (v+1)) w} (code.decode.models point).carrier ∈
      enlargedEnclosure.{u,v,w} worlds arrows seeds seedModel point :=
  HSet.mem_range.mpr ⟨ULift.up code, rfl⟩

theorem enlargement_substitution_square {other : D ⥤ Type (max u v)}
    (change : NaturalHom other base) (point : other.Elements) :
    HSet.enlarge.{max (u+1) (v+1),w} (substitutedEnclosure worlds arrows seeds seedModel change point) =
      enlargedEnclosure.{u,v,w} worlds arrows seeds seedModel
        ((ContextualSmallFamilyUniverse.elementMap change).obj point) :=
  (enlargedEnclosure_eq worlds arrows seeds seedModel _).symm

theorem enlarged_decoder (code : Code worlds arrows seeds seedModel base) (point : base.Elements)
    (member : {value : HSet.{u} // value ∈ (code.decode.models point).carrier}) :
    (ContextualFamilyEnlargement.model.{u,max (max (u+1) (v+1)) w} (code.decode.models point)).decode
      (HSet.enlargedMembersEquiv.{u,max (max (u+1) (v+1)) w} (code.decode.models point).carrier member) =
        ULift.up ((code.decode.models point).decode member) :=
  ContextualFamilyEnlargement.model_decode_enlarge _ _

theorem enlarged_enclosure_has_missing_set (point : base.Elements) :
    HSet.russell (enlargedEnclosure.{u,v,w} worlds arrows seeds seedModel point) ∉
      enlargedEnclosure.{u,v,w} worlds arrows seeds seedModel point := HSet.russell_notMem _

end Cumulativity

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualAuthoredGeneratedEnclosure
