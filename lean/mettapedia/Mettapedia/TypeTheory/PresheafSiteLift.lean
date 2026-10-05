import Mettapedia.TypeTheory.DisplayedPresheafComprehension
import Mettapedia.GSLT.Topos.ConstructivePresheafDependentFunctions

/-!
# Successor lifting of sites and contextual families

Worlds, actual arrows, base values and displayed values are all raised to
one successor level. The category, functors and natural transformations use
explicit laws. Inverse element-context transports retain the complete base
value and its substitution arrow. Sections and context changes commute with
these transports; no inverse or closure capability is supplied.

This translates an original site and its families. It does not assert that
every family in the larger host universe is a translated lower family.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.PresheafSiteLift

open CategoryTheory
open Mettapedia.TypeTheory.DisplayedPresheafComprehension (totalSpace)

universe u v w a b c

/-- A genuine successor carrier of worlds. Its arrows are raised separately. -/
def Site (D : Type u) : Type (u + 1) := ULift.{u + 1, u} D

namespace Site

variable {D : Type u} [Category.{u} D]

instance category : Category.{u + 1} (Site D) where
  Hom first second := ULift.{u + 1, u} (first.down ⟶ second.down)
  id _ := ⟨𝟙 _⟩
  comp first later := ⟨first.down ≫ later.down⟩
  id_comp arrow := ULift.ext _ _ (Category.id_comp arrow.down)
  comp_id arrow := ULift.ext _ _ (Category.comp_id arrow.down)
  assoc first middle last := ULift.ext _ _ (Category.assoc first.down middle.down last.down)

/-- Both worlds and actual arrows are raised. -/
def upFunctor : D ⥤ Site D where
  obj point := ⟨point⟩
  map arrow := ⟨arrow⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def downFunctor : Site D ⥤ D where
  obj point := point.down
  map arrow := arrow.down
  map_id _ := rfl
  map_comp _ _ := rfl

end Site

/-- Explicit composition works across the different site universes. -/
def compose {D : Type u} [Category.{a} D] {E : Type v} [Category.{b} E]
    {F : Type w} [Category.{c} F] (first : D ⥤ E) (later : E ⥤ F) : D ⥤ F where
  obj point := later.obj (first.obj point)
  map arrow := later.map (first.map arrow)
  map_id point := by rw [first.map_id, later.map_id]
  map_comp firstStep laterStep := by rw [first.map_comp, later.map_comp]

def identity (D : Type u) [Category.{a} D] : D ⥤ D where
  obj point := point
  map arrow := arrow
  map_id _ := rfl
  map_comp _ _ := rfl

theorem site_up_down (D : Type u) [Category.{u} D] :
    compose (Site.upFunctor (D := D)) Site.downFunctor = identity D := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

theorem site_down_up (D : Type u) [Category.{u} D] :
    compose (Site.downFunctor (D := D)) Site.upFunctor = identity (Site D) := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

section Presheaves

variable {C : Type u} [Category.{u} C]

/-- The opposite transport raises the underlying contextual arrow too. -/
def upOp : Cᵒᵖ ⥤ (Site C)ᵒᵖ where
  obj point := Opposite.op (Site.upFunctor.obj point.unop)
  map arrow := (Site.upFunctor.map arrow.unop).op
  map_id _ := rfl
  map_comp _ _ := rfl

def downOp : (Site C)ᵒᵖ ⥤ Cᵒᵖ where
  obj point := Opposite.op (Site.downFunctor.obj point.unop)
  map arrow := (Site.downFunctor.map arrow.unop).op
  map_id _ := rfl
  map_comp _ _ := rfl

theorem op_up_down : compose (upOp (C := C)) downOp = identity Cᵒᵖ := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

theorem op_down_up : compose (downOp (C := C)) upOp = identity (Site C)ᵒᵖ := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

theorem downOp_obj_injective : Function.Injective (downOp (C := C)).obj := by
  intro first second same
  exact congrArg (upOp (C := C)).obj same

theorem downOp_map_injective {X Y : (Site C)ᵒᵖ} :
    Function.Injective (fun arrow : X ⟶ Y => downOp.map arrow) := by
  intro first second same
  exact congrArg (upOp (C := C)).map same

variable (P : Cᵒᵖ ⥤ Type u)

/-- The whole presheaf, including its restriction maps, lives on the raised site. -/
def base : (Site C)ᵒᵖ ⥤ Type (u + 1) where
  obj point := ULift.{u + 1, u} (P.obj (downOp.obj point))
  map arrow := TypeCat.ofHom fun value => ULift.up (P.map (downOp.map arrow) value.down)
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro value
    exact ULift.ext _ _ (P.map_id_apply (downOp.obj point) value.down)
  map_comp first later := by
    apply ConcreteCategory.hom_ext
    intro value
    exact ULift.ext _ _ (P.map_comp_apply (downOp.map first) (downOp.map later) value.down)

/-- Lower the world, the actual base value and the underlying context arrow. -/
def elementsDown : (base P).Elements ⥤ P.Elements where
  obj point := ⟨downOp.obj point.1, point.2.down⟩
  map arrow := ⟨downOp.map arrow.val, congrArg ULift.down arrow.property⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def elementsUp : P.Elements ⥤ (base P).Elements where
  obj point := ⟨upOp.obj point.1, ULift.up point.2⟩
  map arrow := ⟨upOp.map arrow.val, congrArg ULift.up arrow.property⟩
  map_id _ := rfl
  map_comp _ _ := rfl

theorem elements_up_down : compose (elementsUp P) (elementsDown P) = identity P.Elements := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

theorem elements_down_up : compose (elementsDown P) (elementsUp P) = identity (base P).Elements := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

theorem elementsDown_obj_injective : Function.Injective (elementsDown P).obj := by
  intro first second same
  exact congrArg (elementsUp P).obj same

theorem elementsDown_map_injective {X Y : (base P).Elements} :
    Function.Injective (fun arrow : X ⟶ Y => (elementsDown P).map arrow) := by
  intro first second same
  exact congrArg (elementsUp P).map same

variable (F : P.Elements ⥤ Type u)

/-- Displayed values and their actual contextual transport are raised together. -/
def family : (base P).Elements ⥤ Type (u + 1) where
  obj point := ULift.{u + 1, u} (F.obj ((elementsDown P).obj point))
  map arrow := TypeCat.ofHom fun value => ULift.up (F.map ((elementsDown P).map arrow) value.down)
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro value
    exact ULift.ext _ _ (F.map_id_apply ((elementsDown P).obj point) value.down)
  map_comp first later := by
    apply ConcreteCategory.hom_ext
    intro value
    exact ULift.ext _ _ (F.map_comp_apply ((elementsDown P).map first) ((elementsDown P).map later) value.down)

def raiseTerm (term : F.sections) : (family P F).sections :=
  ⟨fun point => ULift.up (term.val ((elementsDown P).obj point)), by
    intro _X _Y arrow
    exact congrArg ULift.up (term.property ((elementsDown P).map arrow))⟩

def lowerTerm (term : (family P F).sections) : F.sections :=
  ⟨fun point => (term.val ((elementsUp P).obj point)).down, by
    intro _X _Y arrow
    exact congrArg ULift.down (term.property ((elementsUp P).map arrow))⟩

theorem lower_raise_term (term : F.sections) : lowerTerm P F (raiseTerm P F term) = term := by
  apply Subtype.ext
  funext point
  rfl

theorem raise_lower_term (term : (family P F).sections) : raiseTerm P F (lowerTerm P F term) = term := by
  apply Subtype.ext
  funext point
  rfl

def termEquiv : F.sections ≃ (family P F).sections where
  toFun := raiseTerm P F
  invFun := lowerTerm P F
  left_inv := lower_raise_term P F
  right_inv := raise_lower_term P F

def displayedElementsDown : (family P F).Elements ⥤ F.Elements where
  obj point := ⟨(elementsDown P).obj point.1, point.2.down⟩
  map arrow := ⟨(elementsDown P).map arrow.val, congrArg ULift.down arrow.property⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def displayedElementsUp : F.Elements ⥤ (family P F).Elements where
  obj point := ⟨(elementsUp P).obj point.1, ULift.up point.2⟩
  map arrow := ⟨(elementsUp P).map arrow.val, congrArg ULift.up arrow.property⟩
  map_id _ := rfl
  map_comp _ _ := rfl

theorem displayed_elements_up_down :
    compose (displayedElementsUp P F) (displayedElementsDown P F) = identity F.Elements := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

theorem displayed_elements_down_up :
    compose (displayedElementsDown P F) (displayedElementsUp P F) = identity (family P F).Elements := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

/-- Positions over actual displayed values are raised with their full transport. -/
def body (B : F.Elements ⥤ Type u) : (family P F).Elements ⥤ Type (u + 1) where
  obj point := ULift.{u + 1, u} (B.obj ((displayedElementsDown P F).obj point))
  map arrow := TypeCat.ofHom fun value => ULift.up (B.map ((displayedElementsDown P F).map arrow) value.down)
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro value
    exact ULift.ext _ _ (B.map_id_apply ((displayedElementsDown P F).obj point) value.down)
  map_comp first later := by
    apply ConcreteCategory.hom_ext
    intro value
    exact ULift.ext _ _ (B.map_comp_apply ((displayedElementsDown P F).map first) ((displayedElementsDown P F).map later) value.down)

end Presheaves

section Substitution

variable {C : Type u} [Category.{u} C] {P Q R : Cᵒᵖ ⥤ Type u}

/-- Explicit contextual maps retain the particular underlying arrow. -/
def elementsMap (change : NatTrans Q P) : Q.Elements ⥤ P.Elements where
  obj point := ⟨point.1, change.app point.1 point.2⟩
  map {first second} arrow := ⟨arrow.val, by
    have naturally := congrArg (fun operation => operation first.2) (change.naturality arrow.val)
    exact naturally.symm.trans (congrArg (change.app second.1) arrow.property)⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Both natural values and every actual site restriction are transported. -/
def raiseChange (change : NatTrans Q P) : NatTrans (base Q) (base P) where
  app point := TypeCat.ofHom fun value => ULift.up (change.app (downOp.obj point) value.down)
  naturality _X _Y arrow := by
    apply ConcreteCategory.hom_ext
    intro value
    exact congrArg ULift.up (congrArg (fun operation => operation value.down) (change.naturality (downOp.map arrow)))

theorem raiseChange_identity :
    raiseChange (Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.identity P) =
      Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.identity (base P) := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro value
  rfl

theorem raiseChange_comp (first : NatTrans R Q) (later : NatTrans Q P) :
    raiseChange (Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose first later) =
      Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose (raiseChange first) (raiseChange later) := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro value
  rfl

theorem elements_lower_change (change : NatTrans Q P) :
    compose (elementsMap (raiseChange change)) (elementsDown P) =
      compose (elementsDown Q) (elementsMap change) := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

theorem elements_raise_change (change : NatTrans Q P) :
    compose (elementsMap change) (elementsUp P) =
      compose (elementsUp Q) (elementsMap (raiseChange change)) := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

def reindex (change : NatTrans Q P) (F : P.Elements ⥤ Type u) : Q.Elements ⥤ Type u :=
  Mettapedia.GSLT.Topos.ConstructivePresheaf.restrict (elementsMap change) F

/-- The full lifted displayed functors commute with actual context changes. -/
theorem reindex_family (change : NatTrans Q P) (F : P.Elements ⥤ Type u) :
    family Q (reindex change F) =
      Mettapedia.GSLT.Topos.ConstructivePresheaf.restrict (elementsMap (raiseChange change)) (family P F) := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

def reindexTerm (change : NatTrans Q P) (F : P.Elements ⥤ Type u) (term : F.sections) :
    (reindex change F).sections :=
  ⟨fun point => term.val ((elementsMap change).obj point), by
    intro _X _Y arrow
    exact term.property ((elementsMap change).map arrow)⟩

theorem reindex_term (change : NatTrans Q P) (F : P.Elements ⥤ Type u) (term : F.sections)
    (point : (base Q).Elements) :
    (raiseTerm Q (reindex change F) (reindexTerm change F term)).val point =
      (raiseTerm P F term).val ((elementsMap (raiseChange change)).obj point) := rfl

end Substitution

section Comprehension

variable {C : Type u} [Category.{u} C] (P : Cᵒᵖ ⥤ Type u) (F : P.Elements ⥤ Type u)

/-- Raising an actual comprehension receipt retains both dependent coordinates. -/
def comprehensionTo : NatTrans (base (totalSpace F)) (totalSpace (family P F)) where
  app _ := TypeCat.ofHom fun value => ⟨ULift.up value.down.1, ULift.up value.down.2⟩
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro value
    rfl

def comprehensionFrom : NatTrans (totalSpace (family P F)) (base (totalSpace F)) where
  app _ := TypeCat.ofHom fun value => ULift.up ⟨value.1.down, value.2.down⟩
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro value
    rfl

def comprehensionEquiv (point : (Site C)ᵒᵖ) :
    (base (totalSpace F)).obj point ≃ (totalSpace (family P F)).obj point where
  toFun := (comprehensionTo P F).app point
  invFun := (comprehensionFrom P F).app point
  left_inv _ := rfl
  right_inv _ := rfl

theorem comprehension_left :
    Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose (comprehensionTo P F) (comprehensionFrom P F) =
      Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.identity (base (totalSpace F)) := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro value
  exact (comprehensionEquiv P F point).symm_apply_apply value

theorem comprehension_right :
    Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose (comprehensionFrom P F) (comprehensionTo P F) =
      Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.identity (totalSpace (family P F)) := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro value
  exact (comprehensionEquiv P F point).apply_symm_apply value

/-- Explicit projection does not invoke a functor-category default proof. -/
def projection : NatTrans (totalSpace F) P where
  app _ := TypeCat.ofHom Sigma.fst
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro value
    rfl

def sectionMap (term : F.sections) : NatTrans P (totalSpace F) where
  app point := TypeCat.ofHom fun value => ⟨value, term.val ⟨point, value⟩⟩
  naturality X Y arrow := by
    apply ConcreteCategory.hom_ext
    intro value
    exact congrArg (fun member => (⟨P.map arrow value, member⟩ : (totalSpace F).obj Y))
      (term.property (CategoryOfElements.homMk (F := P)
        ⟨X, value⟩ ⟨Y, P.map arrow value⟩ arrow rfl)).symm

theorem comprehension_projection :
    Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose (comprehensionTo P F) (projection (base P) (family P F)) =
      raiseChange (projection P F) := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro value
  rfl

theorem comprehension_section (term : F.sections) :
    Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose
      (raiseChange (sectionMap P F term)) (comprehensionTo P F) =
        sectionMap (base P) (family P F) (raiseTerm P F term) := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro value
  rfl

end Comprehension

end Mettapedia.TypeTheory.PresheafSiteLift
