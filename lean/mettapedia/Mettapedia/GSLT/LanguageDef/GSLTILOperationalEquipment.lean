import Mettapedia.GSLT.LanguageDef.GSLTILRouteEquipment

/-!
# Operational equipment over GSLTs

The proof-relevant relation equipment is lifted from bare carrier types to
operational GSLTs by the term-carrier functor.

* objects are GSLTs;
* tight arrows are equation- and step-preserving operational translations;
* loose arrows are proof-relevant relations between their term carriers;
* refinement squares map loose witnesses along the two tight boundaries.

This is the common base of the relational route semantics and the functional
execution-path index.  A loose route need not be functional.  When it earns
an exact representation whose selected map is operational, it is vertically
isomorphic to the companion of a tight arrow and therefore acts through the
existing execution-path functor.

The construction does not add a consequence relation, an observer, or an
object-gluing operation.  Those remain doctrines or construction structure
over this operational waist rather than fields of an execution arrow.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.OperationalEquipment

open CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.LooseRelationEquipment
open Mettapedia.GSLT.LanguageDef.GSLTIL.RouteEquipment

universe uTerm

/-! ## Change of base from types to operational GSLTs -/

/-- Tight arrows preserve equations and one-step execution. -/
abbrev Tight (source target : GSLT.{uTerm}) :=
  OperationalTranslation source target

/-- Loose arrows retain an arbitrary type of witnesses for each source and
target term. -/
abbrev LooseRoute (source target : GSLT.{uTerm}) :=
  Loose source.Term target.Term

/-- A refinement square maps every top-route witness along its two tight
operational boundaries to a bottom-route witness. -/
abbrev RefinementSquare
    {source target source' target' : GSLT.{uTerm}}
    (left : Tight source source') (right : Tight target target')
    (top : LooseRoute source target) (bottom : LooseRoute source' target') :=
  Cell left.mapTerm right.mapTerm top bottom

/-- The operational term-carrier functor is the change-of-base map along
which the proof-relevant relation equipment is lifted. -/
def termCarrier :
    CategoryTheory.Functor OperationalTheory.{uTerm} (Type uTerm) where
  obj system := system.theory.Term
  map translation := TypeCat.ofHom translation.mapTerm
  map_id _ := by
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro term
    rfl
  map_comp _ _ := by
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro term
    rfl

@[simp] theorem termCarrier_obj (system : OperationalTheory.{uTerm}) :
    termCarrier.obj system = system.theory.Term :=
  rfl

@[simp] theorem termCarrier_map
    {source target : OperationalTheory.{uTerm}}
    (translation : source ⟶ target) :
    termCarrier.map translation = TypeCat.ofHom translation.mapTerm :=
  rfl

/-! ## Tight, loose, and square composition -/

/-- Tight identity. -/
abbrev tightId (system : GSLT.{uTerm}) : Tight system system :=
  OperationalTranslation.id system

/-- Tight composition in execution order. -/
abbrev tightComp {first middle last : GSLT.{uTerm}}
    (earlier : Tight first middle) (later : Tight middle last) :
    Tight first last :=
  earlier.comp later

/-- Horizontal identity loose route. -/
abbrev looseId (system : GSLT.{uTerm}) : LooseRoute system system :=
  identity

/-- Horizontal composition retains the intermediate term and both route
witnesses. -/
abbrev looseComp {first middle last : GSLT.{uTerm}}
    (earlier : LooseRoute first middle) (later : LooseRoute middle last) :
    LooseRoute first last :=
  LooseRelationEquipment.comp earlier later

/-- Identity refinement square. -/
def squareId {source target : GSLT.{uTerm}}
    (route : LooseRoute source target) :
    RefinementSquare (tightId source) (tightId target) route route :=
  Cell.id route

/-- Vertical composition of refinement squares. -/
def squareVComp
    {source target source' target' source'' target'' : GSLT.{uTerm}}
    {left : Tight source source'} {right : Tight target target'}
    {left' : Tight source' source''} {right' : Tight target' target''}
    {top : LooseRoute source target}
    {middle : LooseRoute source' target'}
    {bottom : LooseRoute source'' target''}
    (upper : RefinementSquare left right top middle)
    (lower : RefinementSquare left' right' middle bottom) :
    RefinementSquare (tightComp left left') (tightComp right right')
      top bottom :=
  by
    change Cell (left'.mapTerm ∘ left.mapTerm)
      (right'.mapTerm ∘ right.mapTerm) top bottom
    exact Cell.vcomp (left := left.mapTerm) (right := right.mapTerm)
      (left' := left'.mapTerm) (right' := right'.mapTerm) upper lower

/-- Horizontal composition maps the retained intermediate term through the
shared tight boundary. -/
def squareHComp
    {first middle last first' middle' last' : GSLT.{uTerm}}
    {left : Tight first first'} {shared : Tight middle middle'}
    {right : Tight last last'}
    {topEarlier : LooseRoute first middle}
    {topLater : LooseRoute middle last}
    {bottomEarlier : LooseRoute first' middle'}
    {bottomLater : LooseRoute middle' last'}
    (earlier : RefinementSquare left shared topEarlier bottomEarlier)
    (later : RefinementSquare shared right topLater bottomLater) :
    RefinementSquare left right (looseComp topEarlier topLater)
      (looseComp bottomEarlier bottomLater) :=
  Cell.hcomp earlier later

/-- The lifted squares inherit interchange exactly. -/
theorem square_interchange
    {a b c a' b' c' a'' b'' c'' : GSLT.{uTerm}}
    {fa : Tight a a'} {fb : Tight b b'} {fc : Tight c c'}
    {ga : Tight a' a''} {gb : Tight b' b''} {gc : Tight c' c''}
    {r : LooseRoute a b} {s : LooseRoute b c}
    {r' : LooseRoute a' b'} {s' : LooseRoute b' c'}
    {r'' : LooseRoute a'' b''} {s'' : LooseRoute b'' c''}
    (upperLeft : RefinementSquare fa fb r r')
    (upperRight : RefinementSquare fb fc s s')
    (lowerLeft : RefinementSquare ga gb r' r'')
    (lowerRight : RefinementSquare gb gc s' s'') :
    squareHComp (squareVComp upperLeft lowerLeft)
        (squareVComp upperRight lowerRight) =
      squareVComp (squareHComp upperLeft upperRight)
        (squareHComp lowerLeft lowerRight) :=
  by
    apply Cell.ext
    intro source target witness
    rfl

/-! ## Companions and conjoints of operational translations -/

/-- Companion of a tight operational translation. -/
def companionRoute {source target : GSLT.{uTerm}}
    (translation : Tight source target) : LooseRoute source target :=
  companion translation.mapTerm

/-- Conjoint of a tight operational translation. -/
def conjointRoute {source target : GSLT.{uTerm}}
    (translation : Tight source target) : LooseRoute target source :=
  conjoint translation.mapTerm

/-- First companion binding square. -/
def companionUnitSquare {source target : GSLT.{uTerm}}
    (translation : Tight source target) :
    RefinementSquare (tightId source) translation (looseId source)
      (companionRoute translation) :=
  companionUnit translation.mapTerm

/-- Second companion binding square. -/
def companionCounitSquare {source target : GSLT.{uTerm}}
    (translation : Tight source target) :
    RefinementSquare translation (tightId target)
      (companionRoute translation) (looseId target) :=
  companionCounit translation.mapTerm

/-- The vertical companion triangle is inherited by change of base. -/
theorem companion_vertical_triangle
    {source target : GSLT.{uTerm}}
    (translation : Tight source target) :
    Cell.vcomp (companionUnitSquare translation)
        (companionCounitSquare translation) =
      tightCell translation.mapTerm :=
  LooseRelationEquipment.companion_vertical_triangle translation.mapTerm

/-- Every companion route has its canonical exact representation. -/
def companionRepresentation {source target : GSLT.{uTerm}}
    (translation : Tight source target) :
    Representation (companionRoute translation) :=
  Representation.companionSelf translation.mapTerm

/-! ## Represented routes are the functional sublayer -/

/-- The horizontal arrow underlying a represented operational route. -/
def representedLoose
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target) :
    LooseRoute source target :=
  route.related

/-- The tight arrow selected by exact representation and operational laws. -/
def representedTight
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target) :
    Tight source target :=
  route.toOperationalTranslation

/-- A represented horizontal route maps exactly to the companion of its
selected tight operational translation. -/
def representedToCompanionSquare
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target) :
    RefinementSquare (tightId source) (tightId target)
      (representedLoose route) (companionRoute (representedTight route)) :=
  route.representation.toCompanionCell

/-- The inverse square recovers every retained route witness. -/
def representedFromCompanionSquare
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target) :
    RefinementSquare (tightId source) (tightId target)
      (companionRoute (representedTight route)) (representedLoose route) :=
  route.representation.fromCompanionCell

/-- The two comparison squares recover the original represented loose route. -/
theorem represented_toCompanion_then_from
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target) :
    Cell.vcomp (representedToCompanionSquare route)
        (representedFromCompanionSquare route) =
      Cell.id (representedLoose route) :=
  route.representation.fromCompanion_vcomp_toCompanion

/-- The inverse order recovers the companion of the selected tight arrow. -/
theorem represented_fromCompanion_then_to
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target) :
    Cell.vcomp (representedFromCompanionSquare route)
        (representedToCompanionSquare route) =
      Cell.id (companionRoute (representedTight route)) :=
  route.representation.toCompanion_vcomp_fromCompanion

@[simp] theorem representedLoose_comp
    {first middle last : GSLT.{uTerm}}
    (earlier : RepresentedOperationalRoute first middle)
    (later : RepresentedOperationalRoute middle last) :
    representedLoose (earlier.comp later) =
      looseComp (representedLoose earlier) (representedLoose later) :=
  rfl

@[simp] theorem representedTight_comp
    {first middle last : GSLT.{uTerm}}
    (earlier : RepresentedOperationalRoute first middle)
    (later : RepresentedOperationalRoute middle last) :
    representedTight (earlier.comp later) =
      tightComp (representedTight earlier) (representedTight later) :=
  RepresentedOperationalRoute.toOperationalTranslation_comp earlier later

/-- The path action of a represented horizontal route is exactly the path
functor of its selected tight arrow. -/
theorem represented_pathFunctor_eq_tight
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target) :
    route.pathFunctor = (representedTight route).pathFunctor :=
  rfl

/-! ## Negative control: loose execution strictly exceeds the tight layer -/

/-- A discrete GSLT used only to expose the route-layer boundary. -/
def discrete (Term : Type uTerm) : GSLT.{uTerm} where
  Term := Term
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun _ _ => False
  rewrites_resp_left := by
    intro _ _ _ _ impossible
    exact False.elim impossible
  rewrites_resp_right := by
    intro _ _ _ impossible _
    exact False.elim impossible

/-- One loose GSLT route with two distinct possible targets. -/
def choiceRoute : LooseRoute (discrete Unit) (discrete Bool) :=
  LooseRelationEquipment.Canary.choice

/-- The choice route executes at both targets. -/
theorem choiceRoute_executes_both :
    Nonempty (choiceRoute () false) ∧ Nonempty (choiceRoute () true) :=
  LooseRelationEquipment.Canary.choice_executes_both

/-- The same route cannot be the companion of a tight translation. -/
theorem choiceRoute_not_representable :
    ¬ Nonempty (Representation choiceRoute) :=
  LooseRelationEquipment.Canary.choice_not_representable

#print axioms termCarrier_map
#print axioms square_interchange
#print axioms companion_vertical_triangle
#print axioms represented_toCompanion_then_from
#print axioms represented_fromCompanion_then_to
#print axioms representedTight_comp
#print axioms represented_pathFunctor_eq_tight
#print axioms choiceRoute_executes_both
#print axioms choiceRoute_not_representable

end Mettapedia.GSLT.LanguageDef.GSLTIL.OperationalEquipment
