import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Arrow lifting for substitutions of presheaf contexts

A natural transformation between type-valued functors induces a functor
between their categories of elements. Every arrow starting at an image
element has a canonical lift, because naturality determines the target
element. This property distinguishes presheaf context substitutions from
arbitrary functors between indexing categories. It does not itself assert
a Beck-Chevalley or dependent-product law.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.PresheafElementSubstitutionLifting

open CategoryTheory

universe u v w uSource vSource uTarget vTarget

/-- A functor admits lifts of all arrows leaving one of its image objects.
The endpoint equality is explicit, so the statement does not hide a choice
of a target representative. This is an existence property, not the full
unique-lifting definition of a discrete opfibration. -/
def OutgoingLiftProperty
    {Source : Type uSource} [Category.{vSource} Source]
    {Target : Type uTarget} [Category.{vTarget} Target]
    (change : Source ⥤ Target) : Prop :=
  ∀ (point : Source) {observed : Target}
    (arrow : change.obj point ⟶ observed),
    ∃ liftedPoint : Source, ∃ liftedArrow : point ⟶ liftedPoint,
      ∃ same : change.obj liftedPoint = observed,
        change.map liftedArrow ≫ eqToHom same = arrow

variable {Context : Type u} [Category.{v} Context]
variable {source target : Context ⥤ Type w}

/-- The only possible target value of a lift of an outgoing arrow. -/
def liftTarget (substitution : source ⟶ target)
    (point : source.Elements) {observed : target.Elements}
    (arrow : substitution.mapElements.obj point ⟶ observed) :
    source.Elements :=
  ⟨observed.1, source.map arrow.val point.2⟩

/-- The canonical arrow in the source category of elements. -/
def liftArrow (substitution : source ⟶ target)
    (point : source.Elements) {observed : target.Elements}
    (arrow : substitution.mapElements.obj point ⟶ observed) :
    point ⟶ liftTarget substitution point arrow :=
  ⟨arrow.val, rfl⟩

/-- Naturality and the observed arrow's endpoint equation show that the
lifted target maps to precisely the requested observed target. -/
theorem map_liftTarget_eq (substitution : source ⟶ target)
    (point : source.Elements) {observed : target.Elements}
    (arrow : substitution.mapElements.obj point ⟶ observed) :
    substitution.mapElements.obj (liftTarget substitution point arrow) =
      observed := by
  cases point with
  | mk pointContext pointValue =>
      cases observed with
      | mk observedContext observedValue =>
          cases arrow with
          | mk underlying follows =>
              change (⟨observedContext,
                substitution.app observedContext
                  (source.map underlying pointValue)⟩ : target.Elements) =
                ⟨observedContext, observedValue⟩
              refine Sigma.ext (by rfl) ?_
              apply heq_of_eq
              change substitution.app observedContext
                  (source.map underlying pointValue) = observedValue
              calc
                _ = target.map underlying
                    (substitution.app pointContext pointValue) := by
                      rw [substitution.naturality_apply underlying pointValue]
                      simp [NatTrans.mapElements]
                      rfl
                _ = observedValue := follows

/-- The lifted arrow has exactly the underlying syntax arrow of the
observed transition; no new operational route is chosen. -/
theorem liftArrow_underlying (substitution : source ⟶ target)
    (point : source.Elements) {observed : target.Elements}
    (arrow : substitution.mapElements.obj point ⟶ observed) :
    (liftArrow substitution point arrow).val = arrow.val := rfl

private theorem eqToHom_underlying
    {family : Context ⥤ Type w} {first second : family.Elements}
    (same : first = second) :
    (eqToHom same : first ⟶ second).val =
      eqToHom (congrArg Sigma.fst same) := by
  cases same
  rfl

/-- After transporting its image endpoint along the naturality equality,
the lifted arrow maps back to the exact observed arrow. -/
theorem map_liftArrow_eq (substitution : source ⟶ target)
    (point : source.Elements) {observed : target.Elements}
    (arrow : substitution.mapElements.obj point ⟶ observed) :
    substitution.mapElements.map (liftArrow substitution point arrow) ≫
      eqToHom (map_liftTarget_eq substitution point arrow) = arrow := by
  let same := map_liftTarget_eq substitution point arrow
  apply CategoryOfElements.ext target
  change arrow.val ≫ (eqToHom same).val = arrow.val
  rw [eqToHom_underlying]
  have base : congrArg Sigma.fst same = rfl := Subsingleton.elim _ _
  rw [base]
  change arrow.val ≫ 𝟙 observed.1 = arrow.val
  simp

/-- Every natural substitution of type-valued contexts has the outgoing
arrow-lifting property, witnessed by the actual functorial image value. -/
theorem mapElements_outgoingLifts (substitution : source ⟶ target) :
    OutgoingLiftProperty substitution.mapElements := by
  intro point observed arrow
  exact ⟨liftTarget substitution point arrow,
    liftArrow substitution point arrow,
    map_liftTarget_eq substitution point arrow,
    map_liftArrow_eq substitution point arrow⟩

/-- Once the underlying syntax arrow is fixed, exactly one source value
can be the endpoint of its lift. The canonical construction supplies it. -/
theorem unique_lift_target_value (substitution : source ⟶ target)
    (point : source.Elements) {observed : target.Elements}
    (arrow : substitution.mapElements.obj point ⟶ observed) :
    ∃! candidateValue : source.obj observed.1,
      ∃ lifted : point ⟶
          (⟨observed.1, candidateValue⟩ : source.Elements),
        lifted.val = arrow.val := by
  refine ⟨source.map arrow.val point.2, ?_, ?_⟩
  · exact ⟨⟨arrow.val, rfl⟩, rfl⟩
  · intro candidateValue witness
    rcases witness with ⟨lifted, sameUnderlying⟩
    exact lifted.property.symm.trans (by rw [sameUnderlying]; rfl)

/-- An arrow between two observed future elements lifts along the same
source-side routes whenever its triangle from the current point commutes.
The lifted arrow retains the underlying syntax arrow exactly. -/
def liftTriangle (substitution : source ⟶ target)
    (point : source.Elements)
    {first second : target.Elements}
    (firstRoute : substitution.mapElements.obj point ⟶ first)
    (secondRoute : substitution.mapElements.obj point ⟶ second)
    (between : first ⟶ second)
    (triangle : firstRoute ≫ between = secondRoute) :
    liftTarget substitution point firstRoute ⟶
      liftTarget substitution point secondRoute := by
  refine ⟨between.val, ?_⟩
  change source.map between.val
      (source.map firstRoute.val point.2) =
    source.map secondRoute.val point.2
  have routeEq : firstRoute.val ≫ between.val = secondRoute.val := by
    simpa only [CategoryOfElements.comp_val] using
      congrArg Subtype.val triangle
  have mapped := congrArg (fun arrow => source.map arrow point.2) routeEq
  exact (source.map_comp_apply firstRoute.val between.val point.2).symm.trans mapped

theorem liftTriangle_underlying (substitution : source ⟶ target)
    (point : source.Elements)
    {first second : target.Elements}
    (firstRoute : substitution.mapElements.obj point ⟶ first)
    (secondRoute : substitution.mapElements.obj point ⟶ second)
    (between : first ⟶ second)
    (triangle : firstRoute ≫ between = secondRoute) :
    (liftTriangle substitution point firstRoute secondRoute
      between triangle).val = between.val := rfl

/-- Lifting an identity triangle gives exactly the identity arrow. -/
theorem liftTriangle_id (substitution : source ⟶ target)
    (point : source.Elements)
    {first : target.Elements}
    (route : substitution.mapElements.obj point ⟶ first) :
    liftTriangle substitution point route route (𝟙 first) (by simp) =
      𝟙 (liftTarget substitution point route) := by
  apply CategoryOfElements.ext source
  rfl

/-- Lifting respects composition of commuting future-arrow triangles. -/
theorem liftTriangle_comp (substitution : source ⟶ target)
    (point : source.Elements)
    {first second third : target.Elements}
    (firstRoute : substitution.mapElements.obj point ⟶ first)
    (secondRoute : substitution.mapElements.obj point ⟶ second)
    (thirdRoute : substitution.mapElements.obj point ⟶ third)
    (firstStep : first ⟶ second)
    (secondStep : second ⟶ third)
    (firstTriangle : firstRoute ≫ firstStep = secondRoute)
    (secondTriangle : secondRoute ≫ secondStep = thirdRoute) :
    liftTriangle substitution point firstRoute thirdRoute
        (firstStep ≫ secondStep)
        (by
          calc
            firstRoute ≫ (firstStep ≫ secondStep) =
                (firstRoute ≫ firstStep) ≫ secondStep :=
                  (Category.assoc _ _ _).symm
            _ = secondRoute ≫ secondStep := by rw [firstTriangle]
            _ = thirdRoute := secondTriangle) =
      liftTriangle substitution point firstRoute secondRoute
          firstStep firstTriangle ≫
        liftTriangle substitution point secondRoute thirdRoute
          secondStep secondTriangle := by
  apply CategoryOfElements.ext source
  rfl

/-- The source-side lifted arrow closes the same triangle as the
observed arrow. -/
theorem liftArrow_triangle (substitution : source ⟶ target)
    (point : source.Elements)
    {first second : target.Elements}
    (firstRoute : substitution.mapElements.obj point ⟶ first)
    (secondRoute : substitution.mapElements.obj point ⟶ second)
    (between : first ⟶ second)
    (triangle : firstRoute ≫ between = secondRoute) :
    liftArrow substitution point firstRoute ≫
        liftTriangle substitution point firstRoute secondRoute
          between triangle =
      liftArrow substitution point secondRoute := by
  cases point with
  | mk pointContext pointValue =>
      apply CategoryOfElements.ext source
      change firstRoute.val ≫ between.val = secondRoute.val
      simpa only [CategoryOfElements.comp_val] using
        congrArg Subtype.val triangle

/-- Every natural substitution induces a functor from observed outgoing
arrows at a point to their canonical source-side lifts. This functor is
not yet the comparison between dependent right-Kan comma categories. -/
def underLiftFunctor (substitution : source ⟶ target)
    (point : source.Elements) :
    Under (substitution.mapElements.obj point) ⥤ Under point where
  obj route := Under.mk (liftArrow substitution point route.hom)
  map {first second} between :=
    Under.homMk
      (liftTriangle substitution point first.hom second.hom
        between.right (Under.w between))
      (liftArrow_triangle substitution point first.hom second.hom
        between.right (Under.w between))
  map_id route := by
    apply StructuredArrow.hom_ext
    apply CategoryOfElements.ext source
    rfl
  map_comp firstStep secondStep := by
    apply StructuredArrow.hom_ext
    apply CategoryOfElements.ext source
    rfl

/-- Projecting the canonical lift back along the substitution recovers
an observed outgoing arrow, with the endpoint equality made explicit.
This is an objectwise isomorphism, not yet a natural isomorphism. -/
def underLift_post_object_iso (substitution : source ⟶ target)
    (point : source.Elements)
    (route : Under (substitution.mapElements.obj point)) :
    ((underLiftFunctor substitution point ⋙
        Under.post substitution.mapElements).obj route) ≅ route := by
  let same := map_liftTarget_eq substitution point route.hom
  refine Under.isoMk (eqToIso same) ?_
  change substitution.mapElements.map
      (liftArrow substitution point route.hom) ≫ eqToHom same = route.hom
  exact map_liftArrow_eq substitution point route.hom

/-- Mapping a lifted commuting triangle back to observed elements
commutes with the explicit endpoint identifications. -/
theorem map_liftTriangle_square (substitution : source ⟶ target)
    (point : source.Elements)
    {first second : target.Elements}
    (firstRoute : substitution.mapElements.obj point ⟶ first)
    (secondRoute : substitution.mapElements.obj point ⟶ second)
    (between : first ⟶ second)
    (triangle : firstRoute ≫ between = secondRoute) :
    substitution.mapElements.map
        (liftTriangle substitution point firstRoute secondRoute between triangle) ≫
      eqToHom (map_liftTarget_eq substitution point secondRoute) =
    eqToHom (map_liftTarget_eq substitution point firstRoute) ≫ between := by
  apply CategoryOfElements.ext target
  let firstSame := map_liftTarget_eq substitution point firstRoute
  let secondSame := map_liftTarget_eq substitution point secondRoute
  change between.val ≫ (eqToHom secondSame).val =
    (eqToHom firstSame).val ≫ between.val
  have firstId : (eqToHom firstSame :
      substitution.mapElements.obj (liftTarget substitution point firstRoute) ⟶
        first).val = 𝟙 first.1 := by
    rw [eqToHom_underlying]
    have base : congrArg Sigma.fst firstSame = rfl := Subsingleton.elim _ _
    rw [base]
    rfl
  have secondId : (eqToHom secondSame :
      substitution.mapElements.obj (liftTarget substitution point secondRoute) ⟶
        second).val = 𝟙 second.1 := by
    rw [eqToHom_underlying]
    have base : congrArg Sigma.fst secondSame = rfl := Subsingleton.elim _ _
    rw [base]
    rfl
  rw [firstId, secondId]
  calc
    between.val ≫ 𝟙 second.1 = between.val := Category.comp_id _
    _ = 𝟙 first.1 ≫ between.val := (Category.id_comp _).symm

/-- The endpoint isomorphisms are natural in commuting triangles.
Thus lifting observed outgoing arrows and projecting them back is
naturally isomorphic to the identity. -/
def underLift_post_iso (substitution : source ⟶ target)
    (point : source.Elements) :
    underLiftFunctor substitution point ⋙
        Under.post substitution.mapElements ≅
      𝟭 (Under (substitution.mapElements.obj point)) :=
  NatIso.ofComponents
    (fun route => underLift_post_object_iso substitution point route)
    (by
      intro first second between
      apply StructuredArrow.hom_ext
      change substitution.mapElements.map
            (liftTriangle substitution point first.hom second.hom
              between.right (Under.w between)) ≫
          eqToHom (map_liftTarget_eq substitution point second.hom) =
        eqToHom (map_liftTarget_eq substitution point first.hom) ≫
          between.right
      exact map_liftTriangle_square substitution point
        first.hom second.hom between.right (Under.w between))

/-- If an outgoing source arrow is observed and then canonically
lifted, its endpoint is the original source element. -/
theorem liftTarget_post_eq (substitution : source ⟶ target)
    (point : source.Elements) (route : Under point) :
    liftTarget substitution point
      (substitution.mapElements.map route.hom) = route.right := by
  refine Sigma.ext (by rfl) ?_
  apply heq_of_eq
  change source.map route.hom.val point.2 = route.right.2
  exact route.hom.property

/-- Source-side round trip for one outgoing arrow, with the endpoint
transport explicit. -/
def post_underLift_object_iso (substitution : source ⟶ target)
    (point : source.Elements) (route : Under point) :
    ((Under.post substitution.mapElements ⋙
        underLiftFunctor substitution point).obj route) ≅ route := by
  let same := liftTarget_post_eq substitution point route
  refine Under.isoMk (eqToIso same) ?_
  change liftArrow substitution point
      (substitution.mapElements.map route.hom) ≫ eqToHom same = route.hom
  apply CategoryOfElements.ext source
  change route.hom.val ≫ (eqToHom same).val = route.hom.val
  rw [eqToHom_underlying]
  have base : congrArg Sigma.fst same = rfl := Subsingleton.elim _ _
  rw [base]
  exact Category.comp_id _

/-- The source-side round-trip isomorphism is natural in commuting
triangles between outgoing arrows. -/
def post_underLift_iso (substitution : source ⟶ target)
    (point : source.Elements) :
    Under.post substitution.mapElements ⋙
        underLiftFunctor substitution point ≅
      𝟭 (Under point) :=
  NatIso.ofComponents
    (fun route => post_underLift_object_iso substitution point route)
    (by
      intro first second between
      apply StructuredArrow.hom_ext
      apply CategoryOfElements.ext source
      change between.right.val ≫
          (eqToHom (liftTarget_post_eq substitution point second)).val =
        (eqToHom (liftTarget_post_eq substitution point first)).val ≫
          between.right.val
      have firstId :
          (eqToHom (liftTarget_post_eq substitution point first) :
            liftTarget substitution point
                (substitution.mapElements.map first.hom) ⟶ first.right).val =
              𝟙 first.right.1 := by
        rw [eqToHom_underlying]
        have base : congrArg Sigma.fst
            (liftTarget_post_eq substitution point first) = rfl :=
          Subsingleton.elim _ _
        rw [base]
        rfl
      have secondId :
          (eqToHom (liftTarget_post_eq substitution point second) :
            liftTarget substitution point
                (substitution.mapElements.map second.hom) ⟶ second.right).val =
              𝟙 second.right.1 := by
        rw [eqToHom_underlying]
        have base : congrArg Sigma.fst
            (liftTarget_post_eq substitution point second) = rfl :=
          Subsingleton.elim _ _
        rw [base]
        rfl
      rw [firstId, secondId]
      calc
        between.right.val ≫ 𝟙 second.right.1 = between.right.val :=
          Category.comp_id _
        _ = 𝟙 first.right.1 ≫ between.right.val :=
          (Category.id_comp _).symm)

/-- Natural substitution induces an equivalence of outgoing-arrow
categories at each source element. The equivalence retains syntax
arrows; it does not yet include dependent evidence over those arrows. -/
def underMapElementsEquivalence (substitution : source ⟶ target)
    (point : source.Elements) :
    Under point ≌ Under (substitution.mapElements.obj point) where
  functor := Under.post substitution.mapElements
  inverse := underLiftFunctor substitution point
  unitIso := (post_underLift_iso substitution point).symm
  counitIso := underLift_post_iso substitution point
  functor_unitIso_comp route := by
    apply StructuredArrow.hom_ext
    apply CategoryOfElements.ext target
    let sourceSame := liftTarget_post_eq substitution point route
    let observedSame := map_liftTarget_eq substitution point
      (substitution.mapElements.map route.hom)
    change (substitution.mapElements.map (eqToHom sourceSame.symm)).val ≫
        (eqToHom observedSame).val =
      𝟙 route.right.1
    have sourceUnderlying :
        (substitution.mapElements.map (eqToHom sourceSame.symm)).val =
          𝟙 route.right.1 := by
      change (eqToHom sourceSame.symm : route.right ⟶
        liftTarget substitution point
          (substitution.mapElements.map route.hom)).val = 𝟙 route.right.1
      rw [eqToHom_underlying]
      have base : congrArg Sigma.fst sourceSame.symm = rfl :=
        Subsingleton.elim _ _
      rw [base]
      rfl
    have observedUnderlying : (eqToHom observedSame :
        substitution.mapElements.obj
          (liftTarget substitution point
            (substitution.mapElements.map route.hom)) ⟶
          substitution.mapElements.obj route.right).val =
        𝟙 route.right.1 := by
      rw [eqToHom_underlying]
      have base : congrArg Sigma.fst observedSame = rfl :=
        Subsingleton.elim _ _
      rw [base]
      rfl
    rw [sourceUnderlying, observedUnderlying]
    exact Category.id_comp _

#print axioms map_liftTarget_eq
#print axioms liftArrow_underlying
#print axioms map_liftArrow_eq
#print axioms mapElements_outgoingLifts
#print axioms unique_lift_target_value
#print axioms liftTriangle
#print axioms liftTriangle_id
#print axioms liftTriangle_comp
#print axioms liftArrow_triangle
#print axioms underLiftFunctor
#print axioms underLift_post_object_iso
#print axioms map_liftTriangle_square
#print axioms underLift_post_iso
#print axioms liftTarget_post_eq
#print axioms post_underLift_object_iso
#print axioms post_underLift_iso
#print axioms underMapElementsEquivalence

end Mettapedia.TypeTheory.PresheafElementSubstitutionLifting
