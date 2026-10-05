import Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassPresheafProducts

/-!
# Constructed base change for full contextual dependent sections

A natural transformation of base presheaves supplies canonical outgoing
arrow lifts in their categories of elements. These lifts retain the actual
context arrow. The resulting future categories, rather than the current
fibre alone, control the contextual dependent product.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassPresheafBaseChange

open CategoryTheory
open Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassPresheafProducts
open Mettapedia.GSLT.Topos.ConstructivePresheaf
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent
open Mettapedia.TypeTheory.DependentFamilySectionDescent (equalityEquiv)
open Mettapedia.TypeTheory.DisplayedPresheafComprehension (totalSpace TotalAt)
open Mettapedia.TypeTheory.DisplayedPresheafIndexedCwfBridge

universe u

namespace Future

variable {D E : Type u} [Category.{u} D] [Category.{u} E]

/-- A future retains both its target and the particular arrow reaching it. -/
structure Objects (point : D) : Type u where
  fst : D
  snd : point ⟶ fst

theorem objects_ext {point : D} {first second : Objects point}
    (sameTarget : first.1 = second.1) (sameArrow : HEq first.2 second.2) : first = second := by
  rcases first with ⟨X, earlier⟩
  rcases second with ⟨Y, later⟩
  change X = Y at sameTarget
  subst Y
  have arrows : earlier = later := eq_of_heq sameArrow
  cases arrows
  rfl

instance category (point : D) : Category.{u} (Objects point) where
  Hom first second := {step : first.1 ⟶ second.1 // first.2 ≫ step = second.2}
  id first := ⟨𝟙 first.1, Category.comp_id _⟩
  comp first second := ⟨first.1 ≫ second.1, by rw [← Category.assoc, first.2, second.2]⟩
  id_comp _ := Subtype.ext (Category.id_comp _)
  comp_id _ := Subtype.ext (Category.comp_id _)
  assoc _ _ _ := Subtype.ext (Category.assoc _ _ _)

def target (point : D) : Objects point ⥤ D where
  obj future := future.1
  map step := step.1
  map_id _ := rfl
  map_comp _ _ := rfl

def map (change : D ⥤ E) (point : D) : Objects point ⥤ Objects (change.obj point) where
  obj future := ⟨change.obj future.1, change.map future.2⟩
  map step := ⟨change.map step.1, by rw [← change.map_comp, step.2]⟩
  map_id _ := Subtype.ext (change.map_id _)
  map_comp _ _ := Subtype.ext (change.map_comp _ _)

def domain (family : D ⥤ Type u) (point : D) : Objects point ⥤ Type u :=
  restrict (target point) family

def argument (family : D ⥤ Type u) (point : D) : (domain family point).Elements ⥤ family.Elements where
  obj future := ⟨future.1.1, future.2⟩
  map step := ⟨step.1.1, step.2⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def result (family : D ⥤ Type u) (body : family.Elements ⥤ Type u) (point : D) :
    (domain family point).Elements ⥤ Type u := restrict (argument family point) body

/-- A full dependent function is exactly a compatible natural section over
all future arrows and all future arguments. -/
def sectionEquiv (family : D ⥤ Type u) (body : family.Elements ⥤ Type u) (point : D) :
    DependentSection family body point ≃ (result family body point).sections where
  toFun function := ⟨fun future => function.app future.1.1 future.1.2 future.2, by
    intro first second step
    rcases first with ⟨⟨X, earlier⟩, arg⟩
    rcases second with ⟨⟨Y, later⟩, nextArg⟩
    rcases step with ⟨⟨step, triangle⟩, follows⟩
    change X ⟶ Y at step
    change family.map step arg = nextArg at follows
    change earlier ≫ step = later at triangle
    subst nextArg
    subst later
    exact function.naturality step earlier arg⟩
  invFun term := {
    app next step arg := term.val ⟨⟨next, step⟩, arg⟩
    naturality step restriction arg := term.property
      (CategoryOfElements.homMk (F := domain family point)
        ⟨⟨_, restriction⟩, arg⟩ ⟨⟨_, restriction ≫ step⟩, family.map step arg⟩
          (⟨step, rfl⟩ : (⟨_, restriction⟩ : Objects point) ⟶ ⟨_, restriction ≫ step⟩) rfl) }
  left_inv function := by
    apply DependentSection.ext
    intro _ _ _
    rfl
  right_inv term := by
    apply Subtype.ext
    funext future
    rcases future with ⟨⟨_, _⟩, _⟩
    rfl

end Future

namespace Cat

variable {D E K : Type u} [Category.{u} D] [Category.{u} E] [Category.{u} K]

def compose (first : D ⥤ E) (second : E ⥤ K) : D ⥤ K where
  obj point := second.obj (first.obj point)
  map step := second.map (first.map step)
  map_id point := by rw [first.map_id, second.map_id]
  map_comp firstStep secondStep := by rw [first.map_comp, second.map_comp]

def identity (D : Type u) [Category.{u} D] : D ⥤ D where
  obj point := point
  map step := step
  map_id _ := rfl
  map_comp _ _ := rfl

theorem dependentValue_heq {A : Type u} {B : A → Type u} (value : (a : A) → B a)
    {first second : A} (same : first = second) : HEq (value first) (value second) := by
  cases same
  rfl

theorem restrict_comp (first : D ⥤ E) (second : E ⥤ K) (family : K ⥤ Type u) :
    restrict first (restrict second family) = restrict (compose first second) family := rfl

theorem restrict_identity (family : D ⥤ Type u) : restrict (identity D) family = family := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

def sectionEquivOfInverse (forward : D ⥤ E) (backward : E ⥤ D)
    (left : compose forward backward = identity D) (right : compose backward forward = identity E)
    (family : E ⥤ Type u) : family.sections ≃ (restrict forward family).sections where
  toFun := CP.restrictSection forward family
  invFun term := CP.castSection
    ((restrict_comp backward forward family).trans
      ((congrArg (fun change => restrict change family) right).trans (restrict_identity family)))
      (CP.restrictSection backward (restrict forward family) term)
  left_inv term := by
    apply Subtype.ext
    funext point
    have castValue := CP.castSection_value
      ((restrict_comp backward forward family).trans
        ((congrArg (fun change => restrict change family) right).trans (restrict_identity family)))
      (CP.restrictSection backward (restrict forward family) (CP.restrictSection forward family term)) point
    have pointEq : forward.obj (backward.obj point) = point :=
      congrArg (fun change : E ⥤ E => change.obj point) right
    exact eq_of_heq (castValue.trans (dependentValue_heq term.val pointEq))
  right_inv term := by
    apply Subtype.ext
    funext point
    have castValue := CP.castSection_value
      ((restrict_comp backward forward family).trans
        ((congrArg (fun change => restrict change family) right).trans (restrict_identity family)))
      (CP.restrictSection backward (restrict forward family) term) (forward.obj point)
    have pointEq : backward.obj (forward.obj point) = point :=
      congrArg (fun change : D ⥤ D => change.obj point) left
    exact eq_of_heq (castValue.trans (dependentValue_heq term.val pointEq))

def elementsTransport {first second : D ⥤ Type u} (same : first = second) :
    first.Elements ⥤ second.Elements := by
  cases same
  exact identity _

theorem elementsTransport_context {first second : D ⥤ Type u} (same : first = second)
    (point : first.Elements) : ((elementsTransport same).obj point).1 = point.1 := by
  cases same
  rfl

theorem elementsTransport_value {first second : D ⥤ Type u} (same : first = second)
    (point : first.Elements) : HEq ((elementsTransport same).obj point).2 point.2 := by
  cases same
  rfl

theorem elementsTransport_arrow {first second : D ⥤ Type u} (same : first = second)
    {X Y : first.Elements} (step : X ⟶ Y) : HEq ((elementsTransport same).map step).1 step.1 := by
  cases same
  rfl

theorem map_heq (change : D ⥤ E) {X X' Y Y' : D} (sourceEq : X = X') (targetEq : Y = Y')
    (first : X ⟶ Y) (second : X' ⟶ Y') (sameArrow : HEq first second) :
    HEq (change.map first) (change.map second) := by
  cases sourceEq
  cases targetEq
  cases eq_of_heq sameArrow
  rfl

theorem equalFunctor_arrow {first second : D ⥤ E} (same : first = second)
    {X Y : D} (step : X ⟶ Y) : HEq (first.map step) (second.map step) := by
  cases same
  rfl

def elementsMap (change : D ⥤ E) (family : E ⥤ Type u) :
    (restrict change family).Elements ⥤ family.Elements where
  obj point := ⟨change.obj point.1, point.2⟩
  map step := ⟨change.map step.1, step.2⟩
  map_id _ := Subtype.ext (change.map_id _)
  map_comp _ _ := Subtype.ext (change.map_comp _ _)

theorem bodyRightEq (forward : D ⥤ E) (backward : E ⥤ D)
    (right : compose backward forward = identity E) (family : E ⥤ Type u) :
    restrict backward (restrict forward family) = family :=
  (restrict_comp backward forward family).trans
    ((congrArg (fun change => restrict change family) right).trans (restrict_identity family))

def elementsBack (forward : D ⥤ E) (backward : E ⥤ D)
    (right : compose backward forward = identity E) (family : E ⥤ Type u) :
    family.Elements ⥤ (restrict forward family).Elements :=
  compose (elementsTransport (bodyRightEq forward backward right family).symm)
    (elementsMap backward (restrict forward family))

theorem elements_right_obj (forward : D ⥤ E) (backward : E ⥤ D)
    (right : compose backward forward = identity E) (family : E ⥤ Type u) (point : family.Elements) :
    (elementsMap forward family).obj ((elementsBack forward backward right family).obj point) = point := by
  have ctx := elementsTransport_context (bodyRightEq forward backward right family).symm point
  have pointEq : forward.obj (backward.obj point.1) = point.1 :=
    congrArg (fun change : E ⥤ E => change.obj point.1) right
  exact Sigma.ext ((congrArg (fun value => forward.obj (backward.obj value)) ctx).trans pointEq)
    (elementsTransport_value (bodyRightEq forward backward right family).symm point)

theorem elements_left_obj (forward : D ⥤ E) (backward : E ⥤ D)
    (left : compose forward backward = identity D)
    (right : compose backward forward = identity E) (family : E ⥤ Type u)
    (point : (restrict forward family).Elements) :
    (elementsBack forward backward right family).obj ((elementsMap forward family).obj point) = point := by
  have ctx := elementsTransport_context (bodyRightEq forward backward right family).symm
    ((elementsMap forward family).obj point)
  have pointEq : backward.obj (forward.obj point.1) = point.1 :=
    congrArg (fun change : D ⥤ D => change.obj point.1) left
  exact Sigma.ext ((congrArg backward.obj ctx).trans pointEq)
    (elementsTransport_value (bodyRightEq forward backward right family).symm
      ((elementsMap forward family).obj point))

private theorem elementsArrow_heq (family : D ⥤ Type u)
    {first first' second second' : family.Elements} (sourceEq : first = first')
    (targetEq : second = second') (left : first ⟶ second) (right : first' ⟶ second')
    (raw : HEq left.1 right.1) : HEq left right := by
  cases sourceEq
  cases targetEq
  exact heq_of_eq (Subtype.ext (eq_of_heq raw))

theorem elements_right_inverse (forward : D ⥤ E) (backward : E ⥤ D)
    (right : compose backward forward = identity E) (family : E ⥤ Type u) :
    compose (elementsBack forward backward right family) (elementsMap forward family) =
      identity family.Elements := by
  refine Functor.hext (elements_right_obj forward backward right family) ?_
  intro first second step
  have raw := elementsTransport_arrow (bodyRightEq forward backward right family).symm step
  have transported := map_heq (compose backward forward)
    (elementsTransport_context (bodyRightEq forward backward right family).symm first)
    (elementsTransport_context (bodyRightEq forward backward right family).symm second) _ _ raw
  exact elementsArrow_heq family
    (elements_right_obj forward backward right family first)
    (elements_right_obj forward backward right family second) _ _
    (transported.trans (equalFunctor_arrow right step.1))

theorem elements_left_inverse (forward : D ⥤ E) (backward : E ⥤ D)
    (left : compose forward backward = identity D)
    (right : compose backward forward = identity E) (family : E ⥤ Type u) :
    compose (elementsMap forward family) (elementsBack forward backward right family) =
      identity (restrict forward family).Elements := by
  refine Functor.hext (elements_left_obj forward backward left right family) ?_
  intro first second step
  have raw := elementsTransport_arrow (bodyRightEq forward backward right family).symm
    ((elementsMap forward family).map step)
  have transported := map_heq backward
    (elementsTransport_context (bodyRightEq forward backward right family).symm
      ((elementsMap forward family).obj first))
    (elementsTransport_context (bodyRightEq forward backward right family).symm
      ((elementsMap forward family).obj second)) _ _ raw
  exact elementsArrow_heq (restrict forward family)
    (elements_left_obj forward backward left right family first)
    (elements_left_obj forward backward left right family second) _ _
    (transported.trans (equalFunctor_arrow left step.1))

def elementSectionEquivOfInverse (forward : D ⥤ E) (backward : E ⥤ D)
    (left : compose forward backward = identity D)
    (right : compose backward forward = identity E) (family : E ⥤ Type u)
    (body : family.Elements ⥤ Type u) :
    body.sections ≃ (restrict (elementsMap forward family) body).sections :=
  sectionEquivOfInverse (elementsMap forward family) (elementsBack forward backward right family)
    (elements_left_inverse forward backward left right family)
    (elements_right_inverse forward backward right family) body

end Cat

variable {C : Type u} [Category.{u} C]
variable {P Q : Cᵒᵖ ⥤ Type u} (change : NatTrans Q P)

private theorem elementArrow_heq (family : Cᵒᵖ ⥤ Type u)
    {first first' second second' : family.Elements} (sourceEq : first = first')
    (targetEq : second = second') (left : first ⟶ second) (right : first' ⟶ second')
    (raw : HEq left.1 right.1) : HEq left right := by
  cases sourceEq
  cases targetEq
  exact heq_of_eq (Subtype.ext (eq_of_heq raw))

def liftTarget (point : Q.Elements) (future : Future.Objects ((elementMap change).obj point)) : Q.Elements :=
  ⟨future.1.1, Q.map future.2.1 point.2⟩

def liftArrow (point : Q.Elements) (future : Future.Objects ((elementMap change).obj point)) :
    point ⟶ liftTarget change point future := CategoryOfElements.homMk _ _ future.2.1 rfl

theorem liftTarget_image (point : Q.Elements)
    (future : Future.Objects ((elementMap change).obj point)) :
    (elementMap change).obj (liftTarget change point future) = future.1 := by
  change (⟨future.1.1, change.app future.1.1 (Q.map future.2.1 point.2)⟩ : P.Elements) = future.1
  have naturally := congrArg (fun operation => operation point.2) (change.naturality future.2.1)
  exact Sigma.ext rfl (heq_of_eq (naturally.trans future.2.2))

def liftFuture (point : Q.Elements) :
    Future.Objects ((elementMap change).obj point) ⥤ Future.Objects point where
  obj future := ⟨liftTarget change point future, liftArrow change point future⟩
  map {first second} step :=
    ⟨CategoryOfElements.homMk _ _ step.1.1 (by
      have triangle := congrArg Subtype.val step.2
      change first.2.1 ≫ step.1.1 = second.2.1 at triangle
      change Q.map step.1.1 (Q.map first.2.1 point.2) = Q.map second.2.1 point.2
      exact (Q.map_comp_apply first.2.1 step.1.1 point.2).symm.trans
        (congrArg (fun arrow => Q.map arrow point.2) triangle)), by
        apply CategoryOfElements.ext Q
        change first.2.1 ≫ step.1.1 = second.2.1
        exact congrArg (fun arrow : (elementMap change).obj point ⟶ second.1 => arrow.1) step.2⟩
  map_id _ := by
    apply Subtype.ext
    apply CategoryOfElements.ext Q
    rfl
  map_comp _ _ := by
    apply Subtype.ext
    apply CategoryOfElements.ext Q
    rfl

theorem liftFuture_map_image {point : Q.Elements}
    {first second : Future.Objects ((elementMap change).obj point)} (step : first ⟶ second) :
    HEq ((elementMap change).map (((liftFuture change point).map step).1)) step.1 := by
  exact elementArrow_heq P (liftTarget_image change point first)
    (liftTarget_image change point second) _ _ (heq_of_eq rfl)

theorem future_forward_backward (point : Q.Elements)
    (future : Future.Objects ((elementMap change).obj point)) :
    (Future.map (elementMap change) point).obj ((liftFuture change point).obj future) = future := by
  exact Future.objects_ext (liftTarget_image change point future)
    (elementArrow_heq P rfl (liftTarget_image change point future) _ _ (heq_of_eq rfl))

theorem future_backward_forward (point : Q.Elements) (future : Future.Objects point) :
    (liftFuture change point).obj ((Future.map (elementMap change) point).obj future) = future := by
  have targetEq : liftTarget change point ((Future.map (elementMap change) point).obj future) = future.1 :=
    Sigma.ext rfl (heq_of_eq future.2.2)
  exact Future.objects_ext targetEq
    (elementArrow_heq Q rfl targetEq _ _ (heq_of_eq rfl))

private theorem futureArrow_heq (family : Cᵒᵖ ⥤ Type u) {point : family.Elements}
    {first first' second second' : Future.Objects point} (sourceEq : first = first')
    (targetEq : second = second') (left : first ⟶ second) (right : first' ⟶ second')
    (raw : HEq left.1.1 right.1.1) : HEq left right := by
  cases sourceEq
  cases targetEq
  exact heq_of_eq (Subtype.ext (Subtype.ext (eq_of_heq raw)))

theorem future_left_inverse (point : Q.Elements) :
    Cat.compose (Future.map (elementMap change) point) (liftFuture change point) =
      Cat.identity (Future.Objects point) := by
  refine Functor.hext (future_backward_forward change point) ?_
  intro first second step
  exact futureArrow_heq Q (future_backward_forward change point first)
    (future_backward_forward change point second) _ _ (heq_of_eq rfl)

theorem future_right_inverse (point : Q.Elements) :
    Cat.compose (liftFuture change point) (Future.map (elementMap change) point) =
      Cat.identity (Future.Objects ((elementMap change).obj point)) := by
  refine Functor.hext (future_forward_backward change point) ?_
  intro first second step
  exact futureArrow_heq P (future_forward_backward change point first)
    (future_forward_backward change point second) _ _ (heq_of_eq rfl)

/-- Exact natural-section base change on the full future categories. Both
inverse functors were constructed from the original context arrows. -/
def futureSectionEquiv (point : Q.Elements)
    (family : Future.Objects ((elementMap change).obj point) ⥤ Type u) :
    family.sections ≃ (restrict (Future.map (elementMap change) point) family).sections :=
  Cat.sectionEquivOfInverse _ _ (future_left_inverse change point)
    (future_right_inverse change point) family

def bodyReindex (domain : P.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u) :
    (PowerClassPresheafProducts.reindex change domain).Elements ⥤ Type u :=
  restrict (Cat.elementsMap (elementMap change) domain) body

theorem futureDomain_reindex (domain : P.Elements ⥤ Type u) (point : Q.Elements) :
    Future.domain (PowerClassPresheafProducts.reindex change domain) point =
      restrict (Future.map (elementMap change) point)
        (Future.domain domain ((elementMap change).obj point)) := rfl

theorem futureResult_reindex (domain : P.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u)
    (point : Q.Elements) :
    Future.result (PowerClassPresheafProducts.reindex change domain) (bodyReindex change domain body) point =
      restrict (Cat.elementsMap (Future.map (elementMap change) point)
        (Future.domain domain ((elementMap change).obj point)))
        (Future.result domain body ((elementMap change).obj point)) := rfl

/-- The contextual Π comparison is invertible because every outgoing
context arrow has the explicitly constructed unique lift above. -/
def piFibreEquiv (domain : P.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u)
    (point : Q.Elements) :
    DependentSection domain body ((elementMap change).obj point) ≃
      DependentSection (PowerClassPresheafProducts.reindex change domain) (bodyReindex change domain body) point :=
  (Future.sectionEquiv domain body ((elementMap change).obj point)).trans
    ((Cat.elementSectionEquivOfInverse (Future.map (elementMap change) point)
      (liftFuture change point) (future_left_inverse change point) (future_right_inverse change point)
      (Future.domain domain ((elementMap change).obj point))
      (Future.result domain body ((elementMap change).obj point))).trans
        ((equalityEquiv (congrArg (fun family => (family.sections : Type u))
          (futureResult_reindex change domain body point).symm)).trans
            (Future.sectionEquiv (PowerClassPresheafProducts.reindex change domain) (bodyReindex change domain body) point).symm))

theorem piFibreEquiv_value (domain : P.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u)
    (point : Q.Elements) (function : DependentSection domain body ((elementMap change).obj point))
    (next : Q.Elements) (step : point ⟶ next) (argument : (PowerClassPresheafProducts.reindex change domain).obj next) :
    (piFibreEquiv change domain body point function).app next step argument =
      function.app ((elementMap change).obj next) ((elementMap change).map step) argument := rfl

def piBaseChange (domain : P.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u) :
    NatTrans (PowerClassPresheafProducts.reindex change (dependentFunctions domain body))
      (dependentFunctions (PowerClassPresheafProducts.reindex change domain) (bodyReindex change domain body)) where
  app point := TypeCat.ofHom (piFibreEquiv change domain body point)
  naturality first second step := by
    apply ConcreteCategory.hom_ext
    intro function
    apply DependentSection.ext
    intro next later argument
    change function.app ((elementMap change).obj next)
        ((elementMap change).map step ≫ (elementMap change).map later) argument =
      function.app ((elementMap change).obj next) ((elementMap change).map (step ≫ later)) argument
    rw [(elementMap change).map_comp]

namespace Nat

variable {D : Type u} [Category.{u} D]
variable {first second : D ⥤ Type u}

def inverse (operation : NatTrans first second) (fibres : ∀ point, first.obj point ≃ second.obj point)
    (realizes : ∀ point value, operation.app point value = fibres point value) : NatTrans second first where
  app point := TypeCat.ofHom ((fibres point).symm)
  naturality source target step := by
    apply ConcreteCategory.hom_ext
    intro value
    apply (fibres target).injective
    have naturally := congrArg (fun function => function ((fibres source).symm value))
      (operation.naturality step)
    change operation.app target (first.map step ((fibres source).symm value)) =
      second.map step (operation.app source ((fibres source).symm value)) at naturally
    rw [realizes, realizes, (fibres source).apply_symm_apply] at naturally
    exact ((fibres target).apply_symm_apply _).trans naturally.symm

theorem inverse_left (operation : NatTrans first second) (fibres : ∀ point, first.obj point ≃ second.obj point)
    (realizes : ∀ point value, operation.app point value = fibres point value) :
    Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose.{u} operation (inverse operation fibres realizes) =
      Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.identity.{u} first := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro value
  exact (congrArg ((fibres point).symm) (realizes point value)).trans
    ((fibres point).symm_apply_apply value)

theorem inverse_right (operation : NatTrans first second) (fibres : ∀ point, first.obj point ≃ second.obj point)
    (realizes : ∀ point value, operation.app point value = fibres point value) :
    Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose.{u} (inverse operation fibres realizes) operation =
      Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.identity.{u} second := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro value
  exact (realizes point _).trans ((fibres point).apply_symm_apply value)

end Nat

def piBaseChangeInverse (domain : P.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u) :
    NatTrans (dependentFunctions (PowerClassPresheafProducts.reindex change domain) (bodyReindex change domain body))
      (PowerClassPresheafProducts.reindex change (dependentFunctions domain body)) :=
  Nat.inverse (piBaseChange change domain body) (piFibreEquiv change domain body) (fun _ _ => rfl)

theorem piBaseChange_left (domain : P.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u) :
    Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose.{u}
      (piBaseChange change domain body) (piBaseChangeInverse change domain body) =
        Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.identity.{u}
          (PowerClassPresheafProducts.reindex change (dependentFunctions domain body)) :=
  Nat.inverse_left (piBaseChange change domain body) (piFibreEquiv change domain body) (fun _ _ => rfl)

theorem piBaseChange_right (domain : P.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u) :
    Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose.{u}
      (piBaseChangeInverse change domain body) (piBaseChange change domain body) =
        Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.identity.{u}
          (dependentFunctions (PowerClassPresheafProducts.reindex change domain) (bodyReindex change domain body)) :=
  Nat.inverse_right (piBaseChange change domain body) (piFibreEquiv change domain body) (fun _ _ => rfl)

def comprehensionChange (domain : P.Elements ⥤ Type u) :
    NatTrans (totalSpace (PowerClassPresheafProducts.reindex change domain)) (totalSpace domain) where
  app X := TypeCat.ofHom (fun value => ⟨change.app X value.1, value.2⟩)
  naturality X Y step := by
    apply ConcreteCategory.hom_ext
    rintro ⟨argument, member⟩
    have naturally := congrArg (fun operation => operation argument) (change.naturality step)
    apply Sigma.ext naturally
    have targetEq : (⟨Y, change.app Y (Q.map step argument)⟩ : P.Elements) =
        ⟨Y, P.map step (change.app X argument)⟩ := Sigma.ext rfl (heq_of_eq naturally)
    exact CP.map_heq domain targetEq
      ((elementMap change).map (CategoryOfElements.homMk (F := Q)
        ⟨X, argument⟩ ⟨Y, Q.map step argument⟩ step rfl))
      (CategoryOfElements.homMk (F := P) ⟨X, change.app X argument⟩
        ⟨Y, P.map step (change.app X argument)⟩ step rfl)
      (elementArrow_heq P rfl targetEq _ _ (heq_of_eq rfl)) member

theorem comprehensionChange_square (domain : P.Elements ⥤ Type u) :
    Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose.{u}
        (comprehensionChange change domain) (PowerClassPresheafProducts.projection domain) =
      Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose.{u}
        (PowerClassPresheafProducts.projection (PowerClassPresheafProducts.reindex change domain)) change := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro _
  rfl

theorem indexedBody_reindex (domain : P.Elements ⥤ Type u)
    (body : (totalSpace domain).Elements ⥤ Type u) :
    indexedBody (PowerClassPresheafProducts.reindex change domain)
        (PowerClassPresheafProducts.reindex (comprehensionChange change domain) body) =
      bodyReindex change domain (indexedBody domain body) := by
  refine Functor.hext (fun _ => rfl) ?_
  intro first second step
  apply heq_of_eq
  have same : (elementMap (comprehensionChange change domain)).map
      ((displayedToTotalElements (PowerClassPresheafProducts.reindex change domain)).map step) =
    (displayedToTotalElements domain).map ((Cat.elementsMap (elementMap change) domain).map step) := by
    apply CategoryOfElements.ext (totalSpace domain)
    exact (displayedToTotalElements_underlying _ step).trans
      (displayedToTotalElements_underlying _ ((Cat.elementsMap (elementMap change) domain).map step)).symm
  exact congrArg body.map same

/-- Actual formation comparison over the original comprehension square. -/
theorem pi_comprehension_baseChange (domain : P.Elements ⥤ Type u)
    (body : (totalSpace domain).Elements ⥤ Type u) :
    piFamily (PowerClassPresheafProducts.reindex change domain)
        (PowerClassPresheafProducts.reindex (comprehensionChange change domain) body) =
      dependentFunctions (PowerClassPresheafProducts.reindex change domain)
        (bodyReindex change domain (indexedBody domain body)) :=
  congrArg (dependentFunctions (PowerClassPresheafProducts.reindex change domain))
    (indexedBody_reindex change domain body)

theorem sigmaBaseChange (domain : P.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u) :
    PowerClassPresheafProducts.reindex change (IndexedSigma.family domain body) =
      IndexedSigma.family (PowerClassPresheafProducts.reindex change domain) (bodyReindex change domain body) := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

theorem sigma_comprehension_baseChange (domain : P.Elements ⥤ Type u)
    (body : (totalSpace domain).Elements ⥤ Type u) :
    PowerClassPresheafProducts.reindex change (sigmaFamily domain body) =
      sigmaFamily (PowerClassPresheafProducts.reindex change domain)
        (PowerClassPresheafProducts.reindex (comprehensionChange change domain) body) :=
  (sigmaBaseChange change domain (indexedBody domain body)).trans
    (congrArg (IndexedSigma.family (PowerClassPresheafProducts.reindex change domain))
      (indexedBody_reindex change domain body).symm)

def sigmaContextAt (domain : P.Elements ⥤ Type u) (body : (totalSpace domain).Elements ⥤ Type u)
    (point : Cᵒᵖ) : (totalSpace (sigmaFamily domain body)).obj point ≃ (totalSpace body).obj point where
  toFun value := ⟨⟨value.1, value.2.1⟩, value.2.2⟩
  invFun value := ⟨value.1.1, ⟨value.1.2, value.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The sum's actual total presheaf is the iterated comprehension, with
both dependent coordinates retained under context arrows. -/
def sigmaContext (domain : P.Elements ⥤ Type u) (body : (totalSpace domain).Elements ⥤ Type u) :
    NatTrans (totalSpace (sigmaFamily domain body)) (totalSpace body) where
  app point := TypeCat.ofHom (sigmaContextAt domain body point)
  naturality X Y step := by
    apply ConcreteCategory.hom_ext
    rintro ⟨base, ⟨argument, member⟩⟩
    have same : (displayedToTotalElements domain).map
        (argumentMap domain (CategoryOfElements.homMk (F := P)
          ⟨X, base⟩ ⟨Y, P.map step base⟩ step rfl) argument) =
      CategoryOfElements.homMk (F := totalSpace domain)
        ⟨X, ⟨base, argument⟩⟩ ⟨Y, (totalSpace domain).map step ⟨base, argument⟩⟩ step rfl := by
      apply CategoryOfElements.ext (totalSpace domain)
      exact displayedToTotalElements_underlying domain _
    exact congrArg (fun value =>
      (⟨(totalSpace domain).map step ⟨base, argument⟩, value⟩ : (totalSpace body).obj Y))
        (congrArg (fun arrow => body.map arrow member) same)

def sigmaContextInverse (domain : P.Elements ⥤ Type u) (body : (totalSpace domain).Elements ⥤ Type u) :
    NatTrans (totalSpace body) (totalSpace (sigmaFamily domain body)) :=
  Nat.inverse (sigmaContext domain body) (sigmaContextAt domain body) (fun _ _ => rfl)

theorem sigmaContext_left (domain : P.Elements ⥤ Type u) (body : (totalSpace domain).Elements ⥤ Type u) :
    Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose.{u}
      (sigmaContext domain body) (sigmaContextInverse domain body) =
        Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.identity.{u} (totalSpace (sigmaFamily domain body)) :=
  Nat.inverse_left (sigmaContext domain body) (sigmaContextAt domain body) (fun _ _ => rfl)

theorem sigmaContext_right (domain : P.Elements ⥤ Type u) (body : (totalSpace domain).Elements ⥤ Type u) :
    Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose.{u}
      (sigmaContextInverse domain body) (sigmaContext domain body) =
        Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.identity.{u} (totalSpace body) :=
  Nat.inverse_right (sigmaContext domain body) (sigmaContextAt domain body) (fun _ _ => rfl)

theorem sigmaContext_projection (domain : P.Elements ⥤ Type u)
    (body : (totalSpace domain).Elements ⥤ Type u) :
    Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose.{u}
      (Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose.{u}
        (sigmaContext domain body) (PowerClassPresheafProducts.projection body))
        (PowerClassPresheafProducts.projection domain) =
      PowerClassPresheafProducts.projection (sigmaFamily domain body) := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro _
  rfl

theorem reindex_identity (family : P.Elements ⥤ Type u) :
    PowerClassPresheafProducts.reindex
      (Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.identity.{u} P) family = family := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

theorem reindex_comp {R : Cᵒᵖ ⥤ Type u} (earlier : NatTrans R Q) (later : NatTrans Q P)
    (family : P.Elements ⥤ Type u) :
    PowerClassPresheafProducts.reindex earlier (PowerClassPresheafProducts.reindex later family) =
      PowerClassPresheafProducts.reindex
        (Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose.{u} earlier later) family := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

theorem piBaseChange_identity (domain : P.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u)
    (point : P.Elements) (function : DependentSection domain body point) :
    piFibreEquiv (Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.identity.{u} P)
        domain body point function = function := by
  apply DependentSection.ext
  intro _ _ _
  rfl

theorem piBaseChange_comp {R : Cᵒᵖ ⥤ Type u} (earlier : NatTrans R Q) (later : NatTrans Q P)
    (domain : P.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u) (point : R.Elements)
    (function : DependentSection domain body
      ((elementMap (Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose.{u} earlier later)).obj point)) :
    piFibreEquiv earlier (PowerClassPresheafProducts.reindex later domain) (bodyReindex later domain body)
        point (piFibreEquiv later domain body ((elementMap earlier).obj point) function) =
      piFibreEquiv (Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose.{u} earlier later)
        domain body point function := by
  apply DependentSection.ext
  intro _ _ _
  rfl

/-- Lambda substitution preserves the entire future table, including
future values that were unavailable in the present fibre. -/
theorem piLambda_substitution_value (domain : P.Elements ⥤ Type u)
    (body : (totalSpace domain).Elements ⥤ Type u) (term : body.sections)
    (first second : Q.Elements) (step : first ⟶ second)
    (argument : (PowerClassPresheafProducts.reindex change domain).obj second) :
    ((piLambda (reindexSection (comprehensionChange change domain) body term)).val first).app second step argument =
      (piFibreEquiv change domain (indexedBody domain body) first
        ((piLambda term).val ((elementMap change).obj first))).app second step argument := rfl

namespace Adjoint

variable {D : Type u} [Category.{u} D]

def castDomain {first second result : D ⥤ Type u} (same : first = second)
    (operation : NatTrans first result) : NatTrans second result :=
  equalityEquiv (congrArg (fun family => NatTrans family result) same) operation

theorem castDomain_value {first second result : D ⥤ Type u} (same : first = second)
    (operation : NatTrans first result) (point : D) (earlier : first.obj point) (later : second.obj point)
    (sameValue : HEq earlier later) : (castDomain same operation).app point later = operation.app point earlier := by
  cases same
  cases eq_of_heq sameValue
  rfl

def castCodomain {parameters first second : D ⥤ Type u} (same : first = second)
    (operation : NatTrans parameters first) : NatTrans parameters second :=
  equalityEquiv (congrArg (fun family => NatTrans parameters family) same) operation

theorem castCodomain_value {parameters first second : D ⥤ Type u} (same : first = second)
    (operation : NatTrans parameters first) (point : D) (argument : parameters.obj point) :
    HEq ((castCodomain same operation).app point argument) (operation.app point argument) := by
  cases same
  rfl

variable (domain : P.Elements ⥤ Type u) (body : (totalSpace domain).Elements ⥤ Type u)

theorem piHomEquiv_value (parameters : P.Elements ⥤ Type u)
    (operation : NatTrans (PowerClassPresheafProducts.reindex
      (PowerClassPresheafProducts.projection domain) parameters) body)
    (first second : P.Elements) (step : first ⟶ second) (parameter : parameters.obj first)
    (argument : domain.obj second) :
    ((piHomEquiv domain body parameters operation).app first parameter).app second step argument =
      operation.app ((displayedToTotalElements domain).obj ⟨second, argument⟩)
        (parameters.map step parameter) := by
  change (castDomain (indexedBody_projection domain parameters)
    (regroupNatEquiv domain _ body operation)).app ⟨second, argument⟩ (parameters.map step parameter) = _
  exact castDomain_value (indexedBody_projection domain parameters) _ _ _ _ (heq_of_eq rfl)

def piMap {other : (totalSpace domain).Elements ⥤ Type u} (operation : NatTrans body other) :
    NatTrans (piFamily domain body) (piFamily domain other) :=
  mapFamily (CP.restrictNat (displayedToTotalElements domain) operation)

theorem pi_natural_parameters {first second : P.Elements ⥤ Type u}
    (earlier : NatTrans first second)
    (operation : NatTrans (PowerClassPresheafProducts.reindex
      (PowerClassPresheafProducts.projection domain) second) body) :
    piHomEquiv domain body first
        (Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose.{u}
          (CP.restrictNat (elementMap (PowerClassPresheafProducts.projection domain)) earlier) operation) =
      Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose.{u} earlier
        (piHomEquiv domain body second operation) := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro parameter
  apply DependentSection.ext
  intro next step argument
  change ((piHomEquiv domain body first _).app point parameter).app next step argument =
    ((piHomEquiv domain body second operation).app point (earlier.app point parameter)).app next step argument
  rw [piHomEquiv_value, piHomEquiv_value]
  exact congrArg (operation.app ((displayedToTotalElements domain).obj ⟨next, argument⟩))
    (congrArg (fun function => function parameter) (earlier.naturality step))

theorem pi_natural_codomain {other : (totalSpace domain).Elements ⥤ Type u}
    (parameters : P.Elements ⥤ Type u)
    (operation : NatTrans (PowerClassPresheafProducts.reindex
      (PowerClassPresheafProducts.projection domain) parameters) body)
    (later : NatTrans body other) :
    piHomEquiv domain other parameters
        (Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose.{u} operation later) =
      Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose.{u}
        (piHomEquiv domain body parameters operation) (piMap domain body later) := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro parameter
  apply DependentSection.ext
  intro next step argument
  change ((piHomEquiv domain other parameters _).app point parameter).app next step argument =
    later.app ((displayedToTotalElements domain).obj ⟨next, argument⟩)
      (((piHomEquiv domain body parameters operation).app point parameter).app next step argument)
  rw [piHomEquiv_value, piHomEquiv_value]
  rfl

theorem sigmaHomEquiv_value (result : P.Elements ⥤ Type u)
    (operation : NatTrans (sigmaFamily domain body) result) (point : (totalSpace domain).Elements)
    (member : body.obj point) :
    (sigmaHomEquiv domain body result operation).app point member =
      operation.app ⟨point.1, point.2.1⟩ ⟨point.2.2, member⟩ := by
  change (castCodomain (indexedBody_projection domain result).symm
    (IndexedSigma.homEquiv domain (indexedBody domain body) result operation)).app
      ((totalElementsToDisplayed domain).obj point) member = _
  exact eq_of_heq (castCodomain_value (indexedBody_projection domain result).symm _ _ _)

def sumMap {other : (totalSpace domain).Elements ⥤ Type u} (operation : NatTrans body other) :
    NatTrans (sigmaFamily domain body) (sigmaFamily domain other) where
  app point := TypeCat.ofHom (fun value =>
    ⟨value.1, operation.app ((displayedToTotalElements domain).obj ⟨point, value.1⟩) value.2⟩)
  naturality first second step := by
    apply ConcreteCategory.hom_ext
    rintro ⟨argument, member⟩
    exact Sigma.ext rfl (heq_of_eq (congrArg (fun function => function member)
      (operation.naturality ((displayedToTotalElements domain).map (argumentMap domain step argument)))))

theorem sigma_natural_codomain {other : (totalSpace domain).Elements ⥤ Type u}
    (earlier : NatTrans other body) (result : P.Elements ⥤ Type u)
    (operation : NatTrans (sigmaFamily domain body) result) :
    sigmaHomEquiv domain other result
        (Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose.{u} (sumMap domain other earlier) operation) =
      Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose.{u} earlier
        (sigmaHomEquiv domain body result operation) := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro member
  change (sigmaHomEquiv domain other result _).app point member =
    (sigmaHomEquiv domain body result operation).app point (earlier.app point member)
  rw [sigmaHomEquiv_value, sigmaHomEquiv_value]
  rcases point with ⟨_, ⟨_, _⟩⟩
  rfl

theorem sigma_natural_result {first second : P.Elements ⥤ Type u}
    (operation : NatTrans (sigmaFamily domain body) first) (later : NatTrans first second) :
    sigmaHomEquiv domain body second
        (Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose.{u} operation later) =
      Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose.{u}
        (sigmaHomEquiv domain body first operation)
        (CP.restrictNat (elementMap (PowerClassPresheafProducts.projection domain)) later) := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro member
  change (sigmaHomEquiv domain body second _).app point member =
    later.app ⟨point.1, point.2.1⟩ ((sigmaHomEquiv domain body first operation).app point member)
  rw [sigmaHomEquiv_value, sigmaHomEquiv_value]
  rfl

end Adjoint

end Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassPresheafBaseChange
