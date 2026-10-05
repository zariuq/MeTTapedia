import Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassPresheafDescent
import Mettapedia.GSLT.Topos.ConstructivePresheafDependentFunctions

/-!
# Constructive contextual products and sums of material-family models

The displayed domain is a genuine functor on a presheaf's category of
elements. Its dependent function object contains compatible functions at
every future restriction, not only a function in the current fibre. The
dependent codomain is regrouped from actual presheaf comprehension without
choosing representatives. The resulting hom equivalences retain the
actual arguments, values and restriction arrows.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassPresheafProducts

open CategoryTheory
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.TypeTheory.DisplayedPresheafComprehension
open Mettapedia.TypeTheory.DisplayedPresheafIndexedCwfBridge
open Mettapedia.TypeTheory.DependentFamilySectionDescent

namespace CP

open Mettapedia.GSLT.Topos.ConstructivePresheaf

universe u
variable {D E : Type u} [Category.{u} D] [Category.{u} E]

def unitFamily : D ⥤ Type u where
  obj _ := PUnit.{u + 1}
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def sectionHomEquiv (family : D ⥤ Type u) : family.sections ≃ NatTrans unitFamily family where
  toFun term :=
    { app point := TypeCat.ofHom (fun _ => term.val point)
      naturality first second step := by
        apply ConcreteCategory.hom_ext
        intro _
        exact (term.property step).symm }
  invFun operation :=
    ⟨fun point => operation.app point PUnit.unit, by
      intro first second step
      exact (congrArg (fun map => map PUnit.unit) (operation.naturality step)).symm⟩
  left_inv term := rfl
  right_inv operation := by
    apply NatTrans.ext
    funext point
    apply ConcreteCategory.hom_ext
    intro value
    cases value
    rfl

def restrictSection (change : D ⥤ E) (family : E ⥤ Type u) (term : family.sections) :
    (restrict change family).sections :=
  ⟨fun point => term.val (change.obj point), by
    intro first second step
    exact term.property (change.map step)⟩

def restrictNat (change : D ⥤ E) {first second : E ⥤ Type u} (operation : NatTrans first second) :
    NatTrans (restrict change first) (restrict change second) where
  app point := operation.app (change.obj point)
  naturality _ _ step := operation.naturality (change.map step)

theorem map_heq (family : D ⥤ Type u) {first second other : D} (same : second = other)
    (left : first ⟶ second) (right : first ⟶ other) (sameArrow : HEq left right)
    (member : family.obj first) : HEq (family.map left member) (family.map right member) := by
  cases same
  cases eq_of_heq sameArrow
  rfl

def castSection {first second : D ⥤ Type u} (same : first = second) (term : first.sections) :
    second.sections := equalityEquiv (congrArg (fun family : D ⥤ Type u => (family.sections : Type u)) same) term

theorem castSection_value {first second : D ⥤ Type u} (same : first = second)
    (term : first.sections) (point : D) : HEq ((castSection same term).val point) (term.val point) := by
  cases same
  rfl

theorem castSection_reverse {first second : D ⥤ Type u} (same : first = second)
    (term : first.sections) : castSection same.symm (castSection same term) = term := by
  cases same
  rfl

end CP

open Mettapedia.GSLT.Topos.ConstructivePresheaf
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent

universe u
variable {C : Type u} [Category.{u} C]
variable {P Q : Cᵒᵖ ⥤ Type u}

/-- Actual comprehension projection, with explicit naturality rather than
the functor-category identity helpers. -/
def projection (family : DisplayedFamily.{u, u, u, u} P) : NatTrans (totalSpace family) P where
  app _ := TypeCat.ofHom Sigma.fst
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro _
    rfl

def sectionMap (family : DisplayedFamily.{u, u, u, u} P) (term : family.sections) :
    NatTrans P (totalSpace family) where
  app point := TypeCat.ofHom (fun value => ⟨value, term.val ⟨point, value⟩⟩)
  naturality first second step := by
    apply ConcreteCategory.hom_ext
    intro value
    exact congrArg (fun member =>
      (⟨P.map step value, member⟩ : TotalAt family second))
      (term.property (CategoryOfElements.homMk (F := P)
        ⟨first, value⟩ ⟨second, P.map step value⟩ step rfl)).symm

/-- Natural base change with explicit element-category laws. -/
def elementMap (change : NatTrans Q P) : Q.Elements ⥤ P.Elements where
  obj point := ⟨point.1, change.app point.1 point.2⟩
  map {first second} step := ⟨step.1, by
    have naturally := congrArg (fun map => map first.2) (change.naturality step.1)
    exact naturally.symm.trans (congrArg (change.app second.1) step.2)⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def reindex (change : NatTrans Q P) (family : DisplayedFamily.{u, u, u, u} P) :
    DisplayedFamily.{u, u, u, u} Q := restrict (elementMap change) family

def reindexSection (change : NatTrans Q P) (family : DisplayedFamily.{u, u, u, u} P)
    (term : family.sections) : (reindex change family).sections :=
  CP.restrictSection (elementMap change) family term

def lastVariable (domain : DisplayedFamily.{u, u, u, u} P) :
    (reindex (projection domain) domain).sections :=
  ⟨fun point => point.2.2, by
    intro first second step
    rcases first with ⟨X, ⟨argument, member⟩⟩
    rcases second with ⟨Y, ⟨nextArgument, nextMember⟩⟩
    rcases step with ⟨step, follows⟩
    change X ⟶ Y at step
    change (⟨P.map step argument,
      domain.map (CategoryOfElements.homMk _ _ step rfl) member⟩ : TotalAt domain Y) =
        ⟨nextArgument, nextMember⟩ at follows
    have firstEq := (Sigma.mk.inj_iff.mp follows).1
    have secondEq := (Sigma.mk.inj_iff.mp follows).2
    have targetEq : (⟨Y, P.map step argument⟩ : P.Elements) = ⟨Y, nextArgument⟩ :=
      Sigma.ext rfl (heq_of_eq firstEq)
    have arrows : HEq (CategoryOfElements.homMk (F := P) ⟨X, argument⟩
      ⟨Y, P.map step argument⟩ step rfl)
        ((elementMap (projection domain)).map
          (CategoryOfElements.homMk (F := totalSpace domain)
            ⟨X, ⟨argument, member⟩⟩ ⟨Y, ⟨nextArgument, nextMember⟩⟩ step follows)) := by
      cases firstEq
      rfl
    exact eq_of_heq ((CP.map_heq domain targetEq _ _ arrows member).symm.trans secondEq)⟩

theorem reindex_section_projection (domain : DisplayedFamily.{u, u, u, u} P)
    (argument : domain.sections) :
    reindex (sectionMap domain argument) (reindex (projection domain) domain) = domain := by
  refine Functor.hext (fun _ => rfl) ?_
  intro first second step
  apply heq_of_eq
  have projected : (elementMap (projection domain)).map
      ((elementMap (sectionMap domain argument)).map step) = step := by
    apply CategoryOfElements.ext P
    rfl
  exact congrArg domain.map projected

theorem lastVariable_value (domain : DisplayedFamily.{u, u, u, u} P)
    (point : (totalSpace domain).Elements) : (lastVariable domain).val point = point.2.2 := rfl

def indexedBody (domain : DisplayedFamily.{u, u, u, u} P)
    (codomain : DisplayedFamily.{u, u, u, u} (totalSpace domain)) : domain.Elements ⥤ Type u :=
  restrict (displayedToTotalElements domain) codomain

theorem regroup_arrow_roundtrip (domain : DisplayedFamily.{u, u, u, u} P)
    {first second : (totalSpace domain).Elements} (step : first ⟶ second) :
    (displayedToTotalElements domain).map ((totalElementsToDisplayed domain).map step) = step := by
  apply CategoryOfElements.ext (totalSpace domain)
  rw [displayedToTotalElements_underlying, totalElementsToDisplayed_underlying]

theorem ungroup_arrow_roundtrip (domain : DisplayedFamily.{u, u, u, u} P)
    {first second : domain.Elements} (step : first ⟶ second) :
    (totalElementsToDisplayed domain).map ((displayedToTotalElements domain).map step) = step := by
  apply CategoryOfElements.ext domain
  apply CategoryOfElements.ext P
  rw [totalElementsToDisplayed_underlying, displayedToTotalElements_underlying]

/-- Regrouping retains natural operations on the entire comprehension
category, including actual arrow and dependent-value conditions. -/
def regroupNatEquiv (domain : DisplayedFamily.{u, u, u, u} P)
    (first second : DisplayedFamily.{u, u, u, u} (totalSpace domain)) :
    NatTrans first second ≃ NatTrans (indexedBody domain first) (indexedBody domain second) where
  toFun := CP.restrictNat (displayedToTotalElements domain)
  invFun operation :=
    { app point := operation.app ((totalElementsToDisplayed domain).obj point)
      naturality firstPoint secondPoint step := by
        have naturally := operation.naturality ((totalElementsToDisplayed domain).map step)
        change first.map ((displayedToTotalElements domain).map ((totalElementsToDisplayed domain).map step)) ≫
            operation.app ((totalElementsToDisplayed domain).obj secondPoint) =
          operation.app ((totalElementsToDisplayed domain).obj firstPoint) ≫
            second.map ((displayedToTotalElements domain).map ((totalElementsToDisplayed domain).map step)) at naturally
        rw [regroup_arrow_roundtrip] at naturally
        exact naturally }
  left_inv operation := by
    apply NatTrans.ext
    funext point
    rcases point with ⟨context, ⟨value, member⟩⟩
    rfl
  right_inv operation := by
    apply NatTrans.ext
    funext point
    rcases point with ⟨⟨context, value⟩, member⟩
    rfl

def regroupSectionEquiv (domain : DisplayedFamily.{u, u, u, u} P)
    (codomain : DisplayedFamily.{u, u, u, u} (totalSpace domain)) :
    codomain.sections ≃ (indexedBody domain codomain).sections where
  toFun := CP.restrictSection (displayedToTotalElements domain) codomain
  invFun term := ⟨fun point => term.val ((totalElementsToDisplayed domain).obj point), by
    intro first second step
    have naturally := term.property ((totalElementsToDisplayed domain).map step)
    change codomain.map ((displayedToTotalElements domain).map ((totalElementsToDisplayed domain).map step))
        (term.val ((totalElementsToDisplayed domain).obj first)) =
      term.val ((totalElementsToDisplayed domain).obj second) at naturally
    rw [regroup_arrow_roundtrip] at naturally
    exact naturally⟩
  left_inv term := by
    apply Subtype.ext
    funext point
    rcases point with ⟨context, ⟨value, member⟩⟩
    rfl
  right_inv term := by
    apply Subtype.ext
    funext point
    rcases point with ⟨⟨context, value⟩, member⟩
    rfl

/-- Actual compatible functions at every future element-category arrow. -/
def piFamily (domain : DisplayedFamily.{u, u, u, u} P)
    (codomain : DisplayedFamily.{u, u, u, u} (totalSpace domain)) :
    DisplayedFamily.{u, u, u, u} P :=
  dependentFunctions domain (indexedBody domain codomain)

theorem indexedBody_projection (domain : DisplayedFamily.{u, u, u, u} P)
    (parameters : DisplayedFamily.{u, u, u, u} P) :
    indexedBody domain (reindex (projection domain) parameters) = overElements domain parameters := by
  refine Functor.hext (fun _ => rfl) ?_
  intro first second step
  apply heq_of_eq
  have projected : (elementMap (projection domain)).map
      ((displayedToTotalElements domain).map step) = step.1 := by
    apply CategoryOfElements.ext P
    exact displayedToTotalElements_underlying domain step
  exact congrArg parameters.map projected

/-- Restriction along the comprehension projection is left adjoint to this
actual all-future dependent product, by a constructed hom equivalence. -/
def piHomEquiv (domain : DisplayedFamily.{u, u, u, u} P)
    (codomain : DisplayedFamily.{u, u, u, u} (totalSpace domain))
    (parameters : DisplayedFamily.{u, u, u, u} P) :
    NatTrans (reindex (projection domain) parameters) codomain ≃
      NatTrans parameters (piFamily domain codomain) :=
  (regroupNatEquiv domain (reindex (projection domain) parameters) codomain).trans
    ((equalityEquiv (congrArg (fun family => NatTrans family (indexedBody domain codomain))
      (indexedBody_projection domain parameters))).trans
        (dependentHomEquiv domain (indexedBody domain codomain) parameters))

/-- Natural body sections and full contextual function sections, without
the legacy constant-functor or right-Kan representative wrappers. -/
def piSectionEquiv (domain : DisplayedFamily.{u, u, u, u} P)
    (codomain : DisplayedFamily.{u, u, u, u} (totalSpace domain)) :
    codomain.sections ≃ (piFamily domain codomain).sections :=
  (regroupSectionEquiv domain codomain).trans
    ((CP.sectionHomEquiv (indexedBody domain codomain)).trans
      ((dependentHomEquiv domain (indexedBody domain codomain) CP.unitFamily).trans
        (CP.sectionHomEquiv (piFamily domain codomain)).symm))

def piLambda {domain : DisplayedFamily.{u, u, u, u} P}
    {codomain : DisplayedFamily.{u, u, u, u} (totalSpace domain)} (body : codomain.sections) :
    (piFamily domain codomain).sections := piSectionEquiv domain codomain body

theorem piLambda_value {domain : DisplayedFamily.{u, u, u, u} P}
    {codomain : DisplayedFamily.{u, u, u, u} (totalSpace domain)} (body : codomain.sections)
    (first second : P.Elements) (step : first ⟶ second) (argument : domain.obj second) :
    ((piLambda body).val first).app second step argument =
      body.val ((displayedToTotalElements domain).obj ⟨second, argument⟩) := rfl

def piBody {domain : DisplayedFamily.{u, u, u, u} P}
    {codomain : DisplayedFamily.{u, u, u, u} (totalSpace domain)}
    (function : (piFamily domain codomain).sections) : codomain.sections :=
  (piSectionEquiv domain codomain).symm function

theorem piBody_value {domain : DisplayedFamily.{u, u, u, u} P}
    {codomain : DisplayedFamily.{u, u, u, u} (totalSpace domain)}
    (function : (piFamily domain codomain).sections) (point : (totalSpace domain).Elements) :
    (piBody function).val point =
      (function.val ⟨point.1, point.2.1⟩).app ⟨point.1, point.2.1⟩ (𝟙 _) point.2.2 := rfl

theorem piBody_lambda {domain : DisplayedFamily.{u, u, u, u} P}
    {codomain : DisplayedFamily.{u, u, u, u} (totalSpace domain)} (body : codomain.sections) :
    piBody (piLambda body) = body := (piSectionEquiv domain codomain).symm_apply_apply body

theorem piLambda_body {domain : DisplayedFamily.{u, u, u, u} P}
    {codomain : DisplayedFamily.{u, u, u, u} (totalSpace domain)}
    (function : (piFamily domain codomain).sections) :
    piLambda (piBody function) = function := (piSectionEquiv domain codomain).apply_symm_apply function

def piApply {domain : DisplayedFamily.{u, u, u, u} P}
    {codomain : DisplayedFamily.{u, u, u, u} (totalSpace domain)}
    (function : (piFamily domain codomain).sections) (argument : domain.sections) :
    (reindex (sectionMap domain argument) codomain).sections :=
  reindexSection (sectionMap domain argument) codomain (piBody function)

theorem piApply_value {domain : DisplayedFamily.{u, u, u, u} P}
    {codomain : DisplayedFamily.{u, u, u, u} (totalSpace domain)}
    (function : (piFamily domain codomain).sections) (argument : domain.sections) (point : P.Elements) :
    (piApply function argument).val point =
      (function.val point).app point (𝟙 point) (argument.val point) := rfl

theorem pi_beta {domain : DisplayedFamily.{u, u, u, u} P}
    {codomain : DisplayedFamily.{u, u, u, u} (totalSpace domain)}
    (body : codomain.sections) (argument : domain.sections) :
    piApply (piLambda body) argument = reindexSection (sectionMap domain argument) codomain body :=
  congrArg (reindexSection (sectionMap domain argument) codomain) (piBody_lambda body)

namespace IndexedSigma

variable {D : Type u} [Category.{u} D]
variable (A : D ⥤ Type u) (B : A.Elements ⥤ Type u)

private theorem map_heq {first second other : A.Elements} (same : second = other)
    (left : first ⟶ second) (right : first ⟶ other) (sameArrow : HEq left.1 right.1)
    (member : B.obj first) : HEq (B.map left member) (B.map right member) := by
  cases same
  have arrows : left = right := Subtype.ext (eq_of_heq sameArrow)
  cases arrows
  rfl

def family : D ⥤ Type u where
  obj point := Σ argument : A.obj point, B.obj ⟨point, argument⟩
  map step := TypeCat.ofHom (fun value =>
    ⟨A.map step value.1, B.map (argumentMap A step value.1) value.2⟩)
  map_id point := by
    apply ConcreteCategory.hom_ext
    rintro ⟨argument, member⟩
    apply Sigma.ext (A.map_id_apply point argument)
    have targetEq : (⟨point, A.map (𝟙 point) argument⟩ : A.Elements) = ⟨point, argument⟩ :=
      Sigma.ext rfl (heq_of_eq (A.map_id_apply point argument))
    exact (map_heq A B targetEq (argumentMap A (𝟙 point) argument) (𝟙 _) (heq_of_eq rfl) member).trans
      (heq_of_eq (B.map_id_apply _ member))
  map_comp {first middle last} earlier later := by
    apply ConcreteCategory.hom_ext
    rintro ⟨argument, member⟩
    apply Sigma.ext (A.map_comp_apply earlier later argument)
    have targetEq :
        (⟨last, A.map (earlier ≫ later) argument⟩ : A.Elements) =
          ⟨last, A.map later (A.map earlier argument)⟩ :=
      Sigma.ext rfl (heq_of_eq (A.map_comp_apply earlier later argument))
    exact (map_heq A B targetEq (argumentMap A (earlier ≫ later) argument)
      (argumentMap A earlier argument ≫ argumentMap A later (A.map earlier argument)) (heq_of_eq rfl) member).trans
        (heq_of_eq (B.map_comp_apply _ _ member))

def homEquiv (H : D ⥤ Type u) : NatTrans (family A B) H ≃ NatTrans B (overElements A H) where
  toFun operation :=
    { app point := TypeCat.ofHom (fun member => operation.app point.1 ⟨point.2, member⟩)
      naturality first second step := by
        rcases first with ⟨X, argument⟩
        rcases second with ⟨Y, nextArgument⟩
        rcases step with ⟨step, follows⟩
        change X ⟶ Y at step
        change A.map step argument = nextArgument at follows
        subst nextArgument
        apply ConcreteCategory.hom_ext
        intro member
        exact congrArg (fun map => map ⟨argument, member⟩) (operation.naturality step) }
  invFun operation :=
    { app point := TypeCat.ofHom (fun value => operation.app ⟨point, value.1⟩ value.2)
      naturality first second step := by
        apply ConcreteCategory.hom_ext
        rintro ⟨argument, member⟩
        exact congrArg (fun map => map member) (operation.naturality (argumentMap A step argument)) }
  left_inv operation := by
    apply NatTrans.ext
    funext point
    apply ConcreteCategory.hom_ext
    rintro ⟨_, _⟩
    rfl
  right_inv operation := by
    apply NatTrans.ext
    funext point
    rcases point with ⟨_, _⟩
    apply ConcreteCategory.hom_ext
    intro _
    rfl

def lift (first : A.sections) : D ⥤ A.Elements where
  obj point := ⟨point, first.val point⟩
  map step := ⟨step, first.property step⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def pair (first : A.sections) (second : (restrict (lift A first) B).sections) :
    (family A B).sections :=
  ⟨fun point => ⟨first.val point, second.val point⟩, by
    intro X Y step
    apply Sigma.ext (first.property step)
    have targetEq : (⟨Y, A.map step (first.val X)⟩ : A.Elements) = ⟨Y, first.val Y⟩ :=
      Sigma.ext rfl (heq_of_eq (first.property step))
    exact (map_heq A B targetEq (argumentMap A step (first.val X))
      ((lift A first).map step) (heq_of_eq rfl) (second.val X)).trans
        (heq_of_eq (second.property step))⟩

def fst (term : (family A B).sections) : A.sections :=
  ⟨fun point => (term.val point).1, by
    intro X Y step
    exact congrArg Sigma.fst (term.property step)⟩

def snd (term : (family A B).sections) : (restrict (lift A (fst A B term)) B).sections :=
  ⟨fun point => (term.val point).2, by
    intro X Y step
    have naturally := term.property step
    change (⟨A.map step (term.val X).1,
      B.map (argumentMap A step (term.val X).1) (term.val X).2⟩ : (family A B).obj Y) =
        term.val Y at naturally
    have targetEq : (⟨Y, A.map step (term.val X).1⟩ : A.Elements) = ⟨Y, (term.val Y).1⟩ :=
      Sigma.ext rfl (heq_of_eq (congrArg Sigma.fst naturally))
    have secondEq : HEq (B.map (argumentMap A step (term.val X).1) (term.val X).2) (term.val Y).2 :=
      (Sigma.mk.inj_iff.mp naturally).2
    exact eq_of_heq ((map_heq A B targetEq (argumentMap A step (term.val X).1)
      ((lift A (fst A B term)).map step) (heq_of_eq rfl) (term.val X).2).symm.trans secondEq)⟩

theorem fst_pair (first : A.sections) (second : (restrict (lift A first) B).sections) :
    fst A B (pair A B first second) = first := rfl

theorem snd_pair (first : A.sections) (second : (restrict (lift A first) B).sections) :
    snd A B (pair A B first second) = second := rfl

theorem pair_fst_snd (term : (family A B).sections) :
    pair A B (fst A B term) (snd A B term) = term := by
  apply Subtype.ext
  funext point
  exact Sigma.eta (term.val point)

def sectionEquiv : (family A B).sections ≃
    (Σ first : A.sections, (restrict (lift A first) B).sections) where
  toFun term := ⟨fst A B term, snd A B term⟩
  invFun term := pair A B term.1 term.2
  left_inv := pair_fst_snd A B
  right_inv term := by
    rcases term with ⟨first, second⟩
    rfl

end IndexedSigma

def sigmaFamily (domain : DisplayedFamily.{u, u, u, u} P)
    (codomain : DisplayedFamily.{u, u, u, u} (totalSpace domain)) :
    DisplayedFamily.{u, u, u, u} P :=
  IndexedSigma.family domain (indexedBody domain codomain)

/-- The actual contextual dependent sum is left adjoint to restriction along
comprehension, with all evidence coordinates retained. -/
def sigmaHomEquiv (domain : DisplayedFamily.{u, u, u, u} P)
    (codomain : DisplayedFamily.{u, u, u, u} (totalSpace domain))
    (result : DisplayedFamily.{u, u, u, u} P) :
    NatTrans (sigmaFamily domain codomain) result ≃
      NatTrans codomain (reindex (projection domain) result) :=
  (IndexedSigma.homEquiv domain (indexedBody domain codomain) result).trans
    ((equalityEquiv (congrArg (fun family => NatTrans (indexedBody domain codomain) family)
      (indexedBody_projection domain result).symm)).trans
        (regroupNatEquiv domain codomain (reindex (projection domain) result)).symm)

theorem indexedBody_lift (domain : DisplayedFamily.{u, u, u, u} P)
    (codomain : DisplayedFamily.{u, u, u, u} (totalSpace domain)) (first : domain.sections) :
    restrict (IndexedSigma.lift domain first) (indexedBody domain codomain) =
      reindex (sectionMap domain first) codomain := by
  refine Functor.hext (fun _ => rfl) ?_
  intro start finish step
  apply heq_of_eq
  have same : (displayedToTotalElements domain).map ((IndexedSigma.lift domain first).map step) =
      (elementMap (sectionMap domain first)).map step := by
    apply CategoryOfElements.ext (totalSpace domain)
    exact displayedToTotalElements_underlying domain ((IndexedSigma.lift domain first).map step)
  exact congrArg codomain.map same

/-- Sections of the sum are exactly a natural first section and a natural
second section over that actual first section. -/
def sigmaSectionEquiv (domain : DisplayedFamily.{u, u, u, u} P)
    (codomain : DisplayedFamily.{u, u, u, u} (totalSpace domain)) :
    (sigmaFamily domain codomain).sections ≃
      (Σ first : domain.sections, (reindex (sectionMap domain first) codomain).sections) :=
  (IndexedSigma.sectionEquiv domain (indexedBody domain codomain)).trans
    { toFun term := ⟨term.1, CP.castSection (indexedBody_lift domain codomain term.1) term.2⟩
      invFun term := ⟨term.1, CP.castSection (indexedBody_lift domain codomain term.1).symm term.2⟩
      left_inv term := by
        rcases term with ⟨first, second⟩
        exact congrArg (Sigma.mk first)
          (CP.castSection_reverse (indexedBody_lift domain codomain first) second)
      right_inv term := by
        rcases term with ⟨first, second⟩
        exact congrArg (Sigma.mk first)
          (CP.castSection_reverse (indexedBody_lift domain codomain first).symm second) }

def sigmaPair {domain : DisplayedFamily.{u, u, u, u} P}
    {codomain : DisplayedFamily.{u, u, u, u} (totalSpace domain)} (first : domain.sections)
    (second : (reindex (sectionMap domain first) codomain).sections) :
    (sigmaFamily domain codomain).sections := (sigmaSectionEquiv domain codomain).symm ⟨first, second⟩

def sigmaFst {domain : DisplayedFamily.{u, u, u, u} P}
    {codomain : DisplayedFamily.{u, u, u, u} (totalSpace domain)}
    (term : (sigmaFamily domain codomain).sections) : domain.sections :=
  (sigmaSectionEquiv domain codomain term).1

def sigmaSnd {domain : DisplayedFamily.{u, u, u, u} P}
    {codomain : DisplayedFamily.{u, u, u, u} (totalSpace domain)}
    (term : (sigmaFamily domain codomain).sections) :
    (reindex (sectionMap domain (sigmaFst term)) codomain).sections :=
  (sigmaSectionEquiv domain codomain term).2

theorem sigmaFst_value {domain : DisplayedFamily.{u, u, u, u} P}
    {codomain : DisplayedFamily.{u, u, u, u} (totalSpace domain)}
    (term : (sigmaFamily domain codomain).sections) (point : P.Elements) :
    (sigmaFst term).val point = (term.val point).1 := rfl

theorem sigmaSnd_value {domain : DisplayedFamily.{u, u, u, u} P}
    {codomain : DisplayedFamily.{u, u, u, u} (totalSpace domain)}
    (term : (sigmaFamily domain codomain).sections) (point : P.Elements) :
    HEq ((sigmaSnd term).val point) (term.val point).2 :=
  CP.castSection_value (indexedBody_lift domain codomain (sigmaFst term))
    (IndexedSigma.snd domain (indexedBody domain codomain) term) point

theorem sigmaPair_value_fst {domain : DisplayedFamily.{u, u, u, u} P}
    {codomain : DisplayedFamily.{u, u, u, u} (totalSpace domain)} (first : domain.sections)
    (second : (reindex (sectionMap domain first) codomain).sections) (point : P.Elements) :
    ((sigmaPair first second).val point).1 = first.val point := rfl

theorem sigmaPair_value_snd {domain : DisplayedFamily.{u, u, u, u} P}
    {codomain : DisplayedFamily.{u, u, u, u} (totalSpace domain)} (first : domain.sections)
    (second : (reindex (sectionMap domain first) codomain).sections) (point : P.Elements) :
    HEq ((sigmaPair first second).val point).2 (second.val point) :=
  CP.castSection_value (indexedBody_lift domain codomain first).symm second point

theorem sigma_beta {domain : DisplayedFamily.{u, u, u, u} P}
    {codomain : DisplayedFamily.{u, u, u, u} (totalSpace domain)} (first : domain.sections)
    (second : (reindex (sectionMap domain first) codomain).sections) :
    sigmaSectionEquiv domain codomain (sigmaPair first second) = ⟨first, second⟩ :=
  (sigmaSectionEquiv domain codomain).apply_symm_apply ⟨first, second⟩

theorem sigma_eta {domain : DisplayedFamily.{u, u, u, u} P}
    {codomain : DisplayedFamily.{u, u, u, u} (totalSpace domain)}
    (term : (sigmaFamily domain codomain).sections) : sigmaPair (sigmaFst term) (sigmaSnd term) = term :=
  (sigmaSectionEquiv domain codomain).symm_apply_apply term

end Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassPresheafProducts
