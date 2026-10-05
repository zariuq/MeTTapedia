import Mettapedia.TypeTheory.ContextualSmallFamilyTypeFormerCoherence

/-!
# Actual comprehension for small families over wider parameters

A nested parameter and argument and an element of the total presheaf
retain the same three coordinates. The regrouping functors below retain
their actual context arrows and are explicitly inverse. Their section
comparison therefore applies to displayed bodies on the genuine
comprehension context, including when the parameter presheaf is wider.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSmallFamilyComprehension

open CategoryTheory ContextualSmallFamilyTypeFormers
open ContextualWitnessCover

universe u v w z
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type v}
variable (domain : base.Elements ⥤ Type u)

def flatten : domain.Elements ⥤ (ContextualSmallFamilyUniverse.total domain).Elements where
  obj argument := ⟨argument.1.1, ⟨argument.1.2, argument.2⟩⟩
  map {first second} step := CategoryOfElements.homMk _ _ step.1.1 (by
    apply Sigma.ext step.1.2
    have target : (⟨second.1.1, base.map step.1.1 first.1.2⟩ : base.Elements) = second.1 :=
      Sigma.ext rfl (heq_of_eq step.1.2)
    exact (ContextualSmallFamilyUniverse.familyMap_heq domain rfl target
      (CategoryOfElements.homMk (F := base) first.1
        ⟨second.1.1, base.map step.1.1 first.1.2⟩ step.1.1 rfl) step.1
      (ContextualSmallFamilyUniverse.elementsArrow_heq rfl target _ _ HEq.rfl)
      first.2 first.2 HEq.rfl).trans (heq_of_eq step.2))
  map_id _ := rfl
  map_comp _ _ := rfl

def unflatten : (ContextualSmallFamilyUniverse.total domain).Elements ⥤ domain.Elements where
  obj receipt := ⟨⟨receipt.1, receipt.2.1⟩, receipt.2.2⟩
  map {first second} step := by
    have pair := step.2
    change (⟨base.map step.1 first.2.1,
      domain.map (CategoryOfElements.homMk (F := base) ⟨first.1, first.2.1⟩
        ⟨second.1, base.map step.1 first.2.1⟩ step.1 rfl) first.2.2⟩ :
          ContextualSmallFamilyUniverse.TotalAt domain second.1) = second.2 at pair
    have parameter := (Sigma.mk.inj_iff.mp pair).1
    have value := (Sigma.mk.inj_iff.mp pair).2
    let contextStep : base.elementsMk first.1 first.2.1 ⟶ base.elementsMk second.1 second.2.1 :=
      CategoryOfElements.homMk (F := base) _ _ step.1 parameter
    refine CategoryOfElements.homMk _ _ contextStep ?_
    apply eq_of_heq
    have target : (⟨second.1, base.map step.1 first.2.1⟩ : base.Elements) =
        ⟨second.1, second.2.1⟩ := Sigma.ext rfl (heq_of_eq parameter)
    exact (ContextualSmallFamilyUniverse.familyMap_heq domain rfl target
      (CategoryOfElements.homMk (F := base) ⟨first.1, first.2.1⟩
        ⟨second.1, base.map step.1 first.2.1⟩ step.1 rfl) contextStep
      (ContextualSmallFamilyUniverse.elementsArrow_heq rfl target _ _ HEq.rfl)
      first.2.2 first.2.2 HEq.rfl).symm.trans value
  map_id _ := rfl
  map_comp _ _ := rfl

def contextCompose {E : Type w} {F : Type z} {K : Type v}
    [Category.{u} E] [Category.{u} F] [Category.{u} K]
    (first : E ⥤ F) (second : F ⥤ K) : E ⥤ K where
  obj point := second.obj (first.obj point)
  map step := second.map (first.map step)
  map_id point := by rw [first.map_id, second.map_id]
  map_comp earlier later := by rw [first.map_comp, second.map_comp]

def contextIdentity (E : Type w) [Category.{u} E] : E ⥤ E where
  obj point := point
  map step := step
  map_id _ := rfl
  map_comp _ _ := rfl

theorem flatten_unflatten : contextCompose (flatten domain) (unflatten domain) = contextIdentity domain.Elements := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

theorem unflatten_flatten : contextCompose (unflatten domain) (flatten domain) =
    contextIdentity (ContextualSmallFamilyUniverse.total domain).Elements := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

theorem flatten_context (argument : domain.Elements) : (flatten domain |>.obj argument).1 = argument.1.1 := rfl

theorem flatten_parameter (argument : domain.Elements) : (flatten domain |>.obj argument).2.1 = argument.1.2 := rfl

theorem flatten_argument (argument : domain.Elements) : (flatten domain |>.obj argument).2.2 = argument.2 := rfl

theorem flatten_arrow {first second : domain.Elements} (step : first ⟶ second) :
    (flatten domain |>.map step).1 = step.1.1 := rfl

def sectionPull {E : Type w} {F : Type z} [Category.{u} E] [Category.{u} F]
    (change : E ⥤ F) (family : F ⥤ Type v) (term : family.sections) :
    (ContextualSmallFamilyUniverse.restrict change family).sections :=
  ⟨fun point => term.val (change.obj point), fun {_ _} step => term.property (change.map step)⟩

def sectionCast {E : Type w} [Category.{u} E] {first second : E ⥤ Type v}
    (same : first = second) (term : first.sections) : second.sections := by
  cases same
  exact term

theorem sectionCast_value {E : Type w} [Category.{u} E] {first second : E ⥤ Type v}
    (same : first = second) (term : first.sections) (point : E) :
    HEq ((sectionCast same term).val point) (term.val point) := by
  cases same
  rfl

def indexedBody (body : (ContextualSmallFamilyUniverse.total domain).Elements ⥤ Type u) :
    domain.Elements ⥤ Type u := ContextualSmallFamilyUniverse.restrict (flatten domain) body

theorem body_roundtrip (body : (ContextualSmallFamilyUniverse.total domain).Elements ⥤ Type u) :
    ContextualSmallFamilyUniverse.restrict (unflatten domain) (indexedBody domain body) = body := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

def bodySectionEquiv (body : (ContextualSmallFamilyUniverse.total domain).Elements ⥤ Type u) :
    body.sections ≃ (indexedBody domain body).sections where
  toFun := sectionPull (flatten domain) body
  invFun term := sectionCast (body_roundtrip domain body)
    (sectionPull (unflatten domain) (indexedBody domain body) term)
  left_inv term := by
    apply Subtype.ext
    funext point
    exact eq_of_heq (sectionCast_value (body_roundtrip domain body)
      (sectionPull (unflatten domain) (indexedBody domain body)
        (sectionPull (flatten domain) body term)) point)
  right_inv term := by
    apply Subtype.ext
    funext point
    exact eq_of_heq (sectionCast_value (body_roundtrip domain body)
      (sectionPull (unflatten domain) (indexedBody domain body) term) ((flatten domain).obj point))

theorem bodySectionEquiv_value (body : (ContextualSmallFamilyUniverse.total domain).Elements ⥤ Type u)
    (term : body.sections) (argument : domain.Elements) :
    (bodySectionEquiv domain body term).val argument = term.val ((flatten domain).obj argument) := rfl

def sigmaDisplayed (body : (ContextualSmallFamilyUniverse.total domain).Elements ⥤ Type u) :
    base.Elements ⥤ Type u := sigma domain (indexedBody domain body)

def piDisplayed (body : (ContextualSmallFamilyUniverse.total domain).Elements ⥤ Type u) :
    base.Elements ⥤ Type u := pi domain (indexedBody domain body)

def sigmaDisplayedSecond (body : (ContextualSmallFamilyUniverse.total domain).Elements ⥤ Type u)
    (point : base.Elements) (term : (sigmaDisplayed domain body).obj point) :
    body.obj ⟨point.1, ⟨point.2, term.1⟩⟩ := term.2

section Substitution

variable {other : D ⥤ Type w} (change : NaturalHom other base)

def totalChange : NaturalHom
    (ContextualSmallFamilyUniverse.total (ContextualSmallFamilyTypeFormerCoherence.domainUnder change domain))
    (ContextualSmallFamilyUniverse.total domain) where
  app point receipt := ⟨change.app point receipt.1, receipt.2⟩
  naturality {first second} step receipt := by
    apply Sigma.ext (change.naturality step receipt.1)
    have target : (⟨second, change.app second (other.map step receipt.1)⟩ : base.Elements) =
        ⟨second, base.map step (change.app first receipt.1)⟩ :=
      Sigma.ext rfl (heq_of_eq (change.naturality step receipt.1).symm)
    exact (ContextualSmallFamilyUniverse.familyMap_heq domain rfl target
      ((ContextualSmallFamilyUniverse.elementMap change).map
        (CategoryOfElements.homMk (F := other) ⟨first, receipt.1⟩
          ⟨second, other.map step receipt.1⟩ step rfl))
      (CategoryOfElements.homMk (F := base) ⟨first, change.app first receipt.1⟩
        ⟨second, base.map step (change.app first receipt.1)⟩ step rfl)
      (ContextualSmallFamilyUniverse.elementsArrow_heq rfl target _ _ HEq.rfl)
      receipt.2 receipt.2 HEq.rfl).symm

theorem comprehension_substitution :
    contextCompose (flatten (ContextualSmallFamilyTypeFormerCoherence.domainUnder change domain))
      (ContextualSmallFamilyUniverse.elementMap (totalChange domain change)) =
    contextCompose (ContextualSmallFamilyTypeFormerCoherence.argumentsUnder change domain) (flatten domain) := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

theorem totalChange_parameter : (totalChange domain change).comp
    (ContextualSmallFamilyUniverse.projection domain) =
      (ContextualSmallFamilyUniverse.projection
        (ContextualSmallFamilyTypeFormerCoherence.domainUnder change domain)).comp change := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem indexedBody_substitution (body : (ContextualSmallFamilyUniverse.total domain).Elements ⥤ Type u) :
    indexedBody (ContextualSmallFamilyTypeFormerCoherence.domainUnder change domain)
      (ContextualSmallFamilyUniverse.substitutedFamily body (totalChange domain change)) =
    ContextualSmallFamilyTypeFormerCoherence.bodyUnder change domain (indexedBody domain body) := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

theorem sigmaDisplayed_substitution (body : (ContextualSmallFamilyUniverse.total domain).Elements ⥤ Type u) :
    sigmaDisplayed (ContextualSmallFamilyTypeFormerCoherence.domainUnder change domain)
      (ContextualSmallFamilyUniverse.substitutedFamily body (totalChange domain change)) =
      ContextualSmallFamilyUniverse.substitutedFamily (sigmaDisplayed domain body) change := by
  unfold sigmaDisplayed
  rw [indexedBody_substitution]
  exact ContextualSmallFamilyTypeFormerCoherence.sigma_substitution change domain (indexedBody domain body)

def piDisplayedSubstitution (body : (ContextualSmallFamilyUniverse.total domain).Elements ⥤ Type u) :
    NatTrans (ContextualSmallFamilyUniverse.substitutedFamily (piDisplayed domain body) change)
      (piDisplayed (ContextualSmallFamilyTypeFormerCoherence.domainUnder change domain)
        (ContextualSmallFamilyUniverse.substitutedFamily body (totalChange domain change))) := by
  unfold piDisplayed
  rw [indexedBody_substitution]
  exact ContextualSmallFamilyTypeFormerCoherence.piSubstitution change domain (indexedBody domain body)

end Substitution

end Mettapedia.TypeTheory.ContextualSmallFamilyComprehension
