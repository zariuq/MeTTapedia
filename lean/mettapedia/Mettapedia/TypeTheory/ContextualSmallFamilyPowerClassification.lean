import Mettapedia.TypeTheory.ContextualSmallFamilyPowerCoherence

/-!
# Parameterized classification by actual small future powers

A map into the total power family over a fixed parameter map corresponds
to a compatible section of its reindexing. Composing with the independent
power comparison classifies exactly the stable subfamilies of the actual
reindexed domain. Both inverse laws hold for whole natural maps, rather
than merely for present membership tests.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSmallFamilyPowerClassification

open _root_.CategoryTheory ContextualWitnessCover ContextualImageFactorization
open ContextualSmallFamilyUniverse ContextualSmallFamilyPowers
open ContextualSmallFamilyTypeFormerCoherence ContextualSmallFamilyPowerCoherence
open MaterialSets.Hypersets.PowerClassPresheafBaseChange

universe u v w
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type v} {other : D ⥤ Type w}
variable (change : NaturalHom other base) (family : base.Elements ⥤ Type u)

abbrev OverMap := {operation : NaturalHom other (total family) // operation.comp (projection family) = change}

def sectionGraph {context : D ⥤ Type w} (displayed : context.Elements ⥤ Type u)
    (term : displayed.sections) : NaturalHom context (total displayed) where
  app point value := ⟨value, term.val ⟨point, value⟩⟩
  naturality {first second} step value := by
    change (⟨context.map step value,
      displayed.map (CategoryOfElements.homMk (F := context)
        ⟨first, value⟩ ⟨second, context.map step value⟩ step rfl)
        (term.val ⟨first, value⟩)⟩ : TotalAt displayed second) = _
    exact congrArg (fun result : displayed.obj ⟨second, context.map step value⟩ =>
      (⟨context.map step value, result⟩ : TotalAt displayed second))
      (term.property (CategoryOfElements.homMk (F := context)
        ⟨first, value⟩ ⟨second, context.map step value⟩ step rfl))

theorem sectionGraph_parameter {context : D ⥤ Type w} (displayed : context.Elements ⥤ Type u)
    (term : displayed.sections) :
    (sectionGraph displayed term).comp (projection displayed) = ContextualSmallMapConstructions.identity context := by
  apply NaturalHom.ext
  intro _ _
  rfl

def fromSection (term : (substitutedFamily family change).sections) : OverMap change family :=
  ⟨(sectionGraph (substitutedFamily family change) term).comp (substitutedTotalMap family change), by
    apply NaturalHom.ext
    intro _ _
    rfl⟩

def pullbackGraph (operation : OverMap change family) :
    NaturalHom other (SubstitutionPullback family change) :=
  pullbackPair (projection family) change operation.val
    (ContextualSmallMapConstructions.identity other) (by
      apply NaturalHom.ext
      intro point value
      exact congrArg (fun map : NaturalHom other base => map.app point value) operation.property)

def receiptMap (operation : OverMap change family) :
    NaturalHom other (total (substitutedFamily family change)) :=
  (pullbackGraph change family operation).comp (substitutionBackward family change)

theorem receiptMap_parameter (operation : OverMap change family) (point : D) (value : other.obj point) :
    ((receiptMap change family operation).app point value).1 = value := rfl

private theorem dependentAt_heq {X : Type w} {Y : X → Type u} (value : ∀ point, Y point)
    {first second : X} (same : first = second) : HEq (value first) (value second) := by
  cases same
  rfl

def toSection (operation : OverMap change family) : (substitutedFamily family change).sections :=
  ⟨fun point => ((receiptMap change family operation).app point.1 point.2).2, by
    intro first second step
    have natural := (receiptMap change family operation).naturality step.1 first.2
    change (⟨other.map step.1 first.2,
      (substitutedFamily family change).map
        (CategoryOfElements.homMk (F := other) first
          ⟨second.1, other.map step.1 first.2⟩ step.1 rfl)
        ((receiptMap change family operation).app first.1 first.2).2⟩ :
          TotalAt (substitutedFamily family change) second.1) =
      (receiptMap change family operation).app second.1 (other.map step.1 first.2) at natural
    have target : (⟨second.1, other.map step.1 first.2⟩ : other.Elements) = second :=
      Sigma.ext rfl (heq_of_eq step.2)
    apply eq_of_heq
    exact (familyMap_heq (substitutedFamily family change) rfl target _ step
      (elementsArrow_heq rfl target _ step HEq.rfl)
      ((receiptMap change family operation).app first.1 first.2).2 _ HEq.rfl).symm.trans
        ((Sigma.mk.inj_iff.mp natural).2.trans
          (dependentAt_heq (fun point : other.Elements =>
            ((receiptMap change family operation).app point.1 point.2).2) target))⟩

theorem toSection_fromSection (term : (substitutedFamily family change).sections) :
    toSection change family (fromSection change family term) = term := by
  apply Subtype.ext
  funext point
  rfl

theorem fromSection_toSection (operation : OverMap change family) :
    fromSection change family (toSection change family operation) = operation := by
  apply Subtype.ext
  apply NaturalHom.ext
  intro point value
  have result := substitution_right family change point ((pullbackGraph change family operation).app point value)
  exact congrArg (fun receipt : (SubstitutionPullback family change).obj point => receipt.val.1) result

def mapSectionEquiv : OverMap change family ≃ (substitutedFamily family change).sections where
  toFun := toSection change family
  invFun := fromSection change family
  left_inv := fromSection_toSection change family
  right_inv := toSection_fromSection change family

variable (domain : base.Elements ⥤ Type u)

def parameterizedClassifier : OverMap change (power domain) ≃ Subfamily (domainUnder change domain) :=
  (mapSectionEquiv change (power domain)).trans
    ((wholeSectionComparison change domain).trans (sectionSubfamilyEquiv (domainUnder change domain)))

theorem parameterized_left (operation : OverMap change (power domain)) :
    (parameterizedClassifier change domain).symm (parameterizedClassifier change domain operation) = operation :=
  (parameterizedClassifier change domain).symm_apply_apply operation

theorem parameterized_right (subfamily : Subfamily (domainUnder change domain)) :
    parameterizedClassifier change domain ((parameterizedClassifier change domain).symm subfamily) = subfamily :=
  (parameterizedClassifier change domain).apply_symm_apply subfamily

theorem parameterized_member (operation : OverMap change (power domain))
    (point : other.Elements) (argument : (domainUnder change domain).obj point) :
    (parameterizedClassifier change domain operation).holds ⟨point, argument⟩ ↔
      member domain ((elementMap change).obj point) argument
        ((toSection change (power domain) operation).val point) :=
  member_substitution change domain point ((toSection change (power domain) operation).val point) argument

/-- Every stable subfamily has one actual whole classifying map over its
fixed parameter map. The statement allows arbitrary noninjective changes. -/
theorem parameterized_universal (subfamily : Subfamily (domainUnder change domain)) :
    ∃! operation : OverMap change (power domain),
      parameterizedClassifier change domain operation = subfamily := by
  refine ⟨(parameterizedClassifier change domain).symm subfamily,
    parameterized_right change domain subfamily, ?_⟩
  intro operation classifies
  exact (parameterizedClassifier change domain).injective
    (classifies.trans (parameterized_right change domain subfamily).symm)

end Mettapedia.TypeTheory.ContextualSmallFamilyPowerClassification
