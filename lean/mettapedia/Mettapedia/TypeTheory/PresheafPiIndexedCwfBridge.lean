import Mettapedia.TypeTheory.PresheafPiEvaluationBaseChange
import Mettapedia.TypeTheory.CategoryIndexedFamilyGeneralPi

/-!
# Presheaf Π base change for the existing indexed-family candidate

The natural isomorphism proved from evidence-bearing pointwise indices
is here specialized to the existing category-indexed CwF's right-Kan
dependent-product candidate. Formation, evaluation, and transpose
commute with natural substitutions of presheaf contexts. This is
semantic coherence on that fragment, not an unrestricted Π
substitution rule or authored judgmental computation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.PresheafPiIndexedCwfBridge

open CategoryTheory
open Mettapedia.TypeTheory.CategoryOfElementsBaseChange
open Mettapedia.TypeTheory.CategoryIndexedFamilyCwf
open Mettapedia.TypeTheory.CategoryIndexedFamilyGeneralPi
open Mettapedia.TypeTheory.PresheafPiLimitComparison
open Mettapedia.TypeTheory.PresheafPiEvaluationBaseChange

universe u

/-- The existing indexed-family right-Kan product obeys a natural
formation-level base-change isomorphism for substitutions between
type-valued presheaf contexts over one syntax category. -/
noncomputable def presheafGeneralPi_formation_baseChangeIso
    {Syntax : Type u} [Category.{u} Syntax]
    {source target : Syntax ⥤ Type u}
    (substitution : source ⟶ target)
    (domain : target.Elements ⥤ Type u)
    (codomain : domain.Elements ⥤ Type u) :
    generalPiFamily
        (context := Cat.of source.Elements)
        (substitution.mapElements ⋙ domain)
        (mapPrecompElements substitution.mapElements domain ⋙ codomain) ≅
      substitution.mapElements ⋙
        generalPiFamily (context := Cat.of target.Elements) domain codomain :=
  chosenPresheafPiBaseChangeIso substitution domain codomain

/-- The existing indexed-family dependent-product evaluator commutes
with the presheaf-context formation comparison. The argument receipt,
including its dependent evidence, is retained by the base-change lift. -/
theorem presheafGeneralPi_evaluation_baseChange
    {Syntax : Type u} [Category.{u} Syntax]
    {source target : Syntax ⥤ Type u}
    (substitution : source ⟶ target)
    (domain : target.Elements ⥤ Type u)
    (codomain : domain.Elements ⥤ Type u) :
    Functor.whiskerLeft
        (CategoryOfElements.π (substitution.mapElements ⋙ domain))
        (presheafGeneralPi_formation_baseChangeIso
          substitution domain codomain).hom ≫
      Functor.whiskerLeft
        (mapPrecompElements substitution.mapElements domain)
        (generalPiEvaluation
          (context := Cat.of target.Elements) domain codomain) =
      generalPiEvaluation
        (context := Cat.of source.Elements)
        (substitution.mapElements ⋙ domain)
        (mapPrecompElements substitution.mapElements domain ⋙ codomain) :=
  chosenPresheafPiBaseChangeIso_evaluation substitution domain codomain

section
set_option backward.isDefEq.respectTransparency false

/-- On natural presheaf substitutions, the Π comparison is uniquely
determined by its action on evaluation. This is a right-Kan universal
property, not a choice of pointwise index representation. -/
theorem presheafGeneralPi_baseChange_hom_unique
    {Syntax : Type u} [Category.{u} Syntax]
    {source target : Syntax ⥤ Type u}
    (substitution : source ⟶ target)
    (domain : target.Elements ⥤ Type u)
    (codomain : domain.Elements ⥤ Type u)
    (candidate :
      generalPiFamily
          (context := Cat.of source.Elements)
          (substitution.mapElements ⋙ domain)
          (mapPrecompElements substitution.mapElements domain ⋙ codomain) ⟶
        substitution.mapElements ⋙
          generalPiFamily (context := Cat.of target.Elements) domain codomain)
    (evaluation :
      Functor.whiskerLeft
          (CategoryOfElements.π (substitution.mapElements ⋙ domain))
          candidate ≫
        Functor.whiskerLeft
          (mapPrecompElements substitution.mapElements domain)
          (generalPiEvaluation
            (context := Cat.of target.Elements) domain codomain) =
        generalPiEvaluation
          (context := Cat.of source.Elements)
          (substitution.mapElements ⋙ domain)
          (mapPrecompElements substitution.mapElements domain ⋙ codomain)) :
    candidate =
      (presheafGeneralPi_formation_baseChangeIso
        substitution domain codomain).hom := by
  let sourceDomain := substitution.mapElements ⋙ domain
  let lifted := mapPrecompElements substitution.mapElements domain
  let sourceBody := lifted ⋙ codomain
  let comparison :=
    presheafGeneralPi_formation_baseChangeIso substitution domain codomain
  let sourceProjection :=
    weaken (context := Cat.of source.Elements) sourceDomain
  have evalInverse :
      Functor.whiskerLeft sourceProjection comparison.inv ≫
        generalPiEvaluation (context := Cat.of source.Elements)
          sourceDomain sourceBody =
      Functor.whiskerLeft lifted
        (generalPiEvaluation
          (context := Cat.of target.Elements) domain codomain) := by
    have forward := presheafGeneralPi_evaluation_baseChange
      substitution domain codomain
    exact ((Functor.isoWhiskerLeft sourceProjection comparison).inv_comp_eq).2
      forward.symm
  have opposite : candidate ≫ comparison.inv =
      𝟙 (generalPiFamily (context := Cat.of source.Elements)
        sourceDomain sourceBody) := by
    apply ((generalPiAdjunction
      (context := Cat.of source.Elements) sourceDomain).homEquiv
        (generalPiFamily (context := Cat.of source.Elements)
          sourceDomain sourceBody) sourceBody).symm.injective
    change
      Functor.whiskerLeft sourceProjection
          (candidate ≫ comparison.inv) ≫
        generalPiEvaluation (context := Cat.of source.Elements)
          sourceDomain sourceBody =
      Functor.whiskerLeft sourceProjection
          (𝟙 (generalPiFamily (context := Cat.of source.Elements)
            sourceDomain sourceBody)) ≫
        generalPiEvaluation (context := Cat.of source.Elements)
          sourceDomain sourceBody
    calc
      _ = (Functor.whiskerLeft sourceProjection candidate ≫
            Functor.whiskerLeft sourceProjection comparison.inv) ≫
          generalPiEvaluation (context := Cat.of source.Elements)
            sourceDomain sourceBody := by rw [Functor.whiskerLeft_comp]
      _ = Functor.whiskerLeft sourceProjection candidate ≫
            (Functor.whiskerLeft sourceProjection comparison.inv ≫
              generalPiEvaluation (context := Cat.of source.Elements)
                sourceDomain sourceBody) := Category.assoc _ _ _
      _ = Functor.whiskerLeft sourceProjection candidate ≫
            Functor.whiskerLeft lifted
              (generalPiEvaluation
                (context := Cat.of target.Elements) domain codomain) := by
          rw [evalInverse]
      _ = generalPiEvaluation (context := Cat.of source.Elements)
            sourceDomain sourceBody := evaluation
      _ = Functor.whiskerLeft sourceProjection
            (𝟙 (generalPiFamily (context := Cat.of source.Elements)
              sourceDomain sourceBody)) ≫
            generalPiEvaluation (context := Cat.of source.Elements)
              sourceDomain sourceBody := by simp
  calc
    candidate = (candidate ≫ comparison.inv) ≫ comparison.hom := by
      rw [Category.assoc, comparison.inv_hom_id, Category.comp_id]
    _ = comparison.hom := by rw [opposite, Category.id_comp]

/-- The Π comparison for the identity presheaf substitution is the
identity on the existing dependent-product family. -/
theorem presheafGeneralPi_baseChange_id
    {Syntax : Type u} [Category.{u} Syntax]
    (context : Syntax ⥤ Type u)
    (domain : context.Elements ⥤ Type u)
    (codomain : domain.Elements ⥤ Type u) :
    (presheafGeneralPi_formation_baseChangeIso
      (𝟙 context) domain codomain).hom = 𝟙 _ := by
  symm
  apply presheafGeneralPi_baseChange_hom_unique
    (𝟙 context) domain codomain (𝟙 _)
  rfl

/-- Identity substitution gives the identity comparison in both
transport directions. -/
theorem presheafGeneralPi_baseChangeIso_id
    {Syntax : Type u} [Category.{u} Syntax]
    (context : Syntax ⥤ Type u)
    (domain : context.Elements ⥤ Type u)
    (codomain : domain.Elements ⥤ Type u) :
    presheafGeneralPi_formation_baseChangeIso
      (𝟙 context) domain codomain = Iso.refl _ := by
  apply Iso.ext
  exact presheafGeneralPi_baseChange_id context domain codomain

/-- Changing presheaf context twice gives the same Π comparison as
changing it once by the composite substitution. -/
theorem presheafGeneralPi_baseChange_comp
    {Syntax : Type u} [Category.{u} Syntax]
    {firstContext middleContext lastContext : Syntax ⥤ Type u}
    (first : firstContext ⟶ middleContext)
    (second : middleContext ⟶ lastContext)
    (domain : lastContext.Elements ⥤ Type u)
    (codomain : domain.Elements ⥤ Type u) :
    (presheafGeneralPi_formation_baseChangeIso
      (first ≫ second) domain codomain).hom =
      (presheafGeneralPi_formation_baseChangeIso first
        (second.mapElements ⋙ domain)
        (mapPrecompElements second.mapElements domain ⋙ codomain)).hom ≫
      Functor.whiskerLeft first.mapElements
        (presheafGeneralPi_formation_baseChangeIso
          second domain codomain).hom := by
  symm
  apply presheafGeneralPi_baseChange_hom_unique
    (first ≫ second) domain codomain _
  let middleDomain := second.mapElements ⋙ domain
  let middleLift := mapPrecompElements second.mapElements domain
  let middleBody := middleLift ⋙ codomain
  let sourceDomain := first.mapElements ⋙ middleDomain
  let sourceLift := mapPrecompElements first.mapElements middleDomain
  let sourceBody := sourceLift ⋙ middleBody
  let sourceProjection :=
    weaken (context := Cat.of firstContext.Elements) sourceDomain
  let middleProjection :=
    weaken (context := Cat.of middleContext.Elements) middleDomain
  let firstComparison :=
    presheafGeneralPi_formation_baseChangeIso first middleDomain middleBody
  let secondComparison :=
    presheafGeneralPi_formation_baseChangeIso second domain codomain
  have firstEvaluation := presheafGeneralPi_evaluation_baseChange
    first middleDomain middleBody
  have secondEvaluation := presheafGeneralPi_evaluation_baseChange
    second domain codomain
  change
    Functor.whiskerLeft sourceProjection
        (firstComparison.hom ≫
          Functor.whiskerLeft first.mapElements secondComparison.hom) ≫
      Functor.whiskerLeft (sourceLift ⋙ middleLift)
        (generalPiEvaluation
          (context := Cat.of lastContext.Elements) domain codomain) =
    generalPiEvaluation
      (context := Cat.of firstContext.Elements) sourceDomain sourceBody
  calc
    _ = (Functor.whiskerLeft sourceProjection firstComparison.hom ≫
          Functor.whiskerLeft sourceLift
            (Functor.whiskerLeft middleProjection secondComparison.hom)) ≫
        Functor.whiskerLeft sourceLift
          (Functor.whiskerLeft middleLift
            (generalPiEvaluation
              (context := Cat.of lastContext.Elements) domain codomain)) := by
          rfl
    _ = Functor.whiskerLeft sourceProjection firstComparison.hom ≫
          (Functor.whiskerLeft sourceLift
              (Functor.whiskerLeft middleProjection secondComparison.hom) ≫
            Functor.whiskerLeft sourceLift
              (Functor.whiskerLeft middleLift
                (generalPiEvaluation
                  (context := Cat.of lastContext.Elements) domain codomain))) :=
          Category.assoc _ _ _
    _ = Functor.whiskerLeft sourceProjection firstComparison.hom ≫
          Functor.whiskerLeft sourceLift
            (generalPiEvaluation
              (context := Cat.of middleContext.Elements)
              middleDomain middleBody) := by
          have liftedSecond := congrArg
            (fun arrow => Functor.whiskerLeft sourceProjection firstComparison.hom ≫
              Functor.whiskerLeft sourceLift arrow) secondEvaluation
          simpa only [Category.assoc, Functor.whiskerLeft_comp,
            middleProjection, secondComparison, middleLift, middleDomain,
            middleBody, weaken] using liftedSecond
    _ = generalPiEvaluation
          (context := Cat.of firstContext.Elements) sourceDomain sourceBody :=
        firstEvaluation

/-- The complete Π base-change isomorphism is coherent under two
successive natural substitutions, including its inverse transport. -/
theorem presheafGeneralPi_baseChangeIso_comp
    {Syntax : Type u} [Category.{u} Syntax]
    {firstContext middleContext lastContext : Syntax ⥤ Type u}
    (first : firstContext ⟶ middleContext)
    (second : middleContext ⟶ lastContext)
    (domain : lastContext.Elements ⥤ Type u)
    (codomain : domain.Elements ⥤ Type u) :
    presheafGeneralPi_formation_baseChangeIso
      (first ≫ second) domain codomain =
      (presheafGeneralPi_formation_baseChangeIso first
        (second.mapElements ⋙ domain)
        (mapPrecompElements second.mapElements domain ⋙ codomain)).trans
      (Functor.isoWhiskerLeft first.mapElements
        (presheafGeneralPi_formation_baseChangeIso
          second domain codomain)) := by
  apply Iso.ext
  exact presheafGeneralPi_baseChange_comp first second domain codomain

end

section
set_option backward.isDefEq.respectTransparency false

/-- Dependent lambda abstraction commutes with natural substitution of
presheaf contexts, after the verified formation comparison. -/
theorem presheafGeneralPi_transpose_baseChange
    {Syntax : Type u} [Category.{u} Syntax]
    {source target : Syntax ⥤ Type u}
    (substitution : source ⟶ target)
    (domain : target.Elements ⥤ Type u)
    (codomain : domain.Elements ⥤ Type u)
    {head : target.Elements ⥤ Type u}
    (body : reindexFamily head
        (weaken (context := Cat.of target.Elements) domain) ⟶ codomain) :
    generalPiTranspose
        (context := Cat.of source.Elements)
        (substitution.mapElements ⋙ domain)
        (Functor.whiskerLeft
          (mapPrecompElements substitution.mapElements domain) body) ≫
      (presheafGeneralPi_formation_baseChangeIso
        substitution domain codomain).hom =
      Functor.whiskerLeft substitution.mapElements
        (generalPiTranspose
          (context := Cat.of target.Elements) domain body) := by
  let sourceDomain := substitution.mapElements ⋙ domain
  let lifted := mapPrecompElements substitution.mapElements domain
  let sourceBody := lifted ⋙ codomain
  let comparison :=
    presheafGeneralPi_formation_baseChangeIso substitution domain codomain
  let sourceTranspose :
      (substitution.mapElements ⋙ head) ⟶
        generalPiFamily (context := Cat.of source.Elements)
          sourceDomain sourceBody :=
    generalPiTranspose (context := Cat.of source.Elements)
      sourceDomain (Functor.whiskerLeft lifted body)
  let targetTranspose :=
    Functor.whiskerLeft substitution.mapElements
      (generalPiTranspose (context := Cat.of target.Elements) domain body)
  let sourceProjection :=
    weaken (context := Cat.of source.Elements) sourceDomain
  let targetProjection :=
    weaken (context := Cat.of target.Elements) domain
  have evalInverse :
      Functor.whiskerLeft sourceProjection comparison.inv ≫
        generalPiEvaluation (context := Cat.of source.Elements)
          sourceDomain sourceBody =
      Functor.whiskerLeft lifted
        (generalPiEvaluation
          (context := Cat.of target.Elements) domain codomain) := by
    have forward := presheafGeneralPi_evaluation_baseChange
      substitution domain codomain
    exact ((Functor.isoWhiskerLeft sourceProjection comparison).inv_comp_eq).2
      forward.symm
  have sourceBeta :
      Functor.whiskerLeft sourceProjection sourceTranspose ≫
        generalPiEvaluation (context := Cat.of source.Elements)
          sourceDomain sourceBody =
      Functor.whiskerLeft lifted body := by
    exact generalPi_beta (context := Cat.of source.Elements)
      (source := substitution.mapElements ⋙ head)
      (codomain := sourceBody)
      sourceDomain (Functor.whiskerLeft lifted body)
  have targetBetaLift :
      Functor.whiskerLeft sourceProjection targetTranspose ≫
        Functor.whiskerLeft lifted
          (generalPiEvaluation
            (context := Cat.of target.Elements) domain codomain) =
      Functor.whiskerLeft lifted body := by
    exact congrArg (Functor.whiskerLeft lifted)
      (generalPi_beta (context := Cat.of target.Elements) domain body)
  have opposite : targetTranspose ≫ comparison.inv = sourceTranspose := by
    apply ((generalPiAdjunction
      (context := Cat.of source.Elements) sourceDomain).homEquiv
        (substitution.mapElements ⋙ head) sourceBody).symm.injective
    change
      Functor.whiskerLeft
          (weaken (context := Cat.of source.Elements) sourceDomain)
          (targetTranspose ≫ comparison.inv) ≫
        generalPiEvaluation (context := Cat.of source.Elements)
          sourceDomain sourceBody =
      Functor.whiskerLeft
          (weaken (context := Cat.of source.Elements) sourceDomain)
          sourceTranspose ≫
        generalPiEvaluation (context := Cat.of source.Elements)
          sourceDomain sourceBody
    calc
      _ = (Functor.whiskerLeft sourceProjection targetTranspose ≫
            Functor.whiskerLeft sourceProjection comparison.inv) ≫
          generalPiEvaluation (context := Cat.of source.Elements)
            sourceDomain sourceBody := by
            rw [Functor.whiskerLeft_comp]
      _ = Functor.whiskerLeft sourceProjection targetTranspose ≫
            (Functor.whiskerLeft sourceProjection comparison.inv ≫
              generalPiEvaluation (context := Cat.of source.Elements)
                sourceDomain sourceBody) :=
          Category.assoc _ _ _
      _ = Functor.whiskerLeft sourceProjection targetTranspose ≫
            Functor.whiskerLeft lifted
              (generalPiEvaluation
                (context := Cat.of target.Elements) domain codomain) := by
          rw [evalInverse]
      _ = Functor.whiskerLeft lifted body := by exact targetBetaLift
      _ = Functor.whiskerLeft sourceProjection sourceTranspose ≫
            generalPiEvaluation (context := Cat.of source.Elements)
              sourceDomain sourceBody := by exact sourceBeta.symm
  calc
    sourceTranspose ≫ comparison.hom =
        (targetTranspose ≫ comparison.inv) ≫ comparison.hom := by rw [opposite]
    _ = targetTranspose := by
      rw [Category.assoc, comparison.inv_hom_id, Category.comp_id]

end

section
set_option backward.isDefEq.respectTransparency false

/-- Dependent lambda abstraction along a two-step context observation
agrees with abstraction along their composite, with both comparison
maps and the original body retained. -/
theorem presheafGeneralPi_transpose_baseChange_comp
    {Syntax : Type u} [Category.{u} Syntax]
    {firstContext middleContext lastContext : Syntax ⥤ Type u}
    (first : firstContext ⟶ middleContext)
    (second : middleContext ⟶ lastContext)
    (domain : lastContext.Elements ⥤ Type u)
    (codomain : domain.Elements ⥤ Type u)
    {head : lastContext.Elements ⥤ Type u}
    (body : reindexFamily head
        (weaken (context := Cat.of lastContext.Elements) domain) ⟶ codomain) :
    (generalPiTranspose
        (context := Cat.of firstContext.Elements)
        (first.mapElements ⋙ (second.mapElements ⋙ domain))
        (Functor.whiskerLeft
          (mapPrecompElements first.mapElements
            (second.mapElements ⋙ domain))
          (Functor.whiskerLeft
            (mapPrecompElements second.mapElements domain) body)) ≫
      (presheafGeneralPi_formation_baseChangeIso first
        (second.mapElements ⋙ domain)
        (mapPrecompElements second.mapElements domain ⋙ codomain)).hom) ≫
      Functor.whiskerLeft first.mapElements
        (presheafGeneralPi_formation_baseChangeIso
          second domain codomain).hom =
    Functor.whiskerLeft (first ≫ second).mapElements
      (generalPiTranspose
        (context := Cat.of lastContext.Elements) domain body) := by
  rw [Category.assoc, ← presheafGeneralPi_baseChange_comp]
  exact presheafGeneralPi_transpose_baseChange
    (first ≫ second) domain codomain body

end

#print axioms presheafGeneralPi_formation_baseChangeIso
#print axioms presheafGeneralPi_evaluation_baseChange
#print axioms presheafGeneralPi_baseChange_hom_unique
#print axioms presheafGeneralPi_baseChangeIso_id
#print axioms presheafGeneralPi_baseChangeIso_comp
#print axioms presheafGeneralPi_transpose_baseChange
#print axioms presheafGeneralPi_transpose_baseChange_comp

end Mettapedia.TypeTheory.PresheafPiIndexedCwfBridge
