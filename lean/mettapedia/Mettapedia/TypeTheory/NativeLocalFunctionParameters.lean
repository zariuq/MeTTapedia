import Mettapedia.TypeTheory.DisplayedPresheafParameterFamilies
import Mettapedia.TypeTheory.DisplayedPresheafPiSubstitutionCoherence
import Mettapedia.TypeTheory.ContextualLocalUniverses

/-!
# Native parameter spaces for dependent function presentations

For a family over a parameter context and a second parameter context, the
dependent product records a natural choice of second parameters at every
future argument. Its total presheaf is the function parameter space.
An actual dependent context map supplies its name by the native product
base-change comparison. Evaluation uses the native adjunction's counit.
No internal universe or arbitrary-model interpretation is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.NativeLocalFunctionParameters

open CategoryTheory
open Mettapedia.Computability.ComputationalTrinity
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafCwf DisplayedPresheafPi DisplayedPresheafSlicePi
open DisplayedPresheafPiSubstitution DisplayedPresheafParameterFamilies
open DisplayedPresheafIndexedCwfBridge CategoryIndexedFamilyGeneralPi
open CategoryOfElementsBaseChange PresheafPiIndexedCwfBridge

universe u
variable {C : Type u} [Category.{u} C]
variable {P X : Face.{u, u, u} C}

noncomputable def choices (A : DisplayedFamily.{u, u, u, u} P)
    (Q : Face.{u, u, u} C) : DisplayedFamily.{u, u, u, u} P :=
  piDisplayed A (parameterFamily (totalSpace A) Q)

noncomputable def parameters (A : DisplayedFamily.{u, u, u, u} P)
    (Q : Face.{u, u, u} C) : Face.{u, u, u} C :=
  totalSpace (choices A Q)

noncomputable def name (f : X ⟶ P) (A : DisplayedFamily.{u, u, u, u} P)
    (Q : Face.{u, u, u} C)
    (g : totalSpace (reindexDisplayed f A) ⟶ Q) : X ⟶ parameters A Q :=
  presheafPair f (choices A Q)
    ((Functor.sectionsFunctor X.Elements).map
      (piSubstitutionIso f A (parameterFamily (totalSpace A) Q)).hom
      (lamDisplayed (parameterSection g)))

theorem name_projection (f : X ⟶ P) (A : DisplayedFamily.{u, u, u, u} P)
    (Q : Face.{u, u, u} C)
    (g : totalSpace (reindexDisplayed f A) ⟶ Q) :
    name f A Q g ≫ totalProjection (choices A Q) = f :=
  presheafPair_weaken _ _ _

noncomputable def argumentFamily (A : DisplayedFamily.{u, u, u, u} P)
    (Q : Face.{u, u, u} C) :
    DisplayedFamily.{u, u, u, u} (parameters A Q) :=
  reindexDisplayed (totalProjection (choices A Q)) A

/-- Evaluation acts on a supplied function parameter at its supplied
dependent argument; the naturality proof uses the complete native counit. -/
noncomputable def evaluation (A : DisplayedFamily.{u, u, u, u} P)
    (Q : Face.{u, u, u} C) : totalSpace (argumentFamily A Q) ⟶ Q where
  app world := TypeCat.ofHom fun receipt =>
    ((displayedProductAdjunction A).counit.app
      (parameterFamily (totalSpace A) Q)).app
      ⟨world, ⟨receipt.1.1, receipt.2⟩⟩ receipt.1.2
  naturality := by
    intro source target arrow
    apply ConcreteCategory.hom_ext
    intro receipt
    let sourcePoint : (totalSpace A).Elements := ⟨source, ⟨receipt.1.1, receipt.2⟩⟩
    let targetPoint : (totalSpace A).Elements :=
      ⟨target, (totalSpace A).map arrow ⟨receipt.1.1, receipt.2⟩⟩
    let step : sourcePoint ⟶ targetPoint := CategoryOfElements.homMk _ _ arrow rfl
    have natural := ((displayedProductAdjunction A).counit.app
      (parameterFamily (totalSpace A) Q)).naturality_apply step receipt.1.2
    exact natural

theorem totalElements_unit_value (A : DisplayedFamily.{u, u, u, u} P)
    (point : (totalSpace A).Elements) :
    (totalElementsEquivalence A).unitIso.hom.app point = 𝟙 point := by
  apply (totalElementsEquivalence A).functor.map_injective
  have triangle := (totalElementsEquivalence A).functor_unitIso_comp point
  have counit :
      (totalElementsEquivalence A).counitIso.hom.app
        ((totalElementsEquivalence A).functor.obj point) = 𝟙 _ := by
    change (eqToHom (displayedElements_roundtrip A)).app
      ((totalElementsEquivalence A).functor.obj point) = _
    rw [eqToHom_app]
    rfl
  rw [counit] at triangle
  erw [Category.comp_id] at triangle
  exact triangle.trans ((totalElementsEquivalence A).functor.map_id point).symm

theorem totalElements_unit_inverse_value (A : DisplayedFamily.{u, u, u, u} P)
    (point : (totalSpace A).Elements) :
    (totalElementsEquivalence A).unitIso.inv.app point = 𝟙 point := by
  have cancel := (totalElementsEquivalence A).unitIso.inv_hom_id_app point
  rw [totalElements_unit_value] at cancel
  erw [Category.comp_id] at cancel
  exact cancel

set_option backward.isDefEq.respectTransparency false in
theorem displayedEvaluation_value (A : DisplayedFamily.{u, u, u, u} P)
    (B : DisplayedFamily.{u, u, u, u} (totalSpace A))
    (point : (totalSpace A).Elements)
    (function : (piDisplayed A B).obj ((totalProjection A).mapElements.obj point)) :
    ((displayedProductAdjunction A).counit.app B).app point function =
      (generalPiEvaluation (context := Cat.of P.Elements) A
        (displayedToTotalElements A ⋙ B)).app
        (totalElementsObjectEquiv A point) function := by
  rcases point with ⟨world, ⟨value, argument⟩⟩
  simp only [displayedProductAdjunction, Adjunction.ofNatIsoLeft_counit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Adjunction.comp_counit_app]
  simp [Functor.whiskeringLeft, eqToIso, Equivalence.toAdjunction_counit,
    Equivalence.symm_counit, Equivalence.congrLeft_unitIso_inv_app,
    Equivalence.funInvIdAssoc_hom_app, totalElements_unit_inverse_value]
  erw [_root_.CategoryTheory.Functor.map_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation retains the supplied argument across the canonical native
product comparison, including the displayed codomain transport. -/
theorem evaluation_baseChange (f : X ⟶ P)
    (A : DisplayedFamily.{u, u, u, u} P)
    (B : DisplayedFamily.{u, u, u, u} (totalSpace A))
    (point : (totalSpace (reindexDisplayed f A)).Elements)
    (function :
      (piDisplayed (reindexDisplayed f A)
        (reindexDisplayed (totalReindexMap f A) B)).obj
        ((totalProjection (reindexDisplayed f A)).mapElements.obj point)) :
    ((displayedProductAdjunction A).counit.app B).app
        ((totalReindexMap f A).mapElements.obj point)
        ((piSubstitutionIso f A B).hom.app
          ((totalProjection (reindexDisplayed f A)).mapElements.obj point) function) =
      ((displayedProductAdjunction (reindexDisplayed f A)).counit.app
        (reindexDisplayed (totalReindexMap f A) B)).app point function := by
  let A' := reindexDisplayed f A
  let B' := displayedToTotalElements A' ⋙ reindexDisplayed (totalReindexMap f A) B
  let B0 := displayedToTotalElements A ⋙ B
  let B1 := mapPrecompElements f.mapElements A ⋙ B0
  let regroup := eqToHom (codomainBaseChange f A B)
  let index := totalElementsObjectEquiv A' point
  have natural := ((generalPiAdjunction (context := Cat.of X.Elements) A').counit.naturality
    regroup)
  have naturalValue := congrArg (fun k => k.app index function) natural
  have base := presheafGeneralPi_evaluation_baseChange f A B0
  have baseValue := congrArg
    (fun k => k.app index
      ((((CategoryOfElements.π A').ran).map regroup).app index.1 function)) base
  rw [displayedEvaluation_value, displayedEvaluation_value]
  rw [piSubstitutionIso_hom]
  change
    (generalPiEvaluation (context := Cat.of P.Elements) A B0).app
      ((mapPrecompElements f.mapElements A).obj index)
      (((presheafGeneralPi_formation_baseChangeIso f A B0).hom.app index.1)
        ((((CategoryOfElements.π A').ran).map regroup).app index.1 function)) =
    (generalPiEvaluation (context := Cat.of X.Elements) A' B').app index function
  have regroupAt : regroup.app index = 𝟙 _ := codomainBaseChange_app f A B index
  have evaluated :
      (generalPiEvaluation (context := Cat.of X.Elements) A' B1).app index
          ((((CategoryOfElements.π A').ran).map regroup).app index.1 function) =
        (generalPiEvaluation (context := Cat.of X.Elements) A' B').app index function := by
    change
      (generalPiEvaluation (context := Cat.of X.Elements) A' B1).app index
          ((((CategoryOfElements.π A').ran).map regroup).app index.1 function) =
        regroup.app index
          ((generalPiEvaluation (context := Cat.of X.Elements) A' B').app index function)
        at naturalValue
    rw [regroupAt] at naturalValue
    exact naturalValue
  exact baseValue.trans evaluated

noncomputable def argumentName (f : X ⟶ P)
    (A : DisplayedFamily.{u, u, u, u} P) (Q : Face.{u, u, u} C)
    (g : totalSpace (reindexDisplayed f A) ⟶ Q) :
    totalSpace (reindexDisplayed f A) ⟶ totalSpace (argumentFamily A Q) :=
  totalReindexMap (name f A Q g) (argumentFamily A Q)

theorem argumentName_projection (f : X ⟶ P)
    (A : DisplayedFamily.{u, u, u, u} P) (Q : Face.{u, u, u} C)
    (g : totalSpace (reindexDisplayed f A) ⟶ Q) :
    argumentName f A Q g ≫ totalProjection (argumentFamily A Q) =
      totalProjection (reindexDisplayed f A) ≫ name f A Q g :=
  totalReindexMap_square _ _

set_option backward.isDefEq.respectTransparency false in
/-- The universal evaluator returns the original dependent parameter map
on every supplied contextual argument. -/
theorem name_evaluation (f : X ⟶ P)
    (A : DisplayedFamily.{u, u, u, u} P) (Q : Face.{u, u, u} C)
    (g : totalSpace (reindexDisplayed f A) ⟶ Q) :
    argumentName f A Q g ≫ evaluation A Q = g := by
  ext world receipt
  let B := parameterFamily (totalSpace A) Q
  let A' := reindexDisplayed f A
  let B' := reindexDisplayed (totalReindexMap f A) B
  let body : B'.sections := parameterSection g
  change
    ((displayedProductAdjunction A).counit.app B).app
      ⟨world, ⟨f.app world receipt.1, receipt.2⟩⟩
      ((piSubstitutionIso f A B).hom.app ⟨world, receipt.1⟩
        ((lamDisplayed body).val ⟨world, receipt.1⟩)) = g.app world receipt
  have comparison := evaluation_baseChange f A B ⟨world, receipt⟩
    ((lamDisplayed body).val ⟨world, receipt.1⟩)
  have evaluated := piSectionEquiv_inverse_value A' B' (lamDisplayed body)
    ⟨world, receipt⟩
  have betaValue := congrArg (fun witness : B'.sections => witness.val ⟨world, receipt⟩)
    ((piSectionEquiv A' B').symm_apply_apply body)
  exact comparison.trans (evaluated.symm.trans betaValue)

noncomputable def readParameters (A : DisplayedFamily.{u, u, u, u} P)
    (Q : Face.{u, u, u} C) (h : X ⟶ parameters A Q) :
    totalSpace (reindexDisplayed (h ≫ totalProjection (choices A Q)) A) ⟶ Q :=
  totalReindexMap h (argumentFamily A Q) ≫ evaluation A Q

set_option backward.isDefEq.respectTransparency false in
/-- A natural function-parameter map is recovered from its base projection
and complete dependent evaluation. This includes all future arguments. -/
theorem name_eta (A : DisplayedFamily.{u, u, u, u} P)
    (Q : Face.{u, u, u} C) (h : X ⟶ parameters A Q) :
    name (h ≫ totalProjection (choices A Q)) A Q (readParameters A Q h) = h := by
  let f := h ≫ totalProjection (choices A Q)
  let B := parameterFamily (totalSpace A) Q
  let A' := reindexDisplayed f A
  let B' := reindexDisplayed (totalReindexMap f A) B
  let k : (reindexDisplayed f (choices A Q)).sections :=
    reindexDisplayedSection h (reindexDisplayed (totalProjection (choices A Q))
      (choices A Q)) (presheafVariable (choices A Q))
  let function : (piDisplayed A' B').sections :=
    (Functor.sectionsFunctor X.Elements).map (piSubstitutionIso f A B).inv k
  have recovered (point : X.Elements) :
      (piSubstitutionIso f A B).hom.app point (function.val point) = k.val point :=
    ConcreteCategory.congr_hom ((piSubstitutionIso f A B).inv_hom_id_app point)
      (k.val point)
  have body : (piSectionEquiv A' B').symm function =
      parameterSection (readParameters A Q h) := by
    apply (Functor.sections_ext_iff).2
    intro point
    have evaluated := piSectionEquiv_inverse_value A' B' function point
    have comparison := evaluation_baseChange f A B point
      (function.val ((totalProjection A').mapElements.obj point))
    have same := recovered ((totalProjection A').mapElements.obj point)
    exact evaluated.trans (comparison.symm.trans
      (congrArg
        (((displayedProductAdjunction A).counit.app B).app
          ((totalReindexMap f A).mapElements.obj point)) same))
  have abstraction : lamDisplayed (parameterSection (readParameters A Q h)) = function :=
    (congrArg lamDisplayed body.symm).trans (pi_eta function)
  ext world value
  apply Sigma.ext (by rfl)
  apply heq_of_eq
  change (piSubstitutionIso f A B).hom.app ⟨world, value⟩
      ((lamDisplayed (parameterSection (readParameters A Q h))).val ⟨world, value⟩) =
    (h.app world value).2
  rw [abstraction]
  exact recovered ⟨world, value⟩

/-- The parameter space represents a base name together with a natural
dependent name over that base, rather than an objectwise choice of values. -/
noncomputable def nameEquiv (A : DisplayedFamily.{u, u, u, u} P)
    (Q : Face.{u, u, u} C) :
    (X ⟶ parameters A Q) ≃
      Σ f : X ⟶ P, (totalSpace (reindexDisplayed f A) ⟶ Q) where
  toFun h := ⟨h ≫ totalProjection (choices A Q), readParameters A Q h⟩
  invFun pair := name pair.1 A Q pair.2
  left_inv := name_eta A Q
  right_inv pair := Sigma.ext (name_projection pair.1 A Q pair.2)
    (heq_of_eq (name_evaluation pair.1 A Q pair.2))

set_option backward.isDefEq.respectTransparency false in
/-- Context substitution precomposes the universal name and its dependent
body map. The represented parameter space itself is retained. -/
theorem name_substitution {Y : Face.{u, u, u} C} (s : Y ⟶ X) (f : X ⟶ P)
    (A : DisplayedFamily.{u, u, u, u} P) (Q : Face.{u, u, u} C)
    (g : totalSpace (reindexDisplayed f A) ⟶ Q) :
    name (s ≫ f) A Q (totalReindexMap s (reindexDisplayed f A) ≫ g) =
      s ≫ name f A Q g := by
  have recovery := name_eta A Q (s ≫ name f A Q g)
  change name (s ≫ f) A Q
      (totalReindexMap (s ≫ name f A Q g) (argumentFamily A Q) ≫ evaluation A Q) =
    s ≫ name f A Q g at recovery
  have sameBody :
      totalReindexMap (s ≫ name f A Q g) (argumentFamily A Q) ≫ evaluation A Q =
        totalReindexMap s (reindexDisplayed f A) ≫ g := by
    rw [← totalReindexMap_comp, Category.assoc]
    change totalReindexMap s (reindexDisplayed f A) ≫
      (argumentName f A Q g ≫ evaluation A Q) = _
    rw [name_evaluation]
  exact (congrArg (name (s ≫ f) A Q) sameBody).symm.trans recovery

end Mettapedia.TypeTheory.NativeLocalFunctionParameters
