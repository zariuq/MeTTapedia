import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedTypeComparison

/-!
# Naturality of the categorical and Set interpretation comparison

Model maps act through their binding and event components at the one-point
stage. Transporting those actual maps through the program and event valuation
equivalence gives the maps of the corresponding ordinary Set semantics.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedTypeComparison

universe u

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedSetSemantics
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels
open Mettapedia.OSLF.Binding.CategoricalBindingModel
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalSubstitutionModel
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment mapJudgment)
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution
  (substJudgment mapJudgment_substJudgment)

variable {S : Signature} {R : List (LocalRule S)}
variable {schema : List (MetaArity S)} {equations : List (EqAxiom S schema)}

private theorem conjugate_apply {C : Type*} [Category C] {F F' G G' : C ⥤ Type u}
    (e : ∀ a, F.obj a ≃ G.obj a) (e' : ∀ a, F'.obj a ≃ G'.obj a)
    (nat : ∀ {a b} (f : a ⟶ b) (x : F.obj a), e b (F.map f x) = G.map f (e a x))
    (nat' : ∀ {a b} (f : a ⟶ b) (x : F'.obj a), e' b (F'.map f x) = G'.map f (e' a x))
    (α : F ⟶ F') (a : C) (x : G.obj a) :
    ((equivalencesNatIso F G e nat).inv ≫ α ≫ (equivalencesNatIso F' G' e' nat').hom).app a x =
      e' a (α.app a ((e a).symm x)) := rfl

private theorem conjugate_apply_equiv {C : Type*} [Category C] {F F' G G' : C ⥤ Type u}
    (e : ∀ a, F.obj a ≃ G.obj a) (e' : ∀ a, F'.obj a ≃ G'.obj a)
    (nat : ∀ {a b} (f : a ⟶ b) (x : F.obj a), e b (F.map f x) = G.map f (e a x))
    (nat' : ∀ {a b} (f : a ⟶ b) (x : F'.obj a), e' b (F'.map f x) = G'.map f (e' a x))
    (α : F ⟶ F') (a : C) (x : F.obj a) :
    ((equivalencesNatIso F G e nat).inv ≫ α ≫ (equivalencesNatIso F' G' e' nat').hom).app a (e a x) =
      e' a (α.app a x) := by
  rw [conjugate_apply, Equiv.symm_apply_apply]

namespace TypeModel

variable (M : CategoricalModel R equations (D := Type u))

/-- Contextual event substitution uses the categorical model's action
with the represented environment converted to its natural family. -/
theorem operational_act (j : Judgment (algebra M)) (e : (operational M).model.carrier j)
    {Δ : Ctx S} (σ : BindingSubstitutionAlgebra.Environment S (algebra M).substitution.Carrier j.1 Δ)
    (target : Judgment (algebra M)) (same : substJudgment j σ = target) :
    (operational M).model.act j e σ target same =
      M.act PUnit (mapJudgment (fromRepresented M) j) e
        (fun t v => (fromRepresented M).raw.map (σ t v))
        (mapJudgment (fromRepresented M) target)
        ((mapJudgment_substJudgment (fromRepresented M) j σ).symm.trans
          (congrArg (mapJudgment (fromRepresented M)) same)) := rfl

/-- Every rule uses the same authored occurrence and its ordered local
premises under the program carrier equivalence. -/
theorem operational_rule {j : Judgment (algebra M)} (shape : Shape R (algebra M) j)
    (children : ∀ i : Fin (R.get shape.1.index).2.premises.length,
      (operational M).model.carrier (childJudgment R (algebra M) shape.1 i)) :
    (operational M).model.rules.act () j ⟨shape, children⟩ =
      (M.rules PUnit).act () (mapJudgment (fromRepresented M) j)
        ⟨mapShape R (fromRepresented M) shape, fun i =>
          ((mapInstance_child R (fromRepresented M) shape.1 i).symm ▸ children i :
            M.objects.StageEvent PUnit (childJudgment R (M.programModel.stage PUnit)
              (mapInstance R (fromRepresented M) shape.1) i))⟩ := rfl

/-- The valuation equivalence is natural in classifier arrows. -/
def valuationIso : (M.stageTarget PUnit).semantics ≅ combinedSetSemantics (operational M) :=
  equivalencesNatIso (M.stageTarget PUnit).semantics (combinedSetSemantics (operational M))
    (valuationEquiv M) (valuationEquiv_transport M)

variable {M} {N P : CategoricalModel R equations (D := Type u)}

/-- The actual stage action of a model map on its Set-valued valuations. -/
def stageSemanticsMap (f : M ⟶ N) :
    (M.stageTarget PUnit).semantics ⟶ (N.stageTarget PUnit).semantics :=
  ClassifierTarget.semanticsMap _ (f.targetHom PUnit)

theorem stageSemanticsMap_id (M : CategoricalModel R equations (D := Type u)) :
    stageSemanticsMap (𝟙 M) = 𝟙 (M.stageTarget PUnit).semantics := by
  apply NatTrans.ext
  funext a
  apply TypeCat.Hom.ext
  apply TypeCat.Fun.ext
  funext value
  exact CategoricalModel.Hom.valuation_id M value

theorem stageSemanticsMap_comp (f : M ⟶ N) (g : N ⟶ P) :
    stageSemanticsMap (f ≫ g) = stageSemanticsMap f ≫ stageSemanticsMap g := by
  apply NatTrans.ext
  funext a
  apply TypeCat.Hom.ext
  apply TypeCat.Fun.ext
  funext value
  exact CategoricalModel.Hom.valuation_comp f g value

/-- The corresponding ordinary semantics map is induced by the model's
actual map of programs and events. No inverse model map is required. -/
def ordinarySemanticsMap (f : M ⟶ N) :
    combinedSetSemantics (operational M) ⟶ combinedSetSemantics (operational N) :=
  (valuationIso M).inv ≫ stageSemanticsMap f ≫ (valuationIso N).hom

/-- The induced ordinary program map preserves the full binding clone. -/
def representedModelMap (f : M ⟶ N) : FreeBindingClone.Hom (algebra M) (algebra N) :=
  FreeBindingClone.Hom.comp (fromRepresented M)
    (FreeBindingClone.Hom.comp (stageMap f.program PUnit) (toRepresented N))

theorem ordinarySemanticsMap_apply (f : M ⟶ N) (a : Classifier R equations)
    (value : (operational M).toTarget.Valuation a) :
    (ordinarySemanticsMap f).app a value =
      valuationEquiv N a (f.valuation ((valuationEquiv M a).symm value)) :=
  conjugate_apply (F := (M.stageTarget PUnit).semantics) (F' := (N.stageTarget PUnit).semantics)
    (G := combinedSetSemantics (operational M)) (G' := combinedSetSemantics (operational N))
    (valuationEquiv M) (valuationEquiv N)
    (valuationEquiv_transport M) (valuationEquiv_transport N) (stageSemanticsMap f) a value

/-- The induced Set-semantics map applies the actual represented binding
map to its whole contextual program interpretation. -/
theorem ordinarySemanticsMap_point (f : M ⟶ N) (a : Classifier R equations)
    (value : (operational M).toTarget.Valuation a) :
    ((ordinarySemanticsMap f).app a value).point =
      FreeBindingClone.Hom.comp value.point (representedModelMap f) := by
  have moved := (f.targetHom PUnit).program_point
    ((recoveredTargetHom M).point value.point)
  have recovered := (recoveredTargetHom M).program_point value.point
  exact (congrArg (fun v => v.point) (ordinarySemanticsMap_apply f a value)).trans
    ((congrArg (fun h => FreeBindingClone.Hom.comp h (toRepresented N)) moved).trans
      (congrArg (fun h => FreeBindingClone.Hom.comp
        (FreeBindingClone.Hom.comp h (stageMap f.program PUnit)) (toRepresented N)) recovered))

/-- Event components use the model map's actual event arrows. -/
theorem ordinarySemanticsMap_event (f : M ⟶ N) (a : Classifier R equations)
    (value : (operational M).toTarget.Valuation a)
    (i : Fin (events R equations a).listed.length) :
    HEq (((ordinarySemanticsMap f).app a value).event i)
      (f.events.stage PUnit _ (((valuationEquiv M a).symm value).event i)) :=
  (congr_arg_heq (fun v : (operational N).toTarget.Valuation a => v.event i)
    (ordinarySemanticsMap_apply f a value)).trans
    ((representedTargetHom_event N (f.valuation ((valuationEquiv M a).symm value)) i).trans
      (CategoricalModel.Hom.valuation_event f ((valuationEquiv M a).symm value) i))

theorem ordinarySemanticsMap_valuationEquiv (f : M ⟶ N) (a : Classifier R equations)
    (value : M.StageValuation PUnit a) :
    (ordinarySemanticsMap f).app a (valuationEquiv M a value) =
      valuationEquiv N a (f.valuation value) :=
  conjugate_apply_equiv (F := (M.stageTarget PUnit).semantics) (F' := (N.stageTarget PUnit).semantics)
    (G := combinedSetSemantics (operational M)) (G' := combinedSetSemantics (operational N))
    (valuationEquiv M) (valuationEquiv N)
    (valuationEquiv_transport M) (valuationEquiv_transport N) (stageSemanticsMap f) a value

theorem ordinarySemanticsMap_id (M : CategoricalModel R equations (D := Type u)) :
    ordinarySemanticsMap (𝟙 M) = 𝟙 (combinedSetSemantics (operational M)) := by
  unfold ordinarySemanticsMap
  rw [stageSemanticsMap_id, Category.id_comp, Iso.inv_hom_id]

theorem ordinarySemanticsMap_comp (f : M ⟶ N) (g : N ⟶ P) :
    ordinarySemanticsMap (f ≫ g) = ordinarySemanticsMap f ≫ ordinarySemanticsMap g := by
  unfold ordinarySemanticsMap
  rw [stageSemanticsMap_comp]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- Corresponding ordinary Set semantics, functorial on every existing
categorical model map. -/
def ordinarySemanticsFunctor : CategoricalModel R equations (D := Type u) ⥤
    (Classifier R equations ⥤ Type u) where
  obj M := combinedSetSemantics (operational M)
  map f := ordinarySemanticsMap f
  map_id M := ordinarySemanticsMap_id M
  map_comp f g := ordinarySemanticsMap_comp f g

/-- The actual classifying semantics on every categorical model map. -/
def categoricalSemanticsFunctor : CategoricalModel R equations (D := Type u) ⥤
    (Classifier R equations ⥤ Type u) where
  obj M := M.classifyingFunctor
  map f := CategoricalModel.classifyingMap f
  map_id M := CategoricalModel.classifyingMap_id M
  map_comp f g := CategoricalModel.classifyingMap_comp f g

/-- The one-point generalized valuation semantics on all model maps. -/
def stageSemanticsFunctor : CategoricalModel R equations (D := Type u) ⥤
    (Classifier R equations ⥤ Type u) where
  obj M := (M.stageTarget PUnit).semantics
  map f := stageSemanticsMap f
  map_id M := stageSemanticsMap_id M
  map_comp f g := stageSemanticsMap_comp f g

theorem stageValueEquiv_modelMap (f : M ⟶ N) (a : Classifier R equations)
    (x : M.classifyingObject a) :
    stageValueEquiv N a ((CategoricalModel.classifyingMap f).app a x) =
      f.valuation (stageValueEquiv M a x) := by
  have point : (pointEquiv (N.classifyingObject a)).symm
      ((CategoricalModel.classifyingMap f).app a x) =
      (pointEquiv (M.classifyingObject a)).symm x ≫ (CategoricalModel.classifyingMap f).app a := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    rfl
  exact (congrArg ((N.valuationsRepresentableBy a).homEquiv) point).trans
    (CategoricalModel.homEquiv_classifyingMap f a ((pointEquiv (M.classifyingObject a)).symm x))

/-- The value comparison commutes with every model map, including maps
which identify events or are not invertible. -/
theorem valueEquiv_modelMap (f : M ⟶ N) (a : Classifier R equations)
    (x : M.classifyingObject a) :
    valueEquiv N a ((CategoricalModel.classifyingMap f).app a x) =
      (ordinarySemanticsMap f).app a (valueEquiv M a x) :=
  equivalenceSquare (stageValueEquiv M a) (stageValueEquiv N a)
    (valuationEquiv M a) (valuationEquiv N a) ((CategoricalModel.classifyingMap f).app a)
    (f.valuation) ((ordinarySemanticsMap f).app a)
    (stageValueEquiv_modelMap f a) (fun value => (ordinarySemanticsMap_valuationEquiv f a value).symm) x

private def classificationStageNatIso : categoricalSemanticsFunctor (R := R) (equations := equations) ≅
    stageSemanticsFunctor :=
  NatIso.ofComponents (fun M => equivalencesNatIso M.classifyingFunctor (M.stageTarget PUnit).semantics
    (stageValueEquiv M) (stageValueEquiv_map M)) (fun {M N} f => by
    apply NatTrans.ext
    funext a
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext x
    exact stageValueEquiv_modelMap f a x)

private def valuationNatIso : stageSemanticsFunctor (R := R) (equations := equations) ≅
    ordinarySemanticsFunctor :=
  NatIso.ofComponents (fun M => valuationIso M) (fun {M N} f => by
    change stageSemanticsMap f ≫ (valuationIso N).hom =
      (valuationIso M).hom ≫ ordinarySemanticsMap f
    simp only [ordinarySemanticsMap, Iso.hom_inv_id_assoc])

/-- The categorical and ordinary Set interpretations are naturally
isomorphic as functors of the entire Type-valued model category. -/
def classificationSetNatIso : categoricalSemanticsFunctor (R := R) (equations := equations) ≅
    ordinarySemanticsFunctor :=
  classificationStageNatIso ≪≫ valuationNatIso

end TypeModel

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedTypeComparison

end
