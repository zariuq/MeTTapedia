import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.ConversionQuotientSubstitution
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerConservativity
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.Elaboration
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.Consistency

/-!
# Inhabited dependent controls for model-valued conversion classes

The tower's preservation, Church--Rosser and annotation-lifting
qualifications are supplied by their earned constructions. Its set model
is constructed relative to the explicit cofinal-inaccessibles hypothesis.
The telescope binds a type X and a member x of X; its interpreted family
varies with X, and its term readout varies with the actual supplied x.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ConversionQuotientControls

open TypedEquality TypedEquality.Annotated TypedEquality.Normalization
open _root_.CategoryTheory
open FormationSensitiveContextual
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.ConversionQuotient
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetInterpretation (universeSet universeSet_closed seed_mem_universeSet)
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetTraceUniverseInterpretation (interpretHead)

universe u

abbrev package : ChurchRules Tower.rules := TowerControls.P₀
abbrev annotatedContext : CCtx Tower.Head 2 := TowerControls.Γ₂

theorem annotatedFormed : CCtxFormed package annotatedContext :=
  .snoc (.snoc .nil ⟨_, .sort _, .headType (.sort _)⟩) ⟨_, .sort _, .var 0⟩

abbrev sourceContext : Context Tower.rules :=
  ⟨2, .snoc (.snoc .nil (.head (.sort Tower.zero))) (.var 0),
    .snoc (.snoc .nil (.headType (.sort _)) (.sort _)) (.var 0) (.sort _)⟩

def typeX : TypeOver sourceContext :=
  ⟨.var 1, .sort Tower.zero, .sort _, .var 1⟩

def valueX : Term sourceContext typeX := ⟨.var 0, .var 0⟩

theorem identityFormation : FormationSensitive.Typing Tower.rules sourceContext.raw
    (.pi (.var 1) (.var 2)) (.head (.sort (.max Tower.zero Tower.zero))) :=
  .piForm (.var 1) (.sort _) (.var 2) (.sort _) (.sorts _ _)

def betaValue : Term sourceContext typeX :=
  ⟨.app (.lam (.var 0)) (.var 0),
    .appElim (.lamIntro identityFormation (.sort _) (.var 0)) (.var 0)⟩

theorem universeIdentityFormation : FormationSensitive.Typing Tower.rules sourceContext.raw
    (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero)))
    (.head (.sort (.max (.succ Tower.zero) (.succ Tower.zero)))) :=
  .piForm (.headType (.sort _)) (.sort _) (.headType (.sort _)) (.sort _) (.sorts _ _)

def computedType : TypeOver sourceContext :=
  ⟨.app (.lam (.var 0)) (.var 1), .sort Tower.zero, .sort _,
    .appElim
      (.lamIntro universeIdentityFormation (.sort _) (.var 0))
      (.var 1)⟩

theorem computedTypeConversion :
    Conv Tower.rules.headEq computedType.code typeX.code Tower.rules.computation :=
  .rel _ _ (.betaPi (.var 0) (.var 1))

def convertedValue : Term sourceContext computedType :=
  valueX.convertType computedType computedTypeConversion.symm

theorem betaConversion : Conv Tower.rules.headEq betaValue.code valueX.code Tower.rules.computation :=
  .rel _ _ (.betaPi (.var 0) (.var 0))

noncomputable def typeReadout (h : CofinalInaccessibles.{u}) :
    QType sourceContext → Value (heads := interpretHead h ∅ ∅ (fun _ => 0))
      (constants := fun _ => ∅) annotatedContext :=
  quotientTypeValue (S := TowerModel.setting fun _ => 0) (source := sourceContext)
    towerLiftingFacts (standardTowerModel h) TowerModel.facts TowerModel.roots TowerModel.heads
    LevelTower.churchRosser annotatedFormed rfl

noncomputable def termReadout (h : CofinalInaccessibles.{u}) :
    QTerm sourceContext → Value (heads := interpretHead h ∅ ∅ (fun _ => 0))
      (constants := fun _ => ∅) annotatedContext :=
  quotientTermValue (S := TowerModel.setting fun _ => 0) (source := sourceContext)
    towerLiftingFacts (standardTowerModel h) TowerModel.facts TowerModel.roots TowerModel.heads
    LevelTower.churchRosser annotatedFormed rfl

noncomputable def suppliedEnvironment (h : CofinalInaccessibles.{u})
    (type value : ZFSet.{u}) (typeSmall : type ∈ universeSet h ∅ (0 : Nat))
    (valueMember : value ∈ type) :
    Environment (heads := interpretHead h ∅ ∅ (fun _ => 0))
      (constants := fun _ => ∅) annotatedContext :=
  ⟨extend (extend Fin.elim0 type) value, (sat_snoc _ _).mpr
    ⟨(sat_snoc _ _).mpr ⟨sat_nil _ _ Fin.elim0, typeSmall⟩, valueMember⟩⟩

theorem read_typeX (h : CofinalInaccessibles.{u})
    (environment : Environment (heads := interpretHead h ∅ ∅ (fun _ => 0))
      (constants := fun _ => ∅) annotatedContext) :
    typeReadout h (QType.mk typeX) environment = environment.val 1 := by
  have comparison := typeValue_annotation (S := TowerModel.setting fun _ => 0)
    towerLiftingFacts (standardTowerModel h) TowerModel.facts TowerModel.roots TowerModel.heads
    LevelTower.churchRosser annotatedFormed rfl typeX
    (code := .var 1) ⟨.sort Tower.zero, .sort _, .var 1⟩ rfl
  exact congrFun comparison environment

theorem read_valueX (h : CofinalInaccessibles.{u})
    (environment : Environment (heads := interpretHead h ∅ ∅ (fun _ => 0))
      (constants := fun _ => ∅) annotatedContext) :
    termReadout h (QTerm.mk valueX) environment = environment.val 0 := by
  have comparison := termValue_annotation (S := TowerModel.setting fun _ => 0)
    towerLiftingFacts (standardTowerModel h) TowerModel.facts TowerModel.roots TowerModel.heads
    LevelTower.churchRosser annotatedFormed rfl valueX
    (code := .var 0) (typeCode := .var 1) (.var 0) rfl rfl
  exact congrFun comparison environment

/-- The readout executes semantic beta and also respects the independently
converted displayed type. -/
theorem computed_readouts (h : CofinalInaccessibles.{u})
    (environment : Environment (heads := interpretHead h ∅ ∅ (fun _ => 0))
      (constants := fun _ => ∅) annotatedContext) :
    typeReadout h (QType.mk computedType) environment = environment.val 1 ∧
      termReadout h (QTerm.mk betaValue) environment = environment.val 0 ∧
      termReadout h (QTerm.mk convertedValue) environment = environment.val 0 := by
  have sameTypes := (QType.mk_eq_iff computedType typeX).mpr computedTypeConversion
  have sameTerms := (QTerm.mk_eq_iff betaValue valueX).mpr ⟨.refl _, betaConversion⟩
  have sameAnnotation : QTerm.mk convertedValue = QTerm.mk valueX :=
    QTerm.mk_convertType valueX computedType computedTypeConversion.symm
  rw [sameTypes, sameTerms, sameAnnotation]
  exact ⟨read_typeX h environment, read_valueX h environment, read_valueX h environment⟩

/-- Different annotation domains survive as syntax while the coherent
admitted beta terms give the same actual supplied value. -/
theorem different_annotations_same_readout (h : CofinalInaccessibles.{u})
    (environment : Environment (heads := interpretHead h ∅ ∅ (fun _ => 0))
      (constants := fun _ => ∅) annotatedContext) :
    (TowerControls.betaAt TowerControls.l0 : CTm Tower.Head 2) ≠ TowerControls.betaAt TowerControls.l1 ∧
      annotationValue (context := annotatedContext) (heads := interpretHead h ∅ ∅ (fun _ => 0))
          (constants := fun _ => ∅) (TowerControls.betaAt TowerControls.l0) environment =
        annotationValue (context := annotatedContext) (TowerControls.betaAt TowerControls.l1) environment := by
  constructor
  · intro same
    cases same
  · have comparison := annotationValue_independent (S := TowerModel.setting fun _ => 0)
      towerLiftingFacts (standardTowerModel h) annotatedFormed
      (CEqual.typed towerLevels (TowerControls.betaAt_equal TowerControls.l0) annotatedFormed).1
      (CEqual.typed towerLevels (TowerControls.betaAt_equal TowerControls.l1) annotatedFormed).1 rfl rfl
    exact congrFun comparison environment

def twoValues : ZFSet.{u} := {∅, {∅}}

theorem twoValues_small (h : CofinalInaccessibles.{u}) :
    twoValues ∈ universeSet h ∅ (0 : Nat) := by
  have emptySmall := empty_mem_universeSet h ∅ (0 : Nat)
  exact (universeSet_closed h ∅ (0 : Nat)).unorderedPair_mem emptySmall
    ((universeSet_closed h ∅ (0 : Nat)).singleton_mem emptySmall)

noncomputable def firstEnvironment (h : CofinalInaccessibles.{u}) :=
  suppliedEnvironment h twoValues ∅ (twoValues_small h) (by simp [twoValues])

noncomputable def secondEnvironment (h : CofinalInaccessibles.{u}) :=
  suppliedEnvironment h twoValues {∅} (twoValues_small h) (by simp [twoValues])

noncomputable def singletonEnvironment (h : CofinalInaccessibles.{u}) :=
  suppliedEnvironment h {∅} ∅
    ((universeSet_closed h ∅ (0 : Nat)).singleton_mem (empty_mem_universeSet h ∅ (0 : Nat)))
    (ZFSet.mem_singleton.mpr rfl)

/-- The bound type variable itself determines the interpreted family. -/
theorem distinct_supplied_types (h : CofinalInaccessibles.{u}) :
    typeReadout h (QType.mk typeX) (firstEnvironment h) ≠
      typeReadout h (QType.mk typeX) (singletonEnvironment h) := by
  rw [read_typeX, read_typeX]
  change twoValues ≠ ({∅} : ZFSet.{u})
  intro same
  have member : ({∅} : ZFSet.{u}) ∈ twoValues := by simp [twoValues]
  rw [same] at member
  have singletonEmpty : ({∅} : ZFSet.{u}) = ∅ := ZFSet.mem_singleton.mp member
  have self : (∅ : ZFSet.{u}) ∈ {∅} := ZFSet.mem_singleton.mpr rfl
  rw [singletonEmpty] at self
  exact ZFSet.notMem_empty _ self

/-- The quotient interpretation is not a constant-family interpretation:
both environments are admitted, and the actual supplied witness is read. -/
theorem distinct_supplied_witnesses (h : CofinalInaccessibles.{u}) :
    termReadout h (QTerm.mk betaValue) (firstEnvironment h) ≠
      termReadout h (QTerm.mk betaValue) (secondEnvironment h) := by
  rw [(computed_readouts h (firstEnvironment h)).2.1,
    (computed_readouts h (secondEnvironment h)).2.1]
  change (∅ : ZFSet.{u}) ≠ {∅}
  intro same
  have self : (∅ : ZFSet.{u}) ∈ {∅} := ZFSet.mem_singleton.mpr rfl
  rw [← same] at self
  exact ZFSet.notMem_empty _ self

/-- Equality of erasures is insufficient without a common admitted type. -/
theorem erasure_alone_not_admission :
    (TowerControls.idU TowerControls.l0 : CTm Tower.Head 0).erase =
        (TowerControls.idU TowerControls.l1).erase ∧
      ∀ type : CTm Tower.Head 0,
        ¬ CEqual package .nil (TowerControls.idU TowerControls.l0) (TowerControls.idU TowerControls.l1) type :=
  ⟨rfl, fun type => TowerControls.idU_not_equal towerFormerFacts .nil type⟩

abbrev extendedSource : Context Tower.rules := FormationSensitiveContextual.extend sourceContext typeX
abbrev extendedContext : CCtx Tower.Head 3 := .snoc annotatedContext (.var 1)

theorem extendedFormed : CCtxFormed package extendedContext :=
  .snoc annotatedFormed ⟨.sort Tower.zero, .sort _, .var 1⟩

/-- Select the new member y for x, while retaining the actual bound type X. -/
abbrev replacementRaw : Sub Tower.Head 2 3 :=
  Fin.cases (.var 0) (fun _ => .var 2)

def replacement : extendedSource ⟶ sourceContext where
  substitution := replacementRaw
  typed := by
    intro index
    refine Fin.cases ?_ ?_ index
    · exact .var 0
    · intro earlier
      refine Fin.cases ?_ ?_ earlier
      · exact .var 2
      · intro impossible
        exact Fin.elim0 impossible

abbrev annotatedReplacement : CSub Tower.Head 2 3 :=
  Fin.cases (.var 0) (fun _ => .var 2)

theorem replacementTyped : CSubstMor package annotatedContext extendedContext annotatedReplacement := by
  intro index
  refine Fin.cases ?_ ?_ index
  · exact .var 0
  · intro earlier
    refine Fin.cases ?_ ?_ earlier
    · exact .var 2
    · intro impossible
      exact Fin.elim0 impossible

theorem replacementErases (index : Fin 2) :
    (annotatedReplacement index).erase = replacement.substitution index := by
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro earlier
    rfl

noncomputable def extendedTermReadout (h : CofinalInaccessibles.{u}) :
    QTerm extendedSource → Value (heads := interpretHead h ∅ ∅ (fun _ => 0))
      (constants := fun _ => ∅) extendedContext :=
  quotientTermValue (S := TowerModel.setting fun _ => 0) (source := extendedSource)
    towerLiftingFacts (standardTowerModel h) TowerModel.facts TowerModel.roots TowerModel.heads
    LevelTower.churchRosser extendedFormed rfl

/-- The actual quotient substitution reads y, not the previously supplied x. -/
theorem substituted_value_readout (h : CofinalInaccessibles.{u})
    (environment : Environment (heads := interpretHead h ∅ ∅ (fun _ => 0))
      (constants := fun _ => ∅) extendedContext) :
    extendedTermReadout h ((QTerm.mk betaValue).reindex replacement) environment =
      environment.val 0 := by
  have comparison := quotientTermValue_reindex (S := TowerModel.setting fun _ => 0)
    (standardTowerModel h) towerLiftingFacts TowerModel.facts TowerModel.roots TowerModel.heads
    LevelTower.churchRosser extendedFormed rfl annotatedFormed rfl replacement replacementTyped
    replacementErases (QTerm.mk betaValue) environment
  exact comparison.trans
    ((computed_readouts h (substitutionEnvironment (standardTowerModel h)
      replacementTyped environment)).2.1)

noncomputable def thirdEnvironment (h : CofinalInaccessibles.{u}) :
    Environment (heads := interpretHead h ∅ ∅ (fun _ => 0))
      (constants := fun _ => ∅) extendedContext :=
  extendEnvironment (firstEnvironment h) (.var 1) {∅} (by
    change ( {∅} : ZFSet.{u}) ∈ twoValues
    simp [twoValues])

/-- The two different admitted arrows are distinguished by an actual value,
even though they preserve the supplied type variable. -/
theorem replacement_changes_readout (h : CofinalInaccessibles.{u}) :
    extendedTermReadout h ((QTerm.mk betaValue).reindex replacement) (thirdEnvironment h) = {∅} ∧
      termReadout h (QTerm.mk betaValue) (firstEnvironment h) = ∅ ∧
      replacement ≠ projectionHom sourceContext typeX := by
  constructor
  · exact substituted_value_readout h (thirdEnvironment h)
  constructor
  · exact (computed_readouts h (firstEnvironment h)).2.1
  · intro same
    have codes := congrArg (fun arrow : extendedSource ⟶ sourceContext => arrow.substitution 0) same
    change Tm.var (0 : Fin 3) = Tm.var (1 : Fin 3) at codes
    cases codes

end ConversionQuotientControls
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
