import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.TypedQuotientValuesSubstitution
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.TypedQuotientControls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.ConversionQuotientControls

/-!
# Actual typed eta readouts at a supplied dependent function

The telescope binds an actual small type X and a supplied function X → X.
The function variable and its generated eta expansion have the same set
value at every satisfying environment, despite their distinct raw conversion
classes. Concrete identity and constant functions remain distinguishable.

The set model remains conditional on the explicit cofinal-inaccessibles
hypothesis. Formation, Church--Rosser and annotation lifting are supplied
by the independently earned tower results.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace Examples.TypedQuotientModelControls

open TypedEquality TypedEquality.Annotated TypedEquality.Normalization
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetInterpretation (universeSet)
open ZFSetDependentProducts (graph graph_mem_piSet)
open ZFSetTraceProducts (traceLam tracePiSet traceApp mem_tracePiSet traceApp_graph_beta)
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetTraceUniverseInterpretation (interpretHead)

universe u

abbrev package : ChurchRules Tower.rules := TowerControls.P₀

abbrev annotatedContext : CCtx Tower.Head 2 :=
  .snoc (.snoc .nil (.head (.sort Tower.zero))) (.pi (.var 0) (.var 1))

theorem annotatedFormed : CCtxFormed package annotatedContext :=
  .snoc (.snoc .nil ⟨_, .sort _, .headType (.sort _)⟩)
    ⟨.sort (.max Tower.zero Tower.zero), .sort _,
      .piForm (.var 0) (.sort _) (.var 1) (.sort _) (.sorts _ _)⟩

noncomputable def termReadout (h : CofinalInaccessibles.{u}) :
    FormationSensitiveTypedQuotient.QTerm TypedQuotientControls.qualification
      TypedQuotientControls.functionContext.erase →
        ConversionQuotient.Value (heads := interpretHead h ∅ ∅ (fun _ => 0))
          (constants := fun _ => ∅) annotatedContext :=
  TypedQuotientValues.termValue TypedQuotientControls.qualification towerLiftingFacts
    (standardTowerModel h) annotatedFormed rfl

theorem function_readout (h : CofinalInaccessibles.{u})
    (environment : ConversionQuotient.Environment
      (heads := interpretHead h ∅ ∅ (fun _ => 0)) (constants := fun _ => ∅) annotatedContext) :
    termReadout h (FormationSensitiveTypedQuotient.QTerm.mk
      TypedQuotientControls.qualification TypedQuotientControls.functionValue.erase) environment =
        environment.val 0 := by
  have comparison := ConversionQuotient.termValue_annotation
    (S := TypedQuotientControls.setting) towerLiftingFacts (standardTowerModel h)
    TypedQuotientControls.qualification.forms TypedQuotientControls.qualification.roots
    TypedQuotientControls.qualification.heads TypedQuotientControls.qualification.church
    annotatedFormed rfl TypedQuotientControls.functionValue.erase
    (code := (.var 0 : CTm Tower.Head 2))
    (typeCode := (.pi (.var 1) (.var 2) : CTm Tower.Head 2))
    (CDerivable.var (P := package) (Γ := annotatedContext) (0 : Fin 2)) rfl rfl
  exact congrFun comparison environment

/-- The generated eta equality retains the exact supplied function value. -/
theorem eta_readout (h : CofinalInaccessibles.{u})
    (environment : ConversionQuotient.Environment
      (heads := interpretHead h ∅ ∅ (fun _ => 0)) (constants := fun _ => ∅) annotatedContext) :
    termReadout h (FormationSensitiveTypedQuotient.QTerm.mk
      TypedQuotientControls.qualification TypedQuotientControls.etaValue.erase) environment =
        environment.val 0 := by
  have same : FormationSensitiveTypedQuotient.QTerm.mk
      TypedQuotientControls.qualification TypedQuotientControls.functionValue.erase =
    FormationSensitiveTypedQuotient.QTerm.mk
      TypedQuotientControls.qualification TypedQuotientControls.etaValue.erase :=
    congrArg Subtype.val TypedQuotientControls.eta_same_typed_class
  rw [← same]
  exact function_readout h environment

noncomputable def suppliedEnvironment (h : CofinalInaccessibles.{u})
    (type function : ZFSet.{u}) (typeSmall : type ∈ universeSet h ∅ (0 : Nat))
    (functionMember : function ∈ tracePiSet type (fun _ => type)) :
    ConversionQuotient.Environment (heads := interpretHead h ∅ ∅ (fun _ => 0))
      (constants := fun _ => ∅) annotatedContext :=
  ⟨extend (extend Fin.elim0 type) function,
    (sat_snoc _ _).mpr ⟨(sat_snoc _ _).mpr ⟨sat_nil _ _ Fin.elim0, typeSmall⟩, functionMember⟩⟩

noncomputable def identityFunction (type : ZFSet.{u}) : ZFSet.{u} := traceLam (graph type id)

theorem identityFunction_member (type : ZFSet.{u}) :
    identityFunction type ∈ tracePiSet type (fun _ => type) :=
  mem_tracePiSet.mpr ⟨graph type id, graph_mem_piSet (fun _ member => member), rfl⟩

noncomputable def constantFunction (type : ZFSet.{u}) : ZFSet.{u} :=
  traceLam (graph type (fun _ => ∅))

theorem constantFunction_member {type : ZFSet.{u}} (inhabited : ∅ ∈ type) :
    constantFunction type ∈ tracePiSet type (fun _ => type) :=
  mem_tracePiSet.mpr ⟨graph type (fun _ => ∅), graph_mem_piSet (fun _ _ => inhabited), rfl⟩

noncomputable def identityEnvironment (h : CofinalInaccessibles.{u}) :=
  suppliedEnvironment h ConversionQuotientControls.twoValues
    (identityFunction ConversionQuotientControls.twoValues) (ConversionQuotientControls.twoValues_small h)
    (identityFunction_member _)

noncomputable def constantEnvironment (h : CofinalInaccessibles.{u}) :=
  suppliedEnvironment h ConversionQuotientControls.twoValues
    (constantFunction ConversionQuotientControls.twoValues) (ConversionQuotientControls.twoValues_small h)
    (constantFunction_member (by simp [ConversionQuotientControls.twoValues]))

/-- On a nonempty variable domain, eta still reads the supplied identity
function and application computes the nonempty selected member. -/
theorem eta_identity_application (h : CofinalInaccessibles.{u}) :
    traceApp (termReadout h (FormationSensitiveTypedQuotient.QTerm.mk
      TypedQuotientControls.qualification TypedQuotientControls.etaValue.erase)
        (identityEnvironment h)) {∅} = ({∅} : ZFSet.{u}) := by
  rw [eta_readout]
  exact traceApp_graph_beta (a := ConversionQuotientControls.twoValues)
    (x := ({∅} : ZFSet.{u})) id (by simp [ConversionQuotientControls.twoValues])

theorem eta_constant_application (h : CofinalInaccessibles.{u}) :
    traceApp (termReadout h (FormationSensitiveTypedQuotient.QTerm.mk
      TypedQuotientControls.qualification TypedQuotientControls.etaValue.erase)
        (constantEnvironment h)) {∅} = (∅ : ZFSet.{u}) := by
  rw [eta_readout]
  exact traceApp_graph_beta (a := ConversionQuotientControls.twoValues)
    (x := ({∅} : ZFSet.{u})) (fun _ => ∅) (by simp [ConversionQuotientControls.twoValues])

/-- Typed eta does not make distinct supplied functions interchangeable. -/
theorem distinct_function_readouts (h : CofinalInaccessibles.{u}) :
    termReadout h (FormationSensitiveTypedQuotient.QTerm.mk
      TypedQuotientControls.qualification TypedQuotientControls.etaValue.erase) (identityEnvironment h) ≠
        termReadout h (FormationSensitiveTypedQuotient.QTerm.mk
          TypedQuotientControls.qualification TypedQuotientControls.etaValue.erase)
            (constantEnvironment h) := by
  intro same
  have applications := congrArg (fun function : ZFSet.{u} => traceApp function {∅}) same
  rw [eta_identity_application, eta_constant_application] at applications
  have self : (∅ : ZFSet.{u}) ∈ {∅} := ZFSet.mem_singleton.mpr rfl
  rw [applications] at self
  exact ZFSet.notMem_empty _ self

noncomputable def rawTermReadout (h : CofinalInaccessibles.{u}) :
    FormationSensitiveContextual.QTerm TypedQuotientControls.functionContext.erase →
      ConversionQuotient.Value (heads := interpretHead h ∅ ∅ (fun _ => 0))
        (constants := fun _ => ∅) annotatedContext :=
  ConversionQuotient.quotientTermValue (S := TypedQuotientControls.setting)
    (source := TypedQuotientControls.functionContext.erase) towerLiftingFacts (standardTowerModel h)
    TypedQuotientControls.qualification.forms TypedQuotientControls.qualification.roots
    TypedQuotientControls.qualification.heads TypedQuotientControls.qualification.church
    annotatedFormed rfl

theorem readout_triangle (h : CofinalInaccessibles.{u})
    (term : FormationSensitiveContextual.QTerm TypedQuotientControls.functionContext.erase)
    (environment : ConversionQuotient.Environment
      (heads := interpretHead h ∅ ∅ (fun _ => 0)) (constants := fun _ => ∅) annotatedContext) :
    termReadout h (FormationSensitiveTypedQuotient.QTerm.ofRaw TypedQuotientControls.qualification term)
      environment = rawTermReadout h term environment :=
  congrFun (TypedQuotientValues.termValue_ofRaw TypedQuotientControls.qualification
    towerLiftingFacts (standardTowerModel h) annotatedFormed rfl term) environment

/-- Distinct raw classes factor to the same genuine model readout through
the typed equality quotient. -/
theorem eta_factorization (h : CofinalInaccessibles.{u})
    (environment : ConversionQuotient.Environment
      (heads := interpretHead h ∅ ∅ (fun _ => 0)) (constants := fun _ => ∅) annotatedContext) :
    FormationSensitiveContextual.QTerm.mk TypedQuotientControls.functionValue.erase ≠
      FormationSensitiveContextual.QTerm.mk TypedQuotientControls.etaValue.erase ∧
    rawTermReadout h (FormationSensitiveContextual.QTerm.mk TypedQuotientControls.functionValue.erase)
        environment = environment.val 0 ∧
    rawTermReadout h (FormationSensitiveContextual.QTerm.mk TypedQuotientControls.etaValue.erase)
        environment = environment.val 0 := by
  refine ⟨TypedQuotientControls.eta_distinct_raw_classes, ?_, ?_⟩
  · exact (readout_triangle h _ environment).symm.trans (function_readout h environment)
  · exact (readout_triangle h _ environment).symm.trans (eta_readout h environment)

noncomputable def memberReadout (h : CofinalInaccessibles.{u}) :
    FormationSensitiveTypedQuotient.QTerm TypedQuotientControls.qualification
      ConversionQuotientControls.sourceContext →
        ConversionQuotient.Value (heads := interpretHead h ∅ ∅ (fun _ => 0))
          (constants := fun _ => ∅) ConversionQuotientControls.annotatedContext :=
  TypedQuotientValues.termValue TypedQuotientControls.qualification towerLiftingFacts
    (standardTowerModel h) ConversionQuotientControls.annotatedFormed rfl

theorem member_readout (h : CofinalInaccessibles.{u})
    (environment : ConversionQuotient.Environment
      (heads := interpretHead h ∅ ∅ (fun _ => 0)) (constants := fun _ => ∅)
        ConversionQuotientControls.annotatedContext) :
    memberReadout h (FormationSensitiveTypedQuotient.QTerm.mk
      TypedQuotientControls.qualification ConversionQuotientControls.betaValue) environment =
        environment.val 0 := by
  have triangle := congrFun (TypedQuotientValues.termValue_ofRaw TypedQuotientControls.qualification
    towerLiftingFacts (standardTowerModel h) ConversionQuotientControls.annotatedFormed rfl
    (FormationSensitiveContextual.QTerm.mk ConversionQuotientControls.betaValue)) environment
  exact triangle.trans ((ConversionQuotientControls.computed_readouts h environment).2.1)

/-- The new typed class action uses the actual nonprojection substitution
selecting the supplied y rather than the older x. -/
theorem reindexed_member_reads_y (h : CofinalInaccessibles.{u}) :
    TypedQuotientValues.termValue TypedQuotientControls.qualification towerLiftingFacts
      (standardTowerModel h) ConversionQuotientControls.extendedFormed rfl
      ((FormationSensitiveTypedQuotient.QTerm.mk TypedQuotientControls.qualification
        ConversionQuotientControls.betaValue).reindex ConversionQuotientControls.replacement)
      (ConversionQuotientControls.thirdEnvironment h) = ({∅} : ZFSet.{u}) := by
  have comparison := TypedQuotientValues.termValue_reindex TypedQuotientControls.qualification
    towerLiftingFacts (standardTowerModel h) ConversionQuotientControls.extendedFormed rfl
    ConversionQuotientControls.annotatedFormed rfl ConversionQuotientControls.replacement
    ConversionQuotientControls.replacementTyped ConversionQuotientControls.replacementErases
    (FormationSensitiveTypedQuotient.QTerm.mk TypedQuotientControls.qualification
      ConversionQuotientControls.betaValue) (ConversionQuotientControls.thirdEnvironment h)
  exact comparison.trans (member_readout h _)

end Examples.TypedQuotientModelControls
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
