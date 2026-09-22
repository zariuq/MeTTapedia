import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeMixedRuleDataOSLFConnection
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.IntrinsicNativeListMapExecutionPath
import Mettapedia.GSLT.Core.OperationalPathFibration

/-!
# The native computation system as an exact executable driver

The mixed rule presentation exposes a request/result interface: a native term
is encoded as rule data, wrapped in `compute`, and evaluated by the generic
MeTTaIL interpreter.  `Computes` records one completed request while retaining
the interpreter as its only execution authority.

This module packages that interface as a GSLT and proves that canonical native
terms form an exactly covered operational subspace.  Forward coverage is the
existing interpreter completeness theorem.  Reverse coverage is the existing
soundness theorem: every result of a request issued at a canonical term is
again canonical and is justified by one intrinsic computational step.

The resulting covered translation retains complete execution routes.  In
particular, mapping a route neither contracts nor expands its primitive-step
sequence; interpreter work performed inside one request remains distinct from
the native transition count.
-/

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace HOLNativeMixedPresentedDriver

open Mettapedia.GSLT
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Presentation
open NativeIndexedFamilies IntrinsicMaps
open IntrinsicNativeListMapComputation
open IntrinsicNativeListMapExecutionPath
open HOLNativeMixedOperationalDecomposition
open HOLNativeMixedRuleData

/-- The intrinsic computational component, without semantic universe-head
equality, regarded as an equality-based GSLT. -/
abbrev nativeSystem (n : Nat) : GSLT :=
  equalityGSLT (Tower.Tm n) ComputationalStep

/-- One driver transition executes one `compute` request using the mixed
rule-data interpreter. -/
abbrev driverSystem : GSLT :=
  equalityGSLT Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Computes

/-- Canonical encoding preserves every intrinsic computational step as one
completed driver request. -/
def encodeOperational (n : Nat) :
    OperationalTranslation (nativeSystem n) driverSystem where
  mapTerm := encoded
  mapEquiv := by
    intro left right same
    exact congrArg encoded same
  mapStep := native_step_complete

/-- Canonical encoding also reflects every driver result originating at an
encoded native term.  Thus the executable driver adds no behavior at those
states. -/
theorem encodeCover (n : Nat) :
    StepCover (nativeSystem n) driverSystem encoded where
  mapStep := native_step_complete
  liftStep := by
    intro source target step
    obtain ⟨reduct, targetEq, nativeStep⟩ := Computes.sound step
    exact ⟨reduct, nativeStep, targetEq.symm⟩

/-- The canonical native fragment is an exactly covered operational subspace
of the executable request/result driver. -/
def encodeCovered (n : Nat) :
    CoveredTranslation (nativeSystem n) driverSystem where
  mapTerm := encoded
  mapEquiv := by
    intro left right same
    exact congrArg encoded same
  cover := encodeCover n

@[simp]
theorem encodeCovered_toOperational (n : Nat) :
    (encodeCovered n).toOperational = encodeOperational n := by
  apply OperationalTranslation.ext
  rfl

/-- At canonical endpoints, driver stepping is neither weaker nor stronger
than intrinsic computational stepping. -/
theorem driver_step_encoded_iff {n : Nat} (source target : Tower.Tm n) :
    (driverSystem.Step (encoded source) (encoded target)) ↔
      ComputationalStep source target :=
  Computes.encoded_iff source target

/-- The driver view and the mechanically generated presentation agree on the
same request/result edge. -/
theorem driver_step_iff_presentation_step {n : Nat}
    (source target : Tower.Tm n) :
    driverSystem.Step (encoded source) (encoded target) ↔
      HOLNativeMixedRuleDataOSLFConnection.presentationTheory.Step
        (HOLNativeMixedRuleData.compute (encoded source)) (encoded target) := by
  rw [driver_step_encoded_iff,
    HOLNativeMixedRuleDataOSLFConnection.presentation_step_iff]

/-- Translate a complete intrinsic computation route into the actual
request/result driver without forgetting its intermediate states. -/
def executePath {n : Nat} {source target : Tower.Tm n}
    (path : ExecutionPath (nativeSystem n) source target) :
    ExecutionPath driverSystem (encoded source) (encoded target) :=
  (encodeOperational n).mapRoute path

/-- The driver wrapper preserves the number of primitive native transitions.
The fuel and internal binding-service work of each request are intentionally
not identified with this count. -/
@[simp]
theorem executePath_length {n : Nat} {source target : Tower.Tm n}
    (path : ExecutionPath (nativeSystem n) source target) :
    (executePath path).length = path.length :=
  OperationalTranslation.mapRoute_length (encodeOperational n) path

/-- Mapping a concatenated computation performs the corresponding two driver
segments in the same order. -/
@[simp]
theorem executePath_append {n : Nat} {source middle target : Tower.Tm n}
    (first : ExecutionPath (nativeSystem n) source middle)
    (second : ExecutionPath (nativeSystem n) middle target) :
    executePath (first.append second) =
      (executePath first).append (executePath second) :=
  OperationalTranslation.mapRoute_append (encodeOperational n) first second

/-! ## Admission of the concrete native List computation -/

/-- The level-zero native List computation is a subtheory of the mixed
computational system.  Both relations deliberately exclude semantic
universe-head equality. -/
def listToNative (n : Nat) :
    OperationalTranslation
      (IntrinsicNativeListMapComputation.reduction Tower.zero n)
      (nativeSystem n) where
  mapTerm := id
  mapEquiv := fun same => same
  mapStep := by
    intro source target step
    change Step (fun _ _ => False) source target
      HOLNativeMixedOperationalDecomposition.jointRules.computation
    induction step with
    | betaPi body argument => exact .betaPi body argument
    | betaSigmaFst first second => exact .betaSigmaFst first second
    | betaSigmaSnd first second => exact .betaSigmaSnd first second
    | head impossible => exact impossible.elim
    | root evidence =>
        apply StepCore.root
        simpa only [Tm.mapHead_id] using
          FormationSensitiveHOLProofListIntegration.executionMorphism.computation
            (FormationSensitiveNativeHOLMapExecution.list_root_include evidence)
    | congPiDom _ ih => exact .congPiDom ih
    | congPiCod _ ih => exact .congPiCod ih
    | congSigmaDom _ ih => exact .congSigmaDom ih
    | congSigmaCod _ ih => exact .congSigmaCod ih
    | congIdTy _ ih => exact .congIdTy ih
    | congIdLeft _ ih => exact .congIdLeft ih
    | congIdRight _ ih => exact .congIdRight ih
    | congLam _ ih => exact .congLam ih
    | congAppFun _ ih => exact .congAppFun ih
    | congAppArg _ ih => exact .congAppArg ih
    | congPairFst _ ih => exact .congPairFst ih
    | congPairSnd _ ih => exact .congPairSnd ih
    | congFst _ ih => exact .congFst ih
    | congSnd _ ih => exact .congSnd ih
    | congRefl _ ih => exact .congRefl ih

/-- The actual List computation followed by canonical rule-data encoding. -/
def listToDriver (n : Nat) :
    OperationalTranslation
      (IntrinsicNativeListMapComputation.reduction Tower.zero n)
      driverSystem :=
  (listToNative n).comp (encodeOperational n)

@[simp]
theorem listToDriver_mapTerm (n : Nat) :
    (listToDriver n).mapTerm = encoded := by
  rfl

/-- Execute a retained level-zero List path through the mixed rule-data
driver, retaining every native beta/iota occurrence. -/
def executeListPath {n : Nat} {source target : Tower.Tm n}
    (path : PathReduces Tower.zero source target) :
    ExecutionPath driverSystem (encoded source) (encoded target) :=
  (listToDriver n).mapRoute path

@[simp]
theorem executeListPath_length {n : Nat} {source target : Tower.Tm n}
    (path : PathReduces Tower.zero source target) :
    (executeListPath path).length = path.length :=
  OperationalTranslation.mapRoute_length (listToDriver n) path

/-- Both map implementations now run through the generic mixed-rule driver,
not merely through the intrinsic relation, while retaining their common
canonical result. -/
def executedFusionPaths {n : Nat}
    (a b c f g : Tower.Tm n) (xs : List (Tower.Tm n)) :
    ExecutionPath driverSystem
        (encoded (applyMap b c f (applyMap a b g (encode a xs))))
        (encoded (encode c (xs.map (fun x => .app f (.app g x))))) ×
      ExecutionPath driverSystem
        (encoded (applyMap a c (compose f g) (encode a xs)))
        (encoded (encode c (xs.map (fun x => .app f (.app g x))))) :=
  let paths := fusion_common_output_paths Tower.zero a b c f g xs
  (executeListPath paths.1, executeListPath paths.2)

/-- Passing through the actual driver preserves the distinct work of the two
map implementations for every finite input. -/
theorem executedFusionPath_lengths {n : Nat}
    (a b c f g : Tower.Tm n) (xs : List (Tower.Tm n)) :
    (executedFusionPaths a b c f g xs).1.length =
        8 * xs.length + 10 ∧
      (executedFusionPaths a b c f g xs).2.length =
        5 * xs.length + 5 := by
  rw [executedFusionPaths, executeListPath_length, executeListPath_length]
  exact fusion_common_output_path_lengths Tower.zero a b c f g xs

/-! ## A boundary canary for semantic conversion versus execution -/

/-- The larger semantic relation has a genuine universe-head edge which is
absent from all three executable views: the List computation, the mixed
request/result driver, and its generated presentation.  This discriminating
control prevents an execution theorem from silently importing the semantic
conversion oracle. -/
theorem semantic_head_edge_outside_every_executable_view {n : Nat} :
    let left : Tower.Tm n := .head (.sort (.max (.param 0) (.param 0)))
    let right : Tower.Tm n := .head (.sort (.param 0))
    (IntrinsicNativeListMapComputation.fullReduction Tower.zero n).Step
        left right /\
      ¬ (IntrinsicNativeListMapComputation.reduction Tower.zero n).Step
        left right /\
      ¬ driverSystem.Step (encoded left) (encoded right) /\
      ¬ HOLNativeMixedRuleDataOSLFConnection.presentationTheory.Step
        (HOLNativeMixedRuleData.compute (encoded left)) (encoded right) := by
  let left : Tower.Tm n := .head (.sort (.max (.param 0) (.param 0)))
  let right : Tower.Tm n := .head (.sort (.param 0))
  change (IntrinsicNativeListMapComputation.fullReduction Tower.zero n).Step
      left right /\
    ¬ (IntrinsicNativeListMapComputation.reduction Tower.zero n).Step
      left right /\
    ¬ driverSystem.Step (encoded left) (encoded right) /\
    ¬ HOLNativeMixedRuleDataOSLFConnection.presentationTheory.Step
      (HOLNativeMixedRuleData.compute (encoded left)) (encoded right)
  have fullList : (IntrinsicNativeListMapComputation.fullReduction
      Tower.zero n).Step left right := by
    change StepCore (listRulesAt Tower.zero).computation
      (listRulesAt Tower.zero).headEq left right
    apply StepCore.head
    change ∀ valuation : Nat → Nat,
      max (valuation 0) (valuation 0) = valuation 0
    intro valuation
    exact max_self _
  have notDriver : ¬ driverSystem.Step (encoded left) (encoded right) := by
    rw [driver_step_encoded_iff]
    exact (distinct_level_spelling_control (n := n)).2
  have notList : ¬ (IntrinsicNativeListMapComputation.reduction Tower.zero n).Step
      left right := by
    intro step
    exact notDriver ((listToDriver n).mapStep step)
  have notPresented :
      ¬ HOLNativeMixedRuleDataOSLFConnection.presentationTheory.Step
        (HOLNativeMixedRuleData.compute (encoded left)) (encoded right) :=
    (HOLNativeMixedRuleDataOSLFConnection.universe_head_equality_outside_presentation
      (n := n)).2
  exact ⟨fullList, notList, notDriver, notPresented⟩

#print axioms encodeCovered_toOperational
#print axioms driver_step_encoded_iff
#print axioms driver_step_iff_presentation_step
#print axioms executePath_length
#print axioms executePath_append
#print axioms listToNative
#print axioms executeListPath_length
#print axioms executedFusionPaths
#print axioms executedFusionPath_lengths
#print axioms semantic_head_edge_outside_every_executable_view

end HOLNativeMixedPresentedDriver
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
