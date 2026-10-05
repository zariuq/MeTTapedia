import Mettapedia.Languages.ProcessCalculi.PiCalculus.FrontierCompleteness
import Mettapedia.Languages.ProcessCalculi.PiCalculus.ObservationBoundary

/-!
# Controls for exhaustive pi execution and native observations

The complete one-step executor finds a non-leading receiver, distinguishes
equal receiver occurrences, and excludes every wrong endpoint even at larger
context bounds. Scope under an enclosing restriction is preserved. Fuel zero
is a bounded sample that misses a real firing; the source-derived frontier
contains it. Atomic canonical observations accept singleton name wrappers
and reject the inaction-valued message. An atomic endpoint can nevertheless
have a non-atomic predecessor in the full one-sort GSLT.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.ReflectionControls
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.GSLT.LanguageDef.BagNormalForm
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.OSLF.MeTTaIL.PatternCode
open PiCalcInstance

def receiver : Pattern := .apply "PiInp" [.fvar "a", .lambda none
  (.apply "PiOut" [.fvar "b", .bvar 0])]

def nonLeadingExchange : Pattern := .collection .hashBag
  [.apply "PiOut" [.fvar "a", .fvar "z"], receiver,
    .apply "PiOut" [.fvar "other", .fvar "w"]] none

def nonLeadingResult : Pattern := .collection .hashBag
  [.apply "PiOut" [.fvar "b", .fvar "z"],
    .apply "PiOut" [.fvar "other", .fvar "w"]] none

def duplicateReceivers : Pattern := .collection .hashBag
  [.apply "PiOut" [.fvar "a", .fvar "z"], receiver, receiver] none

def duplicateResult : Pattern := .collection .hashBag
  [.apply "PiOut" [.fvar "b", .fvar "z"], receiver] none

/-- A restricted channel sends its own name through an input whose released
body still contains a second input binder. -/
def restrictedExchange : Pattern := .apply "PiNu" [.lambda none
  (.collection .hashBag
    [.apply "PiOut" [.bvar 0, .bvar 0],
      .apply "PiInp" [.bvar 0, .lambda none
        (.apply "PiInp" [.fvar "b", .lambda none
          (.apply "PiOut" [.bvar 1, .bvar 0])])]] none)]

def restrictedResult : Pattern := .apply "PiNu" [.lambda none
  (.collection .hashBag
    [.apply "PiInp" [.fvar "b", .lambda none
      (.apply "PiOut" [.bvar 1, .bvar 0])]] none)]

theorem complete_frontier_selects_nonleading_receiver :
    piCalcReducts (piContextDepth nonLeadingExchange) nonLeadingExchange =
      [nonLeadingResult] := by
  decide +kernel

theorem complete_frontier_preserves_duplicate_receivers :
    piCalcReducts (piContextDepth duplicateReceivers) duplicateReceivers =
      [duplicateResult, duplicateResult] := by
  decide +kernel

/-- The received outer name remains index one beneath the retained input;
it is not captured by that input's index-zero variable. -/
theorem complete_frontier_preserves_restricted_name :
    piContextDepth restrictedExchange = 3 ∧
      piCalcReducts (piContextDepth restrictedExchange) restrictedExchange =
        [restrictedResult] := by
  decide +kernel

theorem restricted_step_iff_actual_endpoint (target : Pattern) :
    Step (engineBasePremises RelationEnv.empty) piCalc restrictedExchange target ↔
      target = restrictedResult := by
  rw [← pi_complete_frontier_iff_step,
    complete_frontier_preserves_restricted_name.2]
  exact List.mem_singleton

/-- No executor depth can replace the sent outer name by the retained local
variable. This excludes a capture error at the unbounded execution boundary. -/
theorem captured_restricted_name_rejected_at_every_depth (fuel : Nat) :
    .apply "PiNu" [.lambda none (.collection .hashBag
        [.apply "PiInp" [.fvar "b", .lambda none
          (.apply "PiOut" [.bvar 0, .bvar 0])]] none)] ∉
      piCalcReducts fuel restrictedExchange := by
  intro member
  have firing : Step (engineBasePremises RelationEnv.empty) piCalc restrictedExchange _ :=
    ⟨fuel, mem_rewriteAt_iff_stepAt.mp member⟩
  have captured := (restricted_step_iff_actual_endpoint _).mp firing
  have different : (.apply "PiNu" [.lambda none (.collection .hashBag
      [.apply "PiInp" [.fvar "b", .lambda none
        (.apply "PiOut" [.bvar 0, .bvar 0])]] none)] : Pattern) ≠ restrictedResult := by
    decide +kernel
  exact different captured

/-- The computed list characterizes every unbounded authored successor. -/
theorem nonleading_step_iff_actual_endpoint (target : Pattern) :
    Step (engineBasePremises RelationEnv.empty) piCalc nonLeadingExchange target ↔
      target = nonLeadingResult := by
  rw [← pi_complete_frontier_iff_step, complete_frontier_selects_nonleading_receiver]
  exact List.mem_singleton

theorem duplicate_step_iff_actual_endpoint (target : Pattern) :
    Step (engineBasePremises RelationEnv.empty) piCalc duplicateReceivers target ↔
      target = duplicateResult := by
  rw [← pi_complete_frontier_iff_step, complete_frontier_preserves_duplicate_receivers]
  simp

/-- Every context bound excludes the wrong received name, including bounds
larger than the one used to compute the complete frontier. -/
theorem wrong_endpoint_rejected_at_every_depth (fuel : Nat) :
    .collection .hashBag
        [.apply "PiOut" [.fvar "b", .fvar "wrong"],
          .apply "PiOut" [.fvar "other", .fvar "w"]] none ∉
      piCalcReducts fuel nonLeadingExchange := by
  intro member
  have firing : Step (engineBasePremises RelationEnv.empty) piCalc nonLeadingExchange _ :=
    ⟨fuel, mem_rewriteAt_iff_stepAt.mp member⟩
  have wrong := (nonleading_step_iff_actual_endpoint _).mp firing
  have different : (.collection .hashBag
      [.apply "PiOut" [.fvar "b", .fvar "wrong"],
        .apply "PiOut" [.fvar "other", .fvar "w"]] none : Pattern) ≠ nonLeadingResult := by
    decide +kernel
  exact different wrong

theorem zero_depth_misses_a_real_step :
    piCalcReducts 0 nonLeadingExchange = [] ∧
      Step (engineBasePremises RelationEnv.empty) piCalc nonLeadingExchange nonLeadingResult :=
  ⟨rfl, (nonleading_step_iff_actual_endpoint _).mpr rfl⟩

theorem inactive_input_does_not_inspect_its_continuation (body target : Pattern) :
    piContextDepth (.apply "PiInp" [.fvar "a", .lambda none body]) = 1 ∧
      ¬ Step (engineBasePremises RelationEnv.empty) piCalc
        (.apply "PiInp" [.fvar "a", .lambda none body]) target := by
  refine ⟨rfl, ?_⟩
  intro firing
  have raw := piRawStep_of_step firing
  generalize shape : Pattern.apply "PiInp" [.fvar "a", .lambda none body] = source at raw
  cases raw <;> simp at shape

theorem named_exchange_has_native_atomic_result :
    piCalcDiamond (atomicNativeType 0)
      (piToPattern (.par (.input "a" "x" (.output "b" "x")) (.output "a" "z"))) := by
  exact atomic_enabled_native_diamond (piToPattern_atomic _)
    (piComm_named_step "a" "x" "z" (.output "b" "x") [])

theorem singleton_message_has_same_native_atomic_type :
    atomicNativeType 0
      (.apply "PiOut" [.fvar "a", .collection .hashBag [.fvar "b"] none]) := by
  change AtomicPi 0 (normalForm (some "PiNil") _)
  simpa [normalForm, normalFormList, normalizeBag, bagContents, splice, collapse] using
    (AtomicPi.output (AtomicName.free 0 "a") (AtomicName.free 0 "b"))

theorem process_message_has_no_native_atomic_type :
    ¬ atomicNativeType 0 (.apply "PiOut" [.fvar "a", .apply "PiNil" []]) :=
  process_message_not_atomic 0

def processMessageExchange : Pattern := .collection .hashBag
  [.apply "PiInp" [.fvar "a", .lambda none (.apply "PiNil" [])],
    .apply "PiOut" [.fvar "a", .apply "PiNil" []]] none

private theorem processMessageExchange_not_native_atomic :
    ¬ atomicNativeType 0 processMessageExchange := by
  let components : List Pattern :=
    [.apply "PiInp" [.fvar "a", .lambda none (.apply "PiNil" [])],
      .apply "PiOut" [.fvar "a", .apply "PiNil" []]]
  have kept : bagContents "PiNil" components = components := by
    simp [components, bagContents, splice]
  have normal : normalForm (some "PiNil") processMessageExchange =
      .collection .hashBag (sortPatterns components) none := by
    change normalizeBag (some "PiNil") components = _
    change collapse "PiNil" (sortPatterns (bagContents "PiNil" components)) = _
    rw [kept]
    exact collapse_eq_bag_of_length _ _ (by simp [components])
  intro atomic
  change AtomicPi 0 (normalForm (some "PiNil") processMessageExchange) at atomic
  rw [normal] at atomic
  have all : ∀ element ∈ sortPatterns components, AtomicPi 0 element := by
    cases atomic with
    | parallel all => exact all
  apply process_message_not_atomic 0
  exact all _ (mem_sortPatterns.mpr (by simp [components]))

/-- The native box ranges over all predecessors in the declared one-sort
GSLT. An atomic endpoint can have a predecessor with a process-valued message;
forward closure of the atomic executor does not exclude that predecessor. -/
theorem atomic_endpoint_has_nonatomic_native_predecessor :
    atomicNativeType 0 (.apply "PiNil" []) ∧
      ¬ piCalcBox (atomicNativeType 0) (.apply "PiNil" []) := by
  refine ⟨(AtomicPi.nil 0).normalForm, ?_⟩
  intro boxed
  have firing : PiRawStep processMessageExchange
      (.collection .hashBag [.apply "PiNil" []] none) := by
    simpa [processMessageExchange, Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVar,
      Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVarAt] using
      (PiRawStep.comm (elements :=
      [.apply "PiInp" [.fvar "a", .lambda none (.apply "PiNil" [])],
        .apply "PiOut" [.fvar "a", .apply "PiNil" []]]) (tail := none)
      0 (by decide) 0 (by decide) (.fvar "a") none
      (.apply "PiNil" []) (.apply "PiNil" []) rfl rfl)
  have singleton : EquationEquiv (engineBasePremises RelationEnv.empty) piCalc
      (.collection .hashBag [.apply "PiNil" []] none) (.apply "PiNil" []) :=
    derivedInstance_equivalent (.singleton piBagTheory.bagAlgebraRule rfl
      ⟨piNameContext, [], bag_hasType piBagTheory
        (.cons (piToPattern_hasType .nil) (.nil _ _))⟩)
  exact processMessageExchange_not_native_atomic
    ((pi_native_box_iff_raw _ _).mp boxed _ _ firing singleton)

end Mettapedia.Languages.ProcessCalculi.PiCalculus.ReflectionControls
