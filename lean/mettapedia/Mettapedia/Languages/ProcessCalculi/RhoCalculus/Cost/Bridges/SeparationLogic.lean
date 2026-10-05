import Mettapedia.GSLT.Logic.ResourceFrame
import Mettapedia.OSLF.Bridges.GSLT.ResourceSeparation
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ResourceOperationalEquivalence
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ParallelBudget

/-!
# Separation specifications for actual funded rho transitions

The resource-system frame rules apply to `CostStep`, using its existing exact
resource-event comparison. The complete footprint includes the communication
endpoints and the selected located purses. A frame keeps all its occurrences,
including equal purse or message values: the bag algebra does not deduplicate.

The existential frame rule preserves the location and debit of the chosen
transition. For a demonic specification, every event enabled after extension
must already be enabled locally. Adding a purse or a communication endpoint
can violate that condition; mere separation of the bags does not establish it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Bridges.SeparationLogic

open Mettapedia.GSLT.Causality.ResourceInteraction
open Mettapedia.GSLT.Logic.ResourceFrame
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Bridges.GSLT.ResourceSeparation

universe u

variable {Ground : Type u} [DecidableEq Ground]

/-- Framing an ordinary funded step preserves its exact location and debit. -/
theorem costStep_add_frame {source target : CostConfig Ground}
    {location : CostName Ground} {spend : CostSig Ground}
    (step : CostStep source location spend target) (frame : CostConfig Ground) :
    CostStep (source + frame) location spend (target + frame) := by
  obtain ⟨entry, located, spent, enabled, rfl⟩ := costStep_iff_exists_enabled_resource.mp step
  apply costStep_iff_exists_enabled_resource.mpr
  exact ⟨entry, located, spent, enables_add_frame _ entry enabled frame,
    (fire_add_frame _ entry enabled frame).symm⟩

/-- Framing a supplied ordinary trace preserves every ordered location/debit
label and its actual endpoint. It does not constrain other possible schedules. -/
theorem costTrace_add_frame {source target : CostConfig Ground}
    {labels : List (CostName Ground × CostSig Ground)}
    (trace : CostTrace source labels target) (frame : CostConfig Ground) :
    CostTrace (source + frame) labels (target + frame) := by
  induction trace with
  | nil => exact CostTrace.nil _
  | cons head _ inductionHypothesis =>
      exact CostTrace.cons (costStep_add_frame head frame) inductionHypothesis

private theorem reflectTraceWithPrefix (origin frame : CostConfig Ground)
    (inert : ∀ labels owned,
      CostTrace (origin + frame) labels (owned + frame) →
        NoNewEnabled (costResourceSystem Ground) (fun _ => True) owned frame)
    {source target : CostConfig Ground} {labels : List (CostName Ground × CostSig Ground)}
    (trace : CostTrace source labels target) :
    ∀ owned prefixLabels, source = owned + frame →
      CostTrace (origin + frame) prefixLabels (owned + frame) →
        ∃ ownedTarget, CostTrace owned labels ownedTarget ∧ target = ownedTarget + frame := by
  induction trace with
  | nil config =>
      intro owned _ sourceEq _
      exact ⟨owned, CostTrace.nil owned, sourceEq⟩
  | @cons source middle target location spend labels head _ inductionHypothesis =>
      intro owned prefixLabels sourceEq previous
      rw [sourceEq] at head
      obtain ⟨entry, located, spent, enabled, middleEq⟩ :=
        costStep_iff_exists_enabled_resource.mp head
      have localEnabled := inert prefixLabels owned previous entry trivial enabled
      let ownedMiddle := (costResourceSystem Ground).fire owned entry.2
      have middleFramed : middle = ownedMiddle + frame :=
        middleEq.trans (fire_add_frame _ entry localEnabled frame)
      have localHead : CostStep owned location spend ownedMiddle :=
        costStep_iff_exists_enabled_resource.mpr
          ⟨entry, located, spent, localEnabled, rfl⟩
      have previous' : CostTrace (origin + frame) (prefixLabels ++ [(location, spend)])
          (ownedMiddle + frame) := by
        have extended := previous.append (CostTrace.cons head (CostTrace.nil middle))
        exact middleFramed ▸ extended
      obtain ⟨ownedTarget, localTail, targetEq⟩ :=
        inductionHypothesis ownedMiddle (prefixLabels ++ [(location, spend)]) middleFramed previous'
      exact ⟨ownedTarget, CostTrace.cons localHead localTail, targetEq⟩

/-- A supplied trace reflects to its actual endpoint and exact ordered labels
when its fixed frame enables no new instance at the intermediate states.
The side condition is tested only at states reached by actual framed prefixes. -/
theorem costTrace_reflect_frame {source actualTarget : CostConfig Ground}
    {labels : List (CostName Ground × CostSig Ground)}
    (frame : CostConfig Ground)
    (inert : ∀ prefixLabels owned,
      CostTrace (source + frame) prefixLabels (owned + frame) →
        NoNewEnabled (costResourceSystem Ground) (fun _ => True) owned frame)
    (trace : CostTrace (source + frame) labels actualTarget) :
    ∃ ownedTarget, CostTrace source labels ownedTarget ∧ actualTarget = ownedTarget + frame :=
  reflectTraceWithPrefix source frame inert trace source [] rfl (CostTrace.nil _)

/-- Under the same intermediate-state condition, framing and reflection give
an exact characterization of the supplied finite trace's endpoint and labels. -/
theorem costTrace_iff_framed {source actualTarget : CostConfig Ground}
    {labels : List (CostName Ground × CostSig Ground)}
    (frame : CostConfig Ground)
    (inert : ∀ prefixLabels owned,
      CostTrace (source + frame) prefixLabels (owned + frame) →
        NoNewEnabled (costResourceSystem Ground) (fun _ => True) owned frame) :
    CostTrace (source + frame) labels actualTarget ↔
      ∃ ownedTarget, CostTrace source labels ownedTarget ∧ actualTarget = ownedTarget + frame := by
  constructor
  · exact costTrace_reflect_frame frame inert
  · rintro ⟨ownedTarget, trace, rfl⟩
    exact costTrace_add_frame trace frame

/-- The generic existential specification is exactly a specification of actual
funded rho steps, forgetting no endpoint but existentially quantifying labels. -/
theorem mayTriple_iff (pre post : CostConfig Ground → Prop) :
    MayTriple (costResourceSystem Ground) (fun _ => True) pre post ↔
      ∀ source, pre source → ∃ location spend target,
        CostStep source location spend target ∧ post target := by
  constructor
  · intro specification source holds
    obtain ⟨target, resourceStep, result⟩ := specification source holds
    obtain ⟨location, spend, step⟩ := resource_rewrites_iff_costStep.mp
      ((selectedStep_iff_rewrites _ _ _).mp resourceStep)
    exact ⟨location, spend, target, step, result⟩
  · intro specification source holds
    obtain ⟨location, spend, target, step, result⟩ := specification source holds
    exact ⟨target, (selectedStep_iff_rewrites _ _ _).mpr
      (resource_rewrites_iff_costStep.mpr ⟨location, spend, step⟩), result⟩

/-- The generic progress-and-all-successors specification is exactly the
corresponding condition over `CostStep`, including every location and debit. -/
theorem safeTriple_iff (pre post : CostConfig Ground → Prop) :
    SafeTriple (costResourceSystem Ground) (fun _ => True) pre post ↔
      ∀ source, pre source →
        (∃ location spend target, CostStep source location spend target) ∧
        ∀ location spend target, CostStep source location spend target → post target := by
  constructor
  · intro specification source holds
    obtain ⟨⟨target, resourceStep⟩, all⟩ := specification source holds
    obtain ⟨location, spend, step⟩ := resource_rewrites_iff_costStep.mp
      ((selectedStep_iff_rewrites _ _ _).mp resourceStep)
    refine ⟨⟨location, spend, target, step⟩, ?_⟩
    intro location spend target step
    exact all target ((selectedStep_iff_rewrites _ _ _).mpr
      (resource_rewrites_iff_costStep.mpr ⟨location, spend, step⟩))
  · intro specification source holds
    obtain ⟨⟨location, spend, target, step⟩, all⟩ := specification source holds
    refine ⟨⟨target, (selectedStep_iff_rewrites _ _ _).mpr
      (resource_rewrites_iff_costStep.mpr ⟨location, spend, step⟩)⟩, ?_⟩
    intro target resourceStep
    obtain ⟨location, spend, step⟩ := resource_rewrites_iff_costStep.mp
      ((selectedStep_iff_rewrites _ _ _).mp resourceStep)
    exact all location spend target step

/-- An existential funded execution specification frames unconditionally. -/
theorem funded_may_frame {pre post frame : CostConfig Ground → Prop}
    (specification : ∀ source, pre source → ∃ location spend target,
      CostStep source location spend target ∧ post target) :
    ∀ source, sepConj pre frame source → ∃ location spend target,
      CostStep source location spend target ∧ sepConj post frame target :=
  (mayTriple_iff _ _).mp
    (mayTriple_frame _ ((mayTriple_iff pre post).mpr specification))

/-- The all-successors frame rule uses no-new-enablement of complete funded
events. This condition is expressed by endpoint and purse occurrences. -/
theorem funded_safe_frame {pre post frame : CostConfig Ground → Prop}
    (specification : ∀ source, pre source →
      (∃ location spend target, CostStep source location spend target) ∧
      ∀ location spend target, CostStep source location spend target → post target)
    (inert : ∀ source extension, pre source → frame extension →
      ∀ event : CostedEvent Ground, event.consumed ≤ source + extension →
        event.consumed ≤ source) :
    ∀ source, sepConj pre frame source →
      (∃ location spend target, CostStep source location spend target) ∧
      ∀ location spend target, CostStep source location spend target →
        sepConj post frame target := by
  apply (safeTriple_iff _ _).mp
  apply safeTriple_frame _ ((safeTriple_iff pre post).mpr specification)
  intro source extension localPre framePre entry _ enabled
  apply (CostResourceWave.enables_iff_consumed_le source entry).mpr
  exact inert source extension localPre framePre (CostResourceWave.event entry)
    ((CostResourceWave.enables_iff_consumed_le (source + extension) entry).mp enabled)

omit [DecidableEq Ground] in
/-- The separating footprint specification of one chosen funded event retains
the supplied frame and the chosen event's original labels. -/
theorem event_footprint_frame (event : CostedEvent Ground)
    (frame : CostConfig Ground → Prop) :
    ∀ source, sepConj (fun owned => owned = event.consumed) frame source →
      ∃ target, CostStep source event.location event.spend target ∧
        sepConj (fun owned => owned = event.produced) frame target := by
  rintro _ ⟨owned, extension, _, rfl, rfl, framePre⟩
  refine ⟨event.produced + extension, ?_,
    ⟨event.produced, extension, trivial, rfl, rfl, framePre⟩⟩
  simpa only [add_comm] using event.toCostStepIn extension

/-- A chosen funded event's complete footprint has the generic demonic
specification when control is restricted to this very event. -/
theorem event_safeTriple_frame (event : CostedEvent Ground)
    (frame : CostConfig Ground → Prop) :
    SafeTriple (costResourceSystem Ground) (fun candidate => candidate = event.resourceEntry)
      (sepConj (fun owned => owned = event.consumed) frame)
      (sepConj (fun owned => owned = event.produced) frame) := by
  have input : demand (costResourceSystem Ground) event.resourceEntry = event.consumed := by
    unfold demand
    rw [costResourceSystem_consume, costResourceSystem_read, add_zero]
    rfl
  have output : (costResourceSystem Ground).read event.resourceEntry.2 +
      (costResourceSystem Ground).produce event.resourceEntry.2 = event.produced := by
    rw [costResourceSystem_read, costResourceSystem_produce, zero_add]
    rfl
  simpa only [input, output] using
    footprint_safeTriple_frame (costResourceSystem Ground) event.resourceEntry frame

/-- The complete funded footprint has its expected successor in the existing
native logic generated from the resource GSLT equivalent to `CostStep`. -/
theorem event_nativeDiamond (event : CostedEvent Ground) :
    (semanticDiamond (costResourceSystem Ground).theory
      (nativePredicate (costResourceSystem Ground)
        (fun target => target = event.produced))).1 event.consumed := by
  have step := event.toCostStepIn 0
  simp only [zero_add] at step
  exact (nativeDiamond_iff _ _ _).mpr
    ⟨event.produced, resource_rewrites_iff_costStep.mpr
      ⟨event.location, event.spend, step⟩, rfl⟩

/-- Framed funded footprints satisfy the generated spatial/modal assertion,
with the same operational authority as the ordinary funded transition. -/
theorem event_nativeDiamond_frame (event : CostedEvent Ground)
    (frame : CostConfig Ground → Prop) :
    sepConj (fun owned => owned = event.consumed) frame ≤
      (semanticDiamond (costResourceSystem Ground).theory
        (nativeStar (costResourceSystem Ground)
          (nativePredicate (costResourceSystem Ground) (fun target => target = event.produced))
          (nativePredicate (costResourceSystem Ground) frame))).1 := by
  rintro _ ⟨owned, extension, _, rfl, rfl, framePre⟩
  exact nativeDiamond_star_frame (costResourceSystem Ground) _ _ _
    ⟨event.consumed, extension, trivial, rfl, event_nativeDiamond event, framePre⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Bridges.SeparationLogic
