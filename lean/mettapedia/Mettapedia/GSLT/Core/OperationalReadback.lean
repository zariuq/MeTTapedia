import Mettapedia.GSLT.Core.OperationalRealizationOSLF
import Mettapedia.GSLT.Core.IndexedCommandBlocks
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-!
# Reading arbitrary implementation prefixes back to source executions

A forward realization selects an implementation of a source execution. A
readback consumes an independently given target step: it either leaves the
source unchanged or exposes a source step related to that exact target
endpoint. The relation includes administrative states, not only compiled
boundary states. Readbacks compose and retain a source path for every target
prefix, with at most one source transition per implementation transition.

The separate correspondence law supplies forward execution from every
related administrative state. Together the laws transport finite-reachability
observations in both directions. They do not, by themselves, observe infinite
administration, contextual equivalence, or occurrence identities erased from
proposition-valued steps.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.IndexedOperational

open Mettapedia.GSLT
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

universe uSource uMiddle uTarget

/-- A local no-invention law over actual target steps. Implementations must
prove this law by inverting their own operational rules. -/
structure OperationalReadback (source : GSLT.{uSource}) (target : GSLT.{uTarget}) where
  related : source.Term → target.Term → Prop
  readStep : ∀ {origin : source.Term} {current next : target.Term},
    related origin current → target.Step current next →
      related origin next ∨ ∃ after, source.Step origin after ∧ related after next

namespace OperationalReadback

variable {source : GSLT.{uSource}} {middle : GSLT.{uMiddle}}
    {target : GSLT.{uTarget}}

/-- Every actual implementation prefix has a retained source prefix and a
related final state. The supplied implementation endpoint is unchanged. -/
theorem reflectPath (readback : OperationalReadback source target)
    {origin : source.Term} {current final : target.Term}
    (related : readback.related origin current)
    (path : ExecutionPath target current final) :
    ∃ after, ∃ sourcePath : ExecutionPath source origin after,
      readback.related after final ∧ sourcePath.length ≤ path.length := by
  induction path generalizing origin with
  | refl state => exact ⟨origin, .refl origin, related, le_rfl⟩
  | cons first rest ih =>
      rcases readback.readStep related first.down with unchanged | advanced
      · obtain ⟨after, sourcePath, finalRelated, bound⟩ := ih unchanged
        refine ⟨after, sourcePath, finalRelated, ?_⟩
        change sourcePath.length ≤ rest.length + 1
        omega
      · obtain ⟨next, step, nextRelated⟩ := advanced
        obtain ⟨after, sourcePath, finalRelated, bound⟩ := ih nextRelated
        refine ⟨after, .cons ⟨step⟩ sourcePath, finalRelated, ?_⟩
        change sourcePath.length + 1 ≤ rest.length + 1
        omega

theorem reflectMultiStep (readback : OperationalReadback source target)
    {origin : source.Term} {current final : target.Term}
    (related : readback.related origin current) (path : target.MultiStep current final) :
    ∃ after, source.MultiStep origin after ∧ readback.related after final := by
  obtain ⟨targetPath⟩ := (executionPath_nonempty_iff_multiStep target current final).2 path
  obtain ⟨after, sourcePath, finalRelated, _⟩ := readback.reflectPath related targetPath
  exact ⟨after, executionPathToMultiStep sourcePath, finalRelated⟩

/-- Relational composition allows each compiler stage to retain its own
administrative states. A primitive target step still reads as zero or one
primitive source step. -/
def comp (earlier : OperationalReadback source middle)
    (later : OperationalReadback middle target) : OperationalReadback source target where
  related origin current := ∃ between, earlier.related origin between ∧ later.related between current
  readStep := by
    rintro origin current next ⟨between, before, after⟩ step
    rcases later.readStep after step with unchanged | advanced
    · exact .inl ⟨between, before, unchanged⟩
    · obtain ⟨betweenNext, middleStep, nextRelated⟩ := advanced
      rcases earlier.readStep before middleStep with sourceUnchanged | sourceAdvanced
      · exact .inl ⟨betweenNext, sourceUnchanged, nextRelated⟩
      · obtain ⟨originNext, sourceStep, originRelated⟩ := sourceAdvanced
        exact .inr ⟨originNext, sourceStep, betweenNext, originRelated, nextRelated⟩

end OperationalReadback

/-- Finite operational correspondence through administrative states. The
forward and backward laws are separate obligations on actual executions. -/
structure OperationalCorrespondence (source : GSLT.{uSource}) (target : GSLT.{uTarget})
    extends OperationalReadback source target where
  forward : ∀ {origin after : source.Term} {current : target.Term},
    related origin current → source.Step origin after →
      ∃ final, Nonempty (ExecutionPath target current final) ∧ related after final

namespace OperationalCorrespondence

variable {source : GSLT.{uSource}} {middle : GSLT.{uMiddle}}
    {target : GSLT.{uTarget}}

/-- Source execution remains implementable from a supplied related phase. -/
theorem liftPath (comparison : OperationalCorrespondence source target)
    {origin after : source.Term} {current : target.Term}
    (related : comparison.related origin current)
    (path : ExecutionPath source origin after) :
    ∃ final, Nonempty (ExecutionPath target current final) ∧ comparison.related after final := by
  induction path generalizing current with
  | refl state => exact ⟨current, ⟨.refl current⟩, related⟩
  | cons first rest ih =>
      obtain ⟨between, ⟨firstPath⟩, betweenRelated⟩ := comparison.forward related first.down
      obtain ⟨final, ⟨remaining⟩, finalRelated⟩ := ih betweenRelated
      exact ⟨final, ⟨firstPath.append remaining⟩, finalRelated⟩

theorem liftMultiStep (comparison : OperationalCorrespondence source target)
    {origin after : source.Term} {current : target.Term}
    (related : comparison.related origin current) (path : source.MultiStep origin after) :
    ∃ final, target.MultiStep current final ∧ comparison.related after final := by
  obtain ⟨sourcePath⟩ := (executionPath_nonempty_iff_multiStep source origin after).2 path
  obtain ⟨final, ⟨targetPath⟩, finalRelated⟩ := comparison.liftPath related sourcePath
  exact ⟨final, executionPathToMultiStep targetPath, finalRelated⟩

/-- Staged correspondences use the existing source and target path carriers. -/
def comp (earlier : OperationalCorrespondence source middle)
    (later : OperationalCorrespondence middle target) :
    OperationalCorrespondence source target where
  toOperationalReadback := earlier.toOperationalReadback.comp later.toOperationalReadback
  forward := by
    rintro origin after current ⟨between, beforeRelated, afterRelated⟩ step
    obtain ⟨betweenNext, ⟨middlePath⟩, beforeNextRelated⟩ := earlier.forward beforeRelated step
    obtain ⟨final, path, afterNextRelated⟩ := later.liftPath afterRelated middlePath
    exact ⟨final, path, betweenNext, beforeNextRelated, afterNextRelated⟩

/-- An allowed observation has the same meaning at related source and
administrative target states. This condition is additional to execution. -/
theorem reachable_iff (comparison : OperationalCorrespondence source target)
    (sourceObservation : source.Term → Prop) (targetObservation : target.Term → Prop)
    (observations : ∀ {origin current}, comparison.related origin current →
      (sourceObservation origin ↔ targetObservation current))
    {origin : source.Term} {current : target.Term}
    (related : comparison.related origin current) :
    (∃ after, source.MultiStep origin after ∧ sourceObservation after) ↔
      ∃ final, target.MultiStep current final ∧ targetObservation final := by
  constructor
  · rintro ⟨after, path, holds⟩
    obtain ⟨final, targetPath, finalRelated⟩ := comparison.liftMultiStep related path
    exact ⟨final, targetPath, (observations finalRelated).1 holds⟩
  · rintro ⟨final, path, holds⟩
    obtain ⟨after, sourcePath, finalRelated⟩ := comparison.toOperationalReadback.reflectMultiStep related path
    exact ⟨after, sourcePath, (observations finalRelated).2 holds⟩

/-- Initialization can temporarily hide a source observation. Reflection
at each actual endpoint and realization after a finite implementation path
still suffice for two-sided reachability. Instantaneous observation equality
is not required. -/
theorem reachable_iff_delayed (comparison : OperationalCorrespondence source target)
    (sourceObservation : source.Term → Prop) (targetObservation : target.Term → Prop)
    (reflection : ∀ {origin current}, comparison.related origin current →
      targetObservation current → sourceObservation origin)
    (realization : ∀ {origin current}, comparison.related origin current →
      sourceObservation origin →
        ∃ final, target.MultiStep current final ∧ targetObservation final)
    {origin : source.Term} {current : target.Term}
    (related : comparison.related origin current) :
    (∃ after, source.MultiStep origin after ∧ sourceObservation after) ↔
      ∃ final, target.MultiStep current final ∧ targetObservation final := by
  constructor
  · rintro ⟨after, path, holds⟩
    obtain ⟨between, targetPath, nextRelated⟩ := comparison.liftMultiStep related path
    obtain ⟨final, completion, observed⟩ := realization nextRelated holds
    exact ⟨final, multiStepAppend targetPath completion, observed⟩
  · rintro ⟨final, path, holds⟩
    obtain ⟨after, sourcePath, finalRelated⟩ := comparison.toOperationalReadback.reflectMultiStep related path
    exact ⟨after, sourcePath, reflection finalRelated holds⟩

/-- Universal finite-prefix guarantees transfer too. This is a future
invariant, not the past-directed right adjoint of the OSLF diamond. -/
theorem invariant_iff (comparison : OperationalCorrespondence source target)
    (sourceObservation : source.Term → Prop) (targetObservation : target.Term → Prop)
    (observations : ∀ {origin current}, comparison.related origin current →
      (sourceObservation origin ↔ targetObservation current))
    {origin : source.Term} {current : target.Term}
    (related : comparison.related origin current) :
    (∀ after, source.MultiStep origin after → sourceObservation after) ↔
      ∀ final, target.MultiStep current final → targetObservation final := by
  constructor
  · intro allSource final path
    obtain ⟨after, sourcePath, finalRelated⟩ := comparison.toOperationalReadback.reflectMultiStep related path
    exact (observations finalRelated).1 (allSource after sourcePath)
  · intro allTarget after path
    obtain ⟨final, targetPath, finalRelated⟩ := comparison.liftMultiStep related path
    exact (observations finalRelated).2 (allTarget final targetPath)

end OperationalCorrespondence

/-! ## Connection with the existing generated native diamond -/

/-- The closure diamond is exactly finite execution followed by a saturated
endpoint observation. It does not count implementation instructions. -/
theorem closure_nativeDiamond_iff (system : GSLT.{uSource})
    (predicate : EquationPredicate system.closure) (current : system.Term) :
    (semanticDiamond system.closure predicate).1 current ↔
      ∃ final, system.MultiStep current final ∧ predicate.1 final := by
  change gsltDiamond system.closure predicate.1 current ↔ _
  apply (gsltDiamond_spec system.closure predicate.1 current).trans
  constructor
  · rintro ⟨final, ⟨reached, path, equivalent⟩, holds⟩
    exact ⟨reached, path, (predicate.2 equivalent).2 holds⟩
  · rintro ⟨final, path, holds⟩
    exact ⟨final, ⟨final, path, system.equations.iseqv.refl _⟩, holds⟩

/-- Allowed native reachability types are preserved and reflected by an
actual correspondence, including its administrative states. -/
theorem OperationalCorrespondence.nativeDiamond_iff
    {source : GSLT.{uSource}} {target : GSLT.{uTarget}}
    (comparison : OperationalCorrespondence source target)
    (sourcePredicate : EquationPredicate source.closure)
    (targetPredicate : EquationPredicate target.closure)
    (observations : ∀ {origin current}, comparison.related origin current →
      (sourcePredicate.1 origin ↔ targetPredicate.1 current))
    {origin : source.Term} {current : target.Term}
    (related : comparison.related origin current) :
    (semanticDiamond source.closure sourcePredicate).1 origin ↔
      (semanticDiamond target.closure targetPredicate).1 current := by
  rw [closure_nativeDiamond_iff, closure_nativeDiamond_iff]
  exact comparison.reachable_iff sourcePredicate.1 targetPredicate.1 observations related

/-- The closure-native may observation also admits a finite delay. The
realization premise is a native target reachability claim; its concrete
provider must construct actual implementation steps. -/
theorem OperationalCorrespondence.nativeDiamond_iff_delayed
    {source : GSLT.{uSource}} {target : GSLT.{uTarget}}
    (comparison : OperationalCorrespondence source target)
    (sourcePredicate : EquationPredicate source.closure)
    (targetPredicate : EquationPredicate target.closure)
    (reflection : ∀ {origin current}, comparison.related origin current →
      targetPredicate.1 current → sourcePredicate.1 origin)
    (realization : ∀ {origin current}, comparison.related origin current →
      sourcePredicate.1 origin →
        (semanticDiamond target.closure targetPredicate).1 current)
    {origin : source.Term} {current : target.Term}
    (related : comparison.related origin current) :
    (semanticDiamond source.closure sourcePredicate).1 origin ↔
      (semanticDiamond target.closure targetPredicate).1 current := by
  rw [closure_nativeDiamond_iff, closure_nativeDiamond_iff]
  exact comparison.reachable_iff_delayed sourcePredicate.1 targetPredicate.1 reflection
    (fun relation observed => (closure_nativeDiamond_iff target targetPredicate _).mp
      (realization relation observed)) related

/-- A backward-only readback already rejects invented successful endpoint
observations. It need not lift all alternative source executions from a
partially committed implementation. -/
theorem OperationalReadback.nativeDiamond_reflected
    {source : GSLT.{uSource}} {target : GSLT.{uTarget}}
    (comparison : OperationalReadback source target)
    (sourcePredicate : EquationPredicate source.closure)
    (targetPredicate : EquationPredicate target.closure)
    (observations : ∀ {origin current}, comparison.related origin current →
      targetPredicate.1 current → sourcePredicate.1 origin)
    {origin : source.Term} {current : target.Term}
    (related : comparison.related origin current)
    (possible : (semanticDiamond target.closure targetPredicate).1 current) :
    (semanticDiamond source.closure sourcePredicate).1 origin := by
  obtain ⟨final, path, holds⟩ := (closure_nativeDiamond_iff target _ current).1 possible
  obtain ⟨after, sourcePath, finalRelated⟩ := comparison.reflectMultiStep related path
  exact (closure_nativeDiamond_iff source _ origin).2
    ⟨after, sourcePath, observations finalRelated holds⟩

end Mettapedia.GSLT.IndexedOperational
