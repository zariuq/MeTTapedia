import Mettapedia.OSLF.Framework.InstrumentCutSourceReactions
import Mettapedia.OSLF.Framework.InstrumentMonotonicity
import Mettapedia.OSLF.Framework.PartialStructuralObservers

/-!
# Independent partial observations realized by actual typed probe IPOs

States are independently authored source trees and argument bundles. Their
typed realization traverses every supplied child. The response relation is
defined using actual categorical IPO transitions at the selected probe labels.
It is then compared with the independently defined instrument events and
partial views. The support comparison explicitly requires inhabited origins.
This samples probe labels; it does not equate full interactive bisimulation
with a structural-view kernel.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.InstrumentCutContexts

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedConstructors
open Mettapedia.CategoryTheory.GroundPath
open Mettapedia.GSLT.RedexRelativeCongruence

universe u w

variable {Symbols : Type u} (arity : Symbols → Nat)

abbrev SourceState := InstrumentObservations.State Symbols arity
abbrev SourceLabel := InstrumentObservations.Label Symbols arity

def stateInterface : SourceState arity → Srt Symbols arity
  | .term _ => .base
  | .bundle (.node constructor _) => .arguments constructor

def stateValue : (state : SourceState arity) → Value arity (stateInterface arity state)
  | .term value => embedSource arity value
  | .bundle (.node constructor arguments) => bundle arity constructor (fun position => embedSource arity (arguments position))

def labelProbe : SourceLabel arity → Probe Symbols arity
  | .ask constructor => .ask constructor
  | .get constructor position => .get constructor position
  | .build constructor => .build constructor

def requestedConstructor : SourceLabel arity → Symbols
  | .ask constructor => constructor
  | .get constructor _ => constructor
  | .build constructor => constructor

def ProbeResponse (Origins : Type w) (opened : InstrumentObservations.Policy Symbols)
    (source : SourceState arity) (label : SourceLabel arity) (target : SourceState arity) : Prop :=
  ∃ sourceSort : stateInterface arity source = receiver arity (labelProbe arity label),
    ∃ targetSort : stateInterface arity target = result arity (labelProbe arity label),
      opened (requestedConstructor arity label) ∧
      ActIPO (administrativeRules arity Origins)
        (contextArrow (signature arity) (probeContext arity (labelProbe arity label)))
        (termArrow (signature arity) (sourceSort ▸ stateValue arity source))
        (termArrow (signature arity) (targetSort ▸ stateValue arity target))

theorem event_probe_response {Origins : Type w} (origin : Origins)
    {opened : InstrumentObservations.Policy Symbols} {source target : SourceState arity}
    {label : SourceLabel arity} (event : InstrumentObservations.Event opened source label target) :
    ProbeResponse arity Origins opened source label target := by
  cases event with
  | ask constructor arguments permission =>
    refine ⟨rfl, rfl, permission, ?_⟩
    apply (administrative_step_iff arity Origins (.ask constructor) _ _).mpr
    exact ⟨⟨origin, .ask constructor (fun position => embedSource arity (arguments position))⟩, rfl, rfl⟩
  | get constructor arguments permission position =>
    refine ⟨rfl, rfl, permission, ?_⟩
    apply (administrative_step_iff arity Origins (.get constructor position) _ _).mpr
    exact ⟨⟨origin, .get constructor position (fun position => embedSource arity (arguments position))⟩, rfl, rfl⟩
  | build constructor arguments permission =>
    refine ⟨rfl, rfl, permission, ?_⟩
    apply (administrative_step_iff arity Origins (.build constructor) _ _).mpr
    exact ⟨⟨origin, .build constructor (fun position => embedSource arity (arguments position))⟩, rfl, rfl⟩

set_option backward.isDefEq.respectTransparency false in
theorem probe_response_event {Origins : Type w} {opened : InstrumentObservations.Policy Symbols}
    {source target : SourceState arity} {label : SourceLabel arity}
    (response : ProbeResponse arity Origins opened source label target) :
    InstrumentObservations.Response opened source label target := by
  obtain ⟨sourceSort, targetSort, permission, step⟩ := response
  cases label with
  | ask constructor =>
    cases source with
    | bundle value => cases value; cases sourceSort
    | term value =>
      cases target with
      | term other => cases targetSort
      | bundle other =>
        cases other with
        | node head arguments =>
          have same : head = constructor := Srt.arguments.inj targetSort
          subst head
          obtain ⟨occurrence, first, second⟩ :=
            (administrative_step_iff arity Origins (.ask constructor) _ _).mp step
          rcases occurrence with ⟨origin, instance_⟩
          cases instance_ with
          | ask _ supplied =>
            change bundle arity constructor (fun position => embedSource arity (arguments position)) =
              bundle arity constructor supplied at second
            have argumentRead := Term.node.inj second
            rw [← argumentRead] at first
            have sourceRead : value = InstrumentObservations.Tree.node constructor arguments :=
              embedSource_injective arity first
            subst value
            exact ⟨.ask constructor arguments permission⟩
  | get constructor position =>
    cases source with
    | term value => cases sourceSort
    | bundle value =>
      cases value with
      | node head arguments =>
        have same : head = constructor := Srt.arguments.inj sourceSort
        subst head
        cases target with
        | bundle other => cases other; cases targetSort
        | term other =>
          obtain ⟨occurrence, first, second⟩ :=
            (administrative_step_iff arity Origins (.get constructor position) _ _).mp step
          rcases occurrence with ⟨origin, instance_⟩
          cases instance_ with
          | get _ _ supplied =>
            change bundle arity constructor (fun position => embedSource arity (arguments position)) =
              bundle arity constructor supplied at first
            have argumentRead := Term.node.inj first
            have targetRead : other = arguments position := embedSource_injective arity
              (second.trans (congrFun argumentRead position).symm)
            subst other
            exact ⟨.get constructor arguments permission position⟩
  | build constructor =>
    cases source with
    | term value => cases sourceSort
    | bundle value =>
      cases value with
      | node head arguments =>
        have same : head = constructor := Srt.arguments.inj sourceSort
        subst head
        cases target with
        | bundle other => cases other; cases targetSort
        | term other =>
          obtain ⟨occurrence, first, second⟩ :=
            (administrative_step_iff arity Origins (.build constructor) _ _).mp step
          rcases occurrence with ⟨origin, instance_⟩
          cases instance_ with
          | build _ supplied =>
            change bundle arity constructor (fun position => embedSource arity (arguments position)) =
              bundle arity constructor supplied at first
            have argumentRead := Term.node.inj first
            rw [← argumentRead] at second
            have targetRead : other = InstrumentObservations.Tree.node constructor arguments :=
              embedSource_injective arity second
            subst other
            exact ⟨.build constructor arguments permission⟩

theorem probe_response_iff (Origins : Type w) [Nonempty Origins]
    (opened : InstrumentObservations.Policy Symbols) (source target : SourceState arity) (label : SourceLabel arity) :
    ProbeResponse arity Origins opened source label target ↔ InstrumentObservations.Response opened source label target :=
  ⟨probe_response_event arity, fun ⟨event⟩ => event_probe_response arity (Classical.choice inferInstance) event⟩

theorem probe_response_monotone {Origins : Type w}
    {first second : InstrumentObservations.Policy Symbols} (larger : ∀ constructor, first constructor → second constructor)
    {source target : SourceState arity} {label : SourceLabel arity}
    (response : ProbeResponse arity Origins first source label target) :
    ProbeResponse arity Origins second source label target := by
  obtain ⟨sourceSort, targetSort, permission, step⟩ := response
  exact ⟨sourceSort, targetSort, larger _ permission, step⟩

theorem probe_response_old_label_iff {Origins : Type w}
    {first second : InstrumentObservations.Policy Symbols} (larger : ∀ constructor, first constructor → second constructor)
    {source target : SourceState arity} {label : SourceLabel arity}
    (allowed : first (requestedConstructor arity label)) :
    ProbeResponse arity Origins second source label target ↔ ProbeResponse arity Origins first source label target := by
  constructor
  · rintro ⟨sourceSort, targetSort, _, step⟩
    exact ⟨sourceSort, targetSort, allowed, step⟩
  · exact probe_response_monotone arity larger

structure IsProbeBisimulation (Origins : Type w) (opened : InstrumentObservations.Policy Symbols)
    (relation : SourceState arity → SourceState arity → Prop) : Prop where
  tags : ∀ {source other}, relation source other → InstrumentObservations.tag source = InstrumentObservations.tag other
  forward : ∀ {source other}, relation source other → ∀ {label target},
    ProbeResponse arity Origins opened source label target →
      ∃ matched, ProbeResponse arity Origins opened other label matched ∧ relation target matched
  backward : ∀ {source other}, relation source other → ∀ {label target},
    ProbeResponse arity Origins opened other label target →
      ∃ matched, ProbeResponse arity Origins opened source label matched ∧ relation matched target

def ProbeBisimilar (Origins : Type w) (opened : InstrumentObservations.Policy Symbols)
    (source other : SourceState arity) : Prop :=
  ∃ relation, IsProbeBisimulation arity Origins opened relation ∧ relation source other

theorem IsProbeBisimulation.smaller {Origins : Type w}
    {first second : InstrumentObservations.Policy Symbols} (larger : ∀ constructor, first constructor → second constructor)
    {relation : SourceState arity → SourceState arity → Prop}
    (bisimulation : IsProbeBisimulation arity Origins second relation) :
    IsProbeBisimulation arity Origins first relation where
  tags := bisimulation.tags
  forward := by
    intro source other paired label target response
    have permission : first (requestedConstructor arity label) := by
      obtain ⟨_, _, supplied, _⟩ := response
      exact supplied
    obtain ⟨matched, step, successor⟩ := bisimulation.forward paired (probe_response_monotone arity larger response)
    exact ⟨matched, (probe_response_old_label_iff arity larger permission).mp step, successor⟩
  backward := by
    intro source other paired label target response
    have permission : first (requestedConstructor arity label) := by
      obtain ⟨_, _, supplied, _⟩ := response
      exact supplied
    obtain ⟨matched, step, successor⟩ := bisimulation.backward paired (probe_response_monotone arity larger response)
    exact ⟨matched, (probe_response_old_label_iff arity larger permission).mp step, successor⟩

theorem probe_bisimilar_monotone {Origins : Type w}
    {first second : InstrumentObservations.Policy Symbols} (larger : ∀ constructor, first constructor → second constructor)
    {source other : SourceState arity} (related : ProbeBisimilar arity Origins second source other) :
    ProbeBisimilar arity Origins first source other := by
  obtain ⟨relation, bisimulation, paired⟩ := related
  exact ⟨relation, bisimulation.smaller arity larger, paired⟩

theorem probe_bisimulation_iff (Origins : Type w) [Nonempty Origins]
    (opened : InstrumentObservations.Policy Symbols) (relation : SourceState arity → SourceState arity → Prop) :
    IsProbeBisimulation arity Origins opened relation ↔ InstrumentObservations.IsBisimulation opened relation := by
  constructor
  · intro bisimulation
    refine ⟨bisimulation.tags, ?_, ?_⟩
    · intro source other related label target response
      obtain ⟨matched, step, successors⟩ := bisimulation.forward related
        ((probe_response_iff arity Origins opened source target label).mpr response)
      exact ⟨matched, (probe_response_iff arity Origins opened other matched label).mp step, successors⟩
    · intro source other related label target response
      obtain ⟨matched, step, successors⟩ := bisimulation.backward related
        ((probe_response_iff arity Origins opened other target label).mpr response)
      exact ⟨matched, (probe_response_iff arity Origins opened source matched label).mp step, successors⟩
  · intro bisimulation
    refine ⟨bisimulation.tags, ?_, ?_⟩
    · intro source other related label target response
      obtain ⟨matched, step, successors⟩ := bisimulation.forward related
        ((probe_response_iff arity Origins opened source target label).mp response)
      exact ⟨matched, (probe_response_iff arity Origins opened other matched label).mpr step, successors⟩
    · intro source other related label target response
      obtain ⟨matched, step, successors⟩ := bisimulation.backward related
        ((probe_response_iff arity Origins opened other target label).mp response)
      exact ⟨matched, (probe_response_iff arity Origins opened source matched label).mpr step, successors⟩

/-- The structural kernel is earned for the actual sampled IPO relation.
It does not classify arbitrary future proper reactions or all context labels. -/
theorem probe_term_bisimilar_iff_view (Origins : Type w) [Nonempty Origins]
    (opened : InstrumentObservations.Policy Symbols) (first second : InstrumentObservations.Tree Symbols arity) :
    ProbeBisimilar arity Origins opened (.term first) (.term second) ↔
      InstrumentObservations.view opened first = InstrumentObservations.view opened second := by
  constructor
  · rintro ⟨relation, bisimulation, related⟩
    exact (InstrumentObservations.term_bisimilar_iff_view opened first second).mp
      ⟨relation, (probe_bisimulation_iff arity Origins opened relation).mp bisimulation, related⟩
  · intro same
    obtain ⟨relation, bisimulation, related⟩ := (InstrumentObservations.term_bisimilar_iff_view opened first second).mpr same
    exact ⟨relation, (probe_bisimulation_iff arity Origins opened relation).mpr bisimulation, related⟩

theorem probe_partial_observer_characterization (Origins : Type w) [Nonempty Origins]
    (kit : List Symbols) (first second : InstrumentObservations.Tree Symbols arity) :
    ProbeBisimilar arity Origins (fun constructor => constructor ∈ kit) (.term first) (.term second) ↔
      InstrumentObservations.LogicallyEquivalent (fun constructor => constructor ∈ kit) first second :=
  (probe_term_bisimilar_iff_view arity Origins _ first second).trans
    (InstrumentObservations.logicallyEquivalent_iff_view kit first second).symm

end Mettapedia.OSLF.Framework.InstrumentCutContexts
