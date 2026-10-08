import Mettapedia.OSLF.Framework.SortedTypedInstrumentPayloadProbes
import Mettapedia.OSLF.Framework.SortedTypedInstrumentFiring

/-!
# Actual heterogeneous IPO firings with same-fixed-point payload matching

Transitions encode independently supplied complete categorical context
classes. Every label payload and complete successor is compared by the
same monotone greatest fixed point at its actual sort. Decoder roundtrips
rule out extra label presentations. Fresh administrative label rigidity
recovers exact probe transitions and whole supplied origin receipts.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstruments.PayloadLabels

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RedexRelativeCongruence

universe u v w
variable {profile : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
  {Parallel : profile.Srt → Prop}

def firingSystem (family : ReactionRule (.origin : ContextCategory profile Parallel) → Prop) :
    Mettapedia.GSLT.HigherOrderBisimulation.System.{max u v, max u v, max u v, max u v}
      (vocabulary profile Parallel) (ValueClass (source := profile) (Parallel := Parallel)) where
  act {source target} label first last :=
    ∃ context : ContextClass (signature profile Parallel) (NativeParallel (source := profile) (Parallel := Parallel)) source target,
      encodeContext context = label ∧
        ActIPO family (RawArrow.context context) (RawArrow.value first) (RawArrow.value last)
  Atom := fun _ => PEmpty
  observes := fun atom => PEmpty.elim atom

variable (family : ReactionRule (.origin : ContextCategory profile Parallel) → Prop)

theorem actual_firing_encoded {source target : Srt profile Parallel}
    (context : ContextClass (signature profile Parallel) (NativeParallel (source := profile) (Parallel := Parallel)) source target)
    (first : ValueClass (source := profile) (Parallel := Parallel) source) (last : ValueClass (source := profile) (Parallel := Parallel) target)
    (actual : ActIPO family (RawArrow.context context) (RawArrow.value first) (RawArrow.value last)) :
    (firingSystem family).act (encodeContext context) first last := ⟨context, rfl, actual⟩

theorem act_read_iff {source target : Srt profile Parallel} (label : Label profile Parallel source target)
    (first : ValueClass (source := profile) (Parallel := Parallel) source) (last : ValueClass (source := profile) (Parallel := Parallel) target) :
    (firingSystem family).act label first last ↔
      encodeContext (readContext label) = label ∧
        ActIPO family (RawArrow.context (readContext label))
          (RawArrow.value first) (RawArrow.value last) := by
  constructor
  · rintro ⟨context, labelRead, actual⟩
    have recovered : readContext label = context := by
      rw [← labelRead, read_encodeContext]
    exact ⟨by rw [recovered]; exact labelRead, by rw [recovered]; exact actual⟩
  · rintro ⟨labelRead, actual⟩
    exact ⟨readContext label, labelRead, actual⟩

theorem probe_act_iff (instrument : Probe profile Parallel)
    (first : ValueClass (source := profile) (Parallel := Parallel) (receiver instrument))
    (last : ValueClass (source := profile) (Parallel := Parallel) (result instrument)) :
    (firingSystem family).act (probeLabel instrument) first last ↔
      ActIPO family (RawArrow.context (contextClassOf (SortedTypedInstruments.probeContext instrument)))
        (RawArrow.value first) (RawArrow.value last) := by
  rw [act_read_iff, read_probeLabel, encode_probeContext]
  exact and_iff_right rfl

theorem bisimilar_probe_forward (instrument : Probe profile Parallel)
    {first second : ValueClass (source := profile) (Parallel := Parallel) (receiver instrument)}
    {last : ValueClass (source := profile) (Parallel := Parallel) (result instrument)}
    (related : (firingSystem family).Bisimilar _ first second)
    (actual : ActIPO family (RawArrow.context (contextClassOf (SortedTypedInstruments.probeContext instrument)))
      (RawArrow.value first) (RawArrow.value last)) :
    ∃ matched, ActIPO family (RawArrow.context (contextClassOf (SortedTypedInstruments.probeContext instrument)))
        (RawArrow.value second) (RawArrow.value matched) ∧
      (firingSystem family).Bisimilar _ last matched := by
  have encoded := (probe_act_iff family instrument first last).mpr actual
  obtain ⟨label, matched, step, labels, successors⟩ :=
    ((firingSystem family).bisimilar_unfold.mp related).1 (probeLabel instrument) last encoded
  have literalRead := related_probe_forward (firingSystem family).Bisimilar instrument label labels
  rw [literalRead] at step
  exact ⟨matched, (probe_act_iff family instrument second matched).mp step, successors⟩

theorem literal_bisimilar_implies_payload {sort : Srt profile Parallel}
    {first second : ValueClass (source := profile) (Parallel := Parallel) sort}
    (related : IPOBisimilar family (RawArrow.value first) (RawArrow.value second)) :
    (firingSystem family).Bisimilar sort first second := by
  apply (firingSystem family).coinduction
    (relation := fun _ left right => IPOBisimilar family (RawArrow.value left) (RawArrow.value right))
    ?_ sort first second related
  intro current left right pair
  refine ⟨?_, ?_, fun atom => PEmpty.elim atom⟩
  · intro nextInterface label next step
    obtain ⟨context, labelRead, actual⟩ := step
    obtain ⟨matched, matchedStep, successors⟩ := ipoBisimilar_forward pair actual
    cases matched with
    | value matched =>
      exact ⟨label, matched, ⟨context, labelRead, matchedStep⟩,
        Mettapedia.GSLT.HigherOrderBisimulation.Label.relates_refl
          (fun _ state => ipoBisimilar_refl family (RawArrow.value state)) label, successors⟩
  · intro nextInterface label next step
    obtain ⟨context, labelRead, actual⟩ := step
    obtain ⟨matched, matchedStep, successors⟩ := ipoBisimilar_backward pair actual
    cases matched with
    | value matched =>
      exact ⟨label, matched, ⟨context, labelRead, matchedStep⟩,
        Mettapedia.GSLT.HigherOrderBisimulation.Label.relates_refl
          (fun _ state => ipoBisimilar_refl family (RawArrow.value state)) label, successors⟩

structure PayloadReceipt (profile : Mettapedia.OSLF.SortedConstructors.Signature.{u,v})
    (Parallel : profile.Srt → Prop) (Origins : Type w) where
  occurrence : Occurrence profile Parallel Origins
  step : (firingSystem (rules profile Parallel Origins)).act (probeLabel occurrence.instrument)
    (classOf occurrence.body) (classOf occurrence.output)

def transportReceipt {Origins : Type w}
    (receipt : SortedTypedInstruments.FiringReceipt profile Parallel Origins) : PayloadReceipt profile Parallel Origins :=
  ⟨receipt.occurrence,
    (probe_act_iff (rules profile Parallel Origins) receipt.occurrence.instrument _ _).mpr receipt.step⟩

theorem transportReceipt_origin {Origins : Type w}
    (receipt : SortedTypedInstruments.FiringReceipt profile Parallel Origins) :
    (transportReceipt receipt).occurrence.origin = receipt.occurrence.origin := rfl

theorem transportReceipt_injective {Origins : Type w} :
    Function.Injective (transportReceipt (profile := profile) (Parallel := Parallel) (Origins := Origins)) := by
  intro first second same
  have occurrences := congrArg PayloadReceipt.occurrence same
  cases first with
  | mk first firstStep =>
    cases second with
    | mk second secondStep =>
      change first = second at occurrences
      subst second
      rfl

def directPayloadReceipt {Origins : Type w} (supplied : Occurrence profile Parallel Origins) :
    PayloadReceipt profile Parallel Origins := transportReceipt (directReceipt supplied)

theorem directPayloadReceipt_injective {Origins : Type w} :
    Function.Injective (directPayloadReceipt (profile := profile) (Parallel := Parallel) (Origins := Origins)) :=
  transportReceipt_injective.comp directReceipt_injective

end Mettapedia.OSLF.Framework.SortedTypedInstruments.PayloadLabels
