import Mettapedia.OSLF.Framework.SortedCommutativePayloadProbes
import Mettapedia.OSLF.Framework.SortedCommutativeInstrumentFiring

/-!
# Payload-sensitive bisimulation of actual sorted IPO firings

Transitions encode independently supplied categorical IPO labels. Their
payloads and complete successors are compared by the same monotone greatest
fixed point. The context decoder proves the exact transition readout and
rules out extra label presentations. Administrative receipts retain their
actual origin and entire supplied tuple through this label conversion.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedCommutativeInstruments.PayloadLabels

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RedexRelativeCongruence

universe u w
variable {Symbols : Type u} {arity : Symbols → Nat}

def firingSystem (family : ReactionRule (.origin : ContextCategory arity) → Prop) :
    Mettapedia.GSLT.HigherOrderBisimulation.System.{u, u, u, u}
      (vocabulary arity) (ValueClass arity) where
  act {source target} label first last :=
    ∃ context : ContextClass (signature arity) (Parallel arity) source target,
      encodeContext context = label ∧
        ActIPO family (RawArrow.context context) (RawArrow.value first) (RawArrow.value last)
  Atom := fun _ => PEmpty
  observes := fun atom => PEmpty.elim atom

variable (family : ReactionRule (.origin : ContextCategory arity) → Prop)

theorem actual_firing_encoded {source target : Srt arity}
    (context : ContextClass (signature arity) (Parallel arity) source target)
    (first : ValueClass arity source) (last : ValueClass arity target)
    (actual : ActIPO family (RawArrow.context context) (RawArrow.value first) (RawArrow.value last)) :
    (firingSystem family).act (encodeContext context) first last := ⟨context, rfl, actual⟩

theorem act_read_iff {source target : Srt arity} (label : Label arity source target)
    (first : ValueClass arity source) (last : ValueClass arity target) :
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

theorem probe_act_iff (instrument : Probe arity)
    (first : ValueClass arity (InstrumentCutContexts.receiver (sourceArity arity) instrument))
    (last : ValueClass arity (InstrumentCutContexts.result (sourceArity arity) instrument)) :
    (firingSystem family).act (probeLabel instrument) first last ↔
      ActIPO family (RawArrow.context (contextClassOf (probeContext arity instrument)))
        (RawArrow.value first) (RawArrow.value last) := by
  rw [act_read_iff, read_probeLabel, encode_probeContext]
  exact and_iff_right rfl

theorem bisimilar_probe_forward (instrument : Probe arity)
    {first second : ValueClass arity (InstrumentCutContexts.receiver (sourceArity arity) instrument)}
    {last : ValueClass arity (InstrumentCutContexts.result (sourceArity arity) instrument)}
    (related : (firingSystem family).Bisimilar _ first second)
    (actual : ActIPO family (RawArrow.context (contextClassOf (probeContext arity instrument)))
      (RawArrow.value first) (RawArrow.value last)) :
    ∃ matched, ActIPO family (RawArrow.context (contextClassOf (probeContext arity instrument)))
        (RawArrow.value second) (RawArrow.value matched) ∧
      (firingSystem family).Bisimilar _ last matched := by
  have encoded := (probe_act_iff family instrument first last).mpr actual
  obtain ⟨label, matched, step, labels, successors⟩ :=
    ((firingSystem family).bisimilar_unfold.mp related).1 (probeLabel instrument) last encoded
  have literalRead := related_probe_forward (firingSystem family).Bisimilar instrument label labels
  rw [literalRead] at step
  exact ⟨matched, (probe_act_iff family instrument second matched).mp step, successors⟩

theorem literal_bisimilar_implies_payload {sort : Srt arity}
    {first second : ValueClass arity sort}
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

structure PayloadReceipt (arity : Symbols → Nat) (Origins : Type w) where
  occurrence : Occurrence arity Origins
  step : (firingSystem (rules arity Origins)).act (probeLabel occurrence.instrument)
    (classOf occurrence.body) (classOf occurrence.output)

def transportReceipt {Origins : Type w}
    (receipt : SortedCommutativeInstruments.FiringReceipt arity Origins) : PayloadReceipt arity Origins :=
  ⟨receipt.occurrence,
    (probe_act_iff (rules arity Origins) receipt.occurrence.instrument _ _).mpr receipt.step⟩

theorem transportReceipt_origin {Origins : Type w}
    (receipt : SortedCommutativeInstruments.FiringReceipt arity Origins) :
    (transportReceipt receipt).occurrence.origin = receipt.occurrence.origin := rfl

theorem transportReceipt_injective {Origins : Type w} :
    Function.Injective (transportReceipt (arity := arity) (Origins := Origins)) := by
  intro first second same
  have occurrences := congrArg PayloadReceipt.occurrence same
  cases first with
  | mk first firstStep =>
    cases second with
    | mk second secondStep =>
      change first = second at occurrences
      subst second
      rfl

def directPayloadReceipt {Origins : Type w} (supplied : Occurrence arity Origins) :
    PayloadReceipt arity Origins := transportReceipt (directReceipt supplied)

theorem directPayloadReceipt_injective {Origins : Type w} :
    Function.Injective (directPayloadReceipt (arity := arity) (Origins := Origins)) :=
  transportReceipt_injective.comp directReceipt_injective

end Mettapedia.OSLF.Framework.SortedCommutativeInstruments.PayloadLabels
