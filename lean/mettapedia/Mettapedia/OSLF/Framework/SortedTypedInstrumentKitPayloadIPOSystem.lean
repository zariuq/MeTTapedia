import Mettapedia.OSLF.Framework.SortedTypedInstrumentKitReconstruction
import Mettapedia.OSLF.Framework.SortedTypedInstrumentPayloadIPOSystem

/-!
# Complete typed kit firings with same-fixed-point payload labels

The independently decoded complete context supplies the label skeleton and
every payload. A transition retains support of its actual context, input
and output and a firing in the actual kit category. Thus every stepping
state is an actual kit value; no transition on an unsupported value is
introduced. The ambient value family is retained for the heterogeneous
payload vocabulary, while complete firing comparison is proved at supported
states. Fresh probe rigidity is earned from its empty payload family.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstruments.Kit

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RedexRelativeCongruence

universe u v w z

variable {source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
  {Parallel : source.Srt → Prop} {OriginalOrigins : Type z} {NativeOrigins : Type w}

def payloadSystem (opened : Policy source Parallel)
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel)) :
    Mettapedia.GSLT.HigherOrderBisimulation.System.{max u v, max u v, max u v, max u v}
      (PayloadLabels.vocabulary source Parallel) (ValueClass (source := source) (Parallel := Parallel)) where
  act := fun {firstSort lastSort} label first last =>
    ∃ supplied : ContextClass (signature source Parallel) NativeParallel firstSort lastSort,
      PayloadLabels.encodeContext supplied = label ∧
        ∃ contextSupported : ClassContextSupported opened supplied,
          ∃ firstSupported : ClassSupported opened first, ∃ lastSupported : ClassSupported opened last,
            ActIPO (categoryRules (NativeOrigins := NativeOrigins) originalRules opened)
              (context supplied contextSupported) (value first firstSupported) (value last lastSupported)
  Atom := fun _ => PEmpty
  observes := fun atom => PEmpty.elim atom

variable (opened : Policy source Parallel)
  (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))

theorem payload_actual_firing_iff {firstSort lastSort : Srt source Parallel}
    (supplied : ContextClass (signature source Parallel) NativeParallel firstSort lastSort)
    (contextSupported : ClassContextSupported opened supplied)
    (first : ValueClass (source := source) (Parallel := Parallel) firstSort)
    (firstSupported : ClassSupported opened first)
    (last : ValueClass (source := source) (Parallel := Parallel) lastSort)
    (lastSupported : ClassSupported opened last) :
    (payloadSystem (NativeOrigins := NativeOrigins) opened originalRules).act
      (PayloadLabels.encodeContext supplied) first last ↔
        ActIPO (categoryRules (NativeOrigins := NativeOrigins) originalRules opened)
          (context supplied contextSupported) (value first firstSupported) (value last lastSupported) := by
  constructor
  · rintro ⟨actualContext, same, actualSupport, beforeSupport, afterSupport, actual⟩
    have contextRead := PayloadLabels.encodeContext_injective same
    subst actualContext
    exact actual
  · intro actual
    exact ⟨supplied, rfl, contextSupported, firstSupported, lastSupported, actual⟩

theorem payload_probe_act_iff (instrument : Probe source Parallel)
    (permission : opened (instrumentHead instrument))
    (first : ValueClass (source := source) (Parallel := Parallel) (receiver instrument))
    (firstSupported : ClassSupported opened first)
    (last : ValueClass (source := source) (Parallel := Parallel) (result instrument))
    (lastSupported : ClassSupported opened last) :
    (payloadSystem (NativeOrigins := NativeOrigins) opened originalRules).act
      (PayloadLabels.probeLabel instrument) first last ↔
        ActIPO (categoryRules (NativeOrigins := NativeOrigins) originalRules opened)
          (probeArrow opened instrument permission) (value first firstSupported) (value last lastSupported) := by
  rw [← PayloadLabels.encode_probeContext instrument]
  exact payload_actual_firing_iff opened originalRules _
    ⟨_, probeContext_supported opened instrument permission, rfl⟩ first firstSupported last lastSupported

theorem payload_probe_act_readout (instrument : Probe source Parallel)
    (permission : opened (instrumentHead instrument))
    (first : ValueClass (source := source) (Parallel := Parallel) (receiver instrument))
    (last : ValueClass (source := source) (Parallel := Parallel) (result instrument))
    (actual : (payloadSystem (NativeOrigins := NativeOrigins) opened originalRules).act
      (PayloadLabels.probeLabel instrument) first last) :
    ∃ firstSupported : ClassSupported opened first, ∃ lastSupported : ClassSupported opened last,
      ActIPO (categoryRules (NativeOrigins := NativeOrigins) originalRules opened)
        (probeArrow opened instrument permission) (value first firstSupported) (value last lastSupported) := by
  obtain ⟨supplied, read, contextSupported, firstSupported, lastSupported, step⟩ := actual
  have contextRead : supplied = contextClassOf (probeContext instrument) := by
    apply PayloadLabels.encodeContext_injective
    exact read.trans (PayloadLabels.encode_probeContext instrument).symm
  subst supplied
  exact ⟨firstSupported, lastSupported, step⟩

theorem payload_bisimilar_probe_forward (instrument : Probe source Parallel)
    (permission : opened (instrumentHead instrument))
    {first second : ValueClass (source := source) (Parallel := Parallel) (receiver instrument)}
    {last : ValueClass (source := source) (Parallel := Parallel) (result instrument)}
    (firstSupported : ClassSupported opened first) (secondSupported : ClassSupported opened second)
    (lastSupported : ClassSupported opened last)
    (related : (payloadSystem (NativeOrigins := NativeOrigins) opened originalRules).Bisimilar _ first second)
    (actual : ActIPO (categoryRules (NativeOrigins := NativeOrigins) originalRules opened)
      (probeArrow opened instrument permission) (value first firstSupported) (value last lastSupported)) :
    ∃ matched, ∃ matchedSupported : ClassSupported opened matched,
      ActIPO (categoryRules (NativeOrigins := NativeOrigins) originalRules opened)
        (probeArrow opened instrument permission) (value second secondSupported) (value matched matchedSupported) ∧
          (payloadSystem (NativeOrigins := NativeOrigins) opened originalRules).Bisimilar _ last matched := by
  have encoded := (payload_probe_act_iff opened originalRules instrument permission
    first firstSupported last lastSupported).mpr actual
  obtain ⟨label, matched, step, labels, successors⟩ :=
    ((payloadSystem (NativeOrigins := NativeOrigins) opened originalRules).bisimilar_unfold.mp related).1 _ _ encoded
  have same := PayloadLabels.related_probe_forward _ instrument label labels
  subst label
  obtain ⟨_, matchedSupported, matchedStep⟩ :=
    payload_probe_act_readout opened originalRules instrument permission second matched step
  exact ⟨matched, matchedSupported, matchedStep, successors⟩

theorem literal_bisimilar_implies_payload_bisimilar {sort : Srt source Parallel}
    (first second : ValueClass (source := source) (Parallel := Parallel) sort)
    (firstSupported : ClassSupported opened first) (secondSupported : ClassSupported opened second)
    (related : IPOBisimilar (categoryRules (NativeOrigins := NativeOrigins) originalRules opened)
      (value first firstSupported) (value second secondSupported)) :
    (payloadSystem (NativeOrigins := NativeOrigins) opened originalRules).Bisimilar sort first second := by
  let relation : Mettapedia.GSLT.HigherOrderBisimulation.RelationFamily
      (ValueClass (source := source) (Parallel := Parallel)) := fun _ before after =>
    before = after ∨ ∃ beforeSupported : ClassSupported opened before,
      ∃ afterSupported : ClassSupported opened after,
        IPOBisimilar (categoryRules (NativeOrigins := NativeOrigins) originalRules opened)
          (value before beforeSupported) (value after afterSupported)
  apply (payloadSystem (NativeOrigins := NativeOrigins) opened originalRules).coinduction
    (relation := relation) ?_ sort first second (Or.inr ⟨firstSupported, secondSupported, related⟩)
  intro current before after pair
  have reflexive : ∀ current supplied, relation current supplied supplied := fun _ _ => Or.inl rfl
  rcases pair with same | ⟨beforeSupported, afterSupported, compared⟩
  · subst after
    exact ⟨fun label next step => ⟨label, next, step,
      Mettapedia.GSLT.HigherOrderBisimulation.Label.relates_refl reflexive label, Or.inl rfl⟩,
      fun label next step => ⟨label, next, step,
      Mettapedia.GSLT.HigherOrderBisimulation.Label.relates_refl reflexive label, Or.inl rfl⟩,
      fun atom => PEmpty.elim atom⟩
  · constructor
    · intro target label next step
      obtain ⟨supplied, read, contextSupported, _, nextSupported, actual⟩ := step
      obtain ⟨matched, matchedStep, successors⟩ := ipoBisimilar_forward compared actual
      obtain ⟨matchedArrow, matchedSupport⟩ := matched
      cases matchedArrow with
      | value matched =>
        have matchedSupported := value_class_supported opened matched matchedSupport
        exact ⟨label, matched, ⟨supplied, read, contextSupported, afterSupported, matchedSupported, matchedStep⟩,
          Mettapedia.GSLT.HigherOrderBisimulation.Label.relates_refl reflexive label,
          Or.inr ⟨nextSupported, matchedSupported, successors⟩⟩
    · constructor
      · intro target label next step
        obtain ⟨supplied, read, contextSupported, _, nextSupported, actual⟩ := step
        obtain ⟨matched, matchedStep, successors⟩ := ipoBisimilar_backward compared actual
        obtain ⟨matchedArrow, matchedSupport⟩ := matched
        cases matchedArrow with
        | value matched =>
          have matchedSupported := value_class_supported opened matched matchedSupport
          exact ⟨label, matched, ⟨supplied, read, contextSupported, beforeSupported, matchedSupported, matchedStep⟩,
            Mettapedia.GSLT.HigherOrderBisimulation.Label.relates_refl reflexive label,
            Or.inr ⟨matchedSupported, nextSupported, successors⟩⟩
      · exact fun atom => PEmpty.elim atom

end Mettapedia.OSLF.Framework.SortedTypedInstruments.Kit
