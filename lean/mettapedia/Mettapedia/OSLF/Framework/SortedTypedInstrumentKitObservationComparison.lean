import Mettapedia.OSLF.Framework.SortedTypedInstrumentKitPayloadReconstruction
import Mettapedia.OSLF.Framework.SortedTypedInstrumentKitMonotonicity

/-!
# Complete context and kit comparisons at the generated observational ceiling

The independent generated grammar is monotone under head permissions.
Reconstruction then derives the partial-kit payload implication and complete
context substitution on generated left values. Every stored native child and
parallel residue is retained, and output support is independently earned
from the actual supported context. These scoped comparisons do not assert
arbitrary payload-bisimulation congruence outside the generated subalgebra.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstruments

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RedexRelativeCongruence

universe u v w z

variable {source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
  {Parallel : source.Srt → Prop} {OriginalOrigins : Type z} {NativeOrigins : Type w}

namespace StructuralObservations

theorem supported_monotone {first second : Policy source Parallel}
    (inclusion : ∀ head, first head → second head) {sort : source.Srt}
    (supplied : Term source Parallel sort) (supported : Supported first supplied) : Supported second supplied := by
  induction supplied with
  | zero parallel => exact inclusion _ supported
  | cut parallel before after beforeRead afterRead =>
    exact ⟨inclusion _ supported.1, beforeRead supported.2.1, afterRead supported.2.2⟩
  | node constructor arguments inductionHypothesis =>
    exact ⟨inclusion _ supported.1, fun position => inductionHypothesis position (supported.2 position)⟩

theorem generated_monotone {first second : Policy source Parallel}
    (inclusion : ∀ head, first head → second head) {sort : source.Srt}
    (supplied : Class source Parallel sort) (generated : Generated first supplied) : Generated second supplied := by
  obtain ⟨representative, supported, read⟩ := generated
  exact ⟨representative, supported_monotone inclusion representative supported, read⟩

end StructuralObservations

namespace Kit

theorem payload_bisimulation_monotone_of_generated {first second : Policy source Parallel}
    (subkit : ∀ head, first head → second head)
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    (origins : Nonempty NativeOrigins) {sort : source.Srt} (left : Class source Parallel sort)
    (generated : StructuralObservations.Generated first left)
    (right : ValueClass (source := source) (Parallel := Parallel) (.original sort))
    (rightSupported : ClassSupported first right)
    (related : (payloadSystem (NativeOrigins := NativeOrigins) second originalRules).Bisimilar _
      (classEmbedding left) right) :
    (payloadSystem (NativeOrigins := NativeOrigins) first originalRules).Bisimilar _ (classEmbedding left) right := by
  have same := (payload_bisimilar_iff_embedded_equal_of_generated second originalRules origins left
    (StructuralObservations.generated_monotone subkit left generated) right
    (rightSupported.monotone subkit)).mp related
  exact (payload_bisimilar_iff_embedded_equal_of_generated first originalRules origins
    left generated right rightSupported).mpr same

theorem generated_payload_context_readout (opened : Policy source Parallel)
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    (origins : Nonempty NativeOrigins) {firstSort : source.Srt} {lastSort : Srt source Parallel}
    (left : Class source Parallel firstSort) (generated : StructuralObservations.Generated opened left)
    (right : ValueClass (source := source) (Parallel := Parallel) (.original firstSort))
    (rightSupported : ClassSupported opened right)
    (supplied : ContextClass (signature source Parallel) NativeParallel (.original firstSort) lastSort)
    (contextSupported : ClassContextSupported opened supplied)
    (related : (payloadSystem (NativeOrigins := NativeOrigins) opened originalRules).Bisimilar _
      (classEmbedding left) right) :
    ClassSupported opened (supplied.fill (classEmbedding left)) ∧
      ClassSupported opened (supplied.fill right) ∧
        supplied.fill (classEmbedding left) = supplied.fill right ∧
          (payloadSystem (NativeOrigins := NativeOrigins) opened originalRules).Bisimilar _
            (supplied.fill (classEmbedding left)) (supplied.fill right) := by
  have same := (payload_bisimilar_iff_embedded_equal_of_generated opened originalRules origins
    left generated right rightSupported).mp related
  have complete := congrArg supplied.fill same
  refine ⟨(context_supported_fill_iff opened supplied _).mpr
    ⟨contextSupported, classEmbedding_supported opened left⟩,
    (context_supported_fill_iff opened supplied _).mpr ⟨contextSupported, rightSupported⟩, complete, ?_⟩
  rw [complete]
  exact (payloadSystem (NativeOrigins := NativeOrigins) opened originalRules).bisimilar_refl _ _

theorem generated_observation_preserves_all_source_contexts (opened : Policy source Parallel)
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    (origins : Nonempty NativeOrigins) {firstSort lastSort : source.Srt}
    (left right : Class source Parallel firstSort) (generated : StructuralObservations.Generated opened left)
    (related : (payloadSystem (NativeOrigins := NativeOrigins) opened originalRules).Bisimilar _
      (classEmbedding left) (classEmbedding right)) (supplied : ContextClass source Parallel firstSort lastSort) :
    (payloadSystem (NativeOrigins := NativeOrigins) opened originalRules).Bisimilar _
      (classEmbedding (supplied.fill left)) (classEmbedding (supplied.fill right)) := by
  have same := (payload_bisimilar_iff_source_equal_of_generated opened originalRules origins
    left right generated).mp related
  rw [same]
  exact (payloadSystem (NativeOrigins := NativeOrigins) opened originalRules).bisimilar_refl _ _

end Kit

end Mettapedia.OSLF.Framework.SortedTypedInstruments
