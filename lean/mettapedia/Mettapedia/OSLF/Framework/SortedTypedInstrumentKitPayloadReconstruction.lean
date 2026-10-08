import Mettapedia.OSLF.Framework.SortedTypedInstrumentKitPayloadIPOSystem

/-!
# Generated-subalgebra reconstruction with the kit's own payload fixed point

Every label payload and whole successor is related by the same greatest
fixed point of the actual supported firing system. Locally admitted fresh
probe shapes recover the literal ask/get label independently of that
relation. Recursive child equality earns purity before excluding a competing
original unit-rule get successor. The right value is arbitrary supported
native syntax; the generated left class may have an unopened AC1 raw root.
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
variable (opened : Policy source Parallel)
  (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))

private theorem payload_generated_constructor_reconstruction
    (origins : Nonempty NativeOrigins) (head : SourceHead source Parallel) (permission : opened head)
    (arguments : (position : Fin (headArity head)) → Term source Parallel (headInput head position))
    (childRecovery : ∀ position
      (right : ValueClass (source := source) (Parallel := Parallel) (.original (headInput head position)))
      (_rightSupported : ClassSupported opened right),
      (payloadSystem (NativeOrigins := NativeOrigins) opened originalRules).Bisimilar _
        (classOf (embed (arguments position))) right → classOf (embed (arguments position)) = right)
    (right : ValueClass (source := source) (Parallel := Parallel) (.original (headOutput head)))
    (rightSupported : ClassSupported opened right)
    (related : (payloadSystem (NativeOrigins := NativeOrigins) opened originalRules).Bisimilar _
      (classOf (sourceNode head (fun position => embed (arguments position)))) right) :
    classOf (sourceNode head (fun position => embed (arguments position))) = right := by
  obtain ⟨origin⟩ := origins
  let embedded : Arguments head := fun position => embed (arguments position)
  have children : ∀ position, Supported opened (embedded position) :=
    fun position => embed_supported opened (arguments position)
  have inputSupported : ClassSupported opened (classOf (sourceNode head embedded)) :=
    ⟨_, (sourceNode_supported_iff opened head embedded).mpr children, rfl⟩
  have tupleSupported : ClassSupported opened (classOf (bundle head embedded)) :=
    ⟨_, (bundle_supported_iff opened head embedded).mpr ⟨permission, children⟩, rfl⟩
  have askStep := ask_step opened originalRules origin head embedded permission children
  obtain ⟨matched, matchedSupported, matchedStep, tupleRelated⟩ :=
    payload_bisimilar_probe_forward opened originalRules (.ask head) permission
      inputSupported rightSupported tupleSupported related askStep
  obtain ⟨_matchedOrigin, before, rightRead, wholeTarget⟩ :=
    ask_step_readout opened originalRules head permission right rightSupported matched matchedSupported matchedStep
  subst matched
  have beforeChildren : ∀ position, Supported opened (before position) :=
    ((bundle_supported_iff opened head before).mp
      ((classOf_supported_iff opened (bundle head before)).mp matchedSupported)).2
  have coordinates : ∀ position, classOf (embedded position) = classOf (before position) := by
    intro position
    have getStep := get_step opened originalRules origin head embedded position permission children
    obtain ⟨after, afterSupported, afterStep, childRelated⟩ :=
      payload_bisimilar_probe_forward opened originalRules (.get head position) permission
        tupleSupported matchedSupported ⟨_, children position, rfl⟩ tupleRelated getStep
    have recovered := childRecovery position after afterSupported childRelated
    have pureAfter : classObserverCount after = 0 := by
      rw [← recovered]
      exact classObserverCount_embedding (classOf (arguments position))
    have actualCoordinate := (get_pure_result_readout opened originalRules
      head before position permission beforeChildren after afterSupported pureAfter afterStep).2
    exact recovered.trans actualCoordinate
  exact (sourceNode_class_congruence head embedded before coordinates).trans rightRead.symm

private theorem raw_payload_generated_reconstruction
    (origins : Nonempty NativeOrigins) {sort : source.Srt} (left : Term source Parallel sort) :
    StructuralObservations.Supported opened left →
      ∀ (right : ValueClass (source := source) (Parallel := Parallel) (.original sort))
        (_rightSupported : ClassSupported opened right),
        (payloadSystem (NativeOrigins := NativeOrigins) opened originalRules).Bisimilar _
          (classOf (embed left)) right → classOf (embed left) = right := by
  apply @Term.rec source Parallel
    (fun sort left => StructuralObservations.Supported opened left →
      ∀ (right : ValueClass (source := source) (Parallel := Parallel) (.original sort))
        (rightSupported : ClassSupported opened right),
        (payloadSystem (NativeOrigins := NativeOrigins) opened originalRules).Bisimilar _
          (classOf (embed left)) right → classOf (embed left) = right) (t := left)
  · intro sort parallel supported right rightSupported related
    exact payload_generated_constructor_reconstruction opened originalRules origins (.unit sort parallel) supported
      (fun position => Fin.elim0 position) (fun position => Fin.elim0 position) right rightSupported related
  · intro sort parallel first second firstInduction secondInduction supported right rightSupported related
    let arguments : Fin 2 → Term source Parallel sort := Fin.cases first (fun _ => second)
    have recoveries : ∀ position
        (after : ValueClass (source := source) (Parallel := Parallel) (.original sort))
        (afterSupported : ClassSupported opened after),
        (payloadSystem (NativeOrigins := NativeOrigins) opened originalRules).Bisimilar _
          (classOf (embed (arguments position))) after → classOf (embed (arguments position)) = after := by
      intro position
      fin_cases position
      · exact firstInduction supported.2.1
      · exact secondInduction supported.2.2
    exact payload_generated_constructor_reconstruction opened originalRules origins (.properCut sort parallel) supported.1
      arguments recoveries right rightSupported related
  · intro constructor arguments inductionHypothesis supported right rightSupported related
    exact payload_generated_constructor_reconstruction opened originalRules origins (.ordinary constructor) supported.1
      arguments (fun position => inductionHypothesis position (supported.2 position)) right rightSupported related

theorem payload_bisimilar_iff_embedded_equal_of_generated (origins : Nonempty NativeOrigins)
    {sort : source.Srt} (left : Class source Parallel sort)
    (generated : StructuralObservations.Generated opened left)
    (right : ValueClass (source := source) (Parallel := Parallel) (.original sort))
    (rightSupported : ClassSupported opened right) :
    (payloadSystem (NativeOrigins := NativeOrigins) opened originalRules).Bisimilar _ (classEmbedding left) right ↔
      classEmbedding left = right := by
  constructor
  · obtain ⟨representative, supported, rfl⟩ := generated
    exact raw_payload_generated_reconstruction opened originalRules origins representative supported right rightSupported
  · rintro rfl
    exact (payloadSystem (NativeOrigins := NativeOrigins) opened originalRules).bisimilar_refl _ _

theorem payload_bisimilar_iff_source_equal_of_generated (origins : Nonempty NativeOrigins)
    {sort : source.Srt} (first second : Class source Parallel sort)
    (generated : StructuralObservations.Generated opened first) :
    (payloadSystem (NativeOrigins := NativeOrigins) opened originalRules).Bisimilar _
      (classEmbedding first) (classEmbedding second) ↔ first = second :=
  (payload_bisimilar_iff_embedded_equal_of_generated opened originalRules origins first generated
    (classEmbedding second) (classEmbedding_supported opened second)).trans
      ⟨fun same => classEmbedding_injective same, fun same => congrArg classEmbedding same⟩

theorem literal_iff_payload_bisimilar_of_generated (origins : Nonempty NativeOrigins)
    {sort : source.Srt} (first second : Class source Parallel sort)
    (generated : StructuralObservations.Generated opened first) :
    IPOBisimilar (categoryRules (NativeOrigins := NativeOrigins) originalRules opened)
      (value (classEmbedding first) (classEmbedding_supported opened first))
      (value (classEmbedding second) (classEmbedding_supported opened second)) ↔
        (payloadSystem (NativeOrigins := NativeOrigins) opened originalRules).Bisimilar _
          (classEmbedding first) (classEmbedding second) :=
  (observer_bisimilar_iff_source_equal_of_generated opened originalRules origins first second generated).trans
    (payload_bisimilar_iff_source_equal_of_generated opened originalRules origins first second generated).symm

theorem partialLogicalEquivalent_iff_actual_payload_observer_of_generated (origins : Nonempty NativeOrigins)
    {sort : source.Srt} (first second : Class source Parallel sort)
    (generated : StructuralObservations.Generated opened first) :
    StructuralObservations.PartialLogicalEquivalent opened first second ↔
      (payloadSystem (NativeOrigins := NativeOrigins) opened originalRules).Bisimilar _
        (classEmbedding first) (classEmbedding second) :=
  (StructuralObservations.partialLogicalEquivalent_iff_equal_of_generated opened first second generated).trans
    (payload_bisimilar_iff_source_equal_of_generated opened originalRules origins first second generated).symm

end Mettapedia.OSLF.Framework.SortedTypedInstruments.Kit
