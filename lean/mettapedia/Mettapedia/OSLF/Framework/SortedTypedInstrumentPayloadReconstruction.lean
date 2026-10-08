import Mettapedia.OSLF.Framework.SortedTypedInstrumentPayloadIPOSystem
import Mettapedia.OSLF.Framework.SortedTypedInstrumentCombinedReconstruction

/-!
# Complete heterogeneous reconstruction in the payload-sensitive fixed point

Label values and successors are compared by the same greatest fixed point
at their actual sorts. Fresh probe labels have independently proved empty
payload families, so their matching recovers the complete categorical
probe. Recursive get matching then reconstructs each heterogeneous child
before its earned purity excludes an original-rule successor.

Original rules are arbitrary, including unit redexes. The right state is
arbitrary native syntax at the same original sort. Administrative origins
are explicitly inhabited; no source-sort inhabitance, total erasure,
unique-get-target or current-view converse is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstruments.PayloadLabels

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RedexRelativeCongruence

universe u v w

variable {source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
  {Parallel : source.Srt → Prop} {Origins : Type w}
variable (sourceRules : ReactionRule (.origin : SourceCategory source Parallel) → Prop)

private theorem constructor_reconstruction
    (origins : Nonempty Origins) (head : SourceHead source Parallel)
    (arguments : (position : Fin (headArity head)) → Term source Parallel (headInput head position))
    (childRecovery : ∀ position
      (right : ValueClass (source := source) (Parallel := Parallel) (.original (headInput head position))),
      (firingSystem (combinedSourceRules sourceRules Origins)).Bisimilar _
        (classOf (embed (arguments position))) right → classOf (embed (arguments position)) = right)
    (right : ValueClass (source := source) (Parallel := Parallel) (.original (headOutput head)))
    (related : (firingSystem (combinedSourceRules sourceRules Origins)).Bisimilar _
      (classOf (sourceNode head (fun position => embed (arguments position)))) right) :
    classOf (sourceNode head (fun position => embed (arguments position))) = right := by
  obtain ⟨origin⟩ := origins
  let embedded : Arguments head := fun position => embed (arguments position)
  have askStep : ActIPO (combinedSourceRules sourceRules Origins)
      (SortedTypedInstruments.probeLabel (.ask head))
      (RawArrow.value (classOf (sourceNode head embedded)))
      (RawArrow.value (classOf (bundle head embedded))) := by
    obtain ⟨rule, admitted, reaction, square, minimal, output⟩ := (Occurrence.ask origin head embedded).direct_step
    exact ⟨rule, Or.inl admitted, reaction, square, minimal, output⟩
  obtain ⟨matched, matchedStep, tupleRelated⟩ :=
    bisimilar_probe_forward (combinedSourceRules sourceRules Origins) (.ask head) related askStep
  obtain ⟨_matchedOrigin, before, rightRead, wholeTarget⟩ :=
    (combined_ask_step_iff sourceRules head right matched).mp matchedStep
  rw [wholeTarget] at tupleRelated
  have coordinates : ∀ position, classOf (embedded position) = classOf (before position) := by
    intro position
    have getStep : ActIPO (combinedSourceRules sourceRules Origins)
        (SortedTypedInstruments.probeLabel (.get head position))
        (RawArrow.value (classOf (bundle head embedded)))
        (RawArrow.value (classOf (embedded position))) := by
      obtain ⟨rule, admitted, reaction, square, minimal, output⟩ :=
        (Occurrence.get origin head embedded position).direct_step
      exact ⟨rule, Or.inl admitted, reaction, square, minimal, output⟩
    obtain ⟨after, afterStep, childRelated⟩ :=
      bisimilar_probe_forward (combinedSourceRules sourceRules Origins)
        (.get head position) tupleRelated getStep
    have recovered : classOf (embedded position) = after := childRecovery position after childRelated
    have pureAfter : classObserverCount after = 0 := by
      rw [← recovered]
      exact classObserverCount_embedding (classOf (arguments position))
    have actualCoordinate := (combined_get_pure_result_readout sourceRules
      head before position after pureAfter afterStep).2
    exact recovered.trans actualCoordinate
  exact (sourceNode_class_congruence head embedded before coordinates).trans rightRead.symm

private theorem raw_source_reconstruction
    (origins : Nonempty Origins) {sort : source.Srt} (left : Term source Parallel sort) :
    ∀ right : ValueClass (source := source) (Parallel := Parallel) (.original sort),
      (firingSystem (combinedSourceRules sourceRules Origins)).Bisimilar _
        (classOf (embed left)) right → classOf (embed left) = right := by
  apply @Term.rec source Parallel
    (fun sort left => ∀ right : ValueClass (source := source) (Parallel := Parallel) (.original sort),
      (firingSystem (combinedSourceRules sourceRules Origins)).Bisimilar _
        (classOf (embed left)) right → classOf (embed left) = right) (t := left)
  · intro sort parallel right related
    exact constructor_reconstruction sourceRules origins (.unit sort parallel)
      (fun position => Fin.elim0 position) (fun position => Fin.elim0 position) right related
  · intro sort parallel first second firstInduction secondInduction right related
    let arguments : Fin 2 → Term source Parallel sort := Fin.cases first (fun _ => second)
    have recoveries : ∀ position (after : ValueClass (source := source) (Parallel := Parallel) (.original sort)),
        (firingSystem (combinedSourceRules sourceRules Origins)).Bisimilar _
          (classOf (embed (arguments position))) after → classOf (embed (arguments position)) = after := by
      intro position
      fin_cases position
      · exact firstInduction
      · exact secondInduction
    exact constructor_reconstruction sourceRules origins (.properCut sort parallel)
      arguments recoveries right related
  · intro constructor arguments inductionHypothesis right related
    exact constructor_reconstruction sourceRules origins (.ordinary constructor)
      arguments inductionHypothesis right related

theorem bisimilar_iff_embedded_equal (origins : Nonempty Origins)
    {sort : source.Srt} (left : Class source Parallel sort)
    (right : ValueClass (source := source) (Parallel := Parallel) (.original sort)) :
    (firingSystem (combinedSourceRules sourceRules Origins)).Bisimilar _
      (classEmbedding left) right ↔ classEmbedding left = right := by
  constructor
  · refine Quotient.inductionOn left ?_
    intro raw related
    exact raw_source_reconstruction sourceRules origins raw right related
  · intro same
    rw [same]
    exact (firingSystem (combinedSourceRules sourceRules Origins)).bisimilar_refl _ right

theorem bisimilar_iff_source_equal (origins : Nonempty Origins)
    {sort : source.Srt} (first second : Class source Parallel sort) :
    (firingSystem (combinedSourceRules sourceRules Origins)).Bisimilar _
      (classEmbedding first) (classEmbedding second) ↔ first = second :=
  (bisimilar_iff_embedded_equal sourceRules origins first (classEmbedding second)).trans
    ⟨fun same => classEmbedding_injective same, fun same => congrArg classEmbedding same⟩

theorem raw_bisimilar_iff_source_equation (origins : Nonempty Origins)
    {sort : source.Srt} (first second : Term source Parallel sort) :
    (firingSystem (combinedSourceRules sourceRules Origins)).Bisimilar _
      (classOf (embed first)) (classOf (embed second)) ↔ Equation first second :=
  (bisimilar_iff_source_equal sourceRules origins (classOf first) (classOf second)).trans
    ⟨fun same => Quotient.exact same, fun equation => Quotient.sound equation⟩

theorem source_context_congruence (origins : Nonempty Origins) {firstSort secondSort : source.Srt}
    (context : ContextClass source Parallel firstSort secondSort) {first second : Class source Parallel firstSort}
    (related : (firingSystem (combinedSourceRules sourceRules Origins)).Bisimilar _
      (classEmbedding first) (classEmbedding second)) :
    (firingSystem (combinedSourceRules sourceRules Origins)).Bisimilar _
      (classEmbedding (context.fill first)) (classEmbedding (context.fill second)) := by
  have same := (bisimilar_iff_source_equal sourceRules origins first second).mp related
  exact (bisimilar_iff_source_equal sourceRules origins (context.fill first) (context.fill second)).mpr
    (congrArg context.fill same)

end Mettapedia.OSLF.Framework.SortedTypedInstruments.PayloadLabels
