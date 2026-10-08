import Mettapedia.OSLF.Framework.SortedCommutativeSourceArrowSupport

/-!
# Complete RPO comparison for the conservative source inclusion

An arbitrary extended candidate below a source bound has pure incoming and
outgoing arrows. Its actual apex and all three arrows therefore reconstruct
in the source category. Every competing mediator is pure for the same
reason. This earns preservation and reflection of the entire relative
pushout universal property despite the inclusion not being full.

The comparison concerns source spans and source bounds. Observer-labelled
administrative bounds have auxiliary support and are not covered by it.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedCommutativeInstruments.Source

open _root_.CategoryTheory
open Mettapedia.GSLT.RelativePushout
open Support

universe u

variable {Symbols : Type u} {arity : Symbols → Nat}
variable {W X Y Z : SourceCategory (arity := arity)}
variable {first : W ⟶ X} {second : W ⟶ Y} {left : X ⟶ Z} {right : Y ⟶ Z}

private theorem candidate_eq_of_readouts
    {C : Type u} [Category.{u} C] {w x y z : C}
    {f : w ⟶ x} {g : w ⟶ y} {h : x ⟶ z} {i : y ⟶ z}
    (before after : Candidate f g h i) (apex : before.apex = after.apex)
    (inl : HEq before.inl after.inl) (inr : HEq before.inr after.inr)
    (down : HEq before.down after.down) : before = after := by
  cases before
  cases after
  cases apex
  cases eq_of_heq inl
  cases eq_of_heq inr
  cases eq_of_heq down
  rfl

theorem mapped_candidate_support
    (supplied : Candidate (inclusion.map first) (inclusion.map second)
      (inclusion.map left) (inclusion.map right)) :
    arrowObserverCount supplied.inl = 0 ∧ arrowObserverCount supplied.inr = 0 ∧
      arrowObserverCount supplied.down = 0 := by
  have leftSupport : arrowObserverCount (supplied.inl ≫ supplied.down) = 0 :=
    (congrArg arrowObserverCount supplied.fac_left).trans (arrowObserverCount_embedding left)
  have rightSupport : arrowObserverCount (supplied.inr ≫ supplied.down) = 0 :=
    (congrArg arrowObserverCount supplied.fac_right).trans (arrowObserverCount_embedding right)
  exact ⟨(composite_zero_support _ _ leftSupport).1,
    (composite_zero_support _ _ rightSupport).1, (composite_zero_support _ _ leftSupport).2⟩

theorem mapped_candidate_reconstruction
    (supplied : Candidate (inclusion.map first) (inclusion.map second)
      (inclusion.map left) (inclusion.map right)) :
    ∃ before : Candidate first second left right, mapCandidate inclusion before = supplied := by
  have support := mapped_candidate_support supplied
  rcases supplied with ⟨apex, inl, inr, down, comm, facLeft, facRight⟩
  obtain ⟨beforeApex, apexRead⟩ := arrowObserverCount_zero_target inl support.1
  subst apex
  obtain ⟨beforeLeft, leftRead⟩ := arrowObserverCount_zero_preimage inl support.1
  obtain ⟨beforeRight, rightRead⟩ := arrowObserverCount_zero_preimage inr support.2.1
  obtain ⟨beforeDown, downRead⟩ := arrowObserverCount_zero_preimage down support.2.2
  let before : Candidate first second left right :=
    { apex := beforeApex
      inl := beforeLeft
      inr := beforeRight
      down := beforeDown
      comm := inclusion.map_injective (by
        rw [inclusion.map_comp, inclusion.map_comp, leftRead, rightRead]
        exact comm)
      fac_left := inclusion.map_injective (by
        rw [inclusion.map_comp, leftRead, downRead]
        exact facLeft)
      fac_right := inclusion.map_injective (by
        rw [inclusion.map_comp, rightRead, downRead]
        exact facRight) }
  refine ⟨before, candidate_eq_of_readouts _ _ rfl ?_ ?_ ?_⟩
  · exact heq_of_eq leftRead
  · exact heq_of_eq rightRead
  · exact heq_of_eq downRead

theorem mapped_mediator_support (before after : Candidate first second left right)
    (mediator : inclusion.obj before.apex ⟶ inclusion.obj after.apex)
    (equations : Candidate.Mediates (mapCandidate inclusion before) (mapCandidate inclusion after) mediator) :
    arrowObserverCount mediator = 0 := by
  have pure : arrowObserverCount (mediator ≫ inclusion.map after.down) = 0 :=
    (congrArg arrowObserverCount equations.2.2).trans (arrowObserverCount_embedding before.down)
  exact (composite_zero_support _ _ pure).1

theorem mediates_map {before after : Candidate first second left right}
    {mediator : before.apex ⟶ after.apex} (equations : Candidate.Mediates before after mediator) :
    Candidate.Mediates (mapCandidate inclusion before) (mapCandidate inclusion after) (inclusion.map mediator) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [mapCandidate, inclusion.map_comp] using congrArg inclusion.map equations.1
  · simpa only [mapCandidate, inclusion.map_comp] using congrArg inclusion.map equations.2.1
  · simpa only [mapCandidate, inclusion.map_comp] using congrArg inclusion.map equations.2.2

theorem mediates_of_map {before after : Candidate first second left right}
    {mediator : before.apex ⟶ after.apex}
    (equations : Candidate.Mediates (mapCandidate inclusion before) (mapCandidate inclusion after)
      (inclusion.map mediator)) : Candidate.Mediates before after mediator := by
  refine ⟨inclusion.map_injective ?_, inclusion.map_injective ?_, inclusion.map_injective ?_⟩
  · simpa only [mapCandidate, inclusion.map_comp] using equations.1
  · simpa only [mapCandidate, inclusion.map_comp] using equations.2.1
  · simpa only [mapCandidate, inclusion.map_comp] using equations.2.2

theorem preserves_relativePushout (before : Candidate first second left right)
    (universal : IsRelativePushout before) : IsRelativePushout (mapCandidate inclusion before) := by
  intro after
  obtain ⟨sourceAfter, rfl⟩ := mapped_candidate_reconstruction after
  obtain ⟨mediator, equations, unique⟩ := universal sourceAfter
  refine ⟨inclusion.map mediator, mediates_map equations, ?_⟩
  intro alternative laws
  obtain ⟨sourceAlternative, alternativeRead⟩ :=
    arrowObserverCount_zero_preimage alternative (mapped_mediator_support before sourceAfter alternative laws)
  have sourceLaws : Candidate.Mediates before sourceAfter sourceAlternative :=
    mediates_of_map (by simpa only [alternativeRead] using laws)
  exact alternativeRead.symm.trans (congrArg inclusion.map (unique sourceAlternative sourceLaws))

theorem reflects_relativePushout (before : Candidate first second left right)
    (universal : IsRelativePushout (mapCandidate inclusion before)) : IsRelativePushout before := by
  intro after
  obtain ⟨mediator, equations, unique⟩ := universal (mapCandidate inclusion after)
  obtain ⟨sourceMediator, mediatorRead⟩ :=
    arrowObserverCount_zero_preimage mediator (mapped_mediator_support before after mediator equations)
  refine ⟨sourceMediator, mediates_of_map (by simpa only [mediatorRead] using equations), ?_⟩
  intro alternative laws
  apply inclusion.map_injective
  exact (unique (inclusion.map alternative) (mediates_map laws)).trans mediatorRead.symm

theorem relativePushout_iff_mapped (before : Candidate first second left right) :
    IsRelativePushout before ↔ IsRelativePushout (mapCandidate inclusion before) :=
  ⟨preserves_relativePushout before, reflects_relativePushout before⟩

theorem idemPushout_iff_mapped (square : first ≫ left = second ≫ right) :
    IsIdemPushout first second left right square ↔
      IsIdemPushout (inclusion.map first) (inclusion.map second)
        (inclusion.map left) (inclusion.map right)
        (by rw [← inclusion.map_comp, square, inclusion.map_comp]) := by
  have same : mapCandidate inclusion (Candidate.self first second left right square) =
      Candidate.self (inclusion.map first) (inclusion.map second) (inclusion.map left) (inclusion.map right)
        (by rw [← inclusion.map_comp, square, inclusion.map_comp]) :=
    candidate_eq_of_readouts _ _ rfl HEq.rfl HEq.rfl (heq_of_eq (inclusion.map_id Z))
  simpa only [IsIdemPushout, same] using relativePushout_iff_mapped (Candidate.self first second left right square)

end Mettapedia.OSLF.Framework.SortedCommutativeInstruments.Source
