import Mettapedia.GSLT.Logic.RelativePushout
import Mathlib.CategoryTheory.Equivalence

/-!
# Transport of complete relative pushouts through a based equivalence

All three mediator equations and mediator uniqueness are transported through
the actual full and faithful hom action. Object surjectivity is required for
existence and preservation, since competitors may have arbitrary apices.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.GSLT.RelativePushout

open _root_.CategoryTheory

universe u v u' v'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable (F : C ⥤ D)
variable {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}

def mapCandidate (candidate : Candidate f g h i) :
    Candidate (F.map f) (F.map g) (F.map h) (F.map i) where
  apex := F.obj candidate.apex
  inl := F.map candidate.inl
  inr := F.map candidate.inr
  down := F.map candidate.down
  comm := by rw [← F.map_comp, candidate.comm, F.map_comp]
  fac_left := by rw [← F.map_comp, candidate.fac_left]
  fac_right := by rw [← F.map_comp, candidate.fac_right]

set_option backward.isDefEq.respectTransparency false in
theorem reflects_idemPushout [F.Full] [F.Faithful]
    (square : f ≫ h = g ≫ i)
    (mapped : IsIdemPushout (F.map f) (F.map g) (F.map h) (F.map i)
      (by rw [← F.map_comp, square, F.map_comp])) : IsIdemPushout f g h i square := by
  intro candidate
  obtain ⟨mediator, equations, unique⟩ := mapped (mapCandidate F candidate)
  dsimp only [Candidate.self, mapCandidate, Candidate.Mediates] at equations unique ⊢
  refine ⟨F.preimage mediator, ?_, ?_⟩
  · refine ⟨F.map_injective ?_, F.map_injective ?_, F.map_injective ?_⟩
    · simpa only [F.map_comp, F.map_preimage] using equations.1
    · simpa only [F.map_comp, F.map_preimage] using equations.2.1
    · simpa only [F.map_comp, F.map_preimage, F.map_id] using equations.2.2
  · intro other laws
    apply F.map_injective
    rw [F.map_preimage]
    apply unique
    exact ⟨by simpa only [F.map_comp] using congrArg F.map laws.1,
      by simpa only [F.map_comp] using congrArg F.map laws.2.1,
      by simpa only [F.map_comp, F.map_id] using congrArg F.map laws.2.2⟩

set_option backward.isDefEq.respectTransparency false in
theorem reflects_hasRelativePushouts [F.Full] [F.Faithful]
    (objects : Function.Surjective F.obj)
    (mapped : HasRelativePushouts (F.map f) (F.map g)) : HasRelativePushouts f g := by
  intro target left right square
  have mappedSquare : F.map f ≫ F.map left = F.map g ≫ F.map right := by
    rw [← F.map_comp, square, F.map_comp]
  obtain ⟨candidate, universal⟩ := mapped (F.obj target) (F.map left) (F.map right) mappedSquare
  rcases candidate with ⟨candidateApex, candidateInl, candidateInr, candidateDown,
    candidateComm, candidateLeft, candidateRight⟩
  obtain ⟨apex, rfl⟩ := objects candidateApex
  let lifted : Candidate f g left right :=
    { apex := apex
      inl := F.preimage candidateInl
      inr := F.preimage candidateInr
      down := F.preimage candidateDown
      comm := F.map_injective (by simpa only [F.map_comp, F.map_preimage] using candidateComm)
      fac_left := F.map_injective (by simpa only [F.map_comp, F.map_preimage] using candidateLeft)
      fac_right := F.map_injective (by simpa only [F.map_comp, F.map_preimage] using candidateRight) }
  refine ⟨lifted, ?_⟩
  intro other
  obtain ⟨mediator, equations, unique⟩ := universal (mapCandidate F other)
  dsimp only [Candidate.Mediates, mapCandidate] at equations unique ⊢
  refine ⟨F.preimage mediator, ?_, ?_⟩
  · refine ⟨F.map_injective ?_, F.map_injective ?_, F.map_injective ?_⟩
    · simpa only [lifted, F.map_comp, F.map_preimage] using equations.1
    · simpa only [lifted, F.map_comp, F.map_preimage] using equations.2.1
    · simpa only [lifted, F.map_comp, F.map_preimage] using equations.2.2
  · intro alternative laws
    apply F.map_injective
    rw [F.map_preimage]
    apply unique
    exact ⟨by simpa only [lifted, F.map_comp, F.map_preimage] using congrArg F.map laws.1,
      by simpa only [lifted, F.map_comp, F.map_preimage] using congrArg F.map laws.2.1,
      by simpa only [lifted, F.map_comp, F.map_preimage] using congrArg F.map laws.2.2⟩

set_option backward.isDefEq.respectTransparency false in
theorem preserves_idemPushout [F.Full] [F.Faithful]
    (objects : Function.Surjective F.obj) (square : f ≫ h = g ≫ i)
    (universal : IsIdemPushout f g h i square) :
    IsIdemPushout (F.map f) (F.map g) (F.map h) (F.map i)
      (by rw [← F.map_comp, square, F.map_comp]) := by
  intro candidate
  rcases candidate with ⟨candidateApex, candidateInl, candidateInr, candidateDown,
    candidateComm, candidateLeft, candidateRight⟩
  obtain ⟨apex, rfl⟩ := objects candidateApex
  let lifted : Candidate f g h i :=
    { apex := apex
      inl := F.preimage candidateInl
      inr := F.preimage candidateInr
      down := F.preimage candidateDown
      comm := F.map_injective (by simpa only [F.map_comp, F.map_preimage] using candidateComm)
      fac_left := F.map_injective (by simpa only [F.map_comp, F.map_preimage] using candidateLeft)
      fac_right := F.map_injective (by simpa only [F.map_comp, F.map_preimage] using candidateRight) }
  obtain ⟨mediator, equations, unique⟩ := universal lifted
  dsimp only [Candidate.self, Candidate.Mediates] at equations unique ⊢
  refine ⟨F.map mediator, ?_, ?_⟩
  · exact ⟨by simpa only [lifted, F.map_comp, F.map_preimage] using congrArg F.map equations.1,
      by simpa only [lifted, F.map_comp, F.map_preimage] using congrArg F.map equations.2.1,
      by simpa only [lifted, F.map_comp, F.map_preimage, F.map_id] using congrArg F.map equations.2.2⟩
  · intro alternative laws
    have equal : F.preimage alternative = mediator := by
      apply unique
      refine ⟨F.map_injective ?_, F.map_injective ?_, F.map_injective ?_⟩
      · simpa only [lifted, F.map_comp, F.map_preimage] using laws.1
      · simpa only [lifted, F.map_comp, F.map_preimage] using laws.2.1
      · simpa only [lifted, F.map_comp, F.map_preimage, F.map_id] using laws.2.2
    simpa only [F.map_preimage] using congrArg F.map equal

end Mettapedia.GSLT.RelativePushout
