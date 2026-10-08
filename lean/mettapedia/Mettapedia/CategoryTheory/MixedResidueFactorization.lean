import Mettapedia.CategoryTheory.MixedResidueContexts

/-!
# Constructed common outer factors of typed mixed contexts

Common parallel residues are intersected. Equal outer frames extend the
recursion only when their actual typed frame and complete outer residue agree.
The resulting factorization is independent of closed values or action
commutativity. Its greatest-factor theorem accounts for every supplied common
outer context, including an outer parallel context at a fresh vertex.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.MixedResidue

open _root_.CategoryTheory

universe u v w

variable {Vertex : Type u} [Quiver.{v} Vertex] {Payload : Vertex → Type w}
variable [∀ sort, DecidableEq (Payload sort)]

namespace Context

def subtractOuter {source target : Vertex} (residue : Multiset (Payload target)) :
    Context Payload source target → Context Payload source target
  | .parallel previous => .parallel (previous - residue)
  | .frame previous edge inner => .frame (previous - residue) edge inner

theorem addOuter_subtractOuter {source target : Vertex}
    (residue : Multiset (Payload target)) (context : Context Payload source target)
    (bounded : residue ≤ context.outerBag) :
    (context.subtractOuter residue).addOuter residue = context := by
  cases context with
  | parallel previous =>
    exact congrArg parallel ((add_comm _ _).trans (tsub_add_cancel_of_le bounded))
  | frame previous edge inner =>
    exact congrArg (fun bag => frame bag edge inner)
      ((add_comm _ _).trans (tsub_add_cancel_of_le bounded))

end Context

structure Factorization {first second target : Vertex}
    (left : Context Payload first target) (right : Context Payload second target) where
  apex : Vertex
  inl : Context Payload first apex
  inr : Context Payload second apex
  down : Context Payload apex target
  fac_left : inl.comp down = left
  fac_right : inr.comp down = right

namespace Factorization

variable {first second target : Vertex}

def parallel (left : Context Payload first target) (right : Context Payload second target) :
    Factorization left right where
  apex := target
  inl := left.subtractOuter (left.outerBag ∩ right.outerBag)
  inr := right.subtractOuter (left.outerBag ∩ right.outerBag)
  down := .parallel (left.outerBag ∩ right.outerBag)
  fac_left := Context.addOuter_subtractOuter _ _ Multiset.inter_le_left
  fac_right := Context.addOuter_subtractOuter _ _ Multiset.inter_le_right

def extendFrame {middle : Vertex} {left : Context Payload first middle}
    {right : Context Payload second middle} (factor : Factorization left right)
    (residue : Multiset (Payload target)) (edge : middle ⟶ target) :
    Factorization (.frame residue edge left) (.frame residue edge right) where
  apex := factor.apex
  inl := factor.inl
  inr := factor.inr
  down := .frame residue edge factor.down
  fac_left := congrArg (Context.frame residue edge) factor.fac_left
  fac_right := congrArg (Context.frame residue edge) factor.fac_right

end Factorization

variable [∀ target : Vertex, DecidableEq (Σ middle : Vertex, middle ⟶ target)]

def commonFactor {first second target : Vertex}
    (left : Context Payload first target) (right : Context Payload second target) :
    Factorization left right := by
  cases left with
  | parallel residue => exact Factorization.parallel (.parallel residue) right
  | @frame middle _ residue edge inner =>
    cases right with
    | parallel previous => exact Factorization.parallel (.frame residue edge inner) (.parallel previous)
    | @frame otherMiddle _ previous otherEdge otherInner =>
      if sameBag : residue = previous then
        if sameEdge : (⟨middle, edge⟩ : Σ vertex : Vertex, vertex ⟶ target) = ⟨otherMiddle, otherEdge⟩ then
          cases sameBag
          cases sameEdge
          exact (commonFactor inner otherInner).extendFrame residue edge
        else exact Factorization.parallel (.frame residue edge inner) (.frame previous otherEdge otherInner)
      else exact Factorization.parallel (.frame residue edge inner) (.frame previous otherEdge otherInner)
termination_by left.frameCount
decreasing_by
  subst_vars
  simp_all only [Context.frameCount]
  omega

theorem commonFactor_frame {first second middle target : Vertex}
    (left : Context Payload first middle) (right : Context Payload second middle)
    (residue : Multiset (Payload target)) (edge : middle ⟶ target) :
    commonFactor (.frame residue edge left) (.frame residue edge right) =
      (commonFactor left right).extendFrame residue edge := by
  rw [commonFactor.eq_def]
  simp only [dite_true]
  rfl

theorem commonFactor_outerBag {first second target : Vertex}
    (left : Context Payload first target) (right : Context Payload second target) :
    (commonFactor left right).down.outerBag = left.outerBag ∩ right.outerBag := by
  cases left with
  | parallel residue => rw [commonFactor.eq_def]; rfl
  | @frame middle _ residue edge inner =>
    cases right with
    | parallel previous => rw [commonFactor.eq_def]; rfl
    | @frame otherMiddle _ previous otherEdge otherInner =>
      by_cases sameBag : residue = previous
      · cases sameBag
        by_cases sameEdge : (⟨middle, edge⟩ : Σ vertex : Vertex, vertex ⟶ target) =
            ⟨otherMiddle, otherEdge⟩
        · cases sameEdge
          rw [commonFactor_frame]
          change residue = residue ⊓ residue
          exact (inf_idem residue).symm
        · rw [commonFactor.eq_def]
          dsimp only
          rw [dif_pos rfl, dif_neg sameEdge]
          rfl
      · rw [commonFactor.eq_def]
        dsimp only
        rw [dif_neg sameBag]
        rfl

/-- Every supplied common outer context divides the constructed one. -/
theorem commonFactor_greatest_composed {middle target : Vertex}
    (down : Context Payload middle target) {first second : Vertex}
    (left : Context Payload first middle) (right : Context Payload second middle) :
    ∃ mediator : Context Payload (commonFactor (left.comp down) (right.comp down)).apex middle,
      mediator.comp down = (commonFactor (left.comp down) (right.comp down)).down := by
  induction down with
  | parallel residue =>
    have bounded : residue ≤
        (commonFactor (left.addOuter residue) (right.addOuter residue)).down.outerBag := by
      rw [commonFactor_outerBag, Context.outerBag_addOuter, Context.outerBag_addOuter]
      exact Multiset.le_inter
        (Multiset.le_iff_exists_add.mpr ⟨left.outerBag, rfl⟩)
        (Multiset.le_iff_exists_add.mpr ⟨right.outerBag, rfl⟩)
    exact ⟨(commonFactor (left.addOuter residue) (right.addOuter residue)).down.subtractOuter residue,
      Context.addOuter_subtractOuter _ _ bounded⟩
  | frame residue edge down inductionHypothesis =>
    change ∃ mediator : Context Payload
        (commonFactor (.frame residue edge (left.comp down))
          (.frame residue edge (right.comp down))).apex _,
      mediator.comp (.frame residue edge down) =
        (commonFactor (.frame residue edge (left.comp down))
          (.frame residue edge (right.comp down))).down
    rw [commonFactor_frame]
    obtain ⟨mediator, factor⟩ := inductionHypothesis
    exact ⟨mediator, congrArg (Context.frame residue edge) factor⟩

namespace Factorization

variable {first second target : Vertex}
variable {left : Context Payload first target} {right : Context Payload second target}

def Mediates (chosen other : Factorization left right)
    (mediator : Context Payload chosen.apex other.apex) : Prop :=
  chosen.inl.comp mediator = other.inl ∧ chosen.inr.comp mediator = other.inr ∧
    mediator.comp other.down = chosen.down

/-- The greatest common factor earns the complete universal triangle. -/
theorem commonFactor_universal (other : Factorization left right) :
    ∃! mediator : Context Payload (commonFactor left right).apex other.apex,
      Mediates (commonFactor left right) other mediator := by
  have supplied := commonFactor_greatest_composed other.down other.inl other.inr
  rw [other.fac_left, other.fac_right] at supplied
  obtain ⟨mediator, descent⟩ := supplied
  refine ⟨mediator, ⟨?_, ?_, descent⟩, ?_⟩
  · apply Context.comp_cancel_post other.down
    rw [Context.comp_assoc, descent, (commonFactor left right).fac_left, other.fac_left]
  · apply Context.comp_cancel_post other.down
    rw [Context.comp_assoc, descent, (commonFactor left right).fac_right, other.fac_right]
  · intro alternative laws
    exact Context.comp_cancel_post other.down (laws.2.2.trans descent.symm)

end Factorization

end Mettapedia.CategoryTheory.MixedResidue
