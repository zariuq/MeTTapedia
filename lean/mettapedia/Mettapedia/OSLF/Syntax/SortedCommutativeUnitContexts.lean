import Mettapedia.OSLF.Syntax.SortedCommutativeContextCategory

/-!
# Unit-preserving AC1 contexts are actual identity classes

This is a property of the independently generated free-constructor/AC1
context equations. A constructor frame produces a nonempty head inventory;
a parallel residue can preserve the unit only when that whole residue is
the unit class. Recursive local equations then identify the complete context
with the hole. No faithful ground-action hypothesis is used.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.SortedCommutative

universe u v

variable {signature : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
variable {Parallel : signature.Srt → Prop}

private theorem raw_unit_filling_identity {source target : signature.Srt}
    (sourceParallel : Parallel source) (context : RawContext signature Parallel source target) :
    ∀ targetParallel : Parallel target,
      classOf (context.fill (.zero sourceParallel)) = classOf (.zero targetParallel) →
        target = source ∧ HEq (contextClassOf context)
          (ContextClass.identity (signature := signature) (Parallel := Parallel) source) := by
  apply @RawContext.rec signature Parallel source
    (fun target context => ∀ targetParallel : Parallel target,
      classOf (context.fill (.zero sourceParallel)) = classOf (.zero targetParallel) →
        target = source ∧ HEq (contextClassOf context)
          (ContextClass.identity (signature := signature) (Parallel := Parallel) source)) (t := context)
  · intro _parallel _read
    exact ⟨rfl, HEq.rfl⟩
  · intro constructor position siblings inner _inductionHypothesis targetParallel read
    have inventories := congrArg inventoryQ read
    have counts := congrArg Multiset.card inventories
    change 1 = 0 at counts
    cases counts
  · intro target parallel inner sibling inductionHypothesis targetParallel read
    have inventories := congrArg inventoryQ read
    change inventory (inner.fill (.zero sourceParallel)) + inventory sibling = 0 at inventories
    have counts := congrArg Multiset.card inventories
    rw [Multiset.card_add, Multiset.card_zero] at counts
    have innerEmpty : inventory (inner.fill (.zero sourceParallel)) = 0 :=
      Multiset.card_eq_zero.mp (by omega)
    have siblingEmpty : inventory sibling = 0 := Multiset.card_eq_zero.mp (by omega)
    have innerRead : classOf (inner.fill (.zero sourceParallel)) = classOf (.zero parallel) :=
      inventoryQ_injective innerEmpty
    have siblingRead : classOf sibling = classOf (.zero parallel) := inventoryQ_injective siblingEmpty
    obtain ⟨same, contextRead⟩ := inductionHypothesis parallel innerRead
    subst target
    have equation : ContextEquation (.left parallel inner sibling)
        (.hole : RawContext signature Parallel source source) :=
      (ContextEquation.left parallel (Quotient.exact (eq_of_heq contextRead)) (Quotient.exact siblingRead)).trans
        (ContextEquation.unit parallel .hole)
    exact ⟨rfl, heq_of_eq (Quotient.sound equation)⟩
  · intro target parallel sibling inner inductionHypothesis targetParallel read
    have inventories := congrArg inventoryQ read
    change inventory sibling + inventory (inner.fill (.zero sourceParallel)) = 0 at inventories
    have counts := congrArg Multiset.card inventories
    rw [Multiset.card_add, Multiset.card_zero] at counts
    have innerEmpty : inventory (inner.fill (.zero sourceParallel)) = 0 :=
      Multiset.card_eq_zero.mp (by omega)
    have siblingEmpty : inventory sibling = 0 := Multiset.card_eq_zero.mp (by omega)
    have innerRead : classOf (inner.fill (.zero sourceParallel)) = classOf (.zero parallel) :=
      inventoryQ_injective innerEmpty
    have siblingRead : classOf sibling = classOf (.zero parallel) := inventoryQ_injective siblingEmpty
    obtain ⟨same, contextRead⟩ := inductionHypothesis parallel innerRead
    subst target
    have equation : ContextEquation (.right parallel sibling inner)
        (.hole : RawContext signature Parallel source source) :=
      (ContextEquation.right parallel (Quotient.exact siblingRead) (Quotient.exact (eq_of_heq contextRead))).trans
        ((ContextEquation.comm parallel .hole (.zero parallel)).symm.trans (ContextEquation.unit parallel .hole))
    exact ⟨rfl, heq_of_eq (Quotient.sound equation)⟩

theorem ContextClass.fill_unit_iff_identity {sort : signature.Srt} (parallel : Parallel sort)
    (context : ContextClass signature Parallel sort sort) :
    context.fill (classOf (.zero parallel)) = classOf (.zero parallel) ↔ context = ContextClass.identity sort := by
  constructor
  · revert context
    intro context
    refine Quotient.inductionOn context ?_
    intro raw read
    exact eq_of_heq (raw_unit_filling_identity parallel raw parallel read).2
  · intro same
    subst context
    exact ContextClass.fill_identity _

end Mettapedia.OSLF.SortedCommutative
