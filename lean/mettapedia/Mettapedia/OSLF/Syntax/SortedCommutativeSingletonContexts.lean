import Mettapedia.OSLF.Syntax.SortedCommutativeContextCategory

/-!
# Complete contexts producing one constructor head

A nonempty supplied inventory remains nonempty under every actual context.
If the result has one head, every outer parallel sibling must therefore be
the unit class. Stripping those siblings by the generated local equations
leaves either the actual context identity or a complete outer constructor
frame, retaining its selected position, all siblings and inner context.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.SortedCommutative

universe u v

variable {signature : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
variable {Parallel : signature.Srt → Prop}

theorem RawContext.inventory_fill_ne_zero {source target : signature.Srt}
    (supplied : Term signature Parallel source) (nonempty : inventory supplied ≠ 0)
    (context : RawContext signature Parallel source target) : inventory (context.fill supplied) ≠ 0 := by
  apply @RawContext.rec signature Parallel source
    (fun _ context => inventory (context.fill supplied) ≠ 0) (t := context)
  · exact nonempty
  · intro _constructor _position _siblings _inner _inductionHypothesis
    exact Multiset.singleton_ne_zero _
  · intro _target _parallel inner sibling inductionHypothesis empty
    have counts := congrArg Multiset.card empty
    change (inventory (inner.fill supplied) + inventory sibling).card = 0 at counts
    rw [Multiset.card_add] at counts
    exact inductionHypothesis (Multiset.card_eq_zero.mp (by omega))
  · intro _target _parallel sibling inner inductionHypothesis empty
    have counts := congrArg Multiset.card empty
    change (inventory sibling + inventory (inner.fill supplied)).card = 0 at counts
    rw [Multiset.card_add] at counts
    exact inductionHypothesis (Multiset.card_eq_zero.mp (by omega))

theorem RawContext.singleton_inventory_frame_or_identity {source target : signature.Srt}
    (supplied : Term signature Parallel source) (nonempty : inventory supplied ≠ 0)
    (context : RawContext signature Parallel source target) :
    ∀ head : Head (signature := signature) (Parallel := Parallel) target,
      inventory (context.fill supplied) = {head} →
        (target = source ∧ HEq (contextClassOf context)
          (ContextClass.identity (signature := signature) (Parallel := Parallel) source)) ∨
        ∃ constructor, ∃ position : Fin (signature.arity constructor),
          ∃ siblings : (other : Fin (signature.arity constructor)) → other ≠ position →
            Term signature Parallel (signature.input constructor other),
          ∃ inner : RawContext signature Parallel source (signature.input constructor position),
          ∃ _outputRead : signature.output constructor = target,
            HEq (contextClassOf (RawContext.frame constructor position siblings inner))
              (contextClassOf context) := by
  apply @RawContext.rec signature Parallel source
    (fun target context => ∀ head : Head (signature := signature) (Parallel := Parallel) target,
      inventory (context.fill supplied) = {head} →
        (target = source ∧ HEq (contextClassOf context)
          (ContextClass.identity (signature := signature) (Parallel := Parallel) source)) ∨
        ∃ constructor, ∃ position : Fin (signature.arity constructor),
          ∃ siblings : (other : Fin (signature.arity constructor)) → other ≠ position →
            Term signature Parallel (signature.input constructor other),
          ∃ inner : RawContext signature Parallel source (signature.input constructor position),
          ∃ _outputRead : signature.output constructor = target,
            HEq (contextClassOf (RawContext.frame constructor position siblings inner))
              (contextClassOf context)) (t := context)
  · intro _head _read
    exact Or.inl ⟨rfl, HEq.rfl⟩
  · intro constructor position siblings inner _inductionHypothesis _head _read
    exact Or.inr ⟨constructor, position, siblings, inner, rfl, HEq.rfl⟩
  · intro target parallel inner sibling inductionHypothesis head read
    change inventory (inner.fill supplied) + inventory sibling = {head} at read
    have present := inner.inventory_fill_ne_zero supplied nonempty
    have positive : 0 < (inventory (inner.fill supplied)).card :=
      Nat.pos_of_ne_zero (fun empty => present (Multiset.card_eq_zero.mp empty))
    have counts := congrArg Multiset.card read
    rw [Multiset.card_add, Multiset.card_singleton] at counts
    have siblingEmpty : inventory sibling = 0 := Multiset.card_eq_zero.mp (by omega)
    have siblingRead : classOf sibling = classOf (.zero parallel) := inventoryQ_injective siblingEmpty
    have stripped : contextClassOf (.left parallel inner sibling) = contextClassOf inner :=
      Quotient.sound ((ContextEquation.left parallel (ContextEquation.refl inner)
        (Quotient.exact siblingRead)).trans (ContextEquation.unit parallel inner))
    have innerRead : inventory (inner.fill supplied) = {head} := by
      simpa only [siblingEmpty, add_zero] using read
    rcases inductionHypothesis head innerRead with ⟨same, identityRead⟩ | frame
    · exact Or.inl ⟨same, (heq_of_eq stripped).trans identityRead⟩
    · obtain ⟨constructor, position, siblings, inside, outputRead, frameRead⟩ := frame
      exact Or.inr ⟨constructor, position, siblings, inside, outputRead,
        frameRead.trans (heq_of_eq stripped.symm)⟩
  · intro target parallel sibling inner inductionHypothesis head read
    change inventory sibling + inventory (inner.fill supplied) = {head} at read
    have present := inner.inventory_fill_ne_zero supplied nonempty
    have positive : 0 < (inventory (inner.fill supplied)).card :=
      Nat.pos_of_ne_zero (fun empty => present (Multiset.card_eq_zero.mp empty))
    have counts := congrArg Multiset.card read
    rw [Multiset.card_add, Multiset.card_singleton] at counts
    have siblingEmpty : inventory sibling = 0 := Multiset.card_eq_zero.mp (by omega)
    have siblingRead : classOf sibling = classOf (.zero parallel) := inventoryQ_injective siblingEmpty
    have stripped : contextClassOf (.right parallel sibling inner) = contextClassOf inner :=
      Quotient.sound ((ContextEquation.right parallel (Quotient.exact siblingRead)
        (ContextEquation.refl inner)).trans
          ((ContextEquation.comm parallel inner (.zero parallel)).symm.trans
            (ContextEquation.unit parallel inner)))
    have innerRead : inventory (inner.fill supplied) = {head} := by
      simpa only [siblingEmpty, zero_add] using read
    rcases inductionHypothesis head innerRead with ⟨same, identityRead⟩ | frame
    · exact Or.inl ⟨same, (heq_of_eq stripped).trans identityRead⟩
    · obtain ⟨constructor, position, siblings, inside, outputRead, frameRead⟩ := frame
      exact Or.inr ⟨constructor, position, siblings, inside, outputRead,
        frameRead.trans (heq_of_eq stripped.symm)⟩

end Mettapedia.OSLF.SortedCommutative
