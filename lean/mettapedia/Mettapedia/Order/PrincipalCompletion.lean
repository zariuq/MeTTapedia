import Mathlib.SetTheory.Cardinal.Finite

/-!
# Principal completion fibres in preorders

An upper completion fibre is order-theoretic: it consists of the targets above
one source.  This general construction is shared by Bennett's aspects,
constraint systems, and any other ordered presentation.  Its product theorem
is exact because the product order retains the two components separately.

Compatibility or interaction is additional data.  A coupled fibre is a
subtype of the independent product, and is equivalent to the whole product
exactly when every pair is compatible.
-/

set_option autoImplicit false

namespace Mettapedia.Order.PrincipalCompletion

universe uLeft uRight uLeft' uRight'

/-- The informative family of targets above `source`. -/
abbrev Fibre {α : Type uLeft} [LE α] (source : α) : Type uLeft :=
  {target : α // source ≤ target}

namespace Fibre

variable {α : Type uLeft} [Preorder α]

/-- Forget the completion witness while retaining its target. -/
def target {source : α} (completion : Fibre source) : α :=
  completion.1

/-- Raising the source embeds its smaller completion fibre in the completion
fibre of the weaker source. -/
def contravariantEmbedding {left right : α} (refines : left ≤ right) :
    Fibre right ↪ Fibre left where
  toFun completion := ⟨completion.1, refines.trans completion.2⟩
  inj' := by
    intro first second equal
    apply Subtype.ext
    exact congrArg (fun completion : Fibre left => completion.1) equal

/-- Exact changes of ordered presentation transport principal fibres. -/
def congr {β : Type uRight} [Preorder β]
    (presentation : α ≃o β) (source : α) :
    Fibre source ≃ Fibre (presentation source) where
  toFun completion :=
    ⟨presentation completion.1, presentation.monotone completion.2⟩
  invFun completion :=
    ⟨presentation.symm completion.1, by
      simpa using presentation.symm.monotone completion.2⟩
  left_inv completion := Subtype.ext (presentation.symm_apply_apply completion.1)
  right_inv completion := Subtype.ext (presentation.apply_symm_apply completion.1)

end Fibre

/-! ## Independent products -/

variable {Left : Type uLeft} {Right : Type uRight}
  [Preorder Left] [Preorder Right]

/-- A completion of a pair is exactly a pair of component completions. -/
def productEquiv (left : Left) (right : Right) :
    Fibre (left, right) ≃ Fibre left × Fibre right where
  toFun completion :=
    (⟨completion.1.1, completion.2.1⟩,
      ⟨completion.1.2, completion.2.2⟩)
  invFun completion :=
    ⟨(completion.1.1, completion.2.1),
      ⟨completion.1.2, completion.2.2⟩⟩
  left_inv completion := by
    apply Subtype.ext
    rfl
  right_inv completion := rfl

/-- Cardinal completion variety multiplies under the independent product. -/
theorem mk_productFibre (left : Left) (right : Right) :
    Cardinal.mk (Fibre (left, right)) =
      Cardinal.lift.{uRight} (Cardinal.mk (Fibre left)) *
        Cardinal.lift.{uLeft} (Cardinal.mk (Fibre right)) := by
  rw [Cardinal.mk_congr (productEquiv left right), Cardinal.mk_prod]

/-- The same product law after the finite natural-cardinality readout. -/
theorem natCard_productFibre (left : Left) (right : Right) :
    Nat.card (Fibre (left, right)) =
      Nat.card (Fibre left) * Nat.card (Fibre right) := by
  rw [Nat.card_congr (productEquiv left right), Nat.card_prod]

/-! ## Compatibility-indexed interaction -/

/-- Completions retained by an explicit compatibility relation. -/
abbrev CoupledFibre (left : Left) (right : Right)
    (Compatible : Fibre left → Fibre right → Prop) :=
  {completion : Fibre left × Fibre right //
    Compatible completion.1 completion.2}

/-- Every coupled completion embeds in the independent product completion
fibre.  Surjectivity is not claimed. -/
def coupledEmbedding (left : Left) (right : Right)
    (Compatible : Fibre left → Fibre right → Prop) :
    CoupledFibre left right Compatible ↪ Fibre (left, right) :=
  (Function.Embedding.subtype _).trans
    (productEquiv left right).symm.toEmbedding

/-- If compatibility accepts every pair, coupling recovers the independent
product exactly. -/
def coupledEquivProduct (left : Left) (right : Right)
    (Compatible : Fibre left → Fibre right → Prop)
    (total : ∀ leftCompletion rightCompletion,
      Compatible leftCompletion rightCompletion) :
    CoupledFibre left right Compatible ≃ Fibre (left, right) where
  toFun completion := (productEquiv left right).symm completion.1
  invFun completion :=
    let pair := productEquiv left right completion
    ⟨pair, total pair.1 pair.2⟩
  left_inv completion := by
    apply Subtype.ext
    exact (productEquiv left right).apply_symm_apply completion.1
  right_inv completion :=
    (productEquiv left right).symm_apply_apply completion

/-! ## A strict coupling control -/

namespace CouplingCanary

/-- Boolean `false` has both Boolean targets as order completions. -/
def falseCompletion : Fibre false := ⟨false, le_rfl⟩

def trueCompletion : Fibre false := ⟨true, by decide⟩

/-- Only component completions ending at the same Boolean target are
compatible. -/
def SameTarget (left right : Fibre false) : Prop :=
  left.1 = right.1

/-- The mixed pair is a genuine product completion. -/
def mixedProductCompletion : Fibre (false, false) :=
  (productEquiv false false).symm (falseCompletion, trueCompletion)

/-- The strict compatibility fibre cannot publish the mixed independent
completion. -/
theorem mixedProductCompletion_not_in_coupled_range :
    mixedProductCompletion ∉ Set.range
      (coupledEmbedding false false SameTarget) := by
  rintro ⟨coupled, equal⟩
  have pairEqual := congrArg (productEquiv false false) equal
  have leftEqual : coupled.1.1 = falseCompletion :=
    congrArg Prod.fst pairEqual
  have rightEqual : coupled.1.2 = trueCompletion :=
    congrArg Prod.snd pairEqual
  have same : falseCompletion.1 = trueCompletion.1 := by
    have sameTarget : coupled.1.1.1 = coupled.1.2.1 := coupled.2
    rw [leftEqual, rightEqual] at sameTarget
    exact sameTarget
  exact Bool.false_ne_true same

/-- Therefore compatibility-indexed interaction can be strictly smaller than
the independent product. -/
theorem coupledEmbedding_not_surjective :
    ¬ Function.Surjective (coupledEmbedding false false SameTarget) := by
  intro surjective
  exact mixedProductCompletion_not_in_coupled_range
    (surjective mixedProductCompletion)

end CouplingCanary

end Mettapedia.Order.PrincipalCompletion

#print axioms Mettapedia.Order.PrincipalCompletion.productEquiv
#print axioms Mettapedia.Order.PrincipalCompletion.mk_productFibre
#print axioms Mettapedia.Order.PrincipalCompletion.CouplingCanary.coupledEmbedding_not_surjective
