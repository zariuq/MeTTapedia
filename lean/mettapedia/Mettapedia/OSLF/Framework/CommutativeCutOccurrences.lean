import Mettapedia.OSLF.Framework.CommutativeCutReactiveSystem

/-!
# Selected raw positions and their actual minimal interaction firings

A supplied constructor occurrence locates the left redex component in the
original source tree. Its one-hole context and literal filling equation are
constructed recursively. An independently admitted rule and disjointness of
the supplied right component earn the whole AC1 firing receipt. Distinct
positions remain receipt data even when AC1 identifies their contexts and
complete result classes. This selector covers actual subtrees; arbitrary
AC1 rearrangements still use the more general equation-bearing receipt.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.CommutativeCut

universe u w

variable {Payload : Type u}

inductive SubtermOccurrence : Term Payload → Term Payload → Type u where
  | here (term) : SubtermOccurrence term term
  | left {whole selected} (sibling) : SubtermOccurrence whole selected →
      SubtermOccurrence (.cut whole sibling) selected
  | right {whole selected} (sibling) : SubtermOccurrence whole selected →
      SubtermOccurrence (.cut sibling whole) selected

def SubtermOccurrence.context {whole selected : Term Payload} :
    SubtermOccurrence whole selected → Context Payload
  | .here _ => .hole
  | .left sibling occurrence => .left occurrence.context sibling
  | .right sibling occurrence => .right sibling occurrence.context

theorem SubtermOccurrence.fill {whole selected : Term Payload}
    (occurrence : SubtermOccurrence whole selected) : occurrence.context.fill selected = whole := by
  induction occurrence with
  | here => rfl
  | left sibling occurrence inductionHypothesis =>
    exact congrArg (fun value => Term.cut value sibling) inductionHypothesis
  | right sibling occurrence inductionHypothesis =>
    exact congrArg (Term.cut sibling) inductionHypothesis

theorem SubtermOccurrence.inventory {whole selected : Term Payload}
    (occurrence : SubtermOccurrence whole selected) :
    inventory whole = inventory selected + contextInventory occurrence.context := by
  exact (congrArg CommutativeCut.inventory occurrence.fill).symm.trans
    (fill_inventory occurrence.context selected)

theorem SubtermOccurrence.context_class_equal {whole selected : Term Payload}
    (first second : SubtermOccurrence whole selected) :
    contextClassOf first.context = contextClassOf second.context := by
  apply contextInventoryEquiv.injective
  change contextInventory first.context = contextInventory second.context
  exact add_left_cancel (first.inventory.symm.trans second.inventory)

theorem SubtermOccurrence.complete_result_equal {whole selected : Term Payload}
    (first second : SubtermOccurrence whole selected) (supplied : Term Payload) :
    classOf (first.context.fill supplied) = classOf (second.context.fill supplied) := by
  apply Quotient.sound
  apply (equation_iff_inventory _ _).mpr
  rw [fill_inventory, fill_inventory]
  exact congrArg (fun value => CommutativeCut.inventory supplied + value)
    (congrArg contextInventoryQ (first.context_class_equal second))

variable [DecidableEq Payload] {Origins : Type w}

structure SelectedFiring (admitted : AuthoredRule Payload Origins → Prop)
    (source : Term Payload) where
  rule : AuthoredRule Payload Origins
  allowed : admitted rule
  occurrence : SubtermOccurrence source rule.left
  minimal : contextInventory occurrence.context ∩ inventory rule.right = 0

def SelectedFiring.label {admitted : AuthoredRule Payload Origins → Prop}
    {source : Term Payload} (selected : SelectedFiring admitted source) : Context Payload :=
  .right selected.rule.right .hole

def SelectedFiring.target {admitted : AuthoredRule Payload Origins → Prop}
    {source : Term Payload} (selected : SelectedFiring admitted source) : Term Payload :=
  selected.occurrence.context.fill selected.rule.reactum

def SelectedFiring.receipt {admitted : AuthoredRule Payload Origins → Prop}
    {source : Term Payload} (selected : SelectedFiring admitted source) :
    OccurrenceReceipt admitted source selected.label selected.target where
  rule := selected.rule
  allowed := selected.allowed
  reactionContext := selected.occurrence.context
  square := by
    apply (equation_iff_inventory _ _).mpr
    change inventory selected.rule.right + inventory source =
      inventory (selected.occurrence.context.fill (.cut selected.rule.left selected.rule.right))
    rw [selected.occurrence.inventory, fill_inventory, inventory]
    ac_rfl
  minimal := by
    change (inventory selected.rule.right + 0) ∩ contextInventory selected.occurrence.context = 0
    rw [add_zero, Multiset.inter_comm]
    exact selected.minimal
  targetReadout := Equation.refl _

theorem SelectedFiring.step {admitted : AuthoredRule Payload Origins → Prop}
    {source : Term Payload} (selected : SelectedFiring admitted source) :
    Mettapedia.GSLT.RedexRelativeCongruence.ActIPO (authoredRules admitted)
      (context (contextClassOf selected.label)) (closed (classOf source))
      (closed (classOf selected.target)) := selected.receipt.step

end Mettapedia.OSLF.CommutativeCut
