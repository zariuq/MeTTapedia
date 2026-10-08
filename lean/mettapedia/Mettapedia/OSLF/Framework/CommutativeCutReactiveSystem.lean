import Mettapedia.OSLF.Syntax.CommutativeCutContexts
import Mettapedia.CategoryTheory.GroundMultisetRelativePushout
import Mettapedia.GSLT.Logic.RelativePushoutFunctor

/-!
# Actual AC1 context comparison and retained interaction firings

The independently generated term/context quotients have a full, faithful,
object-surjective comparison with the grounded multiset category. Its earned
RPOs discharge Condition 20.1 for this closed first-order parallel grammar.
The complete IPO criterion earns congruence at every actual context for
literal context labels. Higher-order payload-label matching is separate.
Authored rules retain origins, both
binary redex operands and their entire reactum. Supplied occurrence receipts
add raw context representatives and actual equation proofs, independently of
the existential transition predicate.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.CommutativeCut

open _root_.CategoryTheory
open Mettapedia.CategoryTheory.GroundMonoidAction
open Mettapedia.GSLT.RelativePushout
open Mettapedia.GSLT.RedexRelativeCongruence

universe u w

variable {Payload : Type u}

def contextInventoryHom : ContextClass Payload →* Multiplicative (Multiset Payload) where
  toFun context := Multiplicative.ofAdd (contextInventoryQ context)
  map_one' := rfl
  map_mul' outer inner := congrArg Multiplicative.ofAdd (contextInventoryQ_mul outer inner)

def normalization : Category Payload ⥤ Mettapedia.CategoryTheory.GroundMultiset.Category Payload :=
  Mettapedia.CategoryTheory.GroundMonoidAction.map contextInventoryHom inventoryQ
    (fun context value => (action_inventory context value).trans (add_comm _ _))

instance normalization_faithful : (normalization (Payload := Payload)).Faithful :=
  map_faithful contextInventoryHom inventoryQ _
    (fun _ _ same => contextInventoryEquiv.injective (congrArg Multiplicative.toAdd same))
    inventoryEquiv.injective

instance normalization_full : (normalization (Payload := Payload)).Full := by
  apply map_full
  · intro supplied
    obtain ⟨context, same⟩ := contextInventoryEquiv.surjective supplied.toAdd
    exact ⟨context, congrArg Multiplicative.ofAdd same⟩
  · exact inventoryEquiv.surjective

theorem normalization_objects : Function.Surjective (normalization (Payload := Payload)).obj :=
  map_objects_surjective contextInventoryHom inventoryQ _

def closed (value : Class Payload) : (.origin : Category Payload) ⟶ .interface := valueArrow value

def context (value : ContextClass Payload) : (.interface : Category Payload) ⟶ .interface := contextArrow value

@[simp] theorem normalization_closed (value : Class Payload) :
    normalization.map (closed value) = Mettapedia.CategoryTheory.GroundMultiset.closed (inventoryQ value) := rfl

@[simp] theorem normalization_context (value : ContextClass Payload) :
    normalization.map (context value) = Mettapedia.CategoryTheory.GroundMultiset.parallel (contextInventoryQ value) := rfl

variable [DecidableEq Payload]

/-- Every origin-based redex span, at both actual interfaces, has an RPO.
The property is derived from the constructed hom comparison, not supplied. -/
theorem redex_relativePushouts {first second : Category Payload}
    (agent : (.origin : Category Payload) ⟶ first) (redex : (.origin : Category Payload) ⟶ second) :
    HasRelativePushouts agent redex :=
  reflects_hasRelativePushouts normalization normalization_objects
    (Mettapedia.CategoryTheory.GroundMultiset.redex_relativePushouts
      (normalization.map agent) (normalization.map redex))

theorem ipo_iff (source redex : Class Payload) (label reaction : ContextClass Payload)
    (square : closed source ≫ context label = closed redex ≫ context reaction) :
    IsIdemPushout (closed source) (closed redex) (context label) (context reaction) square ↔
      contextInventoryQ label ∩ contextInventoryQ reaction = 0 := by
  have mappedSquare : Mettapedia.CategoryTheory.GroundMultiset.closed (inventoryQ source) ≫
      Mettapedia.CategoryTheory.GroundMultiset.parallel (contextInventoryQ label) =
      Mettapedia.CategoryTheory.GroundMultiset.closed (inventoryQ redex) ≫
      Mettapedia.CategoryTheory.GroundMultiset.parallel (contextInventoryQ reaction) := by
    rw [Mettapedia.CategoryTheory.GroundMultiset.closed_parallel,
      Mettapedia.CategoryTheory.GroundMultiset.closed_parallel]
    have values : label • source = reaction • redex := Arrow.value.inj square
    exact congrArg Mettapedia.CategoryTheory.GroundMultiset.closed
      (by simpa only [action_inventory] using congrArg inventoryQ values)
  constructor
  · intro least
    have mapped := preserves_idemPushout normalization normalization_objects square least
    exact (Mettapedia.CategoryTheory.GroundMultiset.closed_ipo_iff _ _ _ _ mappedSquare).mp mapped
  · intro disjoint
    apply reflects_idemPushout normalization square
    exact (Mettapedia.CategoryTheory.GroundMultiset.closed_ipo_iff _ _ _ _ mappedSquare).mpr disjoint

theorem bisimulation_congruence (rules : ReactionRule (.origin : Category Payload) → Prop)
    {source target : Category Payload}
    {left right : (.origin : Category Payload) ⟶ source}
    (related : IPOBisimilar rules left right) (suppliedContext : source ⟶ target) :
    IPOBisimilar rules (left ≫ suppliedContext) (right ≫ suppliedContext) :=
  ipoBisimilar_comp (fun _ agent rule _ => redex_relativePushouts agent rule.redex) related suppliedContext

omit [DecidableEq Payload] in
structure AuthoredRule (Payload : Type u) (Origins : Type w) where
  origin : Origins
  left : Term Payload
  right : Term Payload
  reactum : Term Payload

variable {Origins : Type w}

def AuthoredRule.reaction (rule : AuthoredRule Payload Origins) : ReactionRule (.origin : Category Payload) where
  codomain := .interface
  redex := closed (classOf (.cut rule.left rule.right))
  reactum := closed (classOf rule.reactum)

def authoredRules (admitted : AuthoredRule Payload Origins → Prop) : ReactionRule (.origin : Category Payload) → Prop :=
  fun reaction => ∃ rule, admitted rule ∧ rule.reaction = reaction

structure FiringReceipt (admitted : AuthoredRule Payload Origins → Prop)
    (source : Class Payload) (label : ContextClass Payload) (target : Class Payload) where
  rule : AuthoredRule Payload Origins
  allowed : admitted rule
  reactionContext : ContextClass Payload
  square : label • source = reactionContext • classOf (.cut rule.left rule.right)
  minimal : contextInventoryQ label ∩ contextInventoryQ reactionContext = 0
  targetReadout : target = reactionContext • classOf rule.reactum

theorem FiringReceipt.step {admitted : AuthoredRule Payload Origins → Prop}
    {source : Class Payload} {label : ContextClass Payload} {target : Class Payload}
    (receipt : FiringReceipt admitted source label target) :
    ActIPO (authoredRules admitted) (context label) (closed source) (closed target) := by
  have square : closed source ≫ context label = receipt.rule.reaction.redex ≫ context receipt.reactionContext :=
    congrArg closed receipt.square
  refine ⟨receipt.rule.reaction, ⟨receipt.rule, receipt.allowed, rfl⟩,
    context receipt.reactionContext, square, (ipo_iff _ _ _ _ square).mpr receipt.minimal, ?_⟩
  exact congrArg closed receipt.targetReadout

theorem firing_iff_receipt (admitted : AuthoredRule Payload Origins → Prop)
    (source : Class Payload) (label : ContextClass Payload) (target : Class Payload) :
    ActIPO (authoredRules admitted) (context label) (closed source) (closed target) ↔
      Nonempty (FiringReceipt admitted source label target) := by
  constructor
  · rintro ⟨_, ⟨rule, allowed, rfl⟩, reactionContext, square, least, targetReadout⟩
    cases reactionContext with
    | context reactionContext =>
      refine ⟨⟨rule, allowed, reactionContext, Arrow.value.inj square,
        (ipo_iff _ _ _ _ square).mp least, Arrow.value.inj targetReadout⟩⟩
  · rintro ⟨receipt⟩
    exact receipt.step

/-- Supplied raw representatives and rule origins remain independent data.
AC1 may identify two placements; it does not identify these receipt fields. -/
structure OccurrenceReceipt (admitted : AuthoredRule Payload Origins → Prop)
    (source : Term Payload) (label : Context Payload) (target : Term Payload) where
  rule : AuthoredRule Payload Origins
  allowed : admitted rule
  reactionContext : Context Payload
  square : Equation (label.fill source) (reactionContext.fill (.cut rule.left rule.right))
  minimal : contextInventory label ∩ contextInventory reactionContext = 0
  targetReadout : Equation target (reactionContext.fill rule.reactum)

def OccurrenceReceipt.semantic {admitted : AuthoredRule Payload Origins → Prop}
    {source : Term Payload} {label : Context Payload} {target : Term Payload}
    (receipt : OccurrenceReceipt admitted source label target) :
    FiringReceipt admitted (classOf source) (contextClassOf label) (classOf target) where
  rule := receipt.rule
  allowed := receipt.allowed
  reactionContext := contextClassOf receipt.reactionContext
  square := Quotient.sound receipt.square
  minimal := receipt.minimal
  targetReadout := Quotient.sound receipt.targetReadout

theorem OccurrenceReceipt.step {admitted : AuthoredRule Payload Origins → Prop}
    {source : Term Payload} {label : Context Payload} {target : Term Payload}
    (receipt : OccurrenceReceipt admitted source label target) :
    ActIPO (authoredRules admitted) (context (contextClassOf label)) (closed (classOf source)) (closed (classOf target)) :=
  receipt.semantic.step

theorem firing_iff_occurrence (admitted : AuthoredRule Payload Origins → Prop)
    (source : Term Payload) (label : Context Payload) (target : Term Payload) :
    ActIPO (authoredRules admitted) (context (contextClassOf label)) (closed (classOf source)) (closed (classOf target)) ↔
      Nonempty (OccurrenceReceipt admitted source label target) := by
  rw [firing_iff_receipt]
  constructor
  · rintro ⟨receipt⟩
    obtain ⟨reactionContext, same⟩ := Quotient.exists_rep receipt.reactionContext
    refine ⟨⟨receipt.rule, receipt.allowed, reactionContext, ?_, ?_, ?_⟩⟩
    · have square := receipt.square
      rw [← same] at square
      exact Quotient.exact square
    · have minimal := receipt.minimal
      rw [← same] at minimal
      exact minimal
    · have output := receipt.targetReadout
      rw [← same] at output
      exact Quotient.exact output
  · rintro ⟨receipt⟩
    exact ⟨receipt.semantic⟩

end Mettapedia.OSLF.CommutativeCut
