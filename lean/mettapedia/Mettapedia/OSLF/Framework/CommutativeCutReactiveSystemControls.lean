import Mettapedia.OSLF.Framework.CommutativeCutOccurrences

/-!
# Retained payloads, duplicate occurrences and exact least labels

The real Cut equation family admits a binary interaction with an entire Nat
payload. The source contains two identical send occurrences and a spectator;
the result retains one send, the spectator and the supplied acknowledgement.
Different authored origins yield different receipts for the same transition.
An actually enabling label with an extra spectator is not an IPO, and a changed
acknowledgement payload cannot be the supplied complete result.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.CommutativeCut.Controls

open _root_.CategoryTheory
open Mettapedia.GSLT.RelativePushout
open Mettapedia.GSLT.RedexRelativeCongruence

inductive Payload where
  | send (channel : Bool) (value : Nat)
  | receive (channel : Bool)
  | acknowledgement (value : Nat)
  | spectator (identifier : Nat)
  deriving DecidableEq

def authored (origin : Bool) : AuthoredRule Payload Bool where
  origin := origin
  left := .atom (.send false 23)
  right := .atom (.receive false)
  reactum := .atom (.acknowledgement 23)

def admitted (rule : AuthoredRule Payload Bool) : Prop := ∃ origin, rule = authored origin

def source : Term Payload := .cut (.atom (.spectator 7))
  (.cut (.atom (.send false 23)) (.atom (.send false 23)))

def label : Context Payload := .right (.atom (.receive false)) .hole

def reaction : Context Payload := .right
  (.cut (.atom (.send false 23)) (.atom (.spectator 7))) .hole

def target : Term Payload := .cut (.atom (.acknowledgement 23))
  (.cut (.atom (.send false 23)) (.atom (.spectator 7)))

def receipt (origin : Bool) : OccurrenceReceipt admitted source label target where
  rule := authored origin
  allowed := ⟨origin, rfl⟩
  reactionContext := reaction
  square := by
    apply (equation_iff_inventory _ _).mpr
    simp only [source, label, reaction, authored, Context.fill, inventory]
    ac_rfl
  minimal := by
    change ({Payload.receive false} : Multiset Payload) ∩
      ({Payload.send false 23} + {Payload.spectator 7} + 0) = 0
    decide
  targetReadout := Equation.comm (.atom (Payload.acknowledgement 23))
    (.cut (.atom (Payload.send false 23)) (.atom (Payload.spectator 7)))

theorem actual_complete_firing :
    ActIPO (authoredRules admitted) (context (contextClassOf label))
      (closed (classOf source)) (closed (classOf target)) := (receipt false).step

theorem exact_payload_positions (origin : Bool) :
    (receipt origin).rule.left = .atom (.send false 23) ∧
      (receipt origin).rule.right = .atom (.receive false) ∧
      (receipt origin).rule.reactum = .atom (.acknowledgement 23) := ⟨rfl, rfl, rfl⟩

theorem different_origins_same_firing : receipt false ≠ receipt true := by
  intro same
  have origins := congrArg (fun receipt => receipt.rule.origin) same
  cases origins

def firstPosition : SubtermOccurrence source (.atom (.send false 23)) :=
  .right (.atom (Payload.spectator 7))
    (.left (.atom (Payload.send false 23)) (.here (.atom (Payload.send false 23))))

def secondPosition : SubtermOccurrence source (.atom (.send false 23)) :=
  .right (.atom (Payload.spectator 7))
    (.right (.atom (Payload.send false 23)) (.here (.atom (Payload.send false 23))))

def selected (origin choice : Bool) : SelectedFiring admitted source where
  rule := authored origin
  allowed := ⟨origin, rfl⟩
  occurrence := if choice then secondPosition else firstPosition
  minimal := by
    cases choice <;>
      change (({Payload.spectator 7} + ({Payload.send false 23} + 0) : Multiset Payload) ∩
        {Payload.receive false}) = 0 <;> decide

theorem selected_positions_distinct : firstPosition ≠ secondPosition := by
  intro same
  cases same

theorem actual_selected_position_readout (choice : Bool) :
    (selected false choice).occurrence.context.fill (selected false choice).rule.left = source :=
  (selected false choice).occurrence.fill

theorem duplicate_positions_same_complete_result :
    classOf (selected false false).target = classOf (selected false true).target :=
  firstPosition.complete_result_equal secondPosition (.atom (.acknowledgement 23))

theorem duplicate_positions_distinct_raw_receipts :
    (selected false false).receipt.reactionContext ≠ (selected false true).receipt.reactionContext := by
  intro same
  cases same

theorem selected_complete_result (origin choice : Bool) : classOf (selected origin choice).target = classOf target := by
  apply Quotient.sound
  apply (equation_iff_inventory _ _).mpr
  cases choice with
  | false =>
    change ({Payload.spectator 7} + ({Payload.acknowledgement 23} + {Payload.send false 23}) : Multiset Payload) =
      {Payload.acknowledgement 23} + ({Payload.send false 23} + {Payload.spectator 7})
    ac_rfl
  | true =>
    change ({Payload.spectator 7} + ({Payload.send false 23} + {Payload.acknowledgement 23}) : Multiset Payload) =
      {Payload.acknowledgement 23} + ({Payload.send false 23} + {Payload.spectator 7})
    ac_rfl

theorem each_selected_occurrence_really_fires (origin choice : Bool) :
    ActIPO (authoredRules admitted) (context (contextClassOf label))
      (closed (classOf source)) (closed (classOf target)) := by
  rw [← selected_complete_result origin choice]
  exact (selected origin choice).step

theorem complete_occurrence_inventory :
    (inventoryQ (classOf source)).count (.send false 23) = 2 ∧
      (inventoryQ (classOf target)).count (.send false 23) = 1 ∧
      (inventoryQ (classOf target)).count (.acknowledgement 23) = 1 ∧
      (inventoryQ (classOf target)).count (.spectator 7) = 1 := by
  decide

def swappedAndPadded : Term Payload := .cut
  (.cut (.atom (.send false 23)) .zero)
  (.cut (.atom (.send false 23)) (.atom (.spectator 7)))

theorem independent_ac1_class_comparison : source ≠ swappedAndPadded ∧
    classOf source = classOf swappedAndPadded := by
  constructor
  · intro same
    cases same
  · apply Quotient.sound
    apply (equation_iff_inventory _ _).mpr
    simp only [source, swappedAndPadded, inventory]
    ac_rfl

def wasteLabel : Context Payload := .right
  (.cut (.atom (.receive false)) (.atom (.spectator 7))) .hole

def wasteReaction : Context Payload := .right
  (.cut (.atom (.send false 23)) (.cut (.atom (.spectator 7)) (.atom (.spectator 7)))) .hole

theorem enabling_but_not_least :
    ∃ square : closed (classOf source) ≫ context (contextClassOf wasteLabel) =
      (authored false).reaction.redex ≫ context (contextClassOf wasteReaction),
      ¬ IsIdemPushout (closed (classOf source)) (authored false).reaction.redex
        (context (contextClassOf wasteLabel)) (context (contextClassOf wasteReaction)) square := by
  have square : closed (classOf source) ≫ context (contextClassOf wasteLabel) =
      (authored false).reaction.redex ≫ context (contextClassOf wasteReaction) := by
    apply congrArg closed
    apply Quotient.sound
    apply (equation_iff_inventory _ _).mpr
    simp only [source, authored, wasteLabel, wasteReaction, Context.fill, inventory]
    ac_rfl
  refine ⟨square, ?_⟩
  intro least
  have shared := (ipo_iff _ _ _ _ square).mp least
  have impossible : ¬ (({Payload.receive false} + {Payload.spectator 7} + 0 : Multiset Payload) ∩
      ({Payload.send false 23} + ({Payload.spectator 7} + {Payload.spectator 7}) + 0)) = 0 := by decide
  exact impossible shared

def wrongPayload : Term Payload := .cut (.atom (.acknowledgement 24))
  (.cut (.atom (.send false 23)) (.atom (.spectator 7)))

theorem changed_payload_changes_complete_class : classOf target ≠ classOf wrongPayload := by
  intro same
  have counts := congrArg (fun value : Class Payload => (inventoryQ value).count (.acknowledgement 23)) same
  simp [target, wrongPayload, inventoryQ, classOf, inventory] at counts

theorem changed_payload_cannot_fire :
    ¬ ActIPO (authoredRules admitted) (context (contextClassOf label))
      (closed (classOf source)) (closed (classOf wrongPayload)) := by
  rw [firing_iff_occurrence]
  rintro ⟨firing⟩
  obtain ⟨origin, same⟩ := firing.allowed
  have sourceCount := congrArg (Multiset.count (Payload.acknowledgement 24)) firing.square.inventory
  have targetCount := congrArg (Multiset.count (Payload.acknowledgement 24)) firing.targetReadout.inventory
  rw [fill_inventory, fill_inventory] at sourceCount
  rw [fill_inventory] at targetCount
  simp [same, authored, source, label, wrongPayload, contextInventory, inventory] at sourceCount targetCount
  omega

theorem empty_origins_have_no_firing
    (allow : AuthoredRule Payload Empty → Prop) (input output : Class Payload) (probe : ContextClass Payload) :
    ¬ ActIPO (authoredRules allow) (context probe) (closed input) (closed output) := by
  rw [firing_iff_receipt]
  rintro ⟨firing⟩
  exact firing.rule.origin.elim

theorem all_origin_spans_admit_rpos {first second : Category Payload}
    (agent : (.origin : Category Payload) ⟶ first) (redex : (.origin : Category Payload) ⟶ second) :
    HasRelativePushouts agent redex := redex_relativePushouts agent redex

theorem every_actual_context_preserves_bisimulation {first second : Category Payload}
    {left right : (.origin : Category Payload) ⟶ first}
    (related : IPOBisimilar (authoredRules admitted) left right) (frame : first ⟶ second) :
    IPOBisimilar (authoredRules admitted) (left ≫ frame) (right ≫ frame) :=
  bisimulation_congruence (authoredRules admitted) related frame

end Mettapedia.OSLF.CommutativeCut.Controls
