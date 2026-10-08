import Mettapedia.OSLF.Framework.SortedTypedInstrumentKitMonotonicity
import Mettapedia.OSLF.Framework.SortedTypedInstrumentKitFiringComparison
import Mettapedia.OSLF.Framework.SortedTypedInstrumentKitControls
import Mettapedia.OSLF.Framework.SortedTypedInstrumentProbeControls
import Mettapedia.OSLF.Framework.SortedTypedInstrumentUnitReactionCompetition

/-!
# Actual typed kit expansion, future separation and unit competition

The send kit retains its whole heterogeneous bundle and authored origins
under expansion and unique receipt reconstruction. An unopened kit with no
authored rules has no actual firings; opening send strictly separates a send
process from the unit through its genuine ask IPO. The independent binary
unit rule still supplies a competing get result with the complete assay.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstrumentKitTransitionControls

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RelativePushout Mettapedia.GSLT.RedexRelativeCongruence
open SortedTypedInstruments SortedTypedInstrumentControls

abbrev sendHead : SourceHead sourceSignature sourceParallel := .ordinary Symbol.send
abbrev oldKit := SortedTypedInstrumentKitControls.sendKit
abbrev emptyKit := SortedTypedInstrumentKitControls.closedKit

def allKit : Kit.Policy sourceSignature sourceParallel := fun head => head = head
theorem opensAll : ∀ head, oldKit head → allKit head := fun _head _permission => rfl
theorem opensSend : ∀ head, emptyKit head → oldKit head := SortedTypedInstrumentKitControls.opensSend

def noOriginalRules : Empty → ReactionRule (.origin : SourceCategory sourceSignature sourceParallel) := Empty.elim

def arguments : Arguments sendHead := sendArguments 7 (sourcePayload 9)

theorem arguments_supported (opened : Kit.Policy sourceSignature sourceParallel) :
    ∀ position, Kit.Supported opened (arguments position) := by
  intro position
  fin_cases position
  · exact Kit.embed_supported opened (sourceName 7)
  · exact Kit.embed_supported opened (sourcePayload 9)

theorem send_permitted (origin : Nat) :
    Kit.Permitted oldKit (sendAsk origin 7 (sourcePayload 9)) :=
  ⟨rfl, arguments_supported oldKit⟩

def retained (origin : Nat) :
    Source.FiringAt (Kit.Declaration sourceSignature sourceParallel Empty Nat oldKit)
      (fun declaration => Kit.ruleImage (declaration.rule noOriginalRules))
      (sendAsk origin 7 (sourcePayload 9)).agent (sendAsk origin 7 (sourcePayload 9)).label where
  occurrence := .administrative (sendAsk origin 7 (sourcePayload 9)) (send_permitted origin)
  reaction := 𝟙 _
  square := (sendAsk origin 7 (sourcePayload 9)).complete_probe_square.trans
    (Category.comp_id (sendAsk origin 7 (sourcePayload 9)).rule.redex).symm
  minimal := raw_right_identity_isIPO _ (sendAsk origin 7 (sourcePayload 9)).complete_probe_square

def expanded (origin : Nat) := Kit.expandFiring opensAll noOriginalRules (retained origin)

theorem the_expanded_receipt_retains_its_actual_origin :
    (expanded 24).occurrence.origin = (Sum.inr 24 : Empty ⊕ Nat) := rfl

theorem the_expanded_receipt_retains_the_complete_bundle :
    (expanded 24).result = RawArrow.value (classOf (bundle sendHead arguments)) := by
  rw [expanded, Kit.expandFiring_result]
  exact Category.comp_id (sendAsk 24 7 (sourcePayload 9)).rule.reactum

theorem the_unique_old_receipt_keeps_the_whole_firing :
    ∃! before : Source.FiringAt (Kit.Declaration sourceSignature sourceParallel Empty Nat oldKit)
      (fun declaration => Kit.ruleImage (declaration.rule noOriginalRules))
      (sendAsk 24 7 (sourcePayload 9)).agent (sendAsk 24 7 (sourcePayload 9)).label,
        Kit.expandFiring opensAll noOriginalRules before = expanded 24 :=
  Kit.unique_old_firing opensAll noOriginalRules
    (Kit.permitted_bounds _ (send_permitted 24)).1 (Kit.permitted_bounds _ (send_permitted 24)).2 _

theorem duplicate_authored_origins_do_not_merge : expanded 24 ≠ expanded 25 := by
  intro same
  have origins : (Sum.inr 24 : Empty ⊕ Nat) = Sum.inr 25 :=
    congrArg (fun receipt => receipt.occurrence.origin) same
  have different : 24 = 25 := Sum.inr.inj origins
  omega

def bodyAgent (opened : Kit.Policy sourceSignature sourceParallel) :
    Kit.origin opened ⟶ Kit.interface opened (.original .process) :=
  Kit.value (classOf (sourceNode sendHead arguments))
    ⟨_, (Kit.sourceNode_supported_iff opened sendHead arguments).mpr (arguments_supported opened), rfl⟩

def zeroAgent (opened : Kit.Policy sourceSignature sourceParallel) :
    Kit.origin opened ⟶ Kit.interface opened (.original .process) :=
  Kit.value (classOf (embed (.zero rfl : SourceValue .process)))
    ⟨_, Kit.embed_supported opened (.zero rfl : SourceValue .process), rfl⟩

theorem unopened_no_rule_kit_has_no_firing {before after : Kit.Object emptyKit}
    (agent : Kit.origin emptyKit ⟶ before) (label : before ⟶ after)
    (target : Kit.origin emptyKit ⟶ after) :
    ¬ActIPO (Kit.categoryRules (NativeOrigins := Nat) noOriginalRules emptyKit) label agent target := by
  rintro ⟨_, ⟨declaration, _⟩, _, _, _, _⟩
  cases declaration with
  | original absent => exact Empty.elim absent
  | administrative occurrence permitted =>
    cases occurrence <;> exact permitted.1 rfl

theorem the_old_actual_observer_cannot_separate_send_from_unit :
    IPOBisimilar (Kit.categoryRules (NativeOrigins := Nat) noOriginalRules emptyKit)
      (bodyAgent emptyKit) (zeroAgent emptyKit) := by
  refine ⟨fun _ _ _ => True, ?_, True.intro⟩
  intro current left right _
  constructor
  · intro nextInterface label target step
    exact (unopened_no_rule_kit_has_no_firing left label target step).elim
  · intro nextInterface label target step
    exact (unopened_no_rule_kit_has_no_firing right label target step).elim

private theorem no_original_ambient_step_is_administrative {before after : ContextCategory sourceSignature sourceParallel}
    {agent : (.origin : ContextCategory sourceSignature sourceParallel) ⟶ before} {label : before ⟶ after}
    {target : (.origin : ContextCategory sourceSignature sourceParallel) ⟶ after}
    (step : ActIPO (Kit.ambientRules (NativeOrigins := Nat) noOriginalRules oldKit) label agent target) :
    ActIPO (rules sourceSignature sourceParallel Nat) label agent target := by
  rcases step with ⟨_, ⟨declaration, rfl⟩, reaction, square, minimal, output⟩
  cases declaration with
  | original absent => exact Empty.elim absent
  | administrative occurrence permitted =>
    exact ⟨occurrence.rule, ⟨occurrence, rfl⟩, reaction, square, minimal, output⟩

private theorem unit_cannot_match_the_whole_send_ask
    (target : (.origin : ContextCategory sourceSignature sourceParallel) ⟶ .interface (.arguments sendHead)) :
    ¬ActIPO (rules sourceSignature sourceParallel Nat) (probeLabel (.ask sendHead))
      (RawArrow.value (classOf (embed (.zero rfl : SourceValue .process)))) target := by
  cases target with
  | value observed =>
    intro step
    obtain ⟨_origin, tuple, inputRead, _outputRead⟩ := (ask_step_iff sendHead _ observed).mp step
    have counts := congrArg (fun supplied => (inventoryQ supplied).card) inputRead
    change 0 = 1 at counts
    omega

theorem opening_send_genuinely_refines_the_actual_observer :
    ¬IPOBisimilar (Kit.categoryRules (NativeOrigins := Nat) noOriginalRules oldKit)
      ((Kit.expand opensSend).map (bodyAgent emptyKit)) ((Kit.expand opensSend).map (zeroAgent emptyKit)) := by
  intro related
  let receipt := Kit.directAdministrativeFiring noOriginalRules (sendAsk 24 7 (sourcePayload 9)) (send_permitted 24)
  have step : ActIPO (Kit.categoryRules (NativeOrigins := Nat) noOriginalRules oldKit)
      (Kit.administrativeLabel (sendAsk 24 7 (sourcePayload 9)) (send_permitted 24))
      ((Kit.expand opensSend).map (bodyAgent emptyKit)) receipt.result := receipt.step
  obtain ⟨matched, matchedStep, _successors⟩ := ipoBisimilar_forward related step
  have ambient := (Kit.category_step_iff oldKit noOriginalRules _ _ _).mp matchedStep
  exact unit_cannot_match_the_whole_send_ask matched.val (no_original_ambient_step_is_administrative ambient)

theorem actual_all_old_label_bisimulation_monotonicity
    {interface : Kit.Object oldKit} {before after : Kit.origin oldKit ⟶ interface}
    (related : IPOBisimilar (Kit.categoryRules (NativeOrigins := Nat) noOriginalRules allKit)
      ((Kit.expand opensAll).map before) ((Kit.expand opensAll).map after)) :
    IPOBisimilar (Kit.categoryRules (NativeOrigins := Nat) noOriginalRules oldKit) before after :=
  Kit.bisimulation_monotone opensAll noOriginalRules related

def originalRules : Nat → ReactionRule (.origin : SourceCategory sourceSignature sourceParallel) :=
  fun _origin => unitSourceRule rfl (sourcePayload 11)

def originalCompetitor :
    Source.FiringAt (Kit.Declaration sourceSignature sourceParallel Nat Nat oldKit)
      (fun declaration => Kit.ruleImage (declaration.rule originalRules))
      (processGet 24 7 (sourcePayload 9)).agent (processGet 24 7 (sourcePayload 9)).label where
  occurrence := .original 31
  reaction := (unitGetFiring 31 sendHead arguments 1 rfl (sourcePayload 11)).reaction
  square := (unitGetFiring 31 sendHead arguments 1 rfl (sourcePayload 11)).square
  minimal := (unitGetFiring 31 sendHead arguments 1 rfl (sourcePayload 11)).minimal

theorem old_get_bounds_are_wholly_supported :
    Kit.ArrowSupported oldKit (processGet 24 7 (sourcePayload 9)).agent ∧
      Kit.ArrowSupported oldKit (processGet 24 7 (sourcePayload 9)).label :=
  Kit.permitted_bounds _ ⟨rfl, arguments_supported oldKit⟩

theorem actual_original_unit_competition_is_retained :
    (Kit.expandFiring opensAll originalRules originalCompetitor).result =
      RawArrow.value (classOf (.cut (signature := signature sourceSignature sourceParallel)
        (Parallel := NativeParallel) (sort := .original .process) rfl
        (embed (sourcePayload 11)) (getAssay sendHead arguments 1))) := by
  rw [Kit.expandFiring_result]
  rfl

theorem the_whole_original_competitor_has_one_old_receipt_preimage :
    ∃! before : Source.FiringAt (Kit.Declaration sourceSignature sourceParallel Nat Nat oldKit)
      (fun declaration => Kit.ruleImage (declaration.rule originalRules))
      (processGet 24 7 (sourcePayload 9)).agent (processGet 24 7 (sourcePayload 9)).label,
        Kit.expandFiring opensAll originalRules before = Kit.expandFiring opensAll originalRules originalCompetitor :=
  Kit.unique_old_firing opensAll originalRules
    old_get_bounds_are_wholly_supported.1 old_get_bounds_are_wholly_supported.2 _

theorem the_competing_get_result_does_not_erase_the_assay :
    originalCompetitor.result ≠ (processGet 24 7 (sourcePayload 9)).target := by
  intro same
  have counts := congrArg (arrowObserverCount (source := sourceSignature) (Parallel := sourceParallel)) same
  have competitor : arrowObserverCount originalCompetitor.result = 3 := by
    change arrowObserverCount (unitGetFiring 31 sendHead arguments 1 rfl (sourcePayload 11)).result = 3
    rw [unitGetFiring_observerCount]
    have children : ∀ position, observerCount (arguments position) = 0 := by
      intro position
      fin_cases position
      · exact observerCount_embed (sourceName 7)
      · exact observerCount_embed (sourcePayload 9)
    simp only [children, Finset.sum_const_zero, Nat.add_zero]
  have administrative : arrowObserverCount (processGet 24 7 (sourcePayload 9)).target = 0 :=
    observerCount_embed (sourcePayload 9)
  rw [competitor, administrative] at counts
  omega

theorem missing_administrative_origins_cannot_supply_a_receipt
    (supplied : Source.FiringAt (Kit.Declaration sourceSignature sourceParallel Empty Empty allKit)
      (fun declaration => Kit.ruleImage (declaration.rule noOriginalRules))
      (sendAsk 24 7 (sourcePayload 9)).agent (sendAsk 24 7 (sourcePayload 9)).label) : False := by
  cases supplied.occurrence with
  | original absent => exact Empty.elim absent
  | administrative occurrence permitted => exact Empty.elim occurrence.origin

end Mettapedia.OSLF.Framework.SortedTypedInstrumentKitTransitionControls
