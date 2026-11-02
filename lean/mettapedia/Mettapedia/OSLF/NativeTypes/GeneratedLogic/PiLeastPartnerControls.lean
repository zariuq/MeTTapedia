import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiLeastPartners

/-!
# Controls: π's least partners, aware of scope

- **Private hiding**: `(νc) c<d>` and `(νc) c(y).0` are saturated bisimilar to the inert process
  (`hiddenOutput_inert`, `hiddenInput_inert`); the public `c<d>` is not (`publicOutput_not_inert`), told apart by the
  partner `c(y).0`.
- **A restricted channel has no partner**: every least label of `(νc) c<d>` is a redex it takes no part in
  (`hiddenOutput_steps_alone`).
- **Scope extrusion**: `(νv) c<v>` sends its restricted name to the partner `c(y). y<d>`; in the merged scope the
  received name stays restricted, `(νv) v<d>` (`extrusion`), which is again inert (`extruded_inert`). The partner is a
  least label of the sender (`extrusion_least`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.Pi.LeastPartners.Controls

open _root_.CategoryTheory
open Mettapedia.Languages.ProcessCalculi.PiCalculus
open Mettapedia.GSLT.RedexRelativeCongruence (ReactionRule ActIPO)
open Mettapedia.GSLT.BagRelativePushout (Obj bag bag_injective)
open Mettapedia.GSLT.SemiSaturated (Reacts)
open Mettapedia.GSLT.BagHennessyMilner (SaturatedBisimilarIn)

/-- `c<d>` -/
def outputCD : Prime := ⟨.output "c" "d", .output "c" "d"⟩

/-- `c(y).0` -/
def listener : Prime := ⟨.input "c" "y" .nil, .input "c" "y" .nil⟩

/-- `(νc) c<d>` -/
def hiddenOutput : Molecule := ⟨{"c"}, {outputCD}⟩

/-- `(νc) c(y).0` -/
def hiddenInput : Molecule := ⟨{"c"}, {listener}⟩

/-- `c<d>` -/
def publicOutput : Molecule := ⟨∅, {outputCD}⟩

/-- `c(y).0` as a molecule. -/
def publicListener : Molecule := ⟨∅, {listener}⟩

theorem no_internal_of_single {molecule : Molecule} (single : Multiset.card molecule.body = 1) (result : Molecule) :
    ¬ Internal molecule result := by
  rintro ⟨contained, -, -, -⟩
  have := Multiset.card_le_card contained
  simp [single] at this

theorem hiddenOutput_private : hiddenOutput.Private := by
  intro prime member
  obtain rfl := Multiset.mem_singleton.mp member
  decide

theorem hiddenInput_private : hiddenInput.Private := by
  intro prime member
  obtain rfl := Multiset.mem_singleton.mp member
  decide

/-- **`(νc) c<d>` is inert.** -/
theorem hiddenOutput_inert : SaturatedBisimilarIn rules (fun _ => True) {hiddenOutput} 0 :=
  private_inert hiddenOutput_private (no_internal_of_single rfl)

/-- **`(νc) c(y).0` is inert.** -/
theorem hiddenInput_inert : SaturatedBisimilarIn rules (fun _ => True) {hiddenInput} 0 :=
  private_inert hiddenInput_private (no_internal_of_single rfl)

/-- **A restricted channel has no partner.** -/
theorem hiddenOutput_steps_alone {label target : Multiset Molecule}
    (step : ActIPO rules (bag label) (bag {hiddenOutput}) (bag target)) :
    ∃ rule : ReactionRule (Obj Molecule), rules rule ∧ ∃ redex reactum : Multiset Molecule,
      rule.redex = bag redex ∧ rule.reactum = bag reactum ∧ hiddenOutput ∉ redex ∧ label = redex ∧
        target = reactum + {hiddenOutput} := by
  rcases private_steps_alone hiddenOutput_private step with ⟨result, internal, -, -⟩ | alone
  · exact absurd internal (no_internal_of_single rfl result)
  · exact alone

/-- A single molecule with one guarded process has no reaction. -/
theorem single_stuck {molecule : Molecule} (single : Multiset.card molecule.body = 1) (next : Multiset Molecule) :
    ¬ Reacts rules (bag {molecule}) (bag next) := by
  intro reacts
  obtain ⟨rule, member, redex, reactum, redexEq, -, contained, -⟩ :=
    Mettapedia.GSLT.BagSaturated.reacts_iff.mp reacts
  rcases member with ⟨other, result, internal, rfl⟩ | ⟨first, second, result, -, rfl⟩
  · obtain rfl := bag_injective redexEq
    obtain rfl : other = molecule := Multiset.mem_singleton.mp (Multiset.singleton_le.mp contained)
    exact no_internal_of_single single result internal
  · obtain rfl := bag_injective redexEq
    have := Multiset.card_le_card contained
    simp at this

/-- **The public `c<d>` is not inert**: beside `c(y).0` it reacts, and `c(y).0` alone does not. -/
theorem publicOutput_not_inert : ¬ SaturatedBisimilarIn rules (fun _ => True) {publicOutput} 0 := by
  rintro ⟨relation, saturated, related⟩
  obtain ⟨forth, -⟩ := saturated related {publicListener} trivial
  obtain ⟨result, cross⟩ := cross_exists_send (first := publicOutput) (second := publicListener)
    (receiver := listener) (sender := outputCD) (channel := "c") (Multiset.mem_singleton_self _)
    (Multiset.mem_singleton_self _) (Or.inl ⟨"y", .nil, rfl⟩) ⟨"d", rfl⟩ (by decide) (by decide)
  have reacts : Reacts rules (bag {publicOutput} ≫ bag {publicListener}) (bag {result}) := by
    rw [Mettapedia.GSLT.BagRelativePushout.bag_comp]
    refine Mettapedia.GSLT.BagSaturated.reacts_iff.mpr
      ⟨crossRule publicOutput publicListener result, Or.inr ⟨_, _, _, cross, rfl⟩, {publicOutput, publicListener},
        {result}, rfl, rfl, by simp [Multiset.insert_eq_cons, Multiset.singleton_add], by simp [Multiset.insert_eq_cons,
          Multiset.singleton_add]⟩
  obtain ⟨matched, matchedReacts, -⟩ := forth {result} reacts
  rw [Mettapedia.GSLT.BagRelativePushout.bag_comp, zero_add] at matchedReacts
  exact single_stuck rfl matched matchedReacts

/-! ## Scope extrusion -/

/-- `(νv) c<v>` -/
def boundSender : Molecule := ⟨{"v"}, {⟨.output "c" "v", .output "c" "v"⟩}⟩

/-- `c(y). y<d>` -/
def forwarder : Molecule := ⟨∅, {⟨.input "c" "y" (.output "y" "d"), .input "c" "y" (.output "y" "d")⟩}⟩

/-- `(νv) v<d>` -/
def extruded : Molecule := ⟨{"v"}, {⟨.output "v" "d", .output "v" "d"⟩}⟩

theorem forwarder_bodyNames : forwarder.bodyNames = {"c", "d"} := by
  decide

theorem boundSender_bodyNames : boundSender.bodyNames = {"c", "v"} := by
  decide

theorem received : (Process.output "y" "d").substitute "y" "v" = .output "v" "d" := by
  rw [Process.substitute_output]
  decide

/-- **Scope extrusion**: the received restricted name stays restricted in the merged scope. -/
theorem extrusion : Cross forwarder boundSender extruded := by
  have cross := Cross.receive (first := forwarder) (second := boundSender) (first' := forwarder)
    (second' := boundSender) (receiver := ⟨.input "c" "y" (.output "y" "d"), .input "c" "y" (.output "y" "d")⟩)
    (sender := ⟨.output "c" "v", .output "c" "v"⟩) (lifted := ∅)
    (components := {⟨.output "v" "d", .output "v" "d"⟩}) .refl .refl
    ⟨by rw [boundSender_bodyNames]; decide, by rw [forwarder_bodyNames]; decide⟩ (Multiset.mem_singleton_self _)
    (Multiset.mem_singleton_self _) (.input "c" "y" "v" (.output "y" "d"))
    (by rw [received]; exact Lifts.guarded (.output "v" "d")) (Finset.disjoint_empty_left _)
  convert cross using 1
  simp only [extruded, forwarder, boundSender]
  decide

theorem extruded_private : extruded.Private := by
  intro prime member
  obtain rfl := Multiset.mem_singleton.mp member
  decide

/-- **The extruded name stays hidden**: `(νv) v<d>` is inert. -/
theorem extruded_inert : SaturatedBisimilarIn rules (fun _ => True) {extruded} 0 :=
  private_inert extruded_private (no_internal_of_single rfl)

/-- **The receiver is a least label of the bound sender**, and the step extrudes the scope. -/
theorem extrusion_least : ActIPO rules (bag {forwarder}) (bag {boundSender}) (bag {extruded}) := by
  refine actIPO_iff.mpr (Or.inr ⟨forwarder, boundSender, extruded, extrusion, ?_, ?_⟩)
  · decide
  · decide

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.Pi.LeastPartners.Controls
