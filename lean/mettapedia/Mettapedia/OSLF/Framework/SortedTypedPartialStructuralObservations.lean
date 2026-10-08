import Mettapedia.OSLF.Framework.SortedTypedStructuralObservations

/-!
# Typed structural fragments on genuinely generated subalgebras

An observation policy admits declared typed heads. Formula admission and
term support are independently recursive: every proper child must be
supported, and each unit or Cut requires its actual designated parallel
sort. A class is generated when it has a supported representative, allowing
other AC1 representatives to have an unopened root.

Characteristic formulas are admitted for supported terms and separate a
generated left class from every right class at its actual sort. This is the
structural part of the downward-closed subalgebra comparison. It does not
identify a partial instrument IPO system with restricted formulas or infer
that partial equivalence agrees with the current full observer system.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstruments.StructuralObservations

open Mettapedia.OSLF.SortedCommutative

universe u v

variable {source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
  {Parallel : source.Srt → Prop}

abbrev Policy (source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v})
    (Parallel : source.Srt → Prop) := SourceHead source Parallel → Prop

def Formula.Allowed (opened : Policy source Parallel) :
    {sort : source.Srt} → Formula source Parallel sort → Prop
  | sort, .unit parallel => opened (.unit sort parallel)
  | sort, .cut parallel first second =>
      opened (.properCut sort parallel) ∧ first.Allowed opened ∧ second.Allowed opened
  | _, .node constructor arguments =>
      opened (.ordinary constructor) ∧ ∀ position, (arguments position).Allowed opened

def Supported (opened : Policy source Parallel) : {sort : source.Srt} → Term source Parallel sort → Prop
  | sort, .zero parallel => opened (.unit sort parallel)
  | sort, .cut parallel first second =>
      opened (.properCut sort parallel) ∧ Supported opened first ∧ Supported opened second
  | _, .node constructor arguments =>
      opened (.ordinary constructor) ∧ ∀ position, Supported opened (arguments position)

theorem characteristic_allowed_iff (opened : Policy source Parallel) {sort : source.Srt}
    (term : Term source Parallel sort) : (characteristic term).Allowed opened ↔ Supported opened term := by
  induction term with
  | zero parallel => rfl
  | cut parallel first second firstInduction secondInduction =>
    exact and_congr Iff.rfl (and_congr firstInduction secondInduction)
  | node constructor arguments inductionHypothesis =>
    exact and_congr Iff.rfl (forall_congr' inductionHypothesis)

def PartialLogicalEquivalent (opened : Policy source Parallel) {sort : source.Srt}
    (first second : Class source Parallel sort) : Prop :=
  ∀ formula : Formula source Parallel sort, formula.Allowed opened → (Holds formula first ↔ Holds formula second)

theorem partialLogicalEquivalent_iff_equal_of_supported (opened : Policy source Parallel) {sort : source.Srt}
    (first : Term source Parallel sort) (supported : Supported opened first)
    (second : Class source Parallel sort) :
    PartialLogicalEquivalent opened (classOf first) second ↔ classOf first = second := by
  constructor
  · intro equivalent
    have allowed := (characteristic_allowed_iff opened first).mpr supported
    have firstHolds := (characteristic_holds_iff first (classOf first)).mpr rfl
    exact ((characteristic_holds_iff first second).mp
      ((equivalent (characteristic first) allowed).mp firstHolds)).symm
  · rintro rfl
    exact fun _ _ => Iff.rfl

def Generated (opened : Policy source Parallel) {sort : source.Srt} (supplied : Class source Parallel sort) : Prop :=
  ∃ representative : Term source Parallel sort, Supported opened representative ∧ classOf representative = supplied

theorem partialLogicalEquivalent_iff_equal_of_generated (opened : Policy source Parallel) {sort : source.Srt}
    (first second : Class source Parallel sort) (generated : Generated opened first) :
    PartialLogicalEquivalent opened first second ↔ first = second := by
  obtain ⟨representative, supported, rfl⟩ := generated
  exact partialLogicalEquivalent_iff_equal_of_supported opened representative supported second

theorem partialLogicalEquivalent_monotone {smaller larger : Policy source Parallel}
    (included : ∀ head, smaller head → larger head) {sort : source.Srt}
    {first second : Class source Parallel sort} (equivalent : PartialLogicalEquivalent larger first second) :
    PartialLogicalEquivalent smaller first second := by
  have allowedMono : ∀ {sort : source.Srt} (formula : Formula source Parallel sort),
      formula.Allowed smaller → formula.Allowed larger := by
    intro sort formula
    induction formula with
    | unit parallel => exact included _
    | cut parallel first second firstInduction secondInduction =>
      rintro ⟨head, left, right⟩
      exact ⟨included _ head, firstInduction left, secondInduction right⟩
    | node constructor arguments inductionHypothesis =>
      rintro ⟨head, children⟩
      exact ⟨included _ head, fun position => inductionHypothesis position (children position)⟩
  exact fun formula allowed => equivalent formula (allowedMono formula allowed)

end Mettapedia.OSLF.Framework.SortedTypedInstruments.StructuralObservations
