import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.Gluing
import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.Semantics

/-! # Positive and negative controls for origin-sensitive composition -/

namespace Mettapedia.GSLT.LanguageDef.ModuleAlgebra.Controls

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.Extension

private abbrev Spec := Nat × Nat
private abbrev P := Presentation Nat String Spec

private def carrier : Entry Nat String Spec := ⟨0, "Elem", (9, 9)⟩
private def firstRule : Entry Nat String Spec := ⟨1, "First", (0, 1)⟩
private def secondRule : Entry Nat String Spec := ⟨2, "Second", (1, 2)⟩

private def left : P := ⟨{carrier, firstRule}, by decide⟩
private def right : P := ⟨{carrier, secondRule}, by decide⟩
private def whole : P := ⟨{carrier, firstRule, secondRule}, by decide⟩

/-- A diamond import shares the carrier once and keeps both independent rules. -/
theorem shared_ancestor_join : join left right = some whole := by
  apply join_eq_some_iff.mpr
  decide

theorem shared_ancestor_count : whole.val.card = 3 := by decide

theorem shared_ancestor_meet : (meet left right).val = {carrier} := by decide

theorem shared_ancestor_difference : (diff left right).val = {firstRule} := by decide

/-- Declaration compatibility does not make disagreeing interpretations agree. -/
theorem inconsistent_shared_interpretations_cannot_glue :
    ¬ ∃ mediator : Member whole → Nat,
      (∀ entry : Member left, mediator (includeLeft shared_ancestor_join entry) = 1) ∧
      (∀ entry : Member right, mediator (includeRight shared_ancestor_join entry) = 2) := by
  rintro ⟨mediator, onLeft, onRight⟩
  have first := onLeft ⟨carrier, by decide⟩
  have second := onRight ⟨carrier, by decide⟩
  have shared : includeLeft shared_ancestor_join (⟨carrier, by decide⟩ : Member left) =
      includeRight shared_ancestor_join (⟨carrier, by decide⟩ : Member right) := Subtype.ext rfl
  rw [shared] at first
  have impossible : (1 : Nat) = 2 := first.symm.trans second
  cases impossible

theorem self_sharing : join left left = some left := join_self left

private def copied : P := ⟨{⟨3, "First", (0, 1)⟩}, by decide⟩

/-- Matching text and bodies do not grant identity to an independently created declaration. -/
theorem identical_content_collision : join left copied = none := by decide

private def renamed : P := ⟨{⟨1, "Renamed", (0, 1)⟩}, by decide⟩
private def original : P := ⟨{firstRule}, by decide⟩

theorem divergent_shared_replacement : join original renamed = none := by decide

theorem replacement_keeps_origin : replace original 1 "Renamed" (0, 1) = some renamed := by
  apply check_eq_some_iff.mpr
  decide

/-- Meet is left-biased on incompatible representatives of one origin. -/
theorem incompatible_meet_not_commutative : meet original renamed ≠ meet renamed original := by
  intro equal
  have values := congrArg Subtype.val equal
  have unequal : (meet original renamed).val ≠ (meet renamed original).val := by decide
  exact unequal values

theorem difference_uses_origin : (diff original renamed).val = ∅ := by decide

private def template : P := ⟨{⟨1, "One", (0, 1)⟩, ⟨2, "Mult", (1, 2)⟩}, by decide⟩
private def multiplicative := stampPresentation 2 template
private def additive : Presentation (Nat × Nat) String Spec :=
  ⟨{⟨(1, 1), "Zero", (0, 1)⟩, ⟨(1, 2), "Plus", (1, 2)⟩}, by decide⟩
private def sharedBase : Presentation (Nat × Nat) String Spec :=
  ⟨{⟨(0, 0), "Elem", (9, 9)⟩}, by decide⟩
private def additiveBase : Presentation (Nat × Nat) String Spec :=
  ⟨sharedBase.val ∪ additive.val, by decide⟩
private def multiplicativeBase : Presentation (Nat × Nat) String Spec :=
  ⟨sharedBase.val ∪ multiplicative.val, by decide⟩
private def rigFragment : Presentation (Nat × Nat) String Spec :=
  ⟨sharedBase.val ∪ additive.val ∪ multiplicative.val, by decide⟩

/-- Two applications give independent operations while the imported carrier remains shared. -/
theorem generative_rig_join : join additiveBase multiplicativeBase = some rigFragment := by
  apply join_eq_some_iff.mpr
  decide

theorem generative_rig_count : rigFragment.val.card = 5 := by decide

theorem additive_replacements :
    (replace (stampPresentation 1 template) (1, 1) "Zero" (0, 1)).bind
      (fun p => replace p (1, 2) "Plus" (1, 2)) = some additive := by decide

/-- Sharing one application for both structures creates divergent replacements. -/
theorem incorrectly_shared_monoid_rejected :
    join additive (stampPresentation 1 template) = none := by decide

/-- Fresh identity still requires a label policy: freshness alone does not rename exports. -/
theorem generative_same_labels_rejected :
    join (stampPresentation 1 template) (stampPresentation 2 template) = none := by decide

/-- Nested structured authoring actually unions fragments instead of appending duplicates. -/
theorem nested_authoring :
    elaborate (.bundle [.declaration left.val, .bundle [.declaration right.val]]) =
      some whole := by
  apply check_eq_some_iff.mpr
  simp only [DeclarationDocument.values, DeclarationDocument.valuesList, unionFragments,
    List.foldr_cons, List.foldr_nil, List.append_nil, List.cons_append, List.nil_append,
    Finset.union_empty]
  decide

theorem conflict_rejects_document :
    elaborate (.bundle [.declaration left.val, .declaration copied.val]) = none := by
  simpa only [elaborate, DeclarationDocument.values, DeclarationDocument.valuesList,
    unionFragments, List.append_nil, List.cons_append, List.nil_append, Finset.union_empty,
    List.foldr_cons, List.foldr_nil, join] using identical_content_collision

theorem failure_associativity :
    (join left right).bind (fun p => join p copied) =
      (join right copied).bind (fun p => join left p) := join_assoc left right copied

private def core : GSLT := GSLT.discrete Nat

private def meaning : RuleSemantics Spec core where
  step := fun spec source target => source = spec.1 ∧ target = spec.2
  respectsLeft := by
    intro body source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  respectsRight := by
    intro body source target target' step equal
    subst target'
    exact step

private def sameEndpoints : P :=
  ⟨{firstRule, ⟨3, "Alternative", (0, 1)⟩}, by decide⟩

private def firstEvidence : (retained meaning sameEndpoints).steps.Evidence (0 : Nat) (1 : Nat) :=
  ⟨⟨firstRule, by decide⟩, ⟨⟨rfl, rfl⟩⟩⟩

private def alternativeEvidence : (retained meaning sameEndpoints).steps.Evidence (0 : Nat) (1 : Nat) :=
  ⟨⟨⟨3, "Alternative", (0, 1)⟩, by decide⟩, ⟨⟨rfl, rfl⟩⟩⟩

/-- Endpoint agreement does not identify retained declaration occurrences. -/
theorem same_endpoints_distinct_origins : firstEvidence ≠ alternativeEvidence := by
  intro equal
  have impossible : (1 : Nat) = 3 :=
    congrArg (fun evidence => evidence.1.val.origin) equal
  cases impossible

theorem retained_evidence_erases_to_actual_step : (realize meaning sameEndpoints).Step (0 : Nat) (1 : Nat) :=
  (retained meaning sameEndpoints).steps.erase firstEvidence

theorem component_step : (realize meaning left).Step (0 : Nat) (1 : Nat) := by
  exact ⟨firstRule, by decide, rfl, rfl⟩

theorem other_component_step : (realize meaning right).Step (1 : Nat) (2 : Nat) := by
  exact ⟨secondRule, by decide, rfl, rfl⟩

/-- The combined computation switches components at the intermediate state. -/
theorem join_has_mixed_path : (realize meaning whole).MultiStep (0 : Nat) (2 : Nat) := by
  have first := (realize_join_step meaning shared_ancestor_join (0 : Nat) (1 : Nat)).mpr (Or.inl component_step)
  have second := (realize_join_step meaning shared_ancestor_join (1 : Nat) (2 : Nat)).mpr
    (Or.inr other_component_step)
  exact .step first (.step second (@GSLT.MultiStep.refl (realize meaning whole) (2 : Nat)))

private theorem left_never_reaches_two (source : Nat) : ¬ (realize meaning left).Step source (2 : Nat) := by
  rintro ⟨entry, member, step⟩
  simp only [left, Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with rfl | rfl
  · have impossible : (2 : Nat) = 9 := step.2
    cases impossible
  · have impossible : (2 : Nat) = 1 := step.2
    cases impossible

theorem compatible_join_not_conservative : ¬ (realize meaning left).MultiStep (0 : Nat) (2 : Nat) := by
  intro path
  have invariant : ∀ a b, (realize meaning left).MultiStep a b → a ≠ (2 : Nat) → b ≠ (2 : Nat) := by
    intro a b run
    refine @GSLT.MultiStep.rec (realize meaning left)
      (fun a b _ => a ≠ (2 : Nat) → b ≠ (2 : Nat)) ?_ ?_ a b run
    · intro state h
      exact h
    · intro a b c step rest ih _
      apply ih
      intro equal
      subst b
      exact left_never_reaches_two a step
  exact invariant (0 : Nat) (2 : Nat) path (by change (0 : Nat) ≠ 2; decide) rfl

/-- Reflection is earned on a closed region where the added rule cannot fire. -/
theorem reflection_on_closed_region {source target : Nat} (start : source = 9)
    (path : (realize meaning whole).MultiStep source target) :
    (realize meaning left).MultiStep source target := by
  apply realize_join_reflects_on meaning shared_ancestor_join {(9 : Nat)} ?_ ?_ start path
  · intro a b inRegion step
    obtain ⟨entry, member, firing⟩ := step
    simp only [left, Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl
    · exact firing.2
    · have value : a = (9 : Nat) := Set.mem_singleton_iff.mp inRegion
      have impossible : (9 : Nat) = 0 := value.symm.trans firing.1
      cases impossible
  · intro entry member a inRegion b firing
    simp only [right, Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl
    · exact ⟨carrier, by decide, firing⟩
    · have value : a = (9 : Nat) := Set.mem_singleton_iff.mp inRegion
      have impossible : (9 : Nat) = 1 := value.symm.trans firing.1
      cases impossible

end Mettapedia.GSLT.LanguageDef.ModuleAlgebra.Controls
