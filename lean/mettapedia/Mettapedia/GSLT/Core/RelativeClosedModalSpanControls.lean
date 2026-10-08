import Mettapedia.CategoryTheory.InternalPredicateModalSpanComparison
import Mettapedia.CategoryTheory.ElementaryTypePredicateReadout
import Mettapedia.CategoryTheory.PositionedRewritePredicatePower
import Mettapedia.GSLT.Core.RelativeClosedPositionedModalNativeMeaning

/-!
# Exact event comparisons and a larger reduction relation

The smaller relation contains the successor edge; the larger relation also
contains the second successor. Both are actual monic program relations and
the identity closed base map preserves each smaller event. A complete
parameterized postcondition separates their global modal operators. A
nonidentity relabelling of the event carrier instead preserves the full
operator, including future parameter substitutions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedModalSpanControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open Mettapedia.CategoryTheory InternalPredicateModalSpanComparison
open HigherOrderInternalPredicateObject HigherOrderInternalPredicateQuantifier
open ElementaryTypePredicateReadout ProgramReductionTheory

def successor : Nat ⟶ Nat := TypeCat.ofHom Nat.succ
def before : (Nat × Bool) ⟶ Nat := TypeCat.ofHom Prod.fst
def after : (Nat × Bool) ⟶ Nat :=
  TypeCat.ofHom fun event => if event.2 then event.1 + 2 else event.1 + 1

def smaller : Span Type Nat Nat := ⟨Nat, 𝟙 Nat, successor⟩
def larger : Span Type Nat Nat := ⟨Nat × Bool, before, after⟩
def retain : Nat ⟶ Nat × Bool := TypeCat.ofHom fun number => (number, false)

def retainedEvents : Span.Map smaller larger where
  event := retain
  source := rfl
  target := rfl

def smallerGraph : Nat ⟶ Nat ⨯ Nat := prod.lift (𝟙 Nat) successor
def largerGraph : (Nat × Bool) ⟶ Nat ⨯ Nat := prod.lift before after

instance smallerGraph_mono : Mono smallerGraph := by
  unfold smallerGraph
  infer_instance

instance largerGraph_mono : Mono largerGraph := by
  apply (mono_iff_injective largerGraph).mpr
  intro first second same
  have sourceRead := congrArg (prod.fst : Nat ⨯ Nat ⟶ Nat) same
  have targetRead := congrArg (prod.snd : Nat ⨯ Nat ⟶ Nat) same
  change (largerGraph ≫ prod.fst) first = (largerGraph ≫ prod.fst) second at sourceRead
  change (largerGraph ≫ prod.snd) first = (largerGraph ≫ prod.snd) second at targetRead
  rw [largerGraph, prod.lift_fst] at sourceRead
  rw [largerGraph, prod.lift_snd] at targetRead
  rcases first with ⟨number, flag⟩
  rcases second with ⟨other, otherFlag⟩
  change number = other at sourceRead
  subst other
  cases flag <;> cases otherFlag
  · rfl
  · change number + 1 = number + 2 at targetRead
    omega
  · change number + 2 = number + 1 at targetRead
    omega
  · rfl

abbrev closed : LambdaTheory.{1,0} where
  Obj := Type
  instCategory := inferInstance
  instCartesianMonoidal := inferInstance
  instMonoidalClosed := inferInstance
  instHasFiniteLimits := inferInstance

abbrev smallerTheory : Theory.{1,0} := ⟨closed, Nat, Subobject.mk smallerGraph⟩
abbrev largerTheory : Theory.{1,0} := ⟨closed, Nat, Subobject.mk largerGraph⟩

theorem graph_inclusion : smallerTheory.reduction ≤ largerTheory.reduction := by
  apply Subobject.mk_le_mk_of_comm retain
  apply prod.hom_ext
  · rw [Category.assoc, largerGraph, prod.lift_fst, smallerGraph, prod.lift_fst]
    rfl
  · rw [Category.assoc, largerGraph, prod.lift_snd, smallerGraph, prod.lift_snd]
    rfl

/-- An actual admitted program/reduction theory map, with no surjectivity of events. -/
def programMap : ProgramReductionTheory.Map smallerTheory largerTheory where
  closed := LambdaTheoryMap.id closed
  program := Iso.refl Nat
  reduction := Subobject.ofLE _ _ graph_inclusion
  source := by
    change Subobject.ofLE _ _ graph_inclusion ≫ (largerTheory.reduction.arrow ≫ prod.fst) =
      smallerTheory.reduction.arrow ≫ prod.fst ≫ 𝟙 Nat
    rw [← Category.assoc, Subobject.ofLE_arrow, Category.comp_id]
  target := by
    change Subobject.ofLE _ _ graph_inclusion ≫ (largerTheory.reduction.arrow ≫ prod.snd) =
      smallerTheory.reduction.arrow ≫ prod.snd ≫ 𝟙 Nat
    rw [← Category.assoc, Subobject.ofLE_arrow, Category.comp_id]

def actualSmaller : Span Type Nat Nat :=
  ⟨smallerTheory.Event, smallerTheory.source, smallerTheory.target⟩
def actualLarger : Span Type Nat Nat :=
  ⟨largerTheory.Event, largerTheory.source, largerTheory.target⟩

def smallerComparison : Span.Iso smaller actualSmaller where
  events := (Subobject.underlyingIso smallerGraph).symm
  source := by
    change (Subobject.underlyingIso smallerGraph).inv ≫
      ((Subobject.mk smallerGraph).arrow ≫ prod.fst) = 𝟙 Nat
    rw [← Category.assoc, Subobject.underlyingIso_arrow]
    exact prod.lift_fst _ _
  target := by
    change (Subobject.underlyingIso smallerGraph).inv ≫
      ((Subobject.mk smallerGraph).arrow ≫ prod.snd) = successor
    rw [← Category.assoc, Subobject.underlyingIso_arrow]
    exact prod.lift_snd _ _

def largerComparison : Span.Iso larger actualLarger where
  events := (Subobject.underlyingIso largerGraph).symm
  source := by
    change (Subobject.underlyingIso largerGraph).inv ≫
      ((Subobject.mk largerGraph).arrow ≫ prod.fst) = before
    rw [← Category.assoc, Subobject.underlyingIso_arrow]
    exact prod.lift_fst _ _
  target := by
    change (Subobject.underlyingIso largerGraph).inv ≫
      ((Subobject.mk largerGraph).arrow ≫ prod.snd) = after
    rw [← Category.assoc, Subobject.underlyingIso_arrow]
    exact prod.lift_snd _ _

def actualRetainedEvents : Span.Map actualSmaller actualLarger where
  event := programMap.reduction
  source := by
    exact programMap.source.trans (Category.comp_id smallerTheory.source)
  target := by
    exact programMap.target.trans (Category.comp_id smallerTheory.target)

/-- The independently selected postcondition reads both the reduct and its parameter. -/
def postcondition : Subobject (Nat ⊗ Nat) :=
  fromSet {supplied | snd Nat Nat supplied < fst Nat Nat supplied}

def postName : Nat ⟶ power doctrine Nat :=
  PositionedRewritePredicatePower.name doctrine postcondition

theorem postName_read : family doctrine postName = postcondition :=
  PositionedRewritePredicatePower.family_name doctrine postcondition

def smallerOutput := family doctrine (postName ≫ operation doctrine smaller)
def largerOutput := family doctrine (postName ≫ operation doctrine larger)

theorem smaller_output_read (number parameter : Nat) :
    Contains smallerOutput (number, parameter) ↔ parameter < number + 1 := by
  rw [smallerOutput, operation_supplied, postName_read]
  change Contains (doctrine.existsAlong ((𝟙 Nat) ▷ Nat)
    (doctrine.reindex (successor ▷ Nat) postcondition)) (number, parameter) ↔ _
  rw [contains_exists]
  constructor
  · rintro ⟨supplied, admitted, reaches⟩
    change supplied = (number, parameter) at reaches
    subst supplied
    rw [contains_reindex] at admitted
    unfold postcondition at admitted
    rw [contains_fromSet] at admitted
    exact admitted
  · intro admitted
    refine ⟨(number, parameter), ?_, rfl⟩
    rw [contains_reindex]
    unfold postcondition
    rw [contains_fromSet]
    exact admitted

theorem larger_output_read (number parameter : Nat) :
    Contains largerOutput (number, parameter) ↔ parameter < number + 2 := by
  rw [largerOutput, operation_supplied, postName_read]
  change Contains (doctrine.existsAlong (before ▷ Nat)
    (doctrine.reindex (after ▷ Nat) postcondition)) (number, parameter) ↔ _
  rw [contains_exists]
  constructor
  · rintro ⟨supplied, admitted, reaches⟩
    change (supplied.1.1, supplied.2) = (number, parameter) at reaches
    have sourceRead := congrArg Prod.fst reaches
    have parameterRead := congrArg Prod.snd reaches
    rw [contains_reindex] at admitted
    unfold postcondition at admitted
    rw [contains_fromSet] at admitted
    change supplied.2 < (if supplied.1.2 then supplied.1.1 + 2 else supplied.1.1 + 1) at admitted
    rw [sourceRead, parameterRead] at admitted
    by_cases enabled : supplied.1.2 = true
    · rw [if_pos enabled] at admitted
      exact admitted
    · rw [if_neg enabled] at admitted
      omega
  · intro admitted
    refine ⟨((number, true), parameter), ?_, rfl⟩
    rw [contains_reindex]
    unfold postcondition
    rw [contains_fromSet]
    exact admitted

theorem actual_operator_agrees_with_native (span : Span Type Nat Nat) :
    operation doctrine span =
      RelativeClosedPositionedModalNativeMeaning.possibilityOperation doctrine
        span.source span.target :=
  RelativeClosedPositionedModalNativeMeaning.possibilityOperation_complete doctrine _ _

theorem mapped_event_operator_inclusion :
    smallerOutput ≤ largerOutput :=
  operation_supplied_inclusion doctrine retainedEvents postName

theorem a_new_event_changes_the_whole_operator :
    Contains largerOutput (0, 1) ∧ ¬ Contains smallerOutput (0, 1) := by
  rw [larger_output_read, smaller_output_read]
  exact ⟨by omega, Nat.lt_irrefl 1⟩

theorem the_actual_program_map_does_not_preserve_global_possibility :
    RelativeClosedPositionedModalNativeMeaning.possibilityOperation doctrine
        smallerTheory.source smallerTheory.target ≠
      RelativeClosedPositionedModalNativeMeaning.possibilityOperation doctrine
        largerTheory.source largerTheory.target := by
  intro same
  have smallerComplete := operation_equal doctrine smallerComparison
  have largerComplete := operation_equal doctrine largerComparison
  have sameOperation : operation doctrine smaller = operation doctrine larger :=
    smallerComplete.trans ((actual_operator_agrees_with_native actualSmaller).trans
      (same.trans ((actual_operator_agrees_with_native actualLarger).symm.trans largerComplete.symm)))
  have sameOutput : smallerOutput = largerOutput :=
    congrArg (fun arrow => family doctrine (postName ≫ arrow)) sameOperation
  have separator := a_new_event_changes_the_whole_operator
  exact separator.2 (sameOutput.symm ▸ separator.1)

def exchange : (Nat × Bool) ≅ (Nat × Bool) where
  hom := TypeCat.ofHom fun event => (event.1, !event.2)
  inv := TypeCat.ofHom fun event => (event.1, !event.2)
  hom_inv_id := by
    apply ConcreteCategory.ext_apply
    intro event
    change (event.1, ! !event.2) = event
    rcases event with ⟨number, flag⟩
    cases flag <;> rfl
  inv_hom_id := by
    apply ConcreteCategory.ext_apply
    intro event
    change (event.1, ! !event.2) = event
    rcases event with ⟨number, flag⟩
    cases flag <;> rfl

def relabelled : Span Type Nat Nat := ⟨Nat × Bool, exchange.hom ≫ before, exchange.hom ≫ after⟩
def eventRelabelling : Span.Iso relabelled larger := ⟨exchange, rfl, rfl⟩

theorem event_relabelling_is_nonidentity : exchange.hom ≠ 𝟙 (Nat × Bool) := by
  intro same
  have changed := congrArg (fun arrow : (Nat × Bool) ⟶ (Nat × Bool) => (arrow (3, false)).2) same
  exact Bool.false_ne_true changed.symm

theorem complete_operator_is_preserved_by_relabelling :
    operation doctrine relabelled = operation doctrine larger :=
  operation_equal doctrine eventRelabelling

def future : Nat ⟶ Nat := TypeCat.ofHom Nat.succ

theorem relabelled_future_read (number parameter : Nat) :
    Contains (family doctrine ((future ≫ postName) ≫ operation doctrine relabelled))
      (number, parameter) ↔ parameter + 1 < number + 2 := by
  rw [complete_operator_is_preserved_by_relabelling, operation_future, contains_reindex]
  exact larger_output_read number (parameter + 1)

theorem future_parameter_changes_the_answer :
    Contains largerOutput (0, 1) ∧
      ¬ Contains (family doctrine ((future ≫ postName) ≫ operation doctrine relabelled)) (0, 1) := by
  rw [larger_output_read, relabelled_future_read]
  exact ⟨by omega, Nat.lt_irrefl 2⟩

end Mettapedia.GSLT.Core.RelativeClosedModalSpanControls
