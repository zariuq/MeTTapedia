import Mettapedia.CategoryTheory.PositionedRewritePredicateLogic
import Mettapedia.CategoryTheory.ElementaryToposPredicateDoctrine
import Mettapedia.GSLT.Core.AuthoredClosedTheory

/-!
# Native modalities of actual positioned rewrites

A frame retains a rule's complete parameter context, the focus-variable
assignment and the assay context containing the rely inputs and the hole.
Their square is an actual pullback. This represents all admitted rely
instances of that assignment; an arbitrary selected edge is insufficient.

In an elementary target, the earned predicate doctrine interprets the
conditional introduction and the guarded modal image. Supplied assignment
and assay maps reconstruct their complete rule instance by the pullback,
then read the actual authored event and exact reduct. Erased modal support
is kept separate from that supplied operational witness.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.PositionedRewriteModal

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory ProgramReductionTheory AuthoredClosedTheory
open PositionedRewritePredicateLogic

universe u v

variable {theory : Theory.{u,v}} (rule : Rule theory)

/-- Shared parameters may live in the assay and focus contexts. The square
retains their actual consistency; no disjoint-variable split is inferred. -/
structure Frame where
  assignments : theory.closed.Obj
  carrier : theory.closed.Obj
  assay : theory.closed.Obj
  forget : rule.parameters ⟶ assignments
  focus : assignments ⟶ carrier
  instantiate : rule.parameters ⟶ assay
  hole : assay ⟶ carrier
  plug : assay ⟶ theory.program
  square : IsPullback forget instantiate focus hole
  source : instantiate ≫ plug = rule.left

namespace Frame

def ofPosition (position : Position rule)
    {assignments : theory.closed.Obj} (forget : rule.parameters ⟶ assignments)
    (focus : assignments ⟶ position.carrier)
    (square : IsPullback forget (prod.lift position.relies position.focus)
      focus prod.snd) : Frame rule where
  assignments := assignments
  carrier := position.carrier
  assay := position.environment ⨯ position.carrier
  forget := forget
  focus := focus
  instantiate := prod.lift position.relies position.focus
  hole := prod.snd
  plug := position.plug
  square := square
  source := position.decomposition

variable {rule} (frame : Frame rule)

def outgoing : rule.parameters ⟶ frame.assay ⨯ theory.program :=
  prod.lift frame.instantiate rule.right

def doctrine (classifier : Subobject.Classifier theory.closed.Obj) :=
  ElementaryToposPredicateDoctrine.doctrine classifier

variable (classifier : Subobject.Classifier theory.closed.Obj)
variable (relies : Subobject frame.assay)
variable (postcondition : Subobject (frame.assay ⨯ theory.program))

def condition : Subobject rule.parameters :=
  conditional (doctrine classifier).toFirstOrder frame.instantiate relies
    ((doctrine classifier).reindex frame.outgoing postcondition)

def introductionScope : Subobject frame.assignments :=
  introPredicate (doctrine classifier).toFirstOrder frame.forget
    (frame.condition classifier relies postcondition)

def modal : Subobject frame.carrier :=
  modality (doctrine classifier).toFirstOrder frame.forget frame.focus
    (frame.condition classifier relies postcondition)

theorem conditional_introduction_iff (premise : Subobject frame.assignments) :
    (doctrine classifier).reindex frame.forget premise ⊓
        (doctrine classifier).reindex frame.instantiate relies ≤
      (doctrine classifier).reindex frame.outgoing postcondition ↔
    premise ≤ frame.introductionScope classifier relies postcondition :=
  guarded_introduction_iff (doctrine classifier).toFirstOrder
    frame.forget frame.instantiate relies _ premise

theorem guarded_modal_elimination :
    (doctrine classifier).reindex frame.hole (frame.modal classifier relies postcondition) ⊓
        relies ≤
      (doctrine classifier).existsAlong frame.instantiate
        ((doctrine classifier).reindex frame.outgoing postcondition) :=
  guarded_elimination (doctrine classifier).toFirstOrder frame.forget frame.focus
    frame.instantiate frame.hole frame.square relies _

variable {context : theory.closed.Obj}
variable (assignment : context ⟶ frame.assignments) (assay : context ⟶ frame.assay)
variable (compatible : assignment ≫ frame.focus = assay ≫ frame.hole)

/-- This uses the supplied complete assignment, not an existential choice. -/
def suppliedInstance : context ⟶ rule.parameters := frame.square.lift assignment assay compatible

@[reassoc (attr := simp)] theorem suppliedInstance_assignment :
    frame.suppliedInstance assignment assay compatible ≫ frame.forget = assignment :=
  frame.square.lift_fst assignment assay compatible

@[reassoc (attr := simp)] theorem suppliedInstance_assay :
    frame.suppliedInstance assignment assay compatible ≫ frame.instantiate = assay :=
  frame.square.lift_snd assignment assay compatible

/-- The authored origin's actual event is retained without converting its endpoints. -/
def step : context ⟶ theory.Event :=
  frame.suppliedInstance assignment assay compatible ≫ rule.action

theorem step_source : frame.step assignment assay compatible ≫ theory.source = assay ≫ frame.plug := by
  rw [step, Category.assoc, rule.source, ← frame.source, ← Category.assoc,
    suppliedInstance_assay]

theorem step_target : frame.step assignment assay compatible ≫ theory.target =
    frame.suppliedInstance assignment assay compatible ≫ rule.right := by
  rw [step, Category.assoc, rule.target]

variable (intro : (doctrine classifier).reindex assignment
    (frame.introductionScope classifier relies postcondition) = ⊤)
variable (rely : (doctrine classifier).reindex assay relies = ⊤)

include intro in
theorem supplied_modal : (doctrine classifier).reindex (assignment ≫ frame.focus)
    (frame.modal classifier relies postcondition) = ⊤ := by
  apply eq_top_iff.mpr
  have included := (doctrine classifier).reindex_mono assignment
    (supplied_focus (doctrine classifier).toFirstOrder frame.forget frame.focus
      (frame.condition classifier relies postcondition))
  change (doctrine classifier).reindex assignment
      (frame.introductionScope classifier relies postcondition) ≤
    (doctrine classifier).reindex assignment
      ((doctrine classifier).reindex frame.focus (frame.modal classifier relies postcondition)) at included
  rw [intro, ← (doctrine classifier).reindex_comp] at included
  exact included

include intro rely in
/-- Universal introduction plus the supplied rely evidence types the exact reduct. -/
theorem supplied_reduct : (doctrine classifier).reindex
    (prod.lift assay (frame.step assignment assay compatible ≫ theory.target)) postcondition = ⊤ := by
  let instanceMap := frame.suppliedInstance assignment assay compatible
  have complete := supplied_condition (doctrine classifier).toFirstOrder frame.forget
    frame.instantiate assignment assay instanceMap
    (frame.suppliedInstance_assignment assignment assay compatible)
    (frame.suppliedInstance_assay assignment assay compatible) relies
    ((doctrine classifier).reindex frame.outgoing postcondition) intro rely
  have completeRead : (doctrine classifier).reindex
      (instanceMap ≫ frame.outgoing) postcondition = ⊤ :=
    ((doctrine classifier).reindex_comp instanceMap frame.outgoing postcondition).trans complete
  have completeArrow : instanceMap ≫ frame.outgoing =
      prod.lift assay (frame.step assignment assay compatible ≫ theory.target) := by
    apply prod.hom_ext
    · simpa only [outgoing, Category.assoc, prod.lift_fst] using
        frame.suppliedInstance_assay assignment assay compatible
    · simpa only [outgoing, Category.assoc, prod.lift_snd] using
        (frame.step_target assignment assay compatible).symm
  exact completeArrow ▸ completeRead

theorem step_unique (candidate : context ⟶ theory.Event)
    (source : candidate ≫ theory.source = assay ≫ frame.plug)
    (target : candidate ≫ theory.target =
      frame.suppliedInstance assignment assay compatible ≫ rule.right) :
    candidate = frame.step assignment assay compatible :=
  theory.endpoint_joint_cancel (source.trans (frame.step_source assignment assay compatible).symm)
    (target.trans (frame.step_target assignment assay compatible).symm)

variable {future : theory.closed.Obj} (incoming : future ⟶ context)

include compatible in
theorem precomposed_match : (incoming ≫ assignment) ≫ frame.focus =
    (incoming ≫ assay) ≫ frame.hole := by
  rw [Category.assoc, compatible, ← Category.assoc]

theorem suppliedInstance_precompose :
    frame.suppliedInstance (incoming ≫ assignment) (incoming ≫ assay)
      (frame.precomposed_match assignment assay compatible incoming) =
    incoming ≫ frame.suppliedInstance assignment assay compatible := by
  apply frame.square.hom_ext
  · simp only [suppliedInstance_assignment, Category.assoc]
  · simp only [suppliedInstance_assay, Category.assoc]

theorem step_precompose :
    frame.step (incoming ≫ assignment) (incoming ≫ assay)
      (frame.precomposed_match assignment assay compatible incoming) =
    incoming ≫ frame.step assignment assay compatible := by
  rw [step, suppliedInstance_precompose, Category.assoc]
  rfl

end Frame

end Mettapedia.GSLT.Core.PositionedRewriteModal
