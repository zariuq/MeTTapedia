import Mettapedia.OSLF.Syntax.SortedCommutativeContextSyntax
import Mettapedia.OSLF.Syntax.SortedCommutativeFrames

/-!
# Complete normalization of sorted raw context equations

Only designated Cut frames contribute parallel residues. Every free frame
retains its constructor, selected position and all sibling equation classes.
Normalization respects the independently generated context equations and
recovers both actual filling and composition.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.SortedCommutative

open Mettapedia.OSLF.SortedConstructors

universe u v

variable {signature : Signature.{u,v}} {Parallel : signature.Srt → Prop}

namespace MixedContext

def addResidue {source target : signature.Srt} (context : MixedContext signature Parallel source target)
    (supplied : Multiset (ResiduePayload (signature := signature) (Parallel := Parallel) target)) :
    MixedContext signature Parallel source target :=
  Mettapedia.CategoryTheory.MixedResidue.Context.addOuter
    (Payload := fun vertex : Interface signature Parallel => ResiduePayload vertex.sort) supplied context

theorem addResidue_zero {source target : signature.Srt} (context : MixedContext signature Parallel source target) :
    context.addResidue 0 = context :=
  Mettapedia.CategoryTheory.MixedResidue.Context.addOuter_zero context

theorem addResidue_add {source target : signature.Srt} (context : MixedContext signature Parallel source target)
    (first second : Multiset (ResiduePayload (signature := signature) (Parallel := Parallel) target)) :
    (context.addResidue second).addResidue first = context.addResidue (first + second) :=
  Mettapedia.CategoryTheory.MixedResidue.Context.addOuter_add
    (Payload := fun vertex : Interface signature Parallel => ResiduePayload vertex.sort) first second context

end MixedContext

def residueOf {sort : signature.Srt} (parallel : Parallel sort) (term : Term signature Parallel sort) :
    Multiset (ResiduePayload (signature := signature) (Parallel := Parallel) sort) :=
  (inventory term).map (fun head => ⟨head, parallel⟩)

theorem residueOf_values {sort : signature.Srt} (parallel : Parallel sort)
    (term : Term signature Parallel sort) : (residueOf parallel term).map Subtype.val = inventory term := by
  rw [residueOf, Multiset.map_map]
  exact Multiset.map_id _

theorem residueOf_zero {sort : signature.Srt} (parallel : Parallel sort) :
    residueOf parallel (.zero parallel : Term signature Parallel sort) = 0 := rfl

theorem residueOf_cut {sort : signature.Srt} (parallel : Parallel sort)
    (first second : Term signature Parallel sort) :
    residueOf parallel (.cut parallel first second) = residueOf parallel first + residueOf parallel second :=
  Multiset.map_add _ _ _

theorem residueOf_equation {sort : signature.Srt} (parallel : Parallel sort)
    {first second : Term signature Parallel sort} (equation : Equation first second) :
    residueOf parallel first = residueOf parallel second :=
  congrArg (fun supplied => supplied.map (fun head => (⟨head, parallel⟩ : ResiduePayload sort))) equation.inventory

theorem residueOf_filling {sort : signature.Srt} (parallel : Parallel sort)
    (sibling supplied : Term signature Parallel sort) :
    residue (residueOf parallel sibling) (classOf supplied) = classOf (.cut parallel supplied sibling) := by
  apply inventoryQ_injective
  rw [residue_inventory, residueOf_values]
  exact add_comm _ _

theorem Frame.fill_classOf (constructor : signature.Constructor) (position : Fin (signature.arity constructor))
    (siblings : (other : Fin (signature.arity constructor)) → other ≠ position →
      Term signature Parallel (signature.input constructor other))
    (supplied : Term signature Parallel (signature.input constructor position)) :
    Frame.fill (.slot constructor position (fun other absent => classOf (siblings other absent))) (classOf supplied) =
      classOf (.node constructor (RawContext.insert constructor position siblings supplied)) := by
  have readings : Frame.insert constructor position (fun other absent => classOf (siblings other absent)) (classOf supplied) =
      fun other => classOf (RawContext.insert constructor position siblings supplied other) := by
    funext other
    by_cases same : other = position
    · subst other
      simp only [Frame.insert, RawContext.insert, dite_true]
    · simp only [Frame.insert, RawContext.insert, dif_neg same]
  change (Head.node constructor (Frame.insert constructor position
    (fun other absent => classOf (siblings other absent)) (classOf supplied))).class = _
  rw [readings]
  exact Head.class_node constructor _

namespace RawContext

def normalize {source target : signature.Srt} :
    RawContext signature Parallel source target → MixedContext signature Parallel source target
  | .hole => .parallel 0
  | .frame constructor position siblings inner =>
      .frame 0 (.slot constructor position (fun other absent => classOf (siblings other absent))) inner.normalize
  | .left parallel inner sibling => inner.normalize.addResidue (residueOf parallel sibling)
  | .right parallel sibling inner => inner.normalize.addResidue (residueOf parallel sibling)

theorem normalize_comp {source middle target : signature.Srt}
    (inner : RawContext signature Parallel source middle) (outer : RawContext signature Parallel middle target) :
    (inner.comp outer).normalize = inner.normalize.comp outer.normalize := by
  induction outer with
  | hole => exact (Mettapedia.CategoryTheory.MixedResidue.Context.comp_identity _).symm
  | frame constructor position siblings _ inductionHypothesis =>
    exact congrArg (Mettapedia.CategoryTheory.MixedResidue.Context.frame 0
      (Frame.slot constructor position (fun other absent => classOf (siblings other absent)))) inductionHypothesis
  | left parallel outer sibling inductionHypothesis =>
    exact (congrArg (fun context => MixedContext.addResidue context (residueOf parallel sibling)) inductionHypothesis).trans
      (Mettapedia.CategoryTheory.MixedResidue.Context.comp_addOuter inner.normalize outer.normalize (residueOf parallel sibling)).symm
  | right parallel sibling outer inductionHypothesis =>
    exact (congrArg (fun context => MixedContext.addResidue context (residueOf parallel sibling)) inductionHypothesis).trans
      (Mettapedia.CategoryTheory.MixedResidue.Context.comp_addOuter inner.normalize outer.normalize (residueOf parallel sibling)).symm

theorem normalize_filling {source target : signature.Srt}
    (context : RawContext signature Parallel source target) (supplied : Term signature Parallel source) :
    (mixedAction signature Parallel).read context.normalize (classOf supplied) = classOf (context.fill supplied) := by
  induction context with
  | hole => exact residue_zero _
  | frame constructor position siblings _ inductionHypothesis =>
    change residue 0 (Frame.fill (.slot constructor position (fun other absent => classOf (siblings other absent)))
      ((mixedAction signature Parallel).read _ (classOf supplied))) = _
    rw [residue_zero, inductionHypothesis, Frame.fill_classOf]
    rfl
  | left parallel inner sibling inductionHypothesis =>
    exact ((mixedAction signature Parallel).read_addOuter (residueOf parallel sibling) inner.normalize (classOf supplied)).trans
      ((congrArg (residue (residueOf parallel sibling)) inductionHypothesis).trans
        (residueOf_filling parallel sibling (inner.fill supplied)))
  | right parallel sibling inner inductionHypothesis =>
    exact ((mixedAction signature Parallel).read_addOuter (residueOf parallel sibling) inner.normalize (classOf supplied)).trans
      ((congrArg (residue (residueOf parallel sibling)) inductionHypothesis).trans
        ((residueOf_filling parallel sibling (inner.fill supplied)).trans
          (Quotient.sound (Equation.comm parallel (inner.fill supplied) sibling))))

end RawContext

theorem ContextEquation.normalize {source target : signature.Srt}
    {first second : RawContext signature Parallel source target} (equation : ContextEquation first second) :
    first.normalize = second.normalize := by
  induction equation with
  | refl => rfl
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ first second => exact first.trans second
  | frame constructor position siblings _ inductionHypothesis =>
    exact congrArg₂ (fun (edge : Frame signature Parallel (signature.input constructor position) (signature.output constructor))
        (inner : MixedContext signature Parallel source (signature.input constructor position)) =>
        Mettapedia.CategoryTheory.MixedResidue.Context.frame 0 edge inner)
      (congrArg (Frame.slot constructor position) (funext (fun other => funext (fun absent => Quotient.sound (siblings other absent)))))
      inductionHypothesis
  | left parallel _ sibling inductionHypothesis =>
    exact congrArg₂ MixedContext.addResidue inductionHypothesis (residueOf_equation parallel sibling)
  | right parallel sibling _ inductionHypothesis =>
    exact congrArg₂ MixedContext.addResidue inductionHypothesis (residueOf_equation parallel sibling)
  | comm => rfl
  | assoc parallel inner first second =>
    change (inner.normalize.addResidue (residueOf parallel first)).addResidue (residueOf parallel second) =
      inner.normalize.addResidue (residueOf parallel (.cut parallel first second))
    rw [residueOf_cut, MixedContext.addResidue_add, add_comm]
  | unit parallel inner =>
    change inner.normalize.addResidue (residueOf parallel (.zero parallel)) = inner.normalize
    rw [residueOf_zero, MixedContext.addResidue_zero]

end Mettapedia.OSLF.SortedCommutative
