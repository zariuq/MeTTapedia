import Mettapedia.OSLF.Syntax.SortedCommutativeContextNormalization

/-!
# Raw reconstruction of complete mixed context normal forms

Parallel piles are genuine raw terms of their declared sort, reconstructed
from the independently formed equation classes. Reification retains every
free frame and every supplied sibling class. Its complete normalization
roundtrip is earned from the ground inventory theorem and local context laws.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.SortedCommutative

open Mettapedia.OSLF.SortedConstructors

universe u v

variable {signature : Signature.{u,v}} {Parallel : signature.Srt → Prop}

def pile {sort : signature.Srt} (parallel : Parallel sort)
    (supplied : Multiset (Head (signature := signature) (Parallel := Parallel) sort)) :
    Term signature Parallel sort := (assemble parallel supplied).out

theorem pile_class {sort : signature.Srt} (parallel : Parallel sort)
    (supplied : Multiset (Head (signature := signature) (Parallel := Parallel) sort)) :
    classOf (pile parallel supplied) = assemble parallel supplied := Quotient.out_eq _

theorem pile_inventory {sort : signature.Srt} (parallel : Parallel sort)
    (supplied : Multiset (Head (signature := signature) (Parallel := Parallel) sort)) :
    inventory (pile parallel supplied) = supplied :=
  (congrArg inventoryQ (pile_class parallel supplied)).trans (inventoryQ_assemble parallel supplied)

theorem pile_zero {sort : signature.Srt} (parallel : Parallel sort) :
    Equation (pile parallel 0 : Term signature Parallel sort) (.zero parallel) :=
  Quotient.exact (pile_class parallel 0)

theorem pile_residueOf {sort : signature.Srt} (parallel : Parallel sort) (supplied : Term signature Parallel sort) :
    Equation (pile parallel ((residueOf parallel supplied).map Subtype.val)) supplied := by
  apply Quotient.exact (s := equationSetoid (signature := signature) (Parallel := Parallel) sort)
  change classOf (pile parallel ((residueOf parallel supplied).map Subtype.val)) = classOf supplied
  rw [pile_class, residueOf_values, assemble_inventory]

theorem residueOf_pile {sort : signature.Srt} (parallel : Parallel sort)
    (supplied : Multiset (ResiduePayload (signature := signature) (Parallel := Parallel) sort)) :
    residueOf parallel (pile parallel (supplied.map Subtype.val)) = supplied := by
  rw [residueOf, pile_inventory, Multiset.map_map]
  have inverse : (fun head : ResiduePayload (signature := signature) (Parallel := Parallel) sort =>
      (⟨head.val, parallel⟩ : ResiduePayload sort)) = id := by
    funext head
    exact Subtype.ext rfl
  change supplied.map (fun head => (⟨head.val, parallel⟩ : ResiduePayload sort)) = supplied
  rw [inverse, Multiset.map_id]

namespace RawContext

def addBag {source target : signature.Srt}
    (supplied : Multiset (ResiduePayload (signature := signature) (Parallel := Parallel) target))
    (context : RawContext signature Parallel source target) : RawContext signature Parallel source target := by
  classical
  exact if parallel : Parallel target then .left parallel context (pile parallel (supplied.map Subtype.val)) else context

theorem normalize_addBag {source target : signature.Srt}
    (supplied : Multiset (ResiduePayload (signature := signature) (Parallel := Parallel) target))
    (context : RawContext signature Parallel source target) :
    (addBag supplied context).normalize = context.normalize.addResidue supplied := by
  by_cases parallel : Parallel target
  · rw [addBag, dif_pos parallel, normalize, residueOf_pile]
  · have empty : supplied = 0 := Multiset.eq_zero_of_forall_notMem (fun head _ => parallel head.property)
    rw [addBag, dif_neg parallel, empty, MixedContext.addResidue_zero]

theorem addBag_congr {source target : signature.Srt}
    (supplied : Multiset (ResiduePayload (signature := signature) (Parallel := Parallel) target))
    {first second : RawContext signature Parallel source target} (equation : ContextEquation first second) :
    ContextEquation (addBag supplied first) (addBag supplied second) := by
  by_cases parallel : Parallel target
  · simp only [addBag, dif_pos parallel]
    exact .left parallel equation (.refl _)
  · simpa only [addBag, dif_neg parallel] using equation

theorem addBag_zero {source target : signature.Srt} (context : RawContext signature Parallel source target) :
    ContextEquation (addBag 0 context) context := by
  by_cases parallel : Parallel target
  · simp only [addBag, dif_pos parallel, Multiset.map_zero]
    exact (ContextEquation.left parallel (.refl context) (pile_zero parallel)).trans (.unit parallel context)
  · simp only [addBag, dif_neg parallel]
    exact .refl _

theorem addBag_add {source target : signature.Srt}
    (first second : Multiset (ResiduePayload (signature := signature) (Parallel := Parallel) target))
    (context : RawContext signature Parallel source target) :
    ContextEquation (addBag first (addBag second context)) (addBag (first + second) context) := by
  by_cases parallel : Parallel target
  · simp only [addBag, dif_pos parallel]
    apply (ContextEquation.assoc parallel context _ _).trans
    apply ContextEquation.left parallel (.refl context)
    apply (equation_iff_inventory _ _).mpr
    rw [inventory, pile_inventory, pile_inventory, pile_inventory, Multiset.map_add, add_comm]
  · simp only [addBag, dif_neg parallel]
    exact .refl _

end RawContext

def Frame.rawFrame {source target : signature.Srt} (edge : Frame signature Parallel source target)
    {holeSort : signature.Srt} (inner : RawContext signature Parallel holeSort source) :
    RawContext signature Parallel holeSort target := by
  cases edge with
  | slot constructor position siblings =>
    exact .frame constructor position (fun other absent => (siblings other absent).out) inner

theorem Frame.normalize_rawFrame {source target holeSort : signature.Srt}
    (edge : Frame signature Parallel source target) (inner : RawContext signature Parallel holeSort source) :
    (edge.rawFrame inner).normalize =
      Mettapedia.CategoryTheory.MixedResidue.Context.frame 0 edge inner.normalize := by
  cases edge with
  | slot constructor position siblings =>
    apply congrArg (fun edge => Mettapedia.CategoryTheory.MixedResidue.Context.frame 0 edge inner.normalize)
    apply congrArg (Frame.slot constructor position)
    funext other absent
    exact Quotient.out_eq (siblings other absent)

def reifyMixed {source target : Interface signature Parallel} :
    Mettapedia.CategoryTheory.MixedResidue.Context
      (fun vertex : Interface signature Parallel => ResiduePayload (Parallel := Parallel) vertex.sort) source target →
    RawContext signature Parallel source.sort target.sort
  | .parallel supplied => RawContext.addBag supplied .hole
  | .frame supplied edge inner => RawContext.addBag supplied (edge.rawFrame (reifyMixed inner))

theorem normalize_reifyMixed {source target : Interface signature Parallel}
    (context : Mettapedia.CategoryTheory.MixedResidue.Context
      (fun vertex : Interface signature Parallel => ResiduePayload (Parallel := Parallel) vertex.sort) source target) :
    (reifyMixed context).normalize = context := by
  induction context with
  | parallel supplied =>
    rw [reifyMixed, RawContext.normalize_addBag]
    change Mettapedia.CategoryTheory.MixedResidue.Context.parallel (supplied + 0) = _
    rw [add_zero]
  | frame supplied edge inner inductionHypothesis =>
    rw [reifyMixed, RawContext.normalize_addBag, Frame.normalize_rawFrame, inductionHypothesis]
    change Mettapedia.CategoryTheory.MixedResidue.Context.frame (supplied + 0) edge inner = _
    rw [add_zero]

end Mettapedia.OSLF.SortedCommutative
