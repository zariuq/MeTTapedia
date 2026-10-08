import Mettapedia.OSLF.Syntax.SortedCommutativeContextReification

/-!
# Generated context equations reconstructed from normal forms

Both reconstruction directions use the local context equations. Complete
normal-form equality therefore reflects those equations, while equality of a
single ground filling remains insufficient. The resulting equivalence relates
the independently formed raw context quotient to actual mixed contexts.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.SortedCommutative

open Mettapedia.OSLF.SortedConstructors

universe u v

variable {signature : Signature.{u,v}} {Parallel : signature.Srt → Prop}

theorem reifyMixed_addResidue {source target : signature.Srt}
    (context : MixedContext signature Parallel source target)
    (supplied : Multiset (ResiduePayload (signature := signature) (Parallel := Parallel) target)) :
    ContextEquation (reifyMixed (context.addResidue supplied)) (RawContext.addBag supplied (reifyMixed context)) := by
  cases context with
  | parallel previous =>
    exact (RawContext.addBag_add supplied previous RawContext.hole).symm
  | frame previous edge inner =>
    exact (RawContext.addBag_add supplied previous (edge.rawFrame (reifyMixed inner))).symm

theorem reifyMixed_normalize {source target : signature.Srt}
    (context : RawContext signature Parallel source target) :
    ContextEquation (reifyMixed context.normalize) context := by
  induction context with
  | hole => exact RawContext.addBag_zero _
  | frame constructor position siblings inner inductionHypothesis =>
    apply (RawContext.addBag_zero _).trans
    apply ContextEquation.frame constructor position
    · intro other absent
      exact Quotient.exact (Quotient.out_eq (classOf (siblings other absent)))
    · exact inductionHypothesis
  | left parallel inner sibling inductionHypothesis =>
    apply (reifyMixed_addResidue inner.normalize (residueOf parallel sibling)).trans
    apply (RawContext.addBag_congr _ inductionHypothesis).trans
    simp only [RawContext.addBag, dif_pos parallel]
    exact .left parallel (.refl inner) (pile_residueOf parallel sibling)
  | right parallel sibling inner inductionHypothesis =>
    apply (reifyMixed_addResidue inner.normalize (residueOf parallel sibling)).trans
    apply (RawContext.addBag_congr _ inductionHypothesis).trans
    simp only [RawContext.addBag, dif_pos parallel]
    exact (ContextEquation.left parallel (.refl inner) (pile_residueOf parallel sibling)).trans
      (.comm parallel inner sibling)

theorem contextEquation_iff_normalize {source target : signature.Srt}
    (first second : RawContext signature Parallel source target) :
    ContextEquation first second ↔ first.normalize = second.normalize := by
  refine ⟨ContextEquation.normalize, fun same => ?_⟩
  have reconstructed : ContextEquation (reifyMixed first.normalize) (reifyMixed second.normalize) := by
    rw [same]
    exact .refl _
  exact (reifyMixed_normalize first).symm.trans (reconstructed.trans (reifyMixed_normalize second))

def contextEquationSetoid (source target : signature.Srt) : Setoid (RawContext signature Parallel source target) where
  r := ContextEquation
  iseqv := ⟨ContextEquation.refl, ContextEquation.symm, ContextEquation.trans⟩

abbrev ContextClass (signature : Signature.{u,v}) (Parallel : signature.Srt → Prop)
    (source target : signature.Srt) :=
  Quotient (contextEquationSetoid (signature := signature) (Parallel := Parallel) source target)

def contextClassOf {source target : signature.Srt} (context : RawContext signature Parallel source target) :
    ContextClass signature Parallel source target := Quotient.mk _ context

def normalizeContext {source target : signature.Srt} :
    ContextClass signature Parallel source target → MixedContext signature Parallel source target :=
  Quotient.lift RawContext.normalize (fun _ _ equation => equation.normalize)

def contextEquiv (source target : signature.Srt) :
    ContextClass signature Parallel source target ≃ MixedContext signature Parallel source target where
  toFun := normalizeContext
  invFun context := contextClassOf (reifyMixed context)
  left_inv context := Quotient.inductionOn context (fun raw => Quotient.sound (reifyMixed_normalize raw))
  right_inv := normalize_reifyMixed

end Mettapedia.OSLF.SortedCommutative
