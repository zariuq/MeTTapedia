import Mettapedia.CategoryTheory.MixedResidueSeparatedRootIPO
import Mettapedia.OSLF.Framework.SortedCommutativeContextReactiveSystem

/-!
# Complete raw IPOs with a free frame and an outer parallel reaction

The independently generated raw context category is compared through its
earned full normalization. A genuine constructor frame with no outer
residue and a pure parallel context have distinct normal outer shapes.
Their actual commuting bound is therefore its complete relative pushout,
including every competing apex and every mediator equation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.SortedCommutative

open _root_.CategoryTheory
open Mettapedia.GSLT.RelativePushout

universe u v

variable {signature : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
variable {Parallel : signature.Srt → Prop}

theorem raw_frame_parallel_isIdemPushout
    {source : signature.Srt} (constructor : signature.Constructor)
    (position : Fin (signature.arity constructor))
    (siblings : (other : Fin (signature.arity constructor)) → other ≠ position →
      Term signature Parallel (signature.input constructor other))
    (inner : RawContext signature Parallel source (signature.input constructor position))
    (parallel : Parallel (signature.output constructor))
    (sibling : Term signature Parallel (signature.output constructor))
    (first : Class signature Parallel source)
    (second : Class signature Parallel (signature.output constructor))
    (square :
      (contextClassOf (.frame constructor position siblings inner)).fill first =
        (contextClassOf (.left parallel .hole sibling)).fill second) :
    IsIdemPushout (C := RawObject signature Parallel)
      (RawArrow.value first) (RawArrow.value second)
      (RawArrow.context (contextClassOf (.frame constructor position siblings inner)))
      (RawArrow.context (contextClassOf (.left parallel .hole sibling)))
      (congrArg RawArrow.value square) := by
  classical
  let left : RawContext signature Parallel source (signature.output constructor) :=
    .frame constructor position siblings inner
  let right : RawContext signature Parallel (signature.output constructor)
      (signature.output constructor) := .left parallel .hole sibling
  have readings : (mixedAction signature Parallel).read left.normalize first =
      (mixedAction signature Parallel).read right.normalize second :=
    (ContextClass.normalize_filling (contextClassOf left) first).trans
      (square.trans
        (ContextClass.normalize_filling (contextClassOf right) second).symm)
  have normalized := Mettapedia.CategoryTheory.MixedResidue.frame_parallel_isIdemPushout
    (mixedAction signature Parallel)
    first second (Frame.slot constructor position (fun other absent => classOf (siblings other absent)))
    inner.normalize (residueOf parallel sibling)
    (by simpa only [left, right, RawContext.normalize, MixedContext.addResidue,
      Mettapedia.CategoryTheory.MixedResidue.Context.addOuter, add_zero] using readings)
  apply (raw_idemPushout_iff_normalized (congrArg RawArrow.value square)).mpr
  simpa only [normalizeFunctor, normalizeArrow, normalizeContext, contextClassOf, Quotient.lift_mk,
    Mettapedia.CategoryTheory.MixedResidue.valueArrow,
    Mettapedia.CategoryTheory.MixedResidue.contextArrow, RawContext.normalize,
    MixedContext.addResidue, Mettapedia.CategoryTheory.MixedResidue.Context.addOuter,
    add_zero] using normalized

end Mettapedia.OSLF.SortedCommutative
