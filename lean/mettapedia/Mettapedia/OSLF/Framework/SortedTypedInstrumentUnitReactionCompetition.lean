import Mettapedia.OSLF.Framework.SortedTypedInstrumentOriginalProbeTargetSupport
import Mettapedia.OSLF.Syntax.SortedCommutativeSeparatedRootIPO

/-!
# Actual typed unit-rule competition with a complete get assay

At an independently designated parallel result sort, an authored binary Cut
of two units has the source unit class. A genuine outer parallel reaction
places it beside the entire typed get assay. The frame-versus-parallel IPO
universal property proves the competing firing, retaining its supplied
origin, full heterogeneous bundle, whole assay and original reactum.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstruments

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RedexRelativeCongruence

universe u v w

variable {source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
  {Parallel : source.Srt → Prop} {Origins : Type w}

def unitSourceRule {sort : source.Srt} (parallel : Parallel sort) (reactum : Term source Parallel sort) :
    ReactionRule (.origin : SourceCategory source Parallel) where
  codomain := .interface sort
  redex := RawArrow.value (classOf (.cut parallel (.zero parallel) (.zero parallel)))
  reactum := RawArrow.value (classOf reactum)

theorem unitSourceRule_redex_class {sort : source.Srt} (parallel : Parallel sort)
    (reactum : Term source Parallel sort) :
    (unitSourceRule parallel reactum).redex =
      RawArrow.value (classOf (.zero parallel : Term source Parallel sort)) :=
  congrArg RawArrow.value (Quotient.sound (Equation.unit parallel (.zero parallel)))

def getAssay (head : SourceHead source Parallel) (arguments : Arguments head)
    (position : Fin (headArity head)) :
    Value (source := source) (Parallel := Parallel) (.original (headInput head position)) :=
  cut (.get head position) (probe (.get head position)) (bundle head arguments)

def unitGetReaction (head : SourceHead source Parallel) (arguments : Arguments head)
    (position : Fin (headArity head)) (parallel : Parallel (headInput head position)) :
    (.interface (.original (headInput head position)) : ContextCategory source Parallel) ⟶
      .interface (.original (headInput head position)) :=
  RawArrow.context (contextClassOf (RawContext.left (signature := signature source Parallel)
    (Parallel := NativeParallel) (sort := .original (headInput head position))
      parallel .hole (getAssay head arguments position)))

theorem unit_get_square (head : SourceHead source Parallel) (arguments : Arguments head)
    (position : Fin (headArity head)) (parallel : Parallel (headInput head position))
    (reactum : Term source Parallel (headInput head position)) :
    (RawArrow.value (classOf (bundle head arguments)) : (.origin : ContextCategory source Parallel) ⟶
        .interface (.arguments head)) ≫ probeLabel (.get head position) =
      (Source.mapReactionRule (unitSourceRule parallel reactum)).redex ≫
        unitGetReaction head arguments position parallel := by
  have redexZero : (Source.mapReactionRule (unitSourceRule parallel reactum)).redex =
      RawArrow.value (classOf (.zero parallel :
        Value (source := source) (Parallel := Parallel) (.original (headInput head position)))) :=
    congrArg (inclusion source Parallel).map (unitSourceRule_redex_class parallel reactum)
  rw [redexZero]
  apply congrArg RawArrow.value
  have leftRead := congrArg classOf (probeContext_fill (.get head position) (bundle head arguments))
  change classOf ((probeContext (.get head position)).fill (bundle head arguments)) =
    classOf (.cut (signature := signature source Parallel) (Parallel := NativeParallel)
      (sort := .original (headInput head position))
      parallel (.zero parallel) (getAssay head arguments position))
  exact leftRead.trans (Quotient.sound
    ((Equation.comm (signature := signature source Parallel) (Parallel := NativeParallel)
      (sort := .original (headInput head position)) parallel
      (.zero parallel) (getAssay head arguments position)).trans
        (Equation.unit (signature := signature source Parallel) (Parallel := NativeParallel)
          (sort := .original (headInput head position)) parallel (getAssay head arguments position)))).symm

def unitGetFiring (origin : Origins) (head : SourceHead source Parallel) (arguments : Arguments head)
    (position : Fin (headArity head)) (parallel : Parallel (headInput head position))
    (reactum : Term source Parallel (headInput head position)) :
    Source.FiringAt Origins (fun _ => Source.mapReactionRule (unitSourceRule parallel reactum))
      (RawArrow.value (classOf (bundle head arguments)) :
        (.origin : ContextCategory source Parallel) ⟶ .interface (.arguments head))
      (probeLabel (.get head position)) where
  occurrence := origin
  reaction := unitGetReaction head arguments position parallel
  square := unit_get_square head arguments position parallel reactum
  minimal := by
    change Mettapedia.GSLT.RelativePushout.IsIdemPushout (C := ContextCategory source Parallel)
      (RawArrow.value (classOf (bundle head arguments)))
      (RawArrow.value (classOf (embed (.cut parallel (.zero parallel) (.zero parallel)))))
      (RawArrow.context (contextClassOf (probeContext (.get head position))))
      (RawArrow.context (contextClassOf (RawContext.left (signature := signature source Parallel)
        (Parallel := NativeParallel) (sort := .original (headInput head position))
          parallel .hole (getAssay head arguments position)))) _
    unfold probeContext
    apply raw_frame_parallel_isIdemPushout
      (signature := signature source Parallel) (Parallel := NativeParallel)
      (Constructor.cut (.get head position)) 1
    exact RawArrow.value.inj (unit_get_square head arguments position parallel reactum)

theorem unitGetFiring_complete_result (origin : Origins) (head : SourceHead source Parallel)
    (arguments : Arguments head) (position : Fin (headArity head))
    (parallel : Parallel (headInput head position)) (reactum : Term source Parallel (headInput head position)) :
    (unitGetFiring origin head arguments position parallel reactum).result =
      RawArrow.value (classOf (.cut (signature := signature source Parallel) (Parallel := NativeParallel)
        (sort := .original (headInput head position))
        parallel (embed reactum) (getAssay head arguments position))) := rfl

theorem unitGetFiring_observerCount (origin : Origins) (head : SourceHead source Parallel)
    (arguments : Arguments head) (position : Fin (headArity head))
    (parallel : Parallel (headInput head position)) (reactum : Term source Parallel (headInput head position)) :
    arrowObserverCount (unitGetFiring origin head arguments position parallel reactum).result =
      3 + ∑ other, observerCount (arguments other) := by
  rw [unitGetFiring_complete_result]
  change observerCount (embed reactum) + observerCount (getAssay head arguments position) = _
  rw [observerCount_embed, zero_add, getAssay, observerCount_probeCut, observerCount_bundle]
  omega

theorem unitGetFiring_distinct_origins (first second : Origins) (different : first ≠ second)
    (head : SourceHead source Parallel) (arguments : Arguments head) (position : Fin (headArity head))
    (parallel : Parallel (headInput head position)) (reactum : Term source Parallel (headInput head position)) :
    unitGetFiring first head arguments position parallel reactum ≠
      unitGetFiring second head arguments position parallel reactum :=
  fun same => different (congrArg Source.FiringAt.occurrence same)

end Mettapedia.OSLF.Framework.SortedTypedInstruments
