import Mettapedia.OSLF.Syntax.SortedCommutativeSeparatedRootIPO
import Mettapedia.OSLF.Framework.SortedCommutativeSourceFiringComparison
import Mettapedia.OSLF.Framework.SortedCommutativeProbeReconstructionReadout

/-!
# A source unit reaction competing with a complete administrative assay

The independently authored original rule has a literal binary source Cut
redex, both operands the source unit. Its source equation class is the unit.
An outer parallel reaction places this redex beside the entire get assay.
The two distinct outer context shapes earn actual IPO minimality, rather
than merely a matching equation. The complete firing retains its supplied
origin and the additional source reactum beside the whole original assay.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedCommutativeInstruments

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RedexRelativeCongruence
open Support
open scoped BigOperators

universe u w

variable {Symbols : Type u} {arity : Symbols → Nat} {Origins : Type w}

def unitSourceRule (reactum : Source.Value arity) :
    ReactionRule (.origin : Source.SourceCategory (arity := arity)) where
  codomain := .interface (ULift.up ())
  redex := RawArrow.value (classOf (.cut rfl (.zero rfl) (.zero rfl) : Source.Value arity))
  reactum := RawArrow.value (classOf reactum)

theorem unitSourceRule_redex_class (reactum : Source.Value arity) :
    (unitSourceRule reactum).redex =
      RawArrow.value (classOf (.zero rfl : Source.Value arity)) :=
  congrArg RawArrow.value (Quotient.sound (Equation.unit
    (signature := Source.signature arity) (Parallel := Source.Parallel arity)
    (show Source.Parallel arity (ULift.up ()) from rfl) (.zero rfl)))

def getAssay (constructor : SourceSymbol Symbols)
    (arguments : Fin (sourceArity arity constructor) → Source.Value arity)
    (position : Fin (sourceArity arity constructor)) : Value arity .base :=
  cut arity (.get constructor position) (probe arity (.get constructor position))
    (bundle arity constructor (fun other => Source.embed (arguments other)))

def unitGetReaction (constructor : SourceSymbol Symbols)
    (arguments : Fin (sourceArity arity constructor) → Source.Value arity)
    (position : Fin (sourceArity arity constructor)) :
    (.interface .base : ContextCategory arity) ⟶ .interface .base :=
  RawArrow.context (contextClassOf (.left rfl .hole (getAssay constructor arguments position)))

theorem unit_get_square (reactum : Source.Value arity) (constructor : SourceSymbol Symbols)
    (arguments : Fin (sourceArity arity constructor) → Source.Value arity)
    (position : Fin (sourceArity arity constructor)) :
    (RawArrow.value (sourceBundle constructor arguments) :
        (.origin : ContextCategory arity) ⟶ .interface (.arguments constructor)) ≫
      getLabel constructor position =
    (Source.mapReactionRule (unitSourceRule reactum)).redex ≫
      unitGetReaction constructor arguments position := by
  have redexZero : (Source.mapReactionRule (unitSourceRule reactum)).redex =
      RawArrow.value (classOf (.zero rfl : Value arity .base)) :=
    congrArg Source.inclusion.map (unitSourceRule_redex_class reactum)
  rw [redexZero]
  apply congrArg RawArrow.value
  have leftRead := congrArg classOf (probeContext_fill arity (.get constructor position)
    (bundle arity constructor (fun other => Source.embed (arguments other))))
  change classOf ((probeContext arity (.get constructor position)).fill
    (bundle arity constructor (fun other => Source.embed (arguments other)))) =
      classOf (.cut (signature := signature arity) (Parallel := Parallel arity)
        rfl (.zero rfl) (getAssay constructor arguments position))
  exact leftRead.trans (Quotient.sound
    ((Equation.comm (signature := signature arity) (Parallel := Parallel arity)
      rfl (.zero rfl) (getAssay constructor arguments position)).trans
      (Equation.unit (signature := signature arity) (Parallel := Parallel arity)
        rfl (getAssay constructor arguments position)))).symm

def unitGetFiring (origin : Origins) (reactum : Source.Value arity)
    (constructor : SourceSymbol Symbols)
    (arguments : Fin (sourceArity arity constructor) → Source.Value arity)
    (position : Fin (sourceArity arity constructor)) :
    Source.FiringEvidence (.origin : ContextCategory arity) Origins
      (fun _ => Source.mapReactionRule (unitSourceRule reactum)) where
  occurrence := origin
  sourceInterface := .interface (.arguments constructor)
  targetInterface := .interface .base
  agent := RawArrow.value (sourceBundle constructor arguments)
  label := getLabel constructor position
  reaction := unitGetReaction constructor arguments position
  square := unit_get_square reactum constructor arguments position
  minimal := by
    change Mettapedia.GSLT.RelativePushout.IsIdemPushout (C := ContextCategory arity)
      (RawArrow.value (sourceBundle constructor arguments))
      (RawArrow.value (Source.classEmbedding
        (classOf (.cut rfl (.zero rfl) (.zero rfl) : Source.Value arity))))
      (RawArrow.context (contextClassOf (probeContext arity (.get constructor position))))
      (RawArrow.context (contextClassOf
        (.left (signature := signature arity) (Parallel := Parallel arity)
          rfl .hole (getAssay constructor arguments position)))) _
    unfold probeContext
    apply raw_frame_parallel_isIdemPushout
      (signature := signature arity) (Parallel := Parallel arity)
      (Constructor.cut (.get constructor position)) 1
    exact RawArrow.value.inj (unit_get_square reactum constructor arguments position)

theorem unitGetFiring_origin (origin : Origins) (reactum : Source.Value arity)
    (constructor : SourceSymbol Symbols)
    (arguments : Fin (sourceArity arity constructor) → Source.Value arity)
    (position : Fin (sourceArity arity constructor)) :
    (unitGetFiring origin reactum constructor arguments position).occurrence = origin := rfl

theorem unitGetFiring_complete_result (origin : Origins) (reactum : Source.Value arity)
    (constructor : SourceSymbol Symbols)
    (arguments : Fin (sourceArity arity constructor) → Source.Value arity)
    (position : Fin (sourceArity arity constructor)) :
    (unitGetFiring origin reactum constructor arguments position).result =
      RawArrow.value (classOf (.cut (signature := signature arity) (Parallel := Parallel arity)
        rfl (Source.embed reactum)
        (getAssay constructor arguments position))) := rfl

theorem getAssay_observerCount (constructor : SourceSymbol Symbols)
    (arguments : Fin (sourceArity arity constructor) → Source.Value arity)
    (position : Fin (sourceArity arity constructor)) :
    observerCount (getAssay constructor arguments position) = 3 := by
  rw [getAssay, observerCount_probeCut, observerCount_bundle]
  simp only [observerCount_embed, Finset.sum_const_zero]
  rfl

theorem unitGetFiring_observerCount (origin : Origins) (reactum : Source.Value arity)
    (constructor : SourceSymbol Symbols)
    (arguments : Fin (sourceArity arity constructor) → Source.Value arity)
    (position : Fin (sourceArity arity constructor)) :
    arrowObserverCount (unitGetFiring origin reactum constructor arguments position).result = 3 := by
  rw [unitGetFiring_complete_result]
  change observerCount (Source.embed reactum) + observerCount (getAssay constructor arguments position) = 3
  rw [observerCount_embed, getAssay_observerCount]

theorem unitGetFiring_distinct_origins (first second : Origins) (different : first ≠ second)
    (reactum : Source.Value arity) (constructor : SourceSymbol Symbols)
    (arguments : Fin (sourceArity arity constructor) → Source.Value arity)
    (position : Fin (sourceArity arity constructor)) :
    unitGetFiring first reactum constructor arguments position ≠
      unitGetFiring second reactum constructor arguments position :=
  fun same => different (congrArg Source.FiringEvidence.occurrence same)

end Mettapedia.OSLF.Framework.SortedCommutativeInstruments
