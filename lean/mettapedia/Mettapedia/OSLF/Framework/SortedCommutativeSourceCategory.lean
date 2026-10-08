import Mettapedia.OSLF.Syntax.SortedCommutativeSourceContexts

/-!
# The actual source-category inclusion

The original independently formed term/context quotient embeds by a genuine
functor. Complete source filling and composition earn its action laws; the
separate syntax retractions earn faithfulness. The original source itself
has all redex RPOs and literal all-context bisimulation congruence. No claim
reflects extended observations or lifts arbitrary extended mediators back
into the source category.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedCommutativeInstruments.Source

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RelativePushout Mettapedia.GSLT.RedexRelativeCongruence

universe u

variable {Symbols : Type u} {arity : Symbols → Nat}

abbrev SourceCategory := RawObject (signature arity) (Parallel arity)

def objectEmbedding : SourceCategory (arity := arity) → ContextCategory arity
  | .origin => .origin
  | .interface _ => .interface .base

def valueEmbedding {sort : (signature arity).Srt} :
    Class (signature arity) (Parallel arity) sort → SortedCommutativeInstruments.ValueClass arity .base :=
  Quotient.map embed (fun _ _ equation => embed_equation equation)

def contextClassEmbedding {source target : (signature arity).Srt} :
    ContextClass (signature arity) (Parallel arity) source target →
      ContextClass (SortedCommutativeInstruments.signature arity) (SortedCommutativeInstruments.Parallel arity) .base .base :=
  Quotient.map embedContext (fun _ _ equation => embedContext_equation equation)

def arrowEmbedding : {source target : SourceCategory (arity := arity)} →
    (source ⟶ target) → (objectEmbedding source ⟶ objectEmbedding target)
  | _, _, .identity => .identity
  | _, _, .value supplied => RawArrow.value (valueEmbedding supplied)
  | _, _, .context supplied => RawArrow.context (contextClassEmbedding supplied)

def inclusion : SourceCategory (arity := arity) ⥤ ContextCategory arity where
  obj := objectEmbedding
  map := arrowEmbedding
  map_id object := by cases object <;> rfl
  map_comp first second := by
    cases first with
    | identity => rfl
    | value supplied =>
      cases second with
      | context suppliedContext =>
        refine Quotient.inductionOn₂ supplied suppliedContext ?_
        intro raw suppliedContext
        exact congrArg RawArrow.value (congrArg classOf (embedContext_fill suppliedContext raw).symm)
    | context inner =>
      cases second with
      | context outer =>
        refine Quotient.inductionOn₂ inner outer ?_
        intro before after
        exact congrArg RawArrow.context (congrArg contextClassOf (embedContext_comp before after).symm)

instance inclusion_faithful : (inclusion (arity := arity)).Faithful where
  map_injective := by
    intro source target first second same
    cases source with
    | origin =>
      cases target with
      | origin => cases first; cases second; rfl
      | interface sort =>
        cases sort with
        | up sort =>
          cases sort
          cases first with
          | value before =>
            cases second with
            | value after => exact congrArg RawArrow.value (classEmbedding_injective (RawArrow.value.inj same))
    | interface source =>
      cases target with
      | origin => cases first
      | interface target =>
        cases source with
        | up source =>
          cases source
          cases target with
          | up target =>
            cases target
            cases first with
            | context before =>
              cases second with
              | context after => exact congrArg RawArrow.context (contextEmbedding_injective (RawArrow.context.inj same))

theorem source_redex_relativePushouts {first second : SourceCategory (arity := arity)}
    (agent : (.origin : SourceCategory (arity := arity)) ⟶ first)
    (redex : (.origin : SourceCategory (arity := arity)) ⟶ second) : HasRelativePushouts agent redex :=
  raw_redex_relativePushouts agent redex

theorem source_bisimulation_congruence
    (rules : ReactionRule (.origin : SourceCategory (arity := arity)) → Prop)
    {source target : SourceCategory (arity := arity)}
    {first second : (.origin : SourceCategory (arity := arity)) ⟶ source}
    (related : IPOBisimilar rules first second) (context : source ⟶ target) :
    IPOBisimilar rules (first ≫ context) (second ≫ context) :=
  raw_bisimulation_congruence rules related context

theorem inclusion_closed_readout (supplied : Value arity) :
    inclusion.map (RawArrow.value (classOf supplied) : (.origin : SourceCategory (arity := arity)) ⟶ .interface (ULift.up ())) =
      (RawArrow.value (classOf (embed supplied)) : (.origin : ContextCategory arity) ⟶ .interface .base) := rfl

theorem inclusion_context_readout (supplied : Context (arity := arity)) :
    inclusion.map (RawArrow.context (contextClassOf supplied) :
        (.interface (ULift.up ()) : SourceCategory (arity := arity)) ⟶ .interface (ULift.up ())) =
      (RawArrow.context (contextClassOf (embedContext supplied)) :
        (.interface .base : ContextCategory arity) ⟶ .interface .base) := rfl

end Mettapedia.OSLF.Framework.SortedCommutativeInstruments.Source
