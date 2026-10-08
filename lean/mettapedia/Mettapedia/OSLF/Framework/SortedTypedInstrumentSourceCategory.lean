import Mettapedia.OSLF.Framework.SortedTypedInstrumentContextReadout

/-!+# The conservative many-sorted source category inclusion

Every original interface, equation class and complete contextual arrow is
mapped at its declared sort. The actual filling and composition comparisons
earn a genuine functor; independent partial value/context readings earn its
faithfulness. RPO existence and all-source-context congruence hold in the
independently formed source category. Arbitrary extended competitors are not
assumed to have source preimages.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstruments

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RelativePushout Mettapedia.GSLT.RedexRelativeCongruence

universe u v

variable {source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
  {Parallel : source.Srt → Prop}

abbrev SourceCategory (source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v})
    (Parallel : source.Srt → Prop) := RawObject source Parallel

def objectEmbedding : SourceCategory source Parallel → ContextCategory source Parallel
  | .origin => .origin
  | .interface sort => .interface (.original sort)

def arrowEmbedding : {first second : SourceCategory source Parallel} → (first ⟶ second) →
    (objectEmbedding first ⟶ objectEmbedding second)
  | _, _, .identity => .identity
  | _, _, .value supplied => RawArrow.value (classEmbedding supplied)
  | _, _, .context supplied => RawArrow.context (contextEmbedding supplied)

def inclusion (source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v})
    (Parallel : source.Srt → Prop) : SourceCategory source Parallel ⥤ ContextCategory source Parallel where
  obj := objectEmbedding
  map := arrowEmbedding
  map_id object := by cases object <;> rfl
  map_comp first second := by
    cases first with
    | identity => rfl
    | value supplied =>
      cases second with
      | context context => exact congrArg RawArrow.value (contextEmbedding_fill context supplied).symm
    | context before =>
      cases second with
      | context after => exact congrArg RawArrow.context (contextEmbedding_comp before after)

instance inclusion_faithful : (inclusion source Parallel).Faithful where
  map_injective := by
    intro first second before after same
    cases before with
    | identity => cases after; rfl
    | value before =>
      cases after with
      | value after => exact congrArg RawArrow.value (classEmbedding_injective (RawArrow.value.inj same))
    | context before =>
      cases after with
      | context after => exact congrArg RawArrow.context (contextEmbedding_injective (RawArrow.context.inj same))

theorem objectEmbedding_injective :
    Function.Injective (objectEmbedding (source := source) (Parallel := Parallel)) := by
  intro first second same
  cases first <;> cases second <;> cases same <;> rfl

theorem source_redex_relativePushouts {first second : SourceCategory source Parallel}
    (agent : (.origin : SourceCategory source Parallel) ⟶ first)
    (redex : (.origin : SourceCategory source Parallel) ⟶ second) :
    HasRelativePushouts agent redex := raw_redex_relativePushouts agent redex

theorem source_bisimulation_congruence
    (sourceRules : ReactionRule (.origin : SourceCategory source Parallel) → Prop)
    {first second : SourceCategory source Parallel}
    {before after : (.origin : SourceCategory source Parallel) ⟶ first}
    (related : IPOBisimilar sourceRules before after) (context : first ⟶ second) :
    IPOBisimilar sourceRules (before ≫ context) (after ≫ context) :=
  raw_bisimulation_congruence sourceRules related context

theorem inclusion_value_readout {sort : source.Srt} (supplied : Class source Parallel sort) :
    (inclusion source Parallel).map (RawArrow.value supplied :
      (.origin : SourceCategory source Parallel) ⟶ .interface sort) =
        (RawArrow.value (classEmbedding supplied) :
          (.origin : ContextCategory source Parallel) ⟶ .interface (.original sort)) := rfl

theorem inclusion_context_readout {first second : source.Srt}
    (supplied : ContextClass source Parallel first second) :
    (inclusion source Parallel).map (RawArrow.context supplied :
      (.interface first : SourceCategory source Parallel) ⟶ .interface second) =
        (RawArrow.context (contextEmbedding supplied) :
          (.interface (.original first) : ContextCategory source Parallel) ⟶ .interface (.original second)) := rfl

end Mettapedia.OSLF.Framework.SortedTypedInstruments
