import Mettapedia.OSLF.Framework.SortedTypedInstrumentKitTransitions

/-!
# Instrument-set monotonicity for the actual typed IPO systems

A larger kit's bisimulation restricts to all old interfaces and labels.
Every old step maps to the larger system, and every matched larger step
reconstructs an old declaration and its complete old target by the earned
hereditary support argument. This proves the downward behavioral implication
for the actual supported categories, independently of structural test syntax.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstruments.Kit

open _root_.CategoryTheory
open Mettapedia.GSLT.RedexRelativeCongruence

universe u v w z

variable {source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
  {Parallel : source.Srt → Prop} {OriginalOrigins : Type z} {NativeOrigins : Type w}

theorem bisimulation_monotone {first second : Policy source Parallel}
    (subkit : ∀ head, first head → second head)
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    {interface : Object first} {before after : origin first ⟶ interface}
    (related : IPOBisimilar (categoryRules (NativeOrigins := NativeOrigins) originalRules second)
      ((expand subkit).map before) ((expand subkit).map after)) :
    IPOBisimilar (categoryRules (NativeOrigins := NativeOrigins) originalRules first) before after := by
  let relation : (interface : Object first) →
      (origin first ⟶ interface) → (origin first ⟶ interface) → Prop :=
    fun _ left right => IPOBisimilar (categoryRules (NativeOrigins := NativeOrigins) originalRules second)
      ((expand subkit).map left) ((expand subkit).map right)
  refine ⟨relation, ?_, related⟩
  intro current left right currentRelated
  constructor
  · intro nextInterface label next step
    have newStep := category_step_maps subkit originalRules step
    obtain ⟨matched, matchedStep, successors⟩ := ipoBisimilar_forward currentRelated newStep
    obtain ⟨oldMatched, completeReadout, oldStep⟩ := category_step_reflect subkit originalRules matchedStep
    refine ⟨oldMatched, oldStep, ?_⟩
    change IPOBisimilar (categoryRules (NativeOrigins := NativeOrigins) originalRules second)
      ((expand subkit).map next) ((expand subkit).map oldMatched)
    exact completeReadout.symm ▸ successors
  · intro nextInterface label next step
    have newStep := category_step_maps subkit originalRules step
    obtain ⟨matched, matchedStep, successors⟩ := ipoBisimilar_backward currentRelated newStep
    obtain ⟨oldMatched, completeReadout, oldStep⟩ := category_step_reflect subkit originalRules matchedStep
    refine ⟨oldMatched, oldStep, ?_⟩
    change IPOBisimilar (categoryRules (NativeOrigins := NativeOrigins) originalRules second)
      ((expand subkit).map oldMatched) ((expand subkit).map next)
    exact completeReadout.symm ▸ successors

theorem every_supported_context_preserves_bisimilarity (opened : Policy source Parallel)
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    {before after : Object opened} {left right : origin opened ⟶ before}
    (related : IPOBisimilar (categoryRules (NativeOrigins := NativeOrigins) originalRules opened) left right)
    (context : before ⟶ after) :
    IPOBisimilar (categoryRules (NativeOrigins := NativeOrigins) originalRules opened)
      (left ≫ context) (right ≫ context) :=
  bisimulation_context_congruence _ related context

end Mettapedia.OSLF.Framework.SortedTypedInstruments.Kit
