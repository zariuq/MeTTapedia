import Mettapedia.GSLT.LanguageDef.Cost
import Mettapedia.GSLT.Core.NonFactorization
import Mettapedia.GSLT.LanguageDef.CostCanonicalOccurrenceTrace
import Mettapedia.GSLT.LanguageDef.CostHereditaryContextRoute

/-! PROBES for the duplication findings. -/

open Mettapedia.GSLT.Core.NonFactorization

namespace Mettapedia.Algebra

/-- PROBE D1. `WorkSpan.ForgetsObservation` is exactly
`Nonempty (NonTrivialFiber ValuedRun.value (observe ∘ ValuedRun.payload))`
from the PRE-EXISTING `Mettapedia/GSLT/Core/NonFactorization.lean:60`. -/
example {Payload Attribute : Type} (observe : Payload → Attribute) :
    WorkSpan.ForgetsObservation observe ↔
      Nonempty (NonTrivialFiber
        (fun run : WorkSpan.ValuedRun Payload => run.value)
        (fun run : WorkSpan.ValuedRun Payload => observe run.payload)) :=
  ⟨fun ⟨l, r, same, diff⟩ => ⟨⟨l, r, same, diff⟩⟩,
   fun ⟨f⟩ => ⟨f.left, f.right, f.sameShadow, f.differentValue⟩⟩

/-- PROBE D2. The pre-existing form is STRICTLY STRONGER: it concludes
`¬ Factors`, the non-existence of ANY recovery function, where
`ForgetsObservation` concludes only that one pair collides. -/
example {Payload Attribute : Type} (observe : Payload → Attribute)
    {first second : Payload} (separates : observe first ≠ observe second) :
    ¬ Factors (fun run : WorkSpan.ValuedRun Payload => run.value)
        (fun run : WorkSpan.ValuedRun Payload => observe run.payload) :=
  NonTrivialFiber.not_factors ⟨⟨first, 0⟩, ⟨second, 0⟩, rfl, separates⟩

/-- PROBE D3. Likewise for the receipt schema: the honest statement of
"omission is undetectability" is a non-factorization, and it is available. -/
example {Execution Record Attribute : Type}
    (schema : Execution → Record) (observe : Execution → Attribute)
    {left right : Execution}
    (conflated : schema left = schema right)
    (differs : observe left ≠ observe right) :
    ¬ Factors schema observe :=
  NonTrivialFiber.not_factors ⟨left, right, conflated, differs⟩

/-- PROBE D4. And for occurrences: the honest form of "values do not determine
the correspondence" is that the frontier-value map does not factor. -/
example : ¬ Factors (fun relabel : Fin 2 → Fin 2 =>
      fun index => OccurrenceIdentity.duplicateFrontier (relabel index))
    (fun relabel : Fin 2 → Fin 2 => relabel) :=
  NonTrivialFiber.not_factors
    ⟨id, OccurrenceIdentity.exchange, rfl,
      fun equal => OccurrenceIdentity.exchange_ne_id equal.symm⟩

end Mettapedia.Algebra

namespace Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

/-- PROBE D5. `keyDepthThroughContext` (TwoDepthRestorationApex.lean:545)
computes exactly the PRE-EXISTING `keyedCanonicalHoleDepth`
(CostCanonicalOccurrenceTrace.lean:834) — same clauses, different name. -/
theorem probe_keyDepth_dup (declaration : ReflectivePresentationDecl) :
    ∀ (depth : Nat) (context : OneHoleContext),
      CostStaticAtomKeyCospan.keyDepthThroughContext declaration depth context =
        keyedCanonicalHoleDepth declaration depth context
  | _, .hole => rfl
  | _, .apply _ _ inner _ => probe_keyDepth_dup declaration _ inner
  | _, .lambda _ inner => probe_keyDepth_dup declaration _ inner
  | _, .multiLambda _ _ inner => probe_keyDepth_dup declaration _ inner
  | _, .substBody inner _ => probe_keyDepth_dup declaration _ inner
  | _, .substReplacement _ inner => probe_keyDepth_dup declaration _ inner
  | _, .collection _ _ inner _ _ => probe_keyDepth_dup declaration _ inner

-- PROBE D6. A PRE-EXISTING two-depth context function already exists, with a
-- lifting lemma. So "carry two depths through a one-hole context" was solved.
#check @OneHoleContext.canonicalizeHoleDepths
#check @OneHoleContext.canonicalizeByDepths_fill_congr
#check @canonicalizeByAt_fill_congr

/-- PROBE D7. The new `canonicalizeByDepths_foreignQuote_preserves_depth` stops
one step short; the PRE-EXISTING `finishNormalizeReflectiveApply_of_ne_quote`
finishes it, so the lemma consumers actually want is available today. -/
example {Key : Type} [LinearOrder Key]
    (key : Nat → Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl) (foreignQuote : String)
    (foreign : foreignQuote ≠ declaration.quoteConstructor)
    (availableDepth scopeDepth : Nat) (arguments : List Pattern) :
    canonicalizeByDepths key declaration availableDepth scopeDepth
        (.apply foreignQuote arguments) =
      .apply foreignQuote
        (canonicalizeListByDepths key declaration availableDepth scopeDepth
          arguments) := by
  rw [canonicalizeByDepths_foreignQuote_preserves_depth key declaration
    foreignQuote foreign]
  exact finishNormalizeReflectiveApply_of_ne_quote declaration foreign _

end Mettapedia.GSLT.LanguageDef
