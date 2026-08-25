import Mettapedia.Cybernetics.DistinctionConservation
import Mettapedia.GSLT.Dynamics.AnswerEffect
import Mettapedia.GSLT.Dynamics.ProofRelevantNeedProfile

/-!
# Distinction conservation for proof-relevant answers

Answer-effect faithfulness is connected to the general distinction-
conservation criterion without redefining either concept.  The canonical
answer quotients provide two separating controls:

* lists to multisets erase enumeration order;
* multisets to finite support erase occurrence multiplicity.

Revision decoration is a positive operational witness.  It changes artifact
identity while retaining the request and occurrence identity, and its existing
forgetting map is a left inverse.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.AnswerEffects

open Mettapedia.Cybernetics

universe u

namespace AnswerEffect.Morphism

/-- An answer-effect morphism conserves exact distinctions at every answer
type. -/
def DistinctionConserving
    {source target : AnswerEffect.{u}}
    (morphism : AnswerEffect.Morphism source target) : Prop :=
  ∀ {alpha : Type u},
    Distinction.Conserves
      (Distinction.inequality (source.Carrier alpha))
      (Distinction.inequality (target.Carrier alpha))
      (@morphism.map alpha)

/-- The independently defined operational faithfulness condition is exactly
the inequality-distinction conservation law. -/
theorem distinctionConserving_iff_faithful
    {source target : AnswerEffect.{u}}
    (morphism : AnswerEffect.Morphism source target) :
    morphism.DistinctionConserving ↔ morphism.Faithful := by
  constructor
  · intro conserves alpha
    exact (Distinction.conserves_inequality_iff_injective
      (@morphism.map alpha)).mp conserves
  · intro faithful alpha
    exact (Distinction.conserves_inequality_iff_injective
      (@morphism.map alpha)).mpr faithful

theorem id_distinctionConserving (effect : AnswerEffect.{u}) :
    (AnswerEffect.Morphism.id effect).DistinctionConserving := by
  rw [distinctionConserving_iff_faithful]
  intro alpha
  exact Function.injective_id

theorem comp_distinctionConserving
    {first second third : AnswerEffect.{u}}
    (earlier : AnswerEffect.Morphism first second)
    (later : AnswerEffect.Morphism second third)
    (earlierConserves : earlier.DistinctionConserving)
    (laterConserves : later.DistinctionConserving) :
    (earlier.comp later).DistinctionConserving := by
  rw [distinctionConserving_iff_faithful]
  intro alpha
  exact ((distinctionConserving_iff_faithful later).mp laterConserves).comp
    ((distinctionConserving_iff_faithful earlier).mp earlierConserves)

end AnswerEffect.Morphism

/-! ## Real losses in the canonical answer chain -/

theorem listToBag_not_distinctionConserving :
    ¬ listToBag.{0}.DistinctionConserving := by
  rw [AnswerEffect.Morphism.distinctionConserving_iff_faithful]
  exact listToBag_not_faithful

theorem bagToSupport_not_distinctionConserving :
    ¬ bagToSupport.{0}.DistinctionConserving := by
  rw [AnswerEffect.Morphism.distinctionConserving_iff_faithful]
  exact bagToSupport_not_faithful

/-- Enumeration order is a source distinction lost by the list-to-bag
quotient. -/
theorem listToBag_order_collision :
    ([false, true] : List Bool) ≠ [true, false] ∧
      listToBag.{0}.map ([false, true] : List Bool) =
        listToBag.{0}.map ([true, false] : List Bool) := by
  constructor
  · simp
  · change
      (([false, true] : List Bool) : Multiset Bool) =
        (([true, false] : List Bool) : Multiset Bool)
    decide

/-- Occurrence multiplicity is a source distinction lost by the bag-to-
support quotient. -/
theorem bagToSupport_multiplicity_collision :
    ({()} : Multiset Unit) ≠ {(), ()} ∧
      bagToSupport.{0}.map ({()} : Multiset Unit) =
        bagToSupport.{0}.map ({(), ()} : Multiset Unit) := by
  constructor
  · intro equal
    have cardEqual := congrArg Multiset.card equal
    simp at cardEqual
  · classical
    simp

end Mettapedia.GSLT.Dynamics.AnswerEffects

namespace Mettapedia.GSLT.Dynamics.ProofRelevantNeed

open Mettapedia.Cybernetics
open Mettapedia.GSLT.Dynamics.OccurrenceSemantics

universe uSpace uRequest uAnswer

variable {Space : Type uSpace} {Request : Type uRequest}
  {Answer : Type uAnswer}

/-- Revision decoration is a real positive witness: it conserves every exact
occurrence-term distinction because the pre-existing forgetting map is a left
inverse. -/
theorem decorateRevision_distinctionConserving
    (source : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying Space Request) :
    Distinction.Conserves
      (Distinction.inequality (OccurrenceTerm source))
      (Distinction.inequality (RevisionedOccurrenceTerm source keying))
      (decorateRevision source keying) :=
  (Distinction.conserves_inequality_iff_injective _).mpr
    (decorateRevision_injective source keying)

end Mettapedia.GSLT.Dynamics.ProofRelevantNeed

#print axioms Mettapedia.GSLT.Dynamics.AnswerEffects.AnswerEffect.Morphism.distinctionConserving_iff_faithful
#print axioms Mettapedia.GSLT.Dynamics.AnswerEffects.bagToSupport_multiplicity_collision
#print axioms Mettapedia.GSLT.Dynamics.ProofRelevantNeed.decorateRevision_distinctionConserving
