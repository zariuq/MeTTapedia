import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalPartnerObservations

/-!
# Closed parallel congruence of complete partner observations

A full partner label absorbs a fixed closed parallel frame. A relation
extended by its framed pairs therefore matches each contextual step and
returns its targets to the original relation. This earns closed parallel
congruence for partner bisimilarity and complete final observations. It is
not a congruence theorem for quotation, input bodies, or an unrestricted
binding rule format.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalPartnerCongruence

open CanonicalBag CanonicalReaction CanonicalPartnerCoalgebra CanonicalPartnerObservations
open LanguageDefGSLT

/-- Original pairs remain available after the first contextual reaction. -/
def framedRelation (relation : Bag → Bag → Prop) (frame : Bag) : Bag → Bag → Prop :=
  fun source other => relation source other ∨
    ∃ first second, relation first second ∧
      source = append first frame ∧ other = append second frame

/-- The expanded relation is earned using actual associativity of canonical inventories. -/
theorem framed_admitted (relation : Bag → Bag → Prop) (frame : Bag)
    (admitted : Admitted relation) : Admitted (framedRelation relation frame) := by
  intro source other held partner
  rcases held with original | ⟨first, second, paired, rfl, rfl⟩
  · constructor
    · intro target reaction
      obtain ⟨matched, matchedReaction, paired⟩ :=
        (admitted source other original partner).1 target reaction
      exact ⟨matched, matchedReaction, Or.inl paired⟩
    · intro target reaction
      obtain ⟨matched, matchedReaction, paired⟩ :=
        (admitted source other original partner).2 target reaction
      exact ⟨matched, matchedReaction, Or.inl paired⟩
  · constructor
    · intro target reaction
      rw [append_assoc] at reaction
      obtain ⟨matched, matchedReaction, relatedTargets⟩ :=
        (admitted first second paired (append frame partner)).1 target reaction
      rw [← append_assoc] at matchedReaction
      exact ⟨matched, matchedReaction, Or.inl relatedTargets⟩
    · intro target reaction
      rw [append_assoc] at reaction
      obtain ⟨matched, matchedReaction, relatedTargets⟩ :=
        (admitted first second paired (append frame partner)).2 target reaction
      rw [← append_assoc] at matchedReaction
      exact ⟨matched, matchedReaction, Or.inl relatedTargets⟩

theorem bisimilar_append {source other : Bag} (related : Bisimilar source other) (frame : Bag) :
    Bisimilar (append source frame) (append other frame) := by
  obtain ⟨relation, admitted, held⟩ := related
  exact ⟨framedRelation relation frame, framed_admitted relation frame admitted,
    Or.inr ⟨source, other, held, rfl, rfl⟩⟩

theorem observation_append {source other : Bag} (same : observe source = observe other)
    (frame : Bag) : observe (append source frame) = observe (append other frame) :=
  (observation_eq_iff_bisimilar _ _).2
    (bisimilar_append ((observation_eq_iff_bisimilar source other).1 same) frame)

/-- Both independently supplied components may be replaced in a closed parallel context. -/
theorem bisimilar_append_both {source source' partner partner' : Bag}
    (left : Bisimilar source source') (right : Bisimilar partner partner') :
    Bisimilar (append source partner) (append source' partner') := by
  apply bisimilar_trans (bisimilar_append left partner)
  have swapped := bisimilar_append right source'
  simpa only [append_comm partner source', append_comm partner' source'] using swapped

theorem public_parallel_congruent {source other : RhoProcess}
    (related :
      (ParallelContextAdequacy.partnerSystem PEmpty.{1} (fun atom => atom.elim)).Bisimilar
        source other) (frame : RhoProcess) :
    (ParallelContextAdequacy.partnerSystem PEmpty.{1} (fun atom => atom.elim)).Bisimilar
      (ParallelContextAdequacy.par source frame) (ParallelContextAdequacy.par other frame) := by
  apply public_bisimilar_of_canonical
  rw [fromProcess_par, fromProcess_par]
  exact bisimilar_append (canonical_bisimilar_of_public related) (fromProcess frame)

theorem public_observation_parallel {source other : RhoProcess}
    (same : observe (fromProcess source) = observe (fromProcess other)) (frame : RhoProcess) :
    observe (fromProcess (ParallelContextAdequacy.par source frame)) =
      observe (fromProcess (ParallelContextAdequacy.par other frame)) := by
  rw [fromProcess_par, fromProcess_par]
  exact observation_append same (fromProcess frame)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalPartnerCongruence
