import Mettapedia.Enactive.Finite
import Mettapedia.Evidence.TwoLanguage

/-!
# Two-language evidence and enactive abstraction layers

Michael Timothy Bennett's abstraction layer has one vocabulary of facts. Pei
Wang's comparative evidence framework permits distinct belief and evidence
languages. This module gives the exact seam: a two-language layer determines
one shared enactive vocabulary precisely when the semantic images of its two
vocabularies coincide.

The finiteness-free `Enactive.Basic` layer remains primary. The executable
finite theory embeds into it and preserves and reflects completion order; it
cannot equal an abstraction layer whose vocabulary is infinite. Thus finite
enumeration is a checked view, not a claim that a general-purpose system's
possible knowledge has been exhaustively listed.

References:

* P. Wang, *Formalization of Evidence: A Comparative Study*, JAGI 1 (2009).
* M. T. Bennett, *Is Complexity an Illusion?* (2024).
-/

set_option autoImplicit false

namespace Mettapedia.Enactive.TwoLanguageBridge

open Mettapedia.Evidence

universe uWorld uDegree uBelief uEvidence

variable {World : Type uWorld} {Degree : Type uDegree}
  {Belief : Type uBelief} {Evidence : Type uEvidence}

/-- A common one-language projection together with exact receipts that it is
simultaneously the belief-meaning and evidence-meaning vocabulary. -/
structure OneLanguageProjection
    (layer : TwoLanguageLayer World Degree Belief Evidence) where
  abstraction : AbstractionLayer World
  belief_exact :
    abstraction.vocabulary = layer.beliefMeaningVocabulary
  evidence_exact :
    abstraction.vocabulary = layer.evidenceMeaningVocabulary

/-- A common enactive vocabulary exists exactly under Wang's language-
coincidence premise. -/
theorem oneLanguageProjection_nonempty_iff
    (layer : TwoLanguageLayer World Degree Belief Evidence) :
    Nonempty (OneLanguageProjection layer) ↔ layer.LanguagesCoincide := by
  constructor
  · rintro ⟨projection⟩
    exact projection.belief_exact.symm.trans projection.evidence_exact
  · intro coincide
    exact ⟨{
      abstraction := { vocabulary := layer.beliefMeaningVocabulary }
      belief_exact := rfl
      evidence_exact := coincide
    }⟩

/-- A one-vocabulary enactive layer induces a two-language layer only after
the relevance discipline and degree aggregator are supplied. Both syntactic
roles use the same fact carrier in this specialization. -/
def ofAbstractionLayer (layer : AbstractionLayer World)
    (relevant : Fact World → Fact World → Prop)
    (aggregate : Fact World → Set (Fact World) → Degree) :
    TwoLanguageLayer World Degree (Fact World) (Fact World) where
  beliefVocabulary := layer.vocabulary
  evidenceVocabulary := layer.vocabulary
  beliefMeaning := id
  evidenceMeaning := id
  relevant := relevant
  aggregate := aggregate

/-- The one-vocabulary specialization satisfies the coincidence premise. -/
theorem ofAbstractionLayer_languagesCoincide
    (layer : AbstractionLayer World)
    (relevant : Fact World → Fact World → Prop)
    (aggregate : Fact World → Set (Fact World) → Degree) :
    (ofAbstractionLayer layer relevant aggregate).LanguagesCoincide := by
  rfl

/-! ## Finite views do not become foundations -/

namespace Finite

variable [Fintype World] [DecidableEq World]

/-- The abstract vocabulary represented by an executable finite layer is
finite. -/
theorem toAbstract_vocabulary_finite
    (layer : Mettapedia.Enactive.Finite.Layer World) :
    layer.toAbstract.vocabulary.Finite := by
  change
    {fact : Set World | ∃ finiteFact ∈ layer.vocabulary,
      (finiteFact : Set World) = fact}.Finite
  refine
    (layer.vocabulary.finite_toSet.image
      fun finiteFact : Finset World => (finiteFact : Set World)).subset ?_
  rintro fact ⟨finiteFact, member, rfl⟩
  exact ⟨finiteFact, member, rfl⟩

/-- Negative theorem: no executable finite layer can be mistaken for an
abstraction layer with an infinite vocabulary. -/
theorem toAbstract_ne_of_infinite
    (finiteLayer : Mettapedia.Enactive.Finite.Layer World)
    (openLayer : AbstractionLayer World)
    (openVocabulary : openLayer.vocabulary.Infinite) :
    finiteLayer.toAbstract ≠ openLayer := by
  intro equalLayers
  apply openVocabulary
  rw [← equalLayers]
  exact toAbstract_vocabulary_finite finiteLayer

end Finite

#print axioms oneLanguageProjection_nonempty_iff
#print axioms ofAbstractionLayer_languagesCoincide
#print axioms Finite.toAbstract_vocabulary_finite
#print axioms Finite.toAbstract_ne_of_infinite
#print axioms Mettapedia.Enactive.Finite.Layer.Statement.toAbstract_le_iff

end Mettapedia.Enactive.TwoLanguageBridge
