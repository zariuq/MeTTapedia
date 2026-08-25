import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Belief and evidence languages

Pei Wang's comparative framework for evidential reasoning distinguishes a
belief language `L_B` from an evidence language `L_E`; only some approaches
identify them. A degree of belief is written `d(B,E)`, where `B` is a belief
and `E` is a body of available evidence.

This module isolates the reusable mathematics. The two syntactic carriers,
their semantic interpretations, the relevant-evidence relation, and the
aggregation codomain are independent parameters. Irrelevant evidence is
removed before aggregation by construction, so no coherence, probability,
finiteness, or single-language premise is installed in the foundation.

Reference: P. Wang, *Formalization of Evidence: A Comparative Study*, Journal
of Artificial General Intelligence 1 (2009), 25--53.
-/

set_option autoImplicit false

namespace Mettapedia.Evidence

universe uWorld uDegree uBelief uEvidence uSourceEvidence

/-- A two-language evidential layer.

`aggregate` is intentionally unconstrained: binary consequence, scalar belief,
interval belief, proof-relevant evidence, and other readouts are instances.
The informative layer retains the evidence body and relevance relation before
any such readout is selected. -/
structure TwoLanguageLayer
    (World : Type uWorld) (Degree : Type uDegree)
    (Belief : Type uBelief) (Evidence : Type uEvidence) where
  beliefVocabulary : Set Belief
  evidenceVocabulary : Set Evidence
  beliefMeaning : Belief → Set World
  evidenceMeaning : Evidence → Set World
  relevant : Belief → Evidence → Prop
  aggregate : Belief → Set Evidence → Degree

namespace TwoLanguageLayer

variable {World : Type uWorld} {Degree : Type uDegree}
  {Belief : Type uBelief} {Evidence : Type uEvidence}

/-- The vocabulary-bounded evidence scope of a belief. -/
def evidenceScope
    (layer : TwoLanguageLayer World Degree Belief Evidence)
    (belief : Belief) : Set Evidence :=
  {evidence | evidence ∈ layer.evidenceVocabulary ∧ layer.relevant belief evidence}

/-- Degree of belief after restricting the available evidence to the belief's
explicit scope. -/
def degree (layer : TwoLanguageLayer World Degree Belief Evidence)
    (belief : Belief) (available : Set Evidence) : Degree :=
  layer.aggregate belief (available ∩ layer.evidenceScope belief)

/-- Degree depends on the in-scope evidence, not on the ambient evidence body. -/
theorem degree_eq_of_restricted_eq
    (layer : TwoLanguageLayer World Degree Belief Evidence)
    (belief : Belief) {left right : Set Evidence}
    (restricted_eq :
      left ∩ layer.evidenceScope belief = right ∩ layer.evidenceScope belief) :
    layer.degree belief left = layer.degree belief right := by
  exact congrArg (layer.aggregate belief) restricted_eq

/-- Restricting an evidence body twice changes nothing. -/
theorem degree_restrict
    (layer : TwoLanguageLayer World Degree Belief Evidence)
    (belief : Belief) (available : Set Evidence) :
    layer.degree belief (available ∩ layer.evidenceScope belief) =
      layer.degree belief available := by
  apply degree_eq_of_restricted_eq
  ext evidence
  simp

/-- Semantic equivalence compares what two beliefs say about worlds. -/
def SemanticallyEquivalent
    (layer : TwoLanguageLayer World Degree Belief Evidence)
    (left right : Belief) : Prop :=
  layer.beliefMeaning left = layer.beliefMeaning right

/-- Evidential equivalence compares which evidence can bear on two beliefs. -/
def EvidentiallyEquivalent
    (layer : TwoLanguageLayer World Degree Belief Evidence)
    (left right : Belief) : Prop :=
  layer.evidenceScope left = layer.evidenceScope right

/-- Meanings of the authored belief vocabulary. -/
def beliefMeaningVocabulary
    (layer : TwoLanguageLayer World Degree Belief Evidence) : Set (Set World) :=
  {meaning | ∃ belief ∈ layer.beliefVocabulary,
    layer.beliefMeaning belief = meaning}

/-- Meanings of the authored evidence vocabulary. -/
def evidenceMeaningVocabulary
    (layer : TwoLanguageLayer World Degree Belief Evidence) : Set (Set World) :=
  {meaning | ∃ evidence ∈ layer.evidenceVocabulary,
    layer.evidenceMeaning evidence = meaning}

/-- The exact premise under which the two vocabularies admit one shared
semantic vocabulary. -/
def LanguagesCoincide
    (layer : TwoLanguageLayer World Degree Belief Evidence) : Prop :=
  layer.beliefMeaningVocabulary = layer.evidenceMeaningVocabulary

/-! ## Evidence transport -/

/-- Pull an evidence language back along a translation of evidence tokens.
Beliefs and worlds remain fixed; source evidence is interpreted, scoped, and
aggregated through its target image. -/
def pullbackEvidence
    (layer : TwoLanguageLayer World Degree Belief Evidence)
    {SourceEvidence : Type uSourceEvidence}
    (evidenceMap : SourceEvidence → Evidence) :
    TwoLanguageLayer World Degree Belief SourceEvidence where
  beliefVocabulary := layer.beliefVocabulary
  evidenceVocabulary := evidenceMap ⁻¹' layer.evidenceVocabulary
  beliefMeaning := layer.beliefMeaning
  evidenceMeaning := layer.evidenceMeaning ∘ evidenceMap
  relevant := fun belief sourceEvidence =>
    layer.relevant belief (evidenceMap sourceEvidence)
  aggregate := fun belief sourceBody =>
    layer.aggregate belief (evidenceMap '' sourceBody)

/-- Degree is natural under evidence translation: restricting source evidence
and then translating gives the same retained target body as translating first
and applying the target scope. No injectivity premise is needed because scope
membership is a property of the translated evidence token. -/
theorem pullbackEvidence_degree
    (layer : TwoLanguageLayer World Degree Belief Evidence)
    {SourceEvidence : Type uSourceEvidence}
    (evidenceMap : SourceEvidence → Evidence)
    (belief : Belief) (available : Set SourceEvidence) :
    (layer.pullbackEvidence evidenceMap).degree belief available =
      layer.degree belief (evidenceMap '' available) := by
  unfold degree pullbackEvidence evidenceScope
  apply congrArg (layer.aggregate belief)
  ext targetEvidence
  constructor
  · rintro ⟨sourceEvidence, ⟨availableSource, targetMember, relevant⟩, rfl⟩
    exact ⟨⟨sourceEvidence, availableSource, rfl⟩, targetMember, relevant⟩
  · rintro ⟨⟨sourceEvidence, availableSource, rfl⟩, targetMember, relevant⟩
    exact ⟨sourceEvidence, ⟨availableSource, targetMember, relevant⟩, rfl⟩

/-! ## Open vocabularies and finite views -/

/-- Wang-openness at one instant: neither authored vocabulary is finitely
exhaustible. This does not assert that all possible future expressions are
already known; it rules out installing a finite current view as the whole
language. -/
def WangOpen (layer : TwoLanguageLayer World Degree Belief Evidence) : Prop :=
  layer.beliefVocabulary.Infinite ∧ layer.evidenceVocabulary.Infinite

/-- A finite observational view of an open layer. It carries inclusions back
to the primary layer instead of pretending to be an exhaustive replacement. -/
structure FiniteView [DecidableEq Belief] [DecidableEq Evidence]
    (layer : TwoLanguageLayer World Degree Belief Evidence) where
  beliefVocabulary : Finset Belief
  evidenceVocabulary : Finset Evidence
  belief_subset : (beliefVocabulary : Set Belief) ⊆ layer.beliefVocabulary
  evidence_subset : (evidenceVocabulary : Set Evidence) ⊆ layer.evidenceVocabulary

namespace FiniteView

variable [DecidableEq Belief] [DecidableEq Evidence]
  {layer : TwoLanguageLayer World Degree Belief Evidence}

/-- Regard a finite view as a layer with the same semantics and aggregator but
restricted vocabularies. -/
def toLayer (view : FiniteView layer) :
    TwoLanguageLayer World Degree Belief Evidence where
  beliefVocabulary := view.beliefVocabulary
  evidenceVocabulary := view.evidenceVocabulary
  beliefMeaning := layer.beliefMeaning
  evidenceMeaning := layer.evidenceMeaning
  relevant := layer.relevant
  aggregate := layer.aggregate

/-- A finite view preserves degree calculations whose entire evidence body is
visible in that view. -/
theorem degree_eq_parent (view : FiniteView layer) (belief : Belief)
    (available : Set Evidence)
    (visible : available ⊆ (view.evidenceVocabulary : Set Evidence)) :
    view.toLayer.degree belief available = layer.degree belief available := by
  unfold TwoLanguageLayer.degree
  apply congrArg (layer.aggregate belief)
  ext evidence
  simp only [evidenceScope, Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨available_evidence, view_member, relevant⟩
    exact ⟨available_evidence, view.evidence_subset view_member, relevant⟩
  · rintro ⟨available_evidence, _parent_member, relevant⟩
    exact ⟨available_evidence, visible available_evidence, relevant⟩

/-- A finite view is not itself Wang-open. Its inclusions into an open parent
are therefore semantically significant data. -/
theorem not_wangOpen (view : FiniteView layer) :
    ¬ view.toLayer.WangOpen := by
  intro openView
  exact openView.1 view.beliefVocabulary.finite_toSet

/-- Every finite view of a Wang-open layer omits an available belief. -/
theorem exists_omitted_belief (view : FiniteView layer)
    (openLayer : layer.WangOpen) :
    ∃ belief ∈ layer.beliefVocabulary,
      belief ∉ view.beliefVocabulary := by
  by_contra noOmission
  push Not at noOmission
  have finiteParent : layer.beliefVocabulary.Finite :=
    view.beliefVocabulary.finite_toSet.subset fun belief member =>
      noOmission belief member
  exact openLayer.1 finiteParent

/-- Every finite view of a Wang-open layer omits available evidence. -/
theorem exists_omitted_evidence (view : FiniteView layer)
    (openLayer : layer.WangOpen) :
    ∃ evidence ∈ layer.evidenceVocabulary,
      evidence ∉ view.evidenceVocabulary := by
  by_contra noOmission
  push Not at noOmission
  have finiteParent : layer.evidenceVocabulary.Finite :=
    view.evidenceVocabulary.finite_toSet.subset fun evidence member =>
      noOmission evidence member
  exact openLayer.2 finiteParent

end FiniteView

end TwoLanguageLayer

/-! ## Hempel witness: semantic equivalence does not fix evidence scope -/

namespace HempelWitness

/-- One observed object, classified by ravenhood and blackness. -/
structure ObjectState where
  isRaven : Bool
  isBlack : Bool
  deriving DecidableEq

/-- The two classically equivalent belief presentations in the raven paradox. -/
inductive Belief where
  | ravensAreBlack
  | nonBlackThingsAreNotRavens
  deriving DecidableEq

/-- Classical truth conditions for the two belief presentations. They are
implemented from their distinct implications rather than identified by
definition. -/
def beliefMeaning : Belief → Set ObjectState
  | .ravensAreBlack =>
      {object | object.isRaven = true → object.isBlack = true}
  | .nonBlackThingsAreNotRavens =>
      {object | object.isBlack = false → object.isRaven = false}

/-- Nicod-style relevance follows the antecedent of each presentation. Wang's
analysis retains this difference instead of forcing classical equivalence to
identify confirmation scopes. -/
def relevant : Belief → ObjectState → Prop
  | .ravensAreBlack, object => object.isRaven = true
  | .nonBlackThingsAreNotRavens, object => object.isBlack = false

/-- A deliberately informative degree carrier: the retained relevant evidence
body itself. Lossy numerical truth values can be read from this later. -/
def layer : TwoLanguageLayer ObjectState (Set ObjectState) Belief ObjectState where
  beliefVocabulary := Set.univ
  evidenceVocabulary := Set.univ
  beliefMeaning := beliefMeaning
  evidenceMeaning := fun object => {object}
  relevant := relevant
  aggregate := fun _ evidenceBody => evidenceBody

def blackRaven : ObjectState := ⟨true, true⟩
def redPencil : ObjectState := ⟨false, false⟩

/-- The two statements are classically equivalent. -/
theorem belief_meanings_equal :
    layer.SemanticallyEquivalent .ravensAreBlack
      .nonBlackThingsAreNotRavens := by
  ext object
  cases object with
  | mk raven black =>
      cases raven <;> cases black <;>
        simp [layer, beliefMeaning]

/-- A black raven bears on the forward presentation but not its contrapositive
presentation under the stated relevance discipline. -/
theorem blackRaven_degrees_differ :
    layer.degree .ravensAreBlack {blackRaven} = {blackRaven} ∧
      layer.degree .nonBlackThingsAreNotRavens {blackRaven} = ∅ := by
  constructor <;>
    ext object <;>
    simp [TwoLanguageLayer.degree, TwoLanguageLayer.evidenceScope, layer,
      relevant, blackRaven]

/-- A non-black non-raven exhibits the converse relevance difference. -/
theorem redPencil_degrees_differ :
    layer.degree .ravensAreBlack {redPencil} = ∅ ∧
      layer.degree .nonBlackThingsAreNotRavens {redPencil} = {redPencil} := by
  constructor <;>
    ext object <;>
    simp [TwoLanguageLayer.degree, TwoLanguageLayer.evidenceScope, layer,
      relevant, redPencil]

/-- Negative theorem: quotienting beliefs by classical semantic meaning loses
which observations count as evidence. -/
theorem semanticallyEquivalent_not_evidentiallyEquivalent :
    layer.SemanticallyEquivalent .ravensAreBlack
        .nonBlackThingsAreNotRavens ∧
      ¬ layer.EvidentiallyEquivalent .ravensAreBlack
        .nonBlackThingsAreNotRavens := by
  refine ⟨belief_meanings_equal, ?_⟩
  intro scopesEqual
  have atBlackRaven := Set.ext_iff.mp scopesEqual blackRaven
  simp [TwoLanguageLayer.evidenceScope, layer, relevant, blackRaven] at atBlackRaven

#print axioms belief_meanings_equal
#print axioms blackRaven_degrees_differ
#print axioms semanticallyEquivalent_not_evidentiallyEquivalent

end HempelWitness

end Mettapedia.Evidence
