import Mettapedia.GSLT.Distinction.OptionGraph

/-!
# The frontier map of the Prime option graph

For every pair of options that no witness separates yet, the one theorem or fixture that would
close it: a separation, giving each option a different verdict on one case, or an
identification, recording the two as making the same identifications. Each target names the
module it would most naturally live in, the confidence (in percent) that it is provable with the
current infrastructure, and the value (in percent) of closing the pair.

The map is a work queue. `Graph.frontierMapped`, checked by the manifest, says that it covers the
frontier exactly: when a witness closes a pair, its target must be retired, and a new frontier pair
needs a target.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeOptions.FrontierMap

open Mettapedia.GSLT.Distinction.OptionGraph

/-- The targets, one per frontier pair. -/
def targets : List FrontierTarget := [
  { first := "public-observers", second := "region-observers"
    outcome := .identification, kind := .«theorem»
    statement := "Region-bounded adequacy for the λ-to-ρ compiler: two compiled processes are \
      identified by every region-bounded observer exactly when every public observer identifies \
      them."
    firstVerdict := "identifies exactly the pairs region-bounded observers identify"
    secondVerdict := "identifies exactly the pairs public observers identify"
    module := "Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoQuotedCompilerObserverControls"
    confidence := 55, value := 70 },
  { first := "product-site", second := "frame-valued-names"
    outcome := .separation, kind := .«theorem»
    statement := "On contexts times the open sets of Cantor space, a model and a formula whose \
      region value at the empty context is ⊥ and which is forced after a context arrow; in every \
      frame-valued names model, forcing of a bounded formula on a region does not depend on the \
      context."
    firstVerdict := "the region value at one context does not decide forcing after an arrow"
    secondVerdict := "forcing on a region is the same at every context"
    module := "Mettapedia.SetTheory.CarveOuts.Sites.RegionReadingFiber"
    confidence := 80, value := 60 },
  { first := "contextual-forcing", second := "frame-valued-names"
    outcome := .separation, kind := .«theorem»
    statement := "In the names model whose membership has value the clopen left half of Cantor \
      space, excluded middle of membership has value the whole space and is forced on it; \
      contextual forcing over the same contexts does not force it."
    firstVerdict := "excluded middle of membership in the left half is not forced"
    secondVerdict := "excluded middle of membership in the left half is forced on the whole space"
    module := "Mettapedia.SetTheory.CarveOuts.Sites.SiteProjections"
    confidence := 75, value := 65 },
  { first := "sheaf-family-model", second := "open-set-values"
    outcome := .separation, kind := .«theorem»
    statement := "A sheaf model on Cantor space and two formulas whose open-set values at a \
      context agree and which differ after a context arrow: the sheaf form of the region-reading \
      fibre."
    firstVerdict := "keeps the two formulas apart after the arrow"
    secondVerdict := "identifies them at the context"
    module := "Mettapedia.SetTheory.CarveOuts.Sheaves.Forcing"
    confidence := 70, value := 55 },
  { first := "cantor-sheaf-small-maps", second := "cantor-family-small-maps"
    outcome := .identification, kind := .«theorem»
    statement := "Collection for families of sheaves over a small context category, from base \
      collection, so that the two classes satisfy the same small-map axioms; a separation would \
      need an axiom one class fails, and none is expected."
    firstVerdict := "collection from base collection"
    secondVerdict := "collection from base collection, at every context"
    module := "Mettapedia.SetTheory.CarveOuts.Sheaves.FamilySmallMaps"
    confidence := 70, value := 50 },
  { first := "weight-ordinal", second := "weight-complex-born"
    outcome := .separation, kind := .«theorem»
    statement := "A total comparison: checked ordinal priorities are totally compared, while no \
      linear order makes the rational complex amplitudes an ordered ring, since i · i = -1."
    firstVerdict := "totally compared"
    secondVerdict := "no compatible total order"
    module := "Mettapedia.Algebra.RationalComplexAmplitude"
    confidence := 80, value := 35 },
  { first := "weight-ordinal", second := "weight-pln-evidence"
    outcome := .separation, kind := .«theorem»
    statement := "A total comparison: checked ordinal priorities are totally compared, while \
      purely positive and purely negative evidence are incomparable in the order of evidence."
    firstVerdict := "totally compared"
    secondVerdict := "incomparable evidence exists"
    module := "Mettapedia.PLN.Evidence.BinEvNat"
    confidence := 85, value := 40 },
  { first := "internal-set-tower", second := "generated-enclosure-tower"
    outcome := .separation, kind := .«theorem»
    statement := "A small family of a level whose image lies in every closed set containing its \
      index, but not in the enclosure generated by the declared codes and operations: closure \
      under declared operations is weaker than closure under every small family."
    firstVerdict := "contains the image"
    secondVerdict := "does not contain it"
    module := "Mettapedia.GSLT.ConstructiveObservedGeneratedEnclosure"
    confidence := 60, value := 70 },
  { first := "internal-set-tower", second := "proof-theoretic-progression"
    outcome := .separation, kind := .«theorem»
    statement := "Whether a step adds an arithmetized consistency statement: a progression step \
      from T to T + Con(T) adds a sentence T does not prove, by the second incompleteness theorem \
      for consistent Δ₁ extensions of IΣ₁, while a step of the internal tower hosts a model and \
      states no arithmetized consistency."
    firstVerdict := "no arithmetized consistency statement is added"
    secondVerdict := "a sentence the previous theory does not prove is added"
    module := "Mettapedia.SetTheory.OpenTower.Progression"
    confidence := 45, value := 55 },
  { first := "external-level-schema", second := "generated-enclosure-tower"
    outcome := .separation, kind := .«theorem»
    statement := "The image of a level is closed under every small family of the lower level \
      (image_closed), while a generated enclosure is closed only under its declared operations: a \
      family of the lower level whose image the generated enclosure misses."
    firstVerdict := "closed under every small family"
    secondVerdict := "closed under declared operations only"
    module := "Mettapedia.GSLT.ConstructiveObservedGeneratedEnclosure"
    confidence := 55, value := 50 },
  { first := "external-level-schema", second := "proof-theoretic-progression"
    outcome := .separation, kind := .«theorem»
    statement := "The image of a level is elementarily equivalent to the whole lower level \
      (image_elementarilyEquivalent), so the step adds no sentence over it, while a progression \
      step proves a sentence the previous theory does not."
    firstVerdict := "no new first-order sentence"
    secondVerdict := "a new sentence"
    module := "Mettapedia.SetTheory.OpenTower.Progression"
    confidence := 50, value := 45 },
  { first := "generated-enclosure-tower", second := "proof-theoretic-progression"
    outcome := .separation, kind := .«theorem»
    statement := "An observer both can answer: whether a successor step proves an arithmetic \
      sentence the previous step does not. A generated enclosure step is a set-level closure with \
      decoding and proves none; a progression step proves Con of the previous theory."
    firstVerdict := "no new arithmetic sentence"
    secondVerdict := "a new arithmetic sentence"
    module := "Mettapedia.SetTheory.OpenTower.Progression"
    confidence := 35, value := 35 },
  { first := "greatest-stage", second := "strongest-completion"
    outcome := .separation, kind := .«theorem»
    statement := "Both options are refuted. A separation would compare the two refutations on one \
      structure, such as the Lindenbaum algebra of the theory of a stage: a greatest stage fails \
      in ZFSet under cofinally many inaccessibles, a strongest completion for consistent Δ₁ \
      extensions of IΣ₁."
    firstVerdict := "refuted at the level of sets"
    secondVerdict := "refuted over arithmetic"
    module := "Mettapedia.SetTheory.OpenTower.NoIsolatedCompletion"
    confidence := 30, value := 15 },
  { first := "greatest-stage", second := "one-fixed-model"
    outcome := .separation, kind := .«theorem»
    statement := "Either a fixed model that is maximal for elementary extension without being a \
      greatest stage, or a proof that a fixed model as the top is refuted as a greatest stage is, \
      which would identify the two on the greatest-element observer."
    firstVerdict := "refuted"
    secondVerdict := "maximal for another order, or refuted alike"
    module := "Mettapedia.SetTheory.OpenTower.InternalTower"
    confidence := 35, value := 30 },
  { first := "greatest-stage", second := "plural-admitted-family"
    outcome := .separation, kind := .«theorem»
    statement := "The plural family has no greatest member and holds without one: directed unions \
      of consistent rule systems stay consistent (directedUnion_noBottom), and no admitted theory \
      includes every admitted theory."
    firstVerdict := "refuted"
    secondVerdict := "holds without a top"
    module := "Mettapedia.Logic.FinitaryRuleSystem.DirectedUnion"
    confidence := 50, value := 30 },
  { first := "strongest-completion", second := "plural-admitted-family"
    outcome := .separation, kind := .«theorem»
    statement := "The plural family holds without a strongest member: no admitted theory includes \
      every admitted theory, while a strongest completion is refuted by no_isolated_completion."
    firstVerdict := "refuted"
    secondVerdict := "holds without a top"
    module := "Mettapedia.Logic.FinitaryRuleSystem.DirectedUnion"
    confidence := 50, value := 30 },
  { first := "cofinal-extensible-family", second := "one-fixed-model"
    outcome := .separation, kind := .«theorem»
    statement := "The universe law, every set lies in a closed set: it holds of the class of \
      stages (exists_stage_containing) and fails inside any fixed set model of the seven set laws, \
      as inside every least closed set (no_closed_member_around)."
    firstVerdict := "the universe law holds"
    secondVerdict := "the universe law fails inside the model"
    module := "Mettapedia.SetTheory.OpenTower.InternalTower"
    confidence := 70, value := 55 },
  { first := "cofinal-extensible-family", second := "linear-open-tower"
    outcome := .separation, kind := .«theorem»
    statement := "Whether the closed sets of one level are linearly ordered by inclusion: two \
      incomparable closed sets would separate the directed family from a linear tower; otherwise \
      the two agree on the shape of the order."
    firstVerdict := "directed, possibly not linear"
    secondVerdict := "linear"
    module := "Mettapedia.SetTheory.OpenTower.InternalTower"
    confidence := 50, value := 45 },
  { first := "cofinal-extensible-family", second := "plural-admitted-family"
    outcome := .separation, kind := .«theorem»
    statement := "A stage with a Quine atom is admitted by the plural family and joined to stages \
      with Foundation by interpretation, while no stage of the cofinal family has one, since every \
      stage is a set of ZFSet."
    firstVerdict := "no stage with a Quine atom"
    secondVerdict := "a stage with a Quine atom, joined by interpretation"
    module := "Mettapedia.SetTheory.OpenTower.InternalTower"
    confidence := 75, value := 50 },
  { first := "one-fixed-model", second := "linear-open-tower"
    outcome := .separation, kind := .«theorem»
    statement := "An observer of proper extensions within the option: every stage of a linear \
      tower has a proper extension in the tower (no_final_stage), while one fixed model has no \
      proper extension within itself."
    firstVerdict := "no proper extension within it"
    secondVerdict := "a proper extension of every stage"
    module := "Mettapedia.TypeTheory.IndexedUniverseAdequacy"
    confidence := 55, value := 40 },
  { first := "one-fixed-model", second := "plural-admitted-family"
    outcome := .separation, kind := .«theorem»
    statement := "For a consistent Δ₁ extension T of IΣ₁, a sentence neither provable nor \
      refutable in T is true at some completion and false at another: each fixed model decides it, \
      the plural family keeps it undecided."
    firstVerdict := "decides the sentence"
    secondVerdict := "keeps it undecided"
    module := "Mettapedia.SetTheory.OpenTower.NoIsolatedCompletion"
    confidence := 75, value := 60 },
  { first := "no-terminal-set-stage", second := "no-terminal-refinement-stage"
    outcome := .separation, kind := .«theorem»
    statement := "The closed sets of a level under inclusion are not the nonzero elements of a \
      Boolean algebra, since the relative complement of a stage is not a stage; so the statement \
      for sets is not an instance of the statement for refinements."
    firstVerdict := "holds for the order of closed sets"
    secondVerdict := "holds for refinement orders of Boolean algebras"
    module := "Mettapedia.SetTheory.OpenTower.NoIsolatedCompletion"
    confidence := 50, value := 25 },
  { first := "no-terminal-set-stage", second := "no-principal-perspective"
    outcome := .separation, kind := .«theorem»
    statement := "A structure with no terminal stage whose space of perspectives has an isolated \
      point, against the tower of sets, whose perspectives over the stage indices have none \
      (free_ultrafilter_not_isolated)."
    firstVerdict := "no terminal stage"
    secondVerdict := "no isolated perspective"
    module := "Mettapedia.SetTheory.OpenTower.NoIsolatedCompletion"
    confidence := 45, value := 35 },
  { first := "irrelevant-truth", second := "relevant-evidence"
    outcome := .separation, kind := .«theorem»
    statement := "Two proofs of one proposition that an observer counting occurrences separates: \
      proof-relevant evidence keeps them apart, proof-irrelevant truth identifies them."
    firstVerdict := "identifies the two proofs"
    secondVerdict := "keeps them apart"
    module := "Mettapedia.Logic.TheoryModel.Forgetting"
    confidence := 85, value := 60 },
  { first := "irrelevant-truth", second := "extraction-arrows"
    outcome := .separation, kind := .«theorem»
    statement := "An extraction arrow from retained evidence to truth that is a Galois insertion \
      for identification and not for forgetting (identificationInsertion, not_galoisInsertion), \
      against truth bubbles, which have no extraction to read."
    firstVerdict := "no extraction"
    secondVerdict := "an extraction arrow with the insertion property"
    module := "Mettapedia.Logic.TheoryModel.Forgetting"
    confidence := 70, value := 45 },
  { first := "relevant-evidence", second := "extraction-arrows"
    outcome := .separation, kind := .«theorem»
    statement := "A consumer that needs both the truth of a proposition and its retained evidence: \
      extraction arrows supply both with provenance, evidence bubbles alone supply no truth \
      reading."
    firstVerdict := "evidence without a truth reading"
    secondVerdict := "both, related by the arrow"
    module := "Mettapedia.Logic.TheoryModel.Forgetting"
    confidence := 60, value := 40 },
  { first := "authored-witnesses", second := "witness-covers"
    outcome := .separation, kind := .«theorem»
    statement := "A cover with locally available witnesses that does not split into a global \
      authored witness family."
    firstVerdict := "needs a global family"
    secondVerdict := "works with local witnesses"
    module := "Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualWitnessCover"
    confidence := 75, value := 60 },
  { first := "authored-witnesses", second := "internal-collection"
    outcome := .separation, kind := .«theorem»
    statement := "A profile with an internal Collection schema proves a collection instance that \
      no authored witness family supplies."
    firstVerdict := "supplies only authored instances"
    secondVerdict := "proves the instance"
    module := "Mettapedia.SetTheory.CarveOuts.Sheaves.Collection"
    confidence := 55, value := 45 },
  { first := "authored-witnesses", second := "host-choice-collection"
    outcome := .separation, kind := .«theorem»
    statement := "Collection from an authored witness family is choice-free, while host-choice \
      collection uses Classical.choice (baseCollection_of_choice): a choice-free collection \
      theorem for supplied witnesses."
    firstVerdict := "choice-free"
    secondVerdict := "uses host choice"
    module := "Mettapedia.SetTheory.CarveOuts.Sheaves.Collection"
    confidence := 85, value := 65 },
  { first := "witness-covers", second := "internal-collection"
    outcome := .separation, kind := .«theorem»
    statement := "Covers with local witnesses give collection on sheaves without an internal \
      schema, while an internal schema holds in a profile that has no covers."
    firstVerdict := "collection from covers"
    secondVerdict := "collection by axiom"
    module := "Mettapedia.SetTheory.CarveOuts.Sheaves.Collection"
    confidence := 55, value := 40 },
  { first := "witness-covers", second := "host-choice-collection"
    outcome := .separation, kind := .«theorem»
    statement := "Collection on sheaves from covers with local witnesses, choice-free, against the \
      host-choice route (sheafSmall_collection_of_choice)."
    firstVerdict := "choice-free"
    secondVerdict := "uses host choice"
    module := "Mettapedia.SetTheory.CarveOuts.Sheaves.Collection"
    confidence := 70, value := 50 },
  { first := "internal-collection", second := "host-choice-collection"
    outcome := .separation, kind := .«theorem»
    statement := "A model in which the internal Collection schema holds while host choice fails, \
      or the reverse."
    firstVerdict := "holds"
    secondVerdict := "fails"
    module := "Mettapedia.SetTheory.CarveOuts.Sheaves.Collection"
    confidence := 55, value := 40 },
  { first := "no-logic-until-selected", second := "named-bootstrap-core"
    outcome := .separation, kind := .fixture
    statement := "A fixture of the C draft: in a space with no set profile, a logical judgment \
      such as implication introduction is answered by the named bootstrap core and refused when no \
      logic is selected, while a set judgment is refused in both."
    firstVerdict := "refuses the logical judgment"
    secondVerdict := "answers it, naming the core"
    module := "tests/prime/theory_profiles"
    confidence := 80, value := 70 },
  { first := "port-indexed-finality", second := "specialized-sheaf-finality"
    outcome := .separation, kind := .«theorem»
    statement := "The specialized finality for sheaves on Cantor space holds without the \
      Heyting-pretopos and indexed-axiom obligations that porting the indexed final-coalgebra \
      theorem needs."
    firstVerdict := "needs the ambient obligations"
    secondVerdict := "does not"
    module := "Mettapedia.SetTheory.CarveOuts.Sheaves.Finality"
    confidence := 40, value := 75 },
  { first := "product-site-comparison", second := "relative-site-comparison"
    outcome := .separation, kind := .«theorem»
    statement := "A context arrow that pulls a cover back to a non-cover: expressible in a \
      relative site, not in the product site, whose coverage is the same along every context."
    firstVerdict := "coverage fixed along contexts"
    secondVerdict := "coverage may change along an arrow"
    module := "Mettapedia.SetTheory.CarveOuts.Sites.ProductSite"
    confidence := 60, value := 50 },
  { first := "product-site-comparison", second := "context-families-of-sheaves"
    outcome := .identification, kind := .«theorem»
    statement := "Forcing on the product site agrees with forcing in the family of sheaves it \
      sheafifies to (siteForce_iff_sheafForce), to be stated as an identification of the two \
      comparisons on formulas."
    firstVerdict := "forcing on covers"
    secondVerdict := "sheaf forcing, the same verdicts"
    module := "Mettapedia.SetTheory.CarveOuts.Sheaves.Forcing"
    confidence := 85, value := 45 },
  { first := "relative-site-comparison", second := "context-families-of-sheaves"
    outcome := .separation, kind := .«theorem»
    statement := "A relative site whose coverage changes along a context arrow, against families \
      of sheaves on one space, which keep one coverage at every context."
    firstVerdict := "coverage changes"
    secondVerdict := "one coverage"
    module := "Mettapedia.SetTheory.CarveOuts.Sheaves.Families"
    confidence := 50, value := 40 }
]

end Mettapedia.Languages.MeTTa.PrimeOptions.FrontierMap
