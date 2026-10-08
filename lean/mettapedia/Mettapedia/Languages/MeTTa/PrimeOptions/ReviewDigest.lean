import Mettapedia.GSLT.Distinction.OptionGraph
import Mettapedia.Logic.TheoryModel.Forgetting
import Mettapedia.SetTheory.CarveOuts.SheafPowers
import Mettapedia.SetTheory.CarveOuts.Sites.Bridge
import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualCoalgebraFinality
import Mettapedia.GSLT.Causality.ContextBindings
import Mettapedia.GSLT.Dynamics.DemandAgreement
import Mettapedia.GSLT.Causality.StructuralModels

/-!
# Choice points raised by the review, placed in the option graph

Questions the review of the Prime programme raised that were not in the graph, with their
options and the theorems that bear on them. Where nothing separates two options yet, they stay
on the frontier.

* **Proof irrelevance** (`proof-irrelevance`): forgetting proofs as an observer is not a Galois
  insertion, while identifying is.
* **How a collection is licensed** (`collection-route`): authored witnesses, covers, an internal
  Collection principle, or host choice. That Collection needs choice is not a theorem.
* **The logical service of a space with no set profile** (`logical-core`).
* **The route to the hyperset universe of sheaves on Cantor space** (`sheaf-hyperset-route`).
* **The comparison of the contextual model with the sheaf model**
  (`contextual-sheaf-comparison`); parallel context arrows must stay distinct.
* **The order of the causal identification results** (`causal-identification`).

Two further witnesses use options that exist: one shared draw against two independent draws,
in the question of the demand strategy; and the passage from sheaves with values in `Type` to
sheaves one universe up, an arrow whose kind is not yet classified.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeOptions.ReviewDigest

open Lean (Name)
open Mettapedia.GSLT.Distinction.OptionGraph

def questions : List Question := [
  { id := "proof-irrelevance"
    title := "Proof irrelevance"
    summary := "Whether a bubble's propositions are proof-irrelevant truth, proof-relevant \
      evidence, or both with an extraction arrow. Forgetting proofs as an observer weakens; \
      adopting irrelevance as an axiom strengthens."
    facts := [cites [``Mettapedia.Logic.TheoryModel.not_galoisInsertion,
      ``Mettapedia.Logic.TheoryModel.identificationInsertion]] },
  { id := "collection-route"
    title := "How a collection is licensed"
    summary := "Authored witness families, covers with locally available witnesses, an \
      internally assumed Collection principle, or an external host choice. A cover need not \
      split into a global selector; that Collection needs choice is not a theorem."
    facts := [cites [``Mettapedia.SetTheory.CarveOuts.Sheaves.cantorUp_collection_of_choice]] },
  { id := "logical-core"
    title := "The logical service of a space with no set profile"
    summary := "Whether an unselected space has no logic until one is selected, or the named \
      bootstrap logical core: propositions, implication, quantification over every class, \
      equality with its rules, falsity as all p. p, no excluded middle and no set constants. Set \
      judgments are refused either way." },
  { id := "sheaf-hyperset-route"
    title := "Route to the hyperset universe of sheaves on Cantor space"
    summary := "Port the indexed final-coalgebra theorem with its exact hypotheses, or prove a \
      specialized finality for this ambient. Either way: the ambient package, the action of the \
      power class on morphisms, the small-generated subcoalgebra, finality, then anti-foundation \
      by graph decorations."
    facts := [cites [``Mettapedia.SetTheory.CarveOuts.Sheaves.cantorUp_basicSmallMapAxioms,
      ``Mettapedia.SetTheory.CarveOuts.Sheaves.natNNO,
      ``Mettapedia.SetTheory.CarveOuts.Sheaves.cantor_sheaf_not_representable]] },
  { id := "contextual-sheaf-comparison"
    title := "Contextual model and sheaf model"
    summary := "A product site of contexts and regions, a relative site, or context-indexed \
      families of sheaves. The comparison must preserve the small-map class, the power \
      functors, the material readout and dependent decoding, and keep parallel context arrows \
      distinct."
    facts := [cites [``Mettapedia.SetTheory.CarveOuts.Sites.Parallel.selfValue_ne_notSelfValue,
      ``Mettapedia.SetTheory.CarveOuts.Sites.Parallel.same_reach]] },
  { id := "causal-identification"
    title := "Order of the causal identification results"
    summary := "Broad completeness claims, or a scoped embedding of structural causal models with \
      surgery compatibility, then the rules of the do-calculus, adjustment certificates, and \
      identification with failure witnesses."
    facts := [cites [``Mettapedia.GSLT.Causality.ContextBindings.twin_eq_experiment_iff]] }
]

def nodes : List Node := [
  { id := "irrelevant-truth", question := "proof-irrelevance"
    title := "Proof-irrelevant truth bubbles"
    summary := "Propositions whose proofs are not observed." },
  { id := "relevant-evidence", question := "proof-irrelevance"
    title := "Proof-relevant evidence bubbles"
    summary := "Proofs, receipts and occurrences retained as data." },
  { id := "extraction-arrows", question := "proof-irrelevance"
    title := "Both, with extraction arrows"
    summary := "Irrelevant truth beside retained evidence, related by an explicit extraction \
      arrow with retained provenance." },
  { id := "authored-witnesses", question := "collection-route"
    title := "Authored witness families"
    summary := "The source supplies a small family of witnesses and its decoder." },
  { id := "witness-covers", question := "collection-route"
    title := "Witness covers"
    summary := "A cover with locally available witnesses and a totality condition; no global \
      selector." },
  { id := "internal-collection", question := "collection-route"
    title := "An internal Collection principle"
    summary := "A profile adopts a Collection schema, scoped to that profile." },
  { id := "host-choice-collection", question := "collection-route"
    title := "External host choice"
    summary := "The host selects witnesses: a model construction, recorded as a host dependency."
    facts := [cites [``Mettapedia.SetTheory.CarveOuts.Sheaves.cantorUp_collection_of_choice]] },
  { id := "no-logic-until-selected", question := "logical-core"
    title := "No logic until a profile is selected"
    summary := "Internal services refuse as set judgments are refused." },
  { id := "named-bootstrap-core", question := "logical-core"
    title := "The named bootstrap logical core"
    summary := "Prime's own intuitionistic higher-order core, named in every certificate." },
  { id := "port-indexed-finality", question := "sheaf-hyperset-route"
    title := "Port the indexed final-coalgebra theorem"
    summary := "Instantiate the indexed final-coalgebra theorem with the exact ambient and \
      small-map definitions." },
  { id := "specialized-sheaf-finality", question := "sheaf-hyperset-route"
    title := "A specialized finality proof for sheaves on Cantor space"
    summary := "Follow the contextual lane's indexed finality pattern in this ambient."
    facts := [cites
      [``Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualCoalgebraFinality.isTerminal]] },
  { id := "product-site-comparison", question := "contextual-sheaf-comparison"
    title := "Product site of contexts and regions"
    summary := "Contexts times the open sets of Cantor space; right when the two axes are \
      independent." },
  { id := "relative-site-comparison", question := "contextual-sheaf-comparison"
    title := "A relative site"
    summary := "Context changes may change the coverage." },
  { id := "context-families-of-sheaves", question := "contextual-sheaf-comparison"
    title := "Context-indexed families of sheaves"
    summary := "Families over the authored context category, valued in sheaves over an atomless \
      space of perspectives." },
  { id := "broad-causal-completeness", question := "causal-identification"
    title := "Broad completeness claims first"
    summary := "Claim completeness of the do-calculus or of identification for GSLTs in \
      general." },
  { id := "scoped-scm-first", question := "causal-identification"
    title := "A scoped embedding of structural causal models first"
    summary := "Surgery compatibility on the recursive fragment, then the first rule of the \
      do-calculus and a back-door certificate with counterexamples to its side conditions." }
]

/-- The passage from sheaves with values in `Type` to sheaves one universe up. -/
def arrows : List Arrow := [
  { id := "cantor-type-to-one-universe-up", source := "cantor-sheaves-in-type"
    target := "cantor-sheaves-one-universe-up"
    kind := .unclassified
    grades := [.ungraded]
    summary := "Raising the value universe of sheaves on Cantor space by one: a growth of the \
      universe, not a resizing. Representability fails at the base and holds after the lift."
    evidence := [cites [``Mettapedia.SetTheory.CarveOuts.Sheaves.cantor_sheaf_not_representable,
      ``Mettapedia.SetTheory.CarveOuts.Sheaves.cantorUp_basicSmallMapAxioms]]
    contract := {
      entries := [
        .loses .verdicts [``Mettapedia.SetTheory.CarveOuts.Sheaves.cantor_sheaf_not_representable]
          "representability: refuted at the base universe, proved one universe up",
        .unknownAt .laws
          "whether the lift carries the classifying maps of the base to those one universe up",
        .unknownAt (.commitment .choice)
          "host choice enters representability and the natural numbers object"] } }
]

def observers : List Observer := [
  { id := "interventional-defined", title := "The interventional quantity is defined"
    reads := "Whether every model in scope has exactly one solution under every intervention, so \
      that the quantity an identification result is about is defined."
    kind := .«theorem» },
  { id := "shared-coupling", title := "Coupling of two uses"
    reads := "The joint law of two uses of one latent cell: one shared draw, or two independent \
      draws."
    kind := .«theorem», identifies := true }
]

def witnesses : List Witness := [
  { id := "feedback-outside-scope", observer := "interventional-defined"
    left := "broad-causal-completeness", right := "scoped-scm-first"
    case := "The copying loop and the negating loop, against recursive structural models."
    leftVerdict := {
      reading := "Not defined everywhere: models in general include the copying loop, with two \
        solutions, and the negating loop, with none."
      evidence := [cites [``Mettapedia.GSLT.Causality.StructuralModels.copyLoop_two_solutions,
        ``Mettapedia.GSLT.Causality.StructuralModels.negLoop_no_solution]] }
    rightVerdict := {
      reading := "Defined: a recursive model has exactly one solution under every intervention."
      evidence := [cites
        [``Mettapedia.GSLT.Causality.StructuralModels.surgery_exists_unique_solution]] } },
  { id := "twin-vs-experiment", observer := "shared-coupling"
    left := "lazy", right := "resample"
    case := "Two uses of one computation that can return two answers."
    leftVerdict := {
      reading := "Identified: one shared draw; the shared pair equals the resampled pair only \
        when at most one answer is possible."
      evidence := [cites [``Mettapedia.GSLT.Dynamics.DemandAgreement.sharedPair_eq_resampledPair_iff,
        ``Mettapedia.GSLT.Causality.ContextBindings.twin_eq_experiment_iff]] }
    rightVerdict := {
      reading := "Kept apart: two independent draws; with two equal answers the bags differ while \
        the sets agree."
      evidence := [cites
        [``Mettapedia.GSLT.Dynamics.DemandAgreement.twoEqualAnswers_bagsDiffer_setsAgree]] } }
]

end Mettapedia.Languages.MeTTa.PrimeOptions.ReviewDigest
