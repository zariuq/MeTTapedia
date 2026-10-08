import Mettapedia.GSLT.Distinction.OptionGraph
import Mettapedia.SetTheory.CarveOuts.Sites
import Mettapedia.SetTheory.CarveOuts.Sites.RegionReadingFiber
import Mettapedia.SetTheory.CarveOuts.Sites.LabelledPathSite
import Mettapedia.SetTheory.CarveOuts.Sites.ExplicitGSets

/-!
# The site-based top, placed in the option graph

Four questions, each with its arrows, contracts and witnesses.

* **Truth values of contextual forcing** (`site-truth-values`): a frame of cosieves at each
  context of a category, or one frame `Persistent` of the stages reachable from a context. The
  reading by reachable stages keeps joins and falsity in every category and forgets nothing over a
  preorder; parallel arrows and an idempotent endomorphism separate the two.
* **Symmetry and truth values** (`symmetry-and-truth-values`): sets with a group action, or their
  reading through the two-valued truth values. The reading keeps every first-order verdict and
  forgets the action and its global elements.
* **A site-based top** (`site-top`): Kripke–Joyal forcing on contexts times the open sets of
  Cantor space, contextual forcing over the contexts alone, and the Heyting-valued names over
  the frame. Each of the last two is the part of the first that is constant in the other
  coordinate; the frame reading at a context keeps the connectives. Covers separate the product
  site from contextual forcing on the same category.
* **Small maps on the Cantor product site** (`site-small-maps`): one option, with the axioms that
  hold on presheaves and those that remain hypotheses.

`graph` is a local graph of everything in this module; `graph_wellFormed`,
`witnesses_kernelChecked`, `contracts_cited`, `quotients_honest` and `contracts_consistent`
check it.

The frame reading at a context forgets later contexts. With the frame of propositions on
labelled context paths, `x ∈ x` and `⊥` have the same region value at the empty context, and only
`x ∈ x` is forced after the first extension (`laterFiber`). The arrow carries that fibre as its
counterexample (`frameReadingAtContext_counterexampled`). Before the fibre was proved the arrow
claimed none, and a theorem of this module said so; the new theorem replaces it.

The separation of sets with a group action from their frame reading is witnessed twice: on
actions written out by hand, with no axioms (`explicitFiber`), and on Mathlib's category of
actions (`fiber_frameReading`). The product site is also instantiated on the category of
labelled context paths, where two extensions of the empty context are distinct arrows.

A contract cites theorems only. The fibres of the readings (`fiber_reach_parallel`,
`fiber_reach_idempotent`, `fiber_frameReading`, `fiber_frameReading_globalElement`) carry data,
so they are cited as evidence of the arrows and witnesses, and the contracts cite the
theorems they are built from.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeOptions.CarveOutSites

open Lean (Name)
open Mettapedia.GSLT.Distinction.OptionGraph

/-- The report that records the arguments. -/
def report : Document where
  key := "carveouts-site-top-first-slice-report-20261005"
  title := "Carve-outs, the site-based top, first slice: report"
  date := "2026-10-05"

/-! ## Options -/

def questions : List Question := [
  { id := "site-truth-values"
    title := "Truth values of contextual forcing"
    summary := "Whether the truth values of forcing over a context category are a frame of \
      cosieves at each context, or one frame of up-closed sets of stages."
    facts := [cites [``Mettapedia.SetTheory.CarveOuts.Sites.force_iff_mem_id,
      ``Mettapedia.SetTheory.CarveOuts.Sites.cosieveValue_imply,
      ``Mettapedia.SetTheory.CarveOuts.Sites.cosieveValue_transport]] },
  { id := "symmetry-and-truth-values"
    title := "Symmetry and truth values"
    summary := "Sets with a group action against their reading through two-valued truth values." },
  { id := "site-top"
    title := "A site-based top: contexts times regions"
    summary := "Kripke–Joyal forcing on a context category times the open sets of Cantor space, \
      against contextual forcing and against Heyting-valued names on the frame."
    facts := [cites [``Mettapedia.SetTheory.CarveOuts.Sites.site_derivation_sound,
      ``Mettapedia.SetTheory.CarveOuts.Sites.siteForce_transport,
      ``Mettapedia.SetTheory.CarveOuts.Sites.siteForce_local]] },
  { id := "site-small-maps"
    title := "Small maps on the Cantor product site"
    summary := "The basic axioms on a class of small maps, which the final coalgebra of the \
      power-class functor needs of that class, on presheaves over contexts times the open sets \
      of Cantor space." }
]

/-- The basic small-map axioms, and the theorem assembling them on the Cantor product site from
the three that remain hypotheses. -/
def smallMapsLedger : LedgerRef where
  assumptions := none
  ledger := ``Mettapedia.SetTheory.CarveOuts.Sites.SmallMaps.BasicSmallMapAxioms
  proof := ``Mettapedia.SetTheory.CarveOuts.Sites.SmallMaps.cantor_basicSmallMapAxioms

/-- The frame reading of sets with an action of the two-element group, the group of the
witness: the instance at which the arrow's contract is checked. -/
def flipFrameReading : Action Type Mettapedia.SetTheory.CarveOuts.Sites.Flip → Type :=
  Mettapedia.SetTheory.CarveOuts.Sites.frameReading

/-- The verdicts of all sentences on a set with an action of the two-element group. -/
def flipSentenceVerdicts :
    Action Type Mettapedia.SetTheory.CarveOuts.Sites.Flip →
      Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialLogic.Formula 0 → Prop :=
  Mettapedia.SetTheory.CarveOuts.Sites.sentenceVerdicts

def nodes : List Node := [
  { id := "cosieve-truth-values", question := "site-truth-values"
    title := "Cosieves at each context"
    summary := "Truth values of forcing at a context: the cosieves on it, a frame per context, \
      pulled back along arrows." },
  { id := "persistent-truth-values", question := "site-truth-values"
    title := "One frame of reachable stages"
    summary := "Truth values as up-closed sets of the stages reachable from a context." },
  { id := "g-sets", question := "symmetry-and-truth-values", title := "Sets with a group action"
    summary := "Functors on the one-object category of a group."
    readings := [(.formulas .firstOrder, ``flipSentenceVerdicts)] },
  { id := "frame-reading-of-g-sets", question := "symmetry-and-truth-values"
    title := "Read through two-valued truth values"
    summary := "A set with an action, read as a plain set with its membership."
    denotation := some ``flipFrameReading },
  { id := "product-site", question := "site-top", title := "Contexts times regions of Cantor space"
    summary := "Kripke–Joyal forcing: implication and the universal along every arrow, \
      disjunction, existential, equality and membership on covers."
    facts := [cites [``Mettapedia.SetTheory.CarveOuts.Sites.puncture_excluded_middle_not_forced,
      ``Mettapedia.SetTheory.CarveOuts.Sites.halves_neither_disjunct,
      ``Mettapedia.SetTheory.CarveOuts.Sites.world_site_derivation_sound,
      ``Mettapedia.SetTheory.CarveOuts.Sites.parallel_extensions,
      ``Mettapedia.SetTheory.CarveOuts.Sites.world_equality_agrees]] },
  { id := "contextual-forcing", question := "site-top", title := "Contextual forcing"
    summary := "Forcing along the arrows of a context category, without covers." },
  { id := "frame-valued-names", question := "site-top", title := "Heyting-valued names on the frame"
    summary := "Names valued in the open sets of Cantor space, read on bounded formulas." },
  { id := "cantor-presheaf-small-maps", question := "site-small-maps"
    title := "Maps of presheaves with small fibres"
    summary := "On presheaves over the Cantor product site, the maps whose fibres are small at \
      every point."
    ledger := some smallMapsLedger
    facts := [cites [``Mettapedia.SetTheory.CarveOuts.Sites.SmallMaps.cantor_smallMapClass,
      ``Mettapedia.SetTheory.CarveOuts.Sites.SmallMaps.cantor_monosSmall]] }
]

/-! ## Arrows -/

def arrows : List Arrow := [
  { id := "cosieves-to-reach", source := "cosieve-truth-values", target := "persistent-truth-values"
    kind := .observationalQuotient
    grades := [.lossy]
    summary := "A cosieve read by the stages it reaches."
    evidence := [cites [``Mettapedia.SetTheory.CarveOuts.Sites.Cosieve.reach_sup,
      ``Mettapedia.SetTheory.CarveOuts.Sites.Cosieve.reach_bot,
      ``Mettapedia.SetTheory.CarveOuts.Sites.Parallel.fiber_reach_parallel,
      ``Mettapedia.SetTheory.CarveOuts.Sites.Idempotent.fiber_reach_idempotent]]
    contract := {
      entries := [
        .keeps .connectives [``Mettapedia.SetTheory.CarveOuts.Sites.Cosieve.reach_sup,
          ``Mettapedia.SetTheory.CarveOuts.Sites.Cosieve.reach_bot]
          "joins and falsity, in every category",
        .loses .distinctions [``Mettapedia.SetTheory.CarveOuts.Sites.Parallel.same_reach,
          ``Mettapedia.SetTheory.CarveOuts.Sites.Parallel.selfValue_ne_notSelfValue,
          ``Mettapedia.SetTheory.CarveOuts.Sites.Parallel.reach_inf_ne]
          "which of two parallel arrows: a formula and its negation reach the same stage; meets \
          are not kept",
        .loses .verdicts [``Mettapedia.SetTheory.CarveOuts.Sites.Idempotent.reach_holds_not_force,
          ``Mettapedia.SetTheory.CarveOuts.Sites.Idempotent.collapseCosieve_not_id]
          "the verdict at the context itself, under an idempotent endomorphism"] } },
  { id := "persistent-is-cosieves-on-preorders", source := "persistent-truth-values"
    target := "cosieve-truth-values"
    kind := .equivalence
    grades := [.preserved]
    summary := "Over a preorder of stages the two readings agree: forcing at a stage is the \
      persistent value there, and the connectives are the operations of the frame Persistent."
    evidence := [cites [``Mettapedia.SetTheory.CarveOuts.Sites.force_iff_persistentValue,
      ``Mettapedia.SetTheory.CarveOuts.Sites.Cosieve.reach_injective_of_preorder]]
    contract := {
      entries := [
        .keeps (.formulas .firstOrder)
          [``Mettapedia.SetTheory.CarveOuts.Sites.force_iff_persistentValue,
          ``Mettapedia.SetTheory.CarveOuts.Sites.persistentValue_both,
          ``Mettapedia.SetTheory.CarveOuts.Sites.persistentValue_either,
          ``Mettapedia.SetTheory.CarveOuts.Sites.persistentValue_imply,
          ``Mettapedia.SetTheory.CarveOuts.Sites.persistentValue_exist,
          ``Mettapedia.SetTheory.CarveOuts.Sites.persistentValue_all]
          "every formula of contextual logic",
        .keeps .connectives [``Mettapedia.SetTheory.CarveOuts.Sites.sentenceValue_imply,
          ``Mettapedia.SetTheory.CarveOuts.Sites.sentenceValue_both,
          ``Mettapedia.SetTheory.CarveOuts.Sites.sentenceValue_either]
          "for sentences, exactly the operations of Persistent",
        .keeps .distinctions [``Mettapedia.SetTheory.CarveOuts.Sites.Cosieve.reach_injective_of_preorder]
          "the reach of a cosieve determines it"]
      hypotheses := [``Preorder] } },
  { id := "g-sets-read-through-truth-values", source := "g-sets", target := "frame-reading-of-g-sets"
    kind := .observationalQuotient
    grades := [.factors, .lossy]
    summary := "A set with a group action read as its underlying set: every sentence's verdict \
      is a function of the reading."
    evidence := [cites [``Mettapedia.SetTheory.CarveOuts.Sites.factors_frameReading,
      ``Mettapedia.SetTheory.CarveOuts.Sites.fiber_frameReading,
      ``Mettapedia.SetTheory.CarveOuts.Sites.cosieveOrderIsoProp]]
    contract := {
      entries := [
        .keeps (.formulas .firstOrder) [``Mettapedia.SetTheory.CarveOuts.Sites.force_iff_tarski,
          ``Mettapedia.SetTheory.CarveOuts.Sites.factors_frameReading]
          "every formula of membership and equality: forcing over a group is two-valued truth",
        .keeps .connectives [``Mettapedia.SetTheory.CarveOuts.Sites.cosieve_isGlobal,
          ``Mettapedia.SetTheory.CarveOuts.Sites.reach_holds_iff_mem_id]
          "the truth values: every one global, and read by its verdict at the one context",
        .loses .distinctions [``Mettapedia.SetTheory.CarveOuts.Sites.frameReading_swap_trivial,
          ``Mettapedia.SetTheory.CarveOuts.Sites.not_iso_trivial_swap]
          "the action: two non-isomorphic sets with an action and one reading",
        .loses (.evidence .witnesses)
          [``Mettapedia.SetTheory.CarveOuts.Sites.exists_without_global_element,
          ``Mettapedia.SetTheory.CarveOuts.Sites.globalElement_trivial,
          ``Mettapedia.SetTheory.CarveOuts.Sites.not_globalElement_swap]
          "global elements: an existential forced with no fixed point",
        .unknownAt (.operation .pi) "exponentials of sets with an action",
        .unknownAt (.commitment .choice),
        .unknownAt (.commitment .collection),
        .unknownAt (.commitment .universes)] } },
  { id := "contextual-forcing-in-product-site", source := "contextual-forcing", target := "product-site"
    kind := .interpretation
    grades := [.preserved]
    summary := "A model of contextual forcing pulled back along the projection to the contexts: \
      over open sets, a formula is forced at a context and an inhabited region exactly when it is \
      forced at the context."
    evidence := [cites [``Mettapedia.SetTheory.CarveOuts.Sites.siteForce_context_iff,
      ``Mettapedia.SetTheory.CarveOuts.Sites.control_excluded_middle_not_forced]]
    contract := {
      entries := [
        .keeps (.formulas .firstOrder) [``Mettapedia.SetTheory.CarveOuts.Sites.siteForce_context_iff]
          "every formula of contextual logic, at inhabited open sets",
        .keeps .laws [``Mettapedia.SetTheory.CarveOuts.Sites.site_derivation_sound,
          ``Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialLogic.derivation_sound]
          "every intuitionistic natural-deduction derivation is sound in both",
        .unknownAt (.commitment .collection),
        .unknownAt (.operation .pi)] } },
  { id := "frame-names-in-product-site", source := "frame-valued-names", target := "product-site"
    kind := .interpretation
    grades := [.preserved]
    summary := "Heyting-valued names on the frame, identified on each region below their \
      equality, constant in the contexts: a bounded formula is forced on a region exactly when \
      the region is below its truth value."
    evidence := [cites [``Mettapedia.SetTheory.CarveOuts.Sites.siteForce_translate_iff,
      ``Mettapedia.SetTheory.CarveOuts.Sites.iInf_mem_himp_eq,
      ``Mettapedia.SetTheory.CarveOuts.Sites.iSup_mem_inf_eq]]
    contract := {
      entries := [
        .keeps (.formulas .bounded) [``Mettapedia.SetTheory.CarveOuts.Sites.siteForce_translate_iff]
          "every bounded formula, bounded quantifiers read as guarded ones",
        .unknownAt (.formulas .firstOrder) "unbounded quantifiers over all names",
        .unknownAt (.commitment .collection),
        .unknownAt (.commitment .universes)] } },
  { id := "product-site-read-on-frame", source := "product-site", target := "frame-valued-names"
    kind := .observationalQuotient
    grades := [.lossy]
    summary := "At a context, a formula read by its region value: the join of the regions where \
      it is forced. The value decides forcing at the context, not after later arrows."
    evidence := [cites [``Mettapedia.SetTheory.CarveOuts.Sites.siteForce_shrink_iff,
      ``Mettapedia.SetTheory.CarveOuts.Sites.regionValue_imply,
      ``Mettapedia.SetTheory.CarveOuts.Sites.laterFiber]]
    contract := {
      entries := [
        .keeps .verdicts [``Mettapedia.SetTheory.CarveOuts.Sites.siteForce_shrink_iff,
          ``Mettapedia.SetTheory.CarveOuts.Sites.siteForce_iff_le_regionValue]
          "a formula is forced on a region exactly below its value",
        .keeps .connectives [``Mettapedia.SetTheory.CarveOuts.Sites.regionValue_both,
          ``Mettapedia.SetTheory.CarveOuts.Sites.regionValue_either,
          ``Mettapedia.SetTheory.CarveOuts.Sites.regionValue_bottom]
          "meets, joins and bottom of the frame",
        .keeps .connectives [``Mettapedia.SetTheory.CarveOuts.Sites.regionValue_imply]
          "implication, as a meet over the arrows of the context",
        .loses .distinctions [``Mettapedia.SetTheory.CarveOuts.Sites.selfMember_region_bot,
          ``Mettapedia.SetTheory.CarveOuts.Sites.regionValue_bottom,
          ``Mettapedia.SetTheory.CarveOuts.Sites.selfMember_after_extension,
          ``Mettapedia.SetTheory.CarveOuts.Sites.bottom_not_after_extension]
          "later contexts: with the frame of propositions on labelled context paths, x ∈ x and ⊥ \
          have the same value at the empty context and differ after the first extension; not \
          yet shown on the open sets of Cantor space"] } }
]

/-! ## Observers and witnesses -/

def observers : List Observer := [
  { id := "site-reading-identifies", title := "Identification by a reading"
    reads := "Whether the reading gives the two cases the same value."
    kind := .«theorem», identifies := true },
  { id := "excluded-middle-on-halves", title := "Excluded middle on the two halves"
    reads := "Whether excluded middle of membership in the left half is forced on the whole \
      of Cantor space."
    kind := .«theorem» }
]

def witnesses : List Witness := [
  { id := "parallel-arrows", observer := "site-reading-identifies"
    left := "persistent-truth-values", right := "cosieve-truth-values"
    case := "On the walking parallel pair, x ∈ x is forced along one arrow into the second \
      object and ¬ (x ∈ x) along the other."
    leftVerdict := {
      reading := "Identified: both truth values reach exactly the second object."
      evidence := [cites [``Mettapedia.SetTheory.CarveOuts.Sites.Parallel.fiber_reach_parallel,
        ``Mettapedia.SetTheory.CarveOuts.Sites.Parallel.same_reach]] }
    rightVerdict := {
      reading := "Kept apart: the two cosieves are different, and their meet is empty."
      evidence := [cites [``Mettapedia.SetTheory.CarveOuts.Sites.Parallel.selfValue_ne_notSelfValue,
        ``Mettapedia.SetTheory.CarveOuts.Sites.Parallel.reach_inf_ne]] } },
  { id := "idempotent-collapse", observer := "site-reading-identifies"
    left := "persistent-truth-values", right := "cosieve-truth-values"
    case := "In the monoid with an idempotent, x = y for x := true, y := false, against the top \
      truth value."
    leftVerdict := {
      reading := "Identified: both reach the one context, so the reading says the formula \
        holds there."
      evidence := [cites [``Mettapedia.SetTheory.CarveOuts.Sites.Idempotent.fiber_reach_idempotent,
        ``Mettapedia.SetTheory.CarveOuts.Sites.Idempotent.reach_holds_not_force]] }
    rightVerdict := {
      reading := "Kept apart: x = y is forced only after the idempotent, not at the context."
      evidence := [cites [``Mettapedia.SetTheory.CarveOuts.Sites.Idempotent.cosieveValue_equal,
        ``Mettapedia.SetTheory.CarveOuts.Sites.Idempotent.collapseCosieve_ne_top]] } },
  { id := "negation-and-trivial-action", observer := "site-reading-identifies"
    left := "frame-reading-of-g-sets", right := "g-sets"
    case := "Bool with the two-element group acting by negation, and acting trivially; written \
      out by hand as a carrier with an action, and in Mathlib's category of actions."
    leftVerdict := {
      reading := "Identified: both read as Bool, and every sentence gets the same verdict."
      evidence := [cites [``Mettapedia.SetTheory.CarveOuts.Sites.explicitFiber,
        ``Mettapedia.SetTheory.CarveOuts.Sites.explicit_carriers_eq,
        ``Mettapedia.SetTheory.CarveOuts.Sites.fiber_frameReading,
        ``Mettapedia.SetTheory.CarveOuts.Sites.factors_frameReading]] }
    rightVerdict := {
      reading := "Kept apart: they are not isomorphic, and only the trivial action has a fixed \
        point."
      evidence := [cites [``Mettapedia.SetTheory.CarveOuts.Sites.no_explicitIso_trivial_swap,
        ``Mettapedia.SetTheory.CarveOuts.Sites.not_iso_trivial_swap,
        ``Mettapedia.SetTheory.CarveOuts.Sites.fiber_frameReading_globalElement]] } },
  { id := "cantor-halves", observer := "excluded-middle-on-halves"
    left := "contextual-forcing", right := "product-site"
    case := "Membership holds on the regions inside the left half of Cantor space; excluded \
      middle of membership on the whole space, at any context."
    leftVerdict := {
      reading := "Not forced: without covers neither disjunct holds on the whole space."
      evidence := [cites [``Mettapedia.SetTheory.CarveOuts.Sites.halves_excluded_middle,
        ``Mettapedia.SetTheory.CarveOuts.Sites.world_halves_excluded_middle]] }
    rightVerdict := {
      reading := "Forced, through the cover by the two halves, although neither disjunct is \
        forced on the whole space."
      evidence := [cites [``Mettapedia.SetTheory.CarveOuts.Sites.halves_excluded_middle,
        ``Mettapedia.SetTheory.CarveOuts.Sites.halves_neither_disjunct,
        ``Mettapedia.SetTheory.CarveOuts.Sites.world_halves_excluded_middle]] } }
]

/-- The local graph of this module. -/
def graph : Graph where
  documents := [report]
  questions := questions
  nodes := nodes
  arrows := arrows
  observers := observers
  witnesses := witnesses

theorem graph_wellFormed : graph.wellFormed = true := by
  decide +kernel

/-- Every witness rests on theorems only. -/
theorem witnesses_kernelChecked : witnesses.all Witness.kernelChecked = true := by
  decide +kernel

theorem contracts_cited : graph.contractsCited = true := by
  decide +kernel

theorem quotients_honest : graph.quotientsHonest = true := by
  decide +kernel

theorem contracts_consistent : graph.contractsConsistent = true := by
  decide +kernel

/-- **The frame reading at a context forgets later contexts, and says so.** It claims a lossy
grade, and its one entry it does not preserve cites the theorems of the region-reading fibre.
This replaces the earlier check that the arrow claimed no fibre, which held while none was
proved. -/
theorem frameReadingAtContext_counterexampled :
    (arrows.filter (·.id == "product-site-read-on-frame")).map (fun arrow =>
      ((arrow.grades.any fun claim => claim matches .lossy),
        (arrow.contract.entries.filter (·.status == .notPreserved)).map (·.citations))) =
      [(true, [[``Mettapedia.SetTheory.CarveOuts.Sites.selfMember_region_bot,
        ``Mettapedia.SetTheory.CarveOuts.Sites.regionValue_bottom,
        ``Mettapedia.SetTheory.CarveOuts.Sites.selfMember_after_extension,
        ``Mettapedia.SetTheory.CarveOuts.Sites.bottom_not_after_extension]])] := by
  decide +kernel

/-- Every arrow claiming to forget a distinction records a counterexample. -/
theorem lossy_counterexampled : graph.lossyCounterexampled = true := by
  decide +kernel

end Mettapedia.Languages.MeTTa.PrimeOptions.CarveOutSites
