import Mettapedia.GSLT.Distinction.OptionGraph
import Mettapedia.SetTheory.CarveOuts.Sheaves
import Mettapedia.SetTheory.CarveOuts.SheafPowers

/-!
# Families valued in sheaves, placed in the option graph

Two questions, each with its arrows, contracts and witnesses.

* **Forcing on the product site and in sheaves** (`sheaf-forcing`): a presheaf model on the
  product site of contexts and the open sets of Cantor space, read with Kripke–Joyal forcing on
  covers; the family of sheaves it sheafifies to, read with sheaf forcing; the same presheaf model
  read without covers; and the open-set values of formulas at a context.
  * Sheafification preserves and reflects every formula; it forgets the distinction between
    sections that agree locally.
  * Sheaf models are the presheaf models satisfying the sheaf condition, with the same forcing.
  * The value of a formula at a context is an open set, unchanged by sheafification.
  * Without covers, forcing disagrees with sheaf forcing already on an atomic formula.
* **Small maps on sheaves over Cantor space** (`sheaf-small-maps`): sheaves, where epimorphisms
  are local surjections, and families of sheaves over the contexts.

`graph` is a local graph of everything in this module; `graph_wellFormed`,
`witnesses_kernelChecked`, `contracts_cited`, `quotients_honest`, `contracts_consistent` and
`lossy_counterexampled` check it. The open-set reading at a context has no fibre for sheaf
models, and claims none (`sheafReading_claims_no_fibre`). Collection on sheaves is conditional
on collection in the base, a named hypothesis of the small-map option, which host choice
proves.

The small-map option's first ledger assumed (R) for `Type`-valued sheaves on Cantor space, which
is refuted (`cantor_sheaf_not_representable`). Its ledger is now the small-map laws at that
universe; the basic small-map axioms are recorded on Cantor space one universe up, with no
named hypothesis. The first ledger stays on the option as history, and the option
records the refutation.

A contract cites theorems only. The fibre of the sheafification unit (`fiber_sheafUnit`) carries
data, so it is cited as evidence of its arrow, and the contract cites the theorem it is built
from.
-/

set_option autoImplicit false

universe w

namespace Mettapedia.Languages.MeTTa.PrimeOptions.CarveOutSheaves

open Lean (Name)
open CategoryTheory
open Mettapedia.GSLT.Distinction.OptionGraph

/-- The report that records the arguments. -/
def report : Document where
  key := "carveouts-sheaf-slice-report-20261005"
  title := "Carve-outs, families valued in sheaves: report"
  date := "2026-10-05"

/-! ## Options -/

def questions : List Question := [
  { id := "sheaf-forcing"
    title := "Forcing on the product site and in sheaves"
    summary := "Whether Kripke–Joyal forcing on a presheaf model of the product site of contexts \
      and open sets agrees with forcing in the sheaves it sheafifies to."
    facts := [cites [``Mettapedia.SetTheory.CarveOuts.Sheaves.siteForce_iff_of_local,
      ``Mettapedia.SetTheory.CarveOuts.Sheaves.siteForce_iff_sheafForce]] },
  { id := "sheaf-small-maps"
    title := "Small maps on sheaves over Cantor space"
    summary := "The axioms on a class of small maps, on sheaves over Cantor space where \
      epimorphisms are local surjections, and on families of such sheaves over the contexts."
    facts := [cites [``Mettapedia.SetTheory.CarveOuts.Sheaves.sheafSmall_collection,
      ``Mettapedia.SetTheory.CarveOuts.Sheaves.baseCollection_of_choice]] }
]

/-- (R) for sheaves on Cantor space with values in `Type`, the universe of its points: one small
map of which every small map is a pullback. The ledger first recorded for the small-map option
assumed it; it is refuted. -/
def CantorTypeRepresentability : Prop :=
  Mettapedia.SetTheory.CarveOuts.Sites.SmallMaps.RepresentabilityAxiom
    (Mettapedia.SetTheory.CarveOuts.Sheaves.sheafSmall.{w} :
      MorphismProperty (Mettapedia.SetTheory.CarveOuts.Sheaves.SheafOn (ℕ → Bool)))

/-- The refutation of (R) for sheaves on Cantor space with values in `Type`. -/
def typeRepresentabilityRefuted : Refutation where
  hypothesis := ``CantorTypeRepresentability
  scope := "(R) for sheaves on Cantor space with values in Type: every map is small there, and a \
    universal small map would inject the power set of its sections into them"
  refutedBy := [``Mettapedia.SetTheory.CarveOuts.Sheaves.cantor_sheaf_not_representable]

/-- The ledger first recorded for the small-map option: the basic small-map axioms on
`Type`-valued sheaves over Cantor space, from (P1), (I) and (R) as hypotheses. Its hypothesis (R)
is refuted, so it is kept as history only. -/
def conditionalCoalgebraLedger : LedgerRef where
  assumptions := none
  ledger := ``Mettapedia.SetTheory.CarveOuts.Sites.SmallMaps.BasicSmallMapAxioms
  proof := ``Mettapedia.SetTheory.CarveOuts.Sheaves.cantor_sheaf_basicSmallMapAxioms

/-- The established small-map laws at the original value universe. Representability is
refuted there; the separate raised-universe option records its positive construction. -/
def sheafSmallMapsLedger : LedgerRef where
  assumptions := none
  ledger := ``Mettapedia.SetTheory.CarveOuts.Sites.SmallMaps.SmallMapClass
  proof := ``Mettapedia.SetTheory.CarveOuts.Sheaves.cantor_sheafSmallMapClass

def nodes : List Node := [
  { id := "presheaf-model", question := "sheaf-forcing"
    title := "A presheaf model on the product site"
    summary := "A value family on contexts times the open sets of Cantor space, with a persistent \
      membership, read with forcing on covers."
    facts := [cites [``Mettapedia.SetTheory.CarveOuts.Sites.site_derivation_sound,
      ``Mettapedia.SetTheory.CarveOuts.Sites.siteForce_local]] },
  { id := "sheaf-family-model", question := "sheaf-forcing"
    title := "A family of sheaves over the contexts"
    summary := "A functor from the contexts to sheaves on Cantor space, with a persistent and \
      local membership, read with Kripke–Joyal sheaf forcing."
    facts := [cites [``Mettapedia.SetTheory.CarveOuts.Sheaves.sheaf_derivation_sound,
      ``Mettapedia.SetTheory.CarveOuts.Sheaves.extension_sheafify_eq,
      ``Mettapedia.SetTheory.CarveOuts.Sheaves.sheaf_puncture_excluded_middle_not_forced,
      ``Mettapedia.SetTheory.CarveOuts.Sheaves.sheaf_halves_excluded_middle]] },
  { id := "cover-free-forcing", question := "sheaf-forcing"
    title := "The presheaf model read without covers"
    summary := "Contextual forcing along the arrows of the product site, with no covers." },
  { id := "open-set-values", question := "sheaf-forcing"
    title := "Open-set values at a context"
    summary := "A formula at a context read by the join of the open sets on which it is forced." },
  { id := "cantor-sheaf-small-maps", question := "sheaf-small-maps"
    title := "Maps of sheaves with small fibres"
    summary := "On Type-valued sheaves over Cantor space every map has small fibres; \
      epimorphisms are the locally surjective maps. The small-map laws hold, but \
      representability is refuted at this value universe."
    ledger := some sheafSmallMapsLedger
    supersededLedgers := [conditionalCoalgebraLedger]
    refuted := [typeRepresentabilityRefuted]
    hypotheses := [
      { name := ``Mettapedia.SetTheory.CarveOuts.Sheaves.BaseCollection
        conditions := "Collection on sheaves: collection for the maps of Lean's types with \
          small fibres, applied once"
        provedBy := [``Mettapedia.SetTheory.CarveOuts.Sheaves.baseCollection_of_choice] }]
    facts := [cites [``Mettapedia.SetTheory.CarveOuts.Sheaves.cantor_sheafSmallMapClass,
      ``Mettapedia.SetTheory.CarveOuts.Sheaves.cantor_sheafMonosSmall,
      ``Mettapedia.SetTheory.CarveOuts.Sheaves.cantor_sheafCollection,
      ``Mettapedia.SetTheory.CarveOuts.Sheaves.cantor_sheafCollection_of_choice,
      ``Mettapedia.SetTheory.CarveOuts.Sheaves.cantor_sheaf_not_representable,
      ``Mettapedia.SetTheory.CarveOuts.Sheaves.cantor_sheaf_not_basicSmallMapAxioms]] },
  { id := "cantor-family-small-maps", question := "sheaf-small-maps"
    title := "Maps of families of sheaves, small at every context"
    summary := "On functors from the contexts to sheaves over Cantor space, the maps small at \
      every context."
    facts := [cites [``Mettapedia.SetTheory.CarveOuts.Sheaves.cantor_familySmallMapClass,
      ``Mettapedia.SetTheory.CarveOuts.Sheaves.cantor_familyMonosSmall]] }
]

/-! ## Arrows -/

def arrows : List Arrow := [
  { id := "presheaf-model-sheafified", source := "presheaf-model", target := "sheaf-family-model"
    kind := .interpretation
    grades := [.preserved, .lossy]
    summary := "A presheaf model sheafified pointwise in the contexts, with the local image of its \
      membership: every formula is forced on the presheaf model exactly when it is forced in \
      sheaves at the environment carried by the unit."
    evidence := [cites [``Mettapedia.SetTheory.CarveOuts.Sheaves.siteForce_iff_sheafForce,
      ``Mettapedia.SetTheory.CarveOuts.Sheaves.sheafUnit_locallyInjective,
      ``Mettapedia.SetTheory.CarveOuts.Sheaves.sheafUnit_locallySurjective,
      ``Mettapedia.SetTheory.CarveOuts.Sheaves.fiber_sheafUnit]]
    contract := {
      entries := [
        .keeps (.formulas .firstOrder)
          [``Mettapedia.SetTheory.CarveOuts.Sheaves.siteForce_iff_sheafForce,
          ``Mettapedia.SetTheory.CarveOuts.Sheaves.siteForce_iff_of_local]
          "every formula of contextual material logic, at every point and environment",
        .keeps .verdicts
          [``Mettapedia.SetTheory.CarveOuts.Sheaves.sheafForce_sheafify_forward]
          "along every arrow of the contexts",
        .keeps .laws [``Mettapedia.SetTheory.CarveOuts.Sites.site_derivation_sound,
          ``Mettapedia.SetTheory.CarveOuts.Sheaves.sheaf_derivation_sound]
          "every intuitionistic natural-deduction derivation is sound in both",
        .loses .distinctions [``Mettapedia.SetTheory.CarveOuts.Sheaves.sheafUnit_identifies]
          "sections of the presheaf that agree on a cover are identified",
        .unknownAt (.operation .pi),
        .unknownAt (.commitment .collection) "Collection read in the models",
        .unknownAt (.commitment .universes)] } },
  { id := "sheaf-models-in-presheaf-models", source := "sheaf-family-model"
    target := "presheaf-model"
    kind := .restriction
    grades := [.preserved]
    summary := "A sheaf model read as a presheaf model on the product site: sheaf forcing is \
      forcing on covers, restricted to the models that satisfy the sheaf condition."
    evidence := [cites [``Mettapedia.SetTheory.CarveOuts.Sheaves.sheafForce_iff_siteForce,
      ``Mettapedia.SetTheory.CarveOuts.Sheaves.sheaf_eq_of_covered]]
    contract := {
      entries := [
        .keeps (.formulas .firstOrder)
          [``Mettapedia.SetTheory.CarveOuts.Sheaves.sheafForce_iff_siteForce]
          "every formula: the cover clauses for the atoms collapse on sheaves",
        .keeps .laws [``Mettapedia.SetTheory.CarveOuts.Sheaves.sheafForce_transport,
          ``Mettapedia.SetTheory.CarveOuts.Sheaves.sheafForce_local]
          "persistence and locality",
        .keeps .verdicts [``Mettapedia.SetTheory.CarveOuts.Sheaves.extension_sheafify_eq]
          "the extension of a formula at a context is a closed subpresheaf",
        .unknownAt (.operation .pi)] } },
  { id := "sheaf-model-read-on-open-sets", source := "sheaf-family-model"
    target := "open-set-values"
    kind := .observationalQuotient
    grades := [.ungraded]
    summary := "At a context, a formula of a sheaf model read by the join of the open sets on \
      which it is forced."
    evidence := [cites [``Mettapedia.SetTheory.CarveOuts.Sheaves.sheafForce_shrink_iff,
      ``Mettapedia.SetTheory.CarveOuts.Sheaves.sheafRegionValue_eq_regionValue]]
    contract := {
      entries := [
        .keeps .verdicts [``Mettapedia.SetTheory.CarveOuts.Sheaves.sheafForce_shrink_iff]
          "a formula is forced on an open set exactly below its value",
        .keeps .connectives [``Mettapedia.SetTheory.CarveOuts.Sheaves.sheafRegionValue_eq_regionValue,
          ``Mettapedia.SetTheory.CarveOuts.Sites.regionValue_both,
          ``Mettapedia.SetTheory.CarveOuts.Sites.regionValue_either,
          ``Mettapedia.SetTheory.CarveOuts.Sites.regionValue_bottom,
          ``Mettapedia.SetTheory.CarveOuts.Sites.regionValue_imply]
          "meets, joins and the empty set; implication as a meet over the arrows of the context",
        .keeps .verdicts [``Mettapedia.SetTheory.CarveOuts.Sheaves.regionValue_eq_sheafRegionValue]
          "the value is unchanged by sheafification",
        .unknownAt .distinctions "what the reading at one context forgets of the others"] } }
]

/-! ## Observers and witnesses -/

def observers : List Observer := [
  { id := "equality-of-locally-equal-sections", title := "Equality of locally equal sections"
    reads := "Whether the equality of two sections on the whole space, which agree on each half of \
      Cantor space, is forced."
    kind := .«theorem» },
  { id := "identity-of-sections", title := "Identity of sections"
    reads := "Whether two sections on the whole space are one element of the model's carrier."
    kind := .«theorem», identifies := true }
]

def witnesses : List Witness := [
  { id := "sections-agreeing-on-halves", observer := "equality-of-locally-equal-sections"
    left := "cover-free-forcing", right := "sheaf-family-model"
    case := "A presheaf with a Boolean on the whole of Cantor space and a single section on every \
      smaller open set; the two Booleans, at any context."
    leftVerdict := {
      reading := "Refuted: without covers, equality is equality of the two sections."
      evidence := [cites [``Mettapedia.SetTheory.CarveOuts.Sheaves.cover_free_disagrees]] }
    rightVerdict := {
      reading := "Forced: the two halves cover the space, and the sheafification identifies the \
        two sections."
      evidence := [cites [``Mettapedia.SetTheory.CarveOuts.Sheaves.cover_free_disagrees,
        ``Mettapedia.SetTheory.CarveOuts.Sheaves.sheafUnit_identifies]] } },
  { id := "sections-agreeing-on-halves-with-covers", observer := "equality-of-locally-equal-sections"
    left := "cover-free-forcing", right := "presheaf-model"
    case := "The same two Booleans of the same presheaf, at any context."
    leftVerdict := {
      reading := "Refuted: without covers, equality is equality of the two sections."
      evidence := [cites [``Mettapedia.SetTheory.CarveOuts.Sheaves.cover_free_disagrees]] }
    rightVerdict := {
      reading := "Forced on the presheaf model itself: the two halves cover the space and the \
        sections agree on each."
      evidence := [cites [``Mettapedia.SetTheory.CarveOuts.Sheaves.cover_free_disagrees,
        ``Mettapedia.SetTheory.CarveOuts.Sheaves.twoSections_agree_on_halves]] } },
  { id := "open-set-value-of-equality", observer := "equality-of-locally-equal-sections"
    left := "cover-free-forcing", right := "open-set-values"
    case := "The two Booleans of the presheaf on the whole space, which agree on each half."
    leftVerdict := {
      reading := "Refuted: without covers, equality is equality of the two sections."
      evidence := [cites [``Mettapedia.SetTheory.CarveOuts.Sheaves.cover_free_disagrees]] }
    rightVerdict := {
      reading := "Forced: equality is forced on the whole space in sheaves, so its open-set value \
        is the whole space."
      evidence := [cites [``Mettapedia.SetTheory.CarveOuts.Sheaves.cover_free_disagrees,
        ``Mettapedia.SetTheory.CarveOuts.Sheaves.sheafForce_shrink_iff]] } },
  { id := "two-sections-one-image", observer := "identity-of-sections"
    left := "sheaf-family-model", right := "presheaf-model"
    case := "The two Booleans of the presheaf on the whole space, which agree on each half. Every \
      formula gets the same verdict on both options; the carriers differ."
    leftVerdict := {
      reading := "Identified: the unit of sheafification sends both to one section."
      evidence := [cites [``Mettapedia.SetTheory.CarveOuts.Sheaves.sheafUnit_identifies,
        ``Mettapedia.SetTheory.CarveOuts.Sheaves.fiber_sheafUnit]] }
    rightVerdict := {
      reading := "Kept apart: they are two sections of the presheaf."
      evidence := [cites [``Mettapedia.SetTheory.CarveOuts.Sheaves.twoSections_ne]] } }
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

/-- Every arrow claiming to forget a distinction records a counterexample. -/
theorem lossy_counterexampled : graph.lossyCounterexampled = true := by
  decide +kernel

/-- **The open-set reading of a sheaf model claims no forgotten distinction.** No fibre is built
for it: it claims no lossy grade and no entry it does not preserve. -/
theorem sheafReading_claims_no_fibre :
    (arrows.filter (·.id == "sheaf-model-read-on-open-sets")).map (fun arrow =>
      (arrow.grades.any fun claim => claim matches .lossy) ||
        arrow.contract.entries.any (·.status == .notPreserved)) = [false] := by
  decide +kernel

end Mettapedia.Languages.MeTTa.PrimeOptions.CarveOutSheaves
