import Mettapedia.GSLT.Distinction.OptionGraph
import Mettapedia.SetTheory.CarveOuts.SheafPowers
import Mettapedia.GSLT.Distinction.FrontierWitnesses.SheafIdentifications

/-!
# Power classes, natural numbers and representability on sheaves, placed in the option graph

Four questions, with their arrows, contracts and witnesses.

* **The universe of the values** (`sheaf-value-universe`): sheaves on Cantor space with values in
  `Type`, the universe of its points, against sheaves on Cantor space lifted one universe above the
  small fibres.
  * With values in `Type` every map is small; power classes and the smallness of the natural
    numbers hold in that degenerate form, and representability fails by Cantor's theorem.
  * One universe up, some maps are not small and the small-map package S1–S5/P1/I/R holds.
    This does not construct the final coalgebra of the power-class functor; the proofs use
    host choice.
* **Classifying small maps** (`sheaf-small-map-classifier`): the small maps of sheaves are exactly
  the pullbacks of membership in the power class of the generic sheaf.
* **The natural numbers** (`sheaf-natural-numbers`): every parametrised natural numbers object of
  sheaves is the sheaf of locally constant natural numbers, up to isomorphism.
* **Power classes** (`sheaf-power-classes`): small relations into a sheaf are classified by maps
  into its power class.

In each of the last three questions the two options define the same thing, and an equivalence
arrow graded as the same extension records it: small maps and pullbacks of the universal small
map are the same maps (`sheafSmall_iff_universalPullback`); every parametrised natural numbers
object is the locally constant one by a unique isomorphism respecting zero and successor
(`parametrisedNNO_iso_natNNO`); and pulling back membership is a bijection from maps into the
power class onto small relations (`classified_bijective`). `identifications` checks that these
are the three pairs the local graph identifies.

`graph` is a local graph of everything in this module; `graph_wellFormed`,
`witnesses_kernelChecked`, `contracts_cited`, `quotients_honest`, `contracts_consistent` and
`lossy_counterexampled` check it. No arrow claims a forgotten distinction. Whether classifying maps
are unique up to isomorphism of small maps is recorded as unknown. Host choice enters the
encoding of a small map through `Shrink`.

**Obligations of the final coalgebra** (`obligations`). The bundle of basic small-map axioms is
proved one universe up; it feeds the paper's Theorem 3.7 and Corollary 4.3 only together with the
ambient obligations, recorded apart with their status: the Heyting pretopos (open), the indexed
natural numbers object (proved: `natNNO`), the axioms in indexed form (open), the power-class
functor as an indexed functor (open) and the final coalgebra itself (open). For stronger
theories: (E) for Theorem 4.4 (stated, open), (P2) for Theorem 4.5 (open), (M) (proved) and (C)
(proved from base collection) for Theorems 4.5 and 4.7, and (F) for Theorem 4.7 (open).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeOptions.CarveOutSheafPowers

open Lean (Name)
open Mettapedia.GSLT.Distinction.OptionGraph
open Mettapedia.GSLT.Distinction.FrontierWitnesses

/-- The report that records the arguments. -/
def report : Document where
  key := "carveouts-sheaf-powers-report-20261005"
  title := "Carve-outs, power classes, natural numbers and representability on sheaves: report"
  date := "2026-10-05"

/-! ## Questions and options -/

def questions : List Question := [
  { id := "sheaf-value-universe"
    title := "The universe of sheaf values on Cantor space"
    summary := "Whether sheaves of sets on Cantor space take values in the universe of its points \
      or in a universe above the small fibres, compared on the small-map axioms S1–S5/P1/I/R \
      needed for a hyperset final-coalgebra construction."
    facts := [cites [``Mettapedia.SetTheory.CarveOuts.Sheaves.not_representable_of_small_terminal,
      ``Mettapedia.SetTheory.CarveOuts.Sheaves.sheaf_basicSmallMapAxioms_of_small]] },
  { id := "sheaf-small-map-classifier"
    title := "Classifying small maps of sheaves"
    summary := "Whether the small maps of sheaves on a space are the pullbacks of one small map."
    facts := [cites [``Mettapedia.SetTheory.CarveOuts.Sheaves.sheafSmall_representable]] },
  { id := "sheaf-natural-numbers"
    title := "The natural numbers object of sheaves"
    summary := "A parametrised natural numbers object of sheaves on a space, and the sheaf of \
      locally constant natural numbers."
    facts := [cites [``Mettapedia.SetTheory.CarveOuts.Sheaves.sheafSmall_naturalsSmall]] },
  { id := "sheaf-power-classes"
    title := "Power classes of sheaves"
    summary := "Small relations into a sheaf, and maps into its power class of small local \
      families of sections."
    facts := [cites [``Mettapedia.SetTheory.CarveOuts.Sheaves.sheafSmall_powerClassAxiom]] }
]

/-- The small-map axioms S1–S5/P1/I/R, proved for sheaves on the lifted Cantor space.
The host dependencies include choice; this ledger does not assert final-coalgebra existence. -/
def liftedCantorLedger : LedgerRef where
  assumptions := none
  ledger := ``Mettapedia.SetTheory.CarveOuts.Sites.SmallMaps.BasicSmallMapAxioms
  proof := ``Mettapedia.SetTheory.CarveOuts.Sheaves.cantorUp_basicSmallMapAxioms

/-- The open sets form a small type: the hypothesis of the general theorems, proved for the
lifted Cantor space. -/
def smallOpens : NamedHypothesis where
  name := ``Small
  conditions := "Every theorem on a general space: its open sets form a small type"
  provedBy := [``Mettapedia.SetTheory.CarveOuts.Sheaves.cantorUp_opens_small]

def nodes : List Node := [
  { id := "cantor-sheaves-in-type", question := "sheaf-value-universe"
    title := "Sheaves on Cantor space with values in Type"
    summary := "Sheaves of sets on Cantor space, valued in the universe of its points: every \
      map is small, so the small maps are all maps."
    facts := [cites [``Mettapedia.SetTheory.CarveOuts.Sheaves.cantor_sheafSmall_all,
      ``Mettapedia.SetTheory.CarveOuts.Sheaves.cantor_sheaf_powerClassAxiom,
      ``Mettapedia.SetTheory.CarveOuts.Sheaves.cantor_sheaf_naturalsSmall,
      ``Mettapedia.SetTheory.CarveOuts.Sheaves.cantor_sheaf_not_representable,
      ``Mettapedia.SetTheory.CarveOuts.Sheaves.cantor_sheaf_not_basicSmallMapAxioms]] },
  { id := "cantor-sheaves-one-universe-up", question := "sheaf-value-universe"
    title := "Sheaves on Cantor space one universe above the small fibres"
    summary := "Sheaves of sets on Cantor space lifted to the universe w + 1, with the maps whose \
      fibres are w-small."
    ledger := some liftedCantorLedger
    facts := [cites [``Mettapedia.SetTheory.CarveOuts.Sheaves.cantorUp_basicSmallMapAxioms,
      ``Mettapedia.SetTheory.CarveOuts.Sheaves.cantorUp_monosSmall,
      ``Mettapedia.SetTheory.CarveOuts.Sheaves.cantorUp_collection_of_choice,
      ``Mettapedia.SetTheory.CarveOuts.Sheaves.cantorUp_not_all_small]] },
  { id := "small-maps-of-sheaves", question := "sheaf-small-map-classifier"
    title := "Maps of sheaves with small fibres"
    summary := "On a space whose open sets form a small type, with values above the small fibres, \
      the maps whose fibres are small at every open set."
    hypotheses := [smallOpens]
    facts := [cites [``Mettapedia.SetTheory.CarveOuts.Sheaves.sheafSmall_smallMapClass]] },
  { id := "pullbacks-of-generic-membership", question := "sheaf-small-map-classifier"
    title := "Pullbacks of membership in the power class of the generic sheaf"
    summary := "The maps that are pullbacks of membership over the power class of the sheafified \
      codes of small sets."
    hypotheses := [smallOpens]
    facts := [cites [``Mettapedia.SetTheory.CarveOuts.Sheaves.universalMap_small]] },
  { id := "locally-constant-naturals", question := "sheaf-natural-numbers"
    title := "The sheaf of locally constant natural numbers"
    summary := "On an open set, the natural-number functions on its points with open fibres; zero \
      and successor pointwise; recursion glued on the level sets."
    facts := [cites [``Mettapedia.SetTheory.CarveOuts.Sheaves.openFibres_iff_isLocallyConstant,
      ``Mettapedia.SetTheory.CarveOuts.Sheaves.natSheaf_small]] },
  { id := "any-parametrised-nno", question := "sheaf-natural-numbers"
    title := "Any parametrised natural numbers object of sheaves"
    summary := "An object with zero and successor and unique recursion with parameters." },
  { id := "small-relations-into-a-sheaf", question := "sheaf-power-classes"
    title := "Small relations into a sheaf"
    summary := "Subobjects of a product `I ⨯ A` whose projection to `I` is small." },
  { id := "maps-into-power-class", question := "sheaf-power-classes"
    title := "Maps into the power class"
    summary := "Maps from `I` into the sheaf of small local families of sections of `A`."
    hypotheses := [smallOpens]
    facts := [cites [``Mettapedia.SetTheory.CarveOuts.Sheaves.powerPresheaf_isSheaf,
      ``Mettapedia.SetTheory.CarveOuts.Sheaves.memFst_small]] }
]

/-! ## Arrows -/

def arrows : List Arrow := [
  { id := "small-maps-as-pullbacks", source := "small-maps-of-sheaves"
    target := "pullbacks-of-generic-membership"
    kind := .interpretation
    grades := [.preserved]
    summary := "A small map read as a pullback of membership: the map and its encoding into the \
      generic sheaf are classified by a map into the power class, and the square is a pullback."
    evidence := [cites [``Mettapedia.SetTheory.CarveOuts.Sheaves.small_isPullback_universal,
      ``Mettapedia.SetTheory.CarveOuts.Sheaves.encode_jointlyInjective]]
    contract := {
      entries := [
        .keeps (.commitment .universes)
          [``Mettapedia.SetTheory.CarveOuts.Sheaves.sheafSmall_representable,
          ``Mettapedia.SetTheory.CarveOuts.Sheaves.small_isPullback_universal]
          "every small map is a pullback of the universal small map, along the identity cover; \
          the argument uses no points, but covers are read through Mathlib's pointwise topology \
          of open sets (covered_iff_mem)",
        .keeps .distinctions [``Mettapedia.SetTheory.CarveOuts.Sheaves.encode_jointlyInjective]
          "the encoding separates the sections of each fibre",
        .unknownAt .distinctions
          "whether the classifying map is unique up to isomorphism of small maps",
        .unknownAt (.commitment .choice) "an encoding without a chosen equivalence"] } },
  { id := "small-maps-are-pullbacks-of-membership", source := "small-maps-of-sheaves"
    target := "pullbacks-of-generic-membership"
    kind := .equivalence
    grades := [.exactKernel .extension]
    summary := "A map of sheaves is small exactly when it is a pullback of the universal small \
      map: the two options name the same maps."
    evidence := [cites [``SheafIdentifications.sheafSmall_iff_universalPullback]]
    contract := {
      entries := [
        .keeps .verdicts [``SheafIdentifications.sheafSmall_iff_universalPullback]
          "smallness of every map of sheaves, on a space whose open sets form a small type, with \
          values one universe above the small fibres",
        .unknownAt .distinctions
          "whether the classifying square is unique up to isomorphism of small maps"] } },
  { id := "pullbacks-of-membership-small", source := "pullbacks-of-generic-membership"
    target := "small-maps-of-sheaves"
    kind := .restriction
    grades := [.preserved]
    summary := "A pullback of membership is small: membership over the power class is small and \
      small maps are stable under pullback."
    evidence := [cites [``Mettapedia.SetTheory.CarveOuts.Sheaves.universalMap_small,
      ``Mettapedia.SetTheory.CarveOuts.Sheaves.sheafSmall_pullback]]
    contract := {
      entries := [
        .keeps .laws [``Mettapedia.SetTheory.CarveOuts.Sheaves.sheafSmall_pullback,
          ``Mettapedia.SetTheory.CarveOuts.Sheaves.universalMap_small]
          "pullback stability of small maps; covers are read through Mathlib's pointwise \
          topology of open sets (covered_iff_mem)"] } },
  { id := "parametrised-nno-is-locally-constant", source := "any-parametrised-nno"
    target := "locally-constant-naturals"
    kind := .equivalence
    grades := [.exactKernel .extension]
    summary := "Every parametrised natural numbers object of sheaves is the sheaf of locally \
      constant natural numbers, by a unique isomorphism respecting zero and successor, built by \
      recursion in both directions."
    evidence := [cites [``SheafIdentifications.parametrisedNNO_iso_natNNO,
      ``Mettapedia.SetTheory.CarveOuts.Sheaves.paramNNO_hom_ext,
      ``Mettapedia.SetTheory.CarveOuts.Sheaves.paramNNOMap_zero,
      ``Mettapedia.SetTheory.CarveOuts.Sheaves.paramNNOMap_succ]]
    contract := {
      entries := [
        .keeps .distinctions [``SheafIdentifications.parametrisedNNO_iso_natNNO]
          "the isomorphism respecting zero and successor is unique",
        .keeps .laws [``Mettapedia.SetTheory.CarveOuts.Sheaves.paramNNOMap_zero,
          ``Mettapedia.SetTheory.CarveOuts.Sheaves.paramNNOMap_succ,
          ``Mettapedia.SetTheory.CarveOuts.Sheaves.paramNNO_hom_ext]
          "zero and successor, and maps determined by them",
        .keeps .laws [``Mettapedia.SetTheory.CarveOuts.Sheaves.recMap_zero,
          ``Mettapedia.SetTheory.CarveOuts.Sheaves.recMap_succ,
          ``Mettapedia.SetTheory.CarveOuts.Sheaves.natRec_ext]
          "recursion with parameters for the locally constant natural numbers, glued on level \
          sets of points",
        .keeps .verdicts [``Mettapedia.SetTheory.CarveOuts.Sheaves.sheafSmall_naturalsSmall]
          "smallness of the natural numbers object; the proof uses points: natural-number \
          functions on points and their level sets"] } },
  { id := "relations-classified-by-power-class", source := "small-relations-into-a-sheaf"
    target := "maps-into-power-class"
    kind := .equivalence
    grades := [.exactKernel .extension]
    summary := "A small relation is the pullback of membership along a unique map into the power \
      class: pulling back membership is a bijection from maps into the power class onto small \
      relations."
    evidence := [cites [``SheafIdentifications.classified_bijective,
      ``Mettapedia.SetTheory.CarveOuts.Sheaves.sheafSmall_powerClassAxiom,
      ``Mettapedia.SetTheory.CarveOuts.Sheaves.classify_isPullback,
      ``Mettapedia.SetTheory.CarveOuts.Sheaves.pullback_mem_iff]]
    contract := {
      entries := [
        .keeps .distinctions [``SheafIdentifications.classified_bijective,
          ``Mettapedia.SetTheory.CarveOuts.Sheaves.sheafSmall_powerClassAxiom]
          "distinct small relations have distinct classifying maps, and every map classifies \
          a small relation; the argument uses no \
          points, but covers are read through Mathlib's pointwise topology of open sets \
          (covered_iff_mem)",
        .keeps .verdicts [``Mettapedia.SetTheory.CarveOuts.Sheaves.pullback_mem_iff]
          "a section is in the relation exactly when its member is in its family",
        .unknownAt (.commitment .universes)
          "a predicative power class; the families of sections are sets of the host"] } }
]

/-! ## Observers and witnesses -/

def observers : List Observer := [
  { id := "universal-small-map", title := "A universal small map"
    reads := "Whether one small map has every small map as a pullback over an epimorphism."
    kind := .«theorem» },
  { id := "every-map-small", title := "Every map is small"
    reads := "Whether every map to the terminal sheaf has small fibres."
    kind := .«theorem» }
]

def witnesses : List Witness := [
  { id := "representability-on-cantor", observer := "universal-small-map"
    left := "cantor-sheaves-in-type", right := "cantor-sheaves-one-universe-up"
    case := "Sheaves of sets on Cantor space, with the maps whose fibres are w-small at every open \
      set."
    leftVerdict := {
      reading := "Refuted: a universal map would inject the power set of its sections into them, \
        on a nonempty open set."
      evidence := [cites [``Mettapedia.SetTheory.CarveOuts.Sheaves.cantor_sheaf_not_representable,
        ``Mettapedia.SetTheory.CarveOuts.Sheaves.not_representable_of_small_terminal]] }
    rightVerdict := {
      reading := "Holds: membership in the power class of the generic sheaf, already globally."
      evidence := [cites [``Mettapedia.SetTheory.CarveOuts.Sheaves.cantorUp_basicSmallMapAxioms,
        ``Mettapedia.SetTheory.CarveOuts.Sheaves.sheafSmall_representable]] } },
  { id := "all-maps-small-on-cantor", observer := "every-map-small"
    left := "cantor-sheaves-in-type", right := "cantor-sheaves-one-universe-up"
    case := "The map to the terminal sheaf from the sheaf of functions on points into a universe \
      of types."
    leftVerdict := {
      reading := "Every map is small: the fibres lie in Type."
      evidence := [cites [``Mettapedia.SetTheory.CarveOuts.Sheaves.cantor_sheafSmall_all]] }
    rightVerdict := {
      reading := "Not small: the fibre on the whole space contains a copy of Type w."
      evidence := [cites [``Mettapedia.SetTheory.CarveOuts.Sheaves.cantorUp_not_all_small]] } }
]

/-! ## Obligations of the final coalgebra -/

/-- The paper whose theorems the obligations feed. -/
def finalCoalgebraPaper : Document where
  key := "van-den-berg-de-marchi-2007"
  title := "Models of non-well-founded sets via an indexed final coalgebra theorem (van den Berg \
    and De Marchi)"
  date := "2007"

/-- What the indexed final coalgebra theorem and its corollaries need, on sheaves over Cantor
space lifted one universe, with the status of each. Theorem 3.7 gives the indexed final
coalgebra of the power-class functor; Corollary 4.3 makes it a model of `CZF₀ + AFA`; Theorems
4.4, 4.5 and 4.7 give stronger theories from further axioms. -/
def obligations : List Obligation := [
  { id := "basic-small-map-axioms", source := finalCoalgebraPaper.key
    title := "The basic small-map axioms (S1)–(S5), (P1), (I), (R)"
    feeds := ["Theorem 3.7", "Corollary 4.3"], status := .proved
    statement := some ``Mettapedia.SetTheory.CarveOuts.Sites.SmallMaps.BasicSmallMapAxioms
    evidence := [``Mettapedia.SetTheory.CarveOuts.Sheaves.cantorUp_basicSmallMapAxioms]
    note := "On sheaves over Cantor space lifted one universe, in non-indexed form. Rule (I) \
      quantifies over the parametrised natural numbers objects that are given: it assumes one \
      rather than carrying one." },
  { id := "heyting-pretopos", source := finalCoalgebraPaper.key
    title := "The ambient category is a Heyting pretopos"
    feeds := ["Theorem 3.7"], status := .«open»
    note := "Not stated." },
  { id := "indexed-nno", source := finalCoalgebraPaper.key
    title := "An indexed natural numbers object"
    feeds := ["Theorem 3.7"], status := .proved
    statement := some ``Mettapedia.SetTheory.CarveOuts.Sites.SmallMaps.ParamNNO
    evidence := [``Mettapedia.SetTheory.CarveOuts.Sheaves.natNNO,
      ``Mettapedia.SetTheory.CarveOuts.Sheaves.natRec_ext,
      ``Mettapedia.SetTheory.CarveOuts.Sheaves.sheafSmall_naturalsSmall]
    note := "The sheaf of locally constant natural numbers, with recursion with parameters, is \
      the paper's indexed natural numbers object, on sheaves over any space. It is built and \
      small; the bundle's rule (I) does not carry it." },
  { id := "indexed-basic-axioms", source := finalCoalgebraPaper.key
    title := "The basic small-map axioms in indexed form, stable under slicing"
    feeds := ["Theorem 3.7"], status := .«open»
    note := "Not stated." },
  { id := "power-class-indexed-functor", source := finalCoalgebraPaper.key
    title := "The power-class functor as an indexed functor"
    feeds := ["Theorem 3.7"], status := .«open»
    note := "Not stated." },
  { id := "indexed-final-coalgebra", source := finalCoalgebraPaper.key
    title := "The indexed final coalgebra of the power-class functor"
    feeds := ["Theorem 3.7", "Corollary 4.3"], status := .«open»
    note := "Not built. Once built, Corollary 4.3 makes it a model of CZF₀ + AFA." },
  { id := "exponentiation", source := finalCoalgebraPaper.key
    title := "(E) Dependent products along small maps preserve small maps"
    feeds := ["Theorem 4.4"], status := .«open»
    statement := some ``Mettapedia.SetTheory.CarveOuts.Sites.SmallMaps.ExponentiationAxiom
    note := "Stated, not proved. With it Theorem 4.4 gives CST + AFA." },
  { id := "power-sets-p2", source := finalCoalgebraPaper.key
    title := "(P2) Power sets"
    feeds := ["Theorem 4.5"], status := .«open»
    note := "Not stated. With (M) and (C), Theorem 4.5 gives IZF⁻ + AFA." },
  { id := "monos-small", source := finalCoalgebraPaper.key
    title := "(M) Every monomorphism is small"
    feeds := ["Theorem 4.5"], status := .proved
    statement := some ``Mettapedia.SetTheory.CarveOuts.Sites.SmallMaps.MonosSmall
    evidence := [``Mettapedia.SetTheory.CarveOuts.Sheaves.cantorUp_monosSmall] },
  { id := "collection", source := finalCoalgebraPaper.key
    title := "(C) Collection"
    feeds := ["Theorem 4.5", "Theorem 4.7"], status := .proved
    statement := some ``Mettapedia.SetTheory.CarveOuts.Sites.SmallMaps.CollectionAxiom
    evidence := [``Mettapedia.SetTheory.CarveOuts.Sheaves.cantorUp_collection_of_choice]
    hypotheses := [
      { name := ``Mettapedia.SetTheory.CarveOuts.Sheaves.BaseCollection
        conditions := "Collection on sheaves is proved from collection in the base, which host \
          choice proves"
        provedBy := [``Mettapedia.SetTheory.CarveOuts.Sheaves.baseCollection_of_choice] }] },
  { id := "fullness-f", source := finalCoalgebraPaper.key
    title := "(F) Fullness"
    feeds := ["Theorem 4.7"], status := .«open»
    note := "Not stated. With (C), Theorem 4.7 gives CZF⁻ + AFA." }
]

/-- The local graph of this module. -/
def graph : Graph where
  documents := [report, finalCoalgebraPaper]
  questions := questions
  nodes := nodes
  arrows := arrows
  observers := observers
  witnesses := witnesses
  obligations := obligations

theorem graph_wellFormed : graph.wellFormed = true := by
  decide +kernel

/-- Proved obligations cite declarations, and open ones cite none. -/
theorem obligations_cited : graph.obligationsCited = true := by
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

/-- **The three identifications**: the pairs of options the local graph proves to define the
same thing. -/
theorem identifications : graph.equivalences = [
    ("small-maps-of-sheaves", "pullbacks-of-generic-membership"),
    ("locally-constant-naturals", "any-parametrised-nno"),
    ("small-relations-into-a-sheaf", "maps-into-power-class")] := by
  decide +kernel

/-- **No arrow of this module claims a forgotten distinction**: none is graded lossy and none
records an aspect it does not preserve. -/
theorem claims_no_fibre :
    arrows.all (fun arrow => !(arrow.grades.any fun claim => claim matches .lossy) &&
      !(arrow.contract.entries.any (·.status == .notPreserved))) = true := by
  decide +kernel

end Mettapedia.Languages.MeTTa.PrimeOptions.CarveOutSheafPowers
