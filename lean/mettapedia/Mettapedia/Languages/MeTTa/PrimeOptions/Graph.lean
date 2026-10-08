import Mettapedia.GSLT.Distinction.OptionGraph
import Mettapedia.Languages.MeTTa.PrimeOptions.ContextChoices
import Mettapedia.Languages.MeTTa.PrimeOptions.CarveOuts
import Mettapedia.Languages.MeTTa.PrimeOptions.CarveOutSites
import Mettapedia.Languages.MeTTa.PrimeOptions.CarveOutSheaves
import Mettapedia.Languages.MeTTa.PrimeOptions.CarveOutSheafPowers
import Mettapedia.Languages.MeTTa.PrimeOptions.ReplayPins
import Mettapedia.Languages.MeTTa.PrimeOptions.WeightAlgebras
import Mettapedia.Languages.MeTTa.PrimeOptions.OpenTower
import Mettapedia.Languages.MeTTa.PrimeOptions.ReviewDigest
import Mettapedia.Languages.MeTTa.PrimeOptions.FrontierMap

/-!
# The options explored for HO MeTTa Prime, as an option graph

The registry below holds the options explored for Prime's design, including
those ruled out, in the shape of `GSLT.Distinction.OptionGraph`:

* the set-theory profile of the extensional face: Megalodon HOTG, rejected as
  the default and kept as an explicit well-founded profile, beside the
  hyperset profile and bare logic;
* the anti-foundation views Foundation, Aczel, Scott, Finsler and Boffa, with
  their factorizations and fibres;
* the demand strategies eager, lazy and resample, with exact translations and
  observer-dependent defects;
* the causal rungs association, intervention and counterfactual;
* three routes to an equality that proofs can use, in the Megalodon HOTG
  profile of the C draft, as fixtures;
* the observer classes of the λ-to-ρ compiler: public, region-bounded and
  reflective;
* three design shapes ruled out: a decidable core first, Prime as a dependent
  type theory plus a model, and laziness as one global rule;
* the equivalence the set face sees of an observed contextual execution, with
  exact kernel, readout and quotient theorems;
* the eight choice points of the context operators, placed from their records
  (`PrimeOptions.ContextChoices`);
* the carve-outs of the Heyting-valued top and of the hyperset top, the comparison of
  Megalodon's checked graph decorations with Lean's hypersets, and the two presentations
  called HOTG (`PrimeOptions.CarveOuts`).

Declarations are cited by name. `PrimeOptions.Manifest` checks every cited
declaration against the kernel; the generator of the published graph checks
fixtures, documents and quotations against their sources.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeOptions

open Lean (Name)
open Mettapedia.GSLT.Distinction.OptionGraph

/-! ## Documents -/

def documents : List Document := [
  { key := "options-20260929"
    title := "Options for organising HO MeTTa Prime's foundation top-down"
    date := "2026-09-29" },
  { key := "foundation-contract-20260926"
    title := "Native simple types, HOL and the choice of HOTG"
    date := "2026-09-26" },
  { key := "quarantine-brief-20261004"
    title := "Quarantining the Megalodon HOTG set theory: the task brief"
    date := "2026-10-04" },
  { key := "spine-report-20261005"
    title := "The name-passing λ, scoped π and core-ρ execution spine: report"
    date := "2026-10-05" },
  { key := "spine-module"
    title := "Lean module: the name-passing lambda, scoped pi and core-rho execution spine"
    date := "2026-10-05" },
  { key := "quoted-controls-module"
    title := "Lean module: quoted implementation code is outside the public-channel observer contract"
    date := "2026-10-05" },
  { key := "diaconescu-module"
    title := "Lean module: Diaconescu's theorem, in set form"
    date := "2026-10-04" },
  { key := "bare-theory-module"
    title := "Lean module: the bare profile as an empty higher-order theory"
    date := "2026-10-04" },
  { key := "abduction-report-20261005"
    title := "PN and PS by abduction, Tian-Pearl's combined bounds, rung-3 identification over \
      two random steps: report"
    date := "2026-10-05" },
  { key := "note-carve-out"
    title := "Design note: the top-down carve-out"
    date := "2026-10-02" },
  { key := "note-trinity"
    title := "Design note: the semantic trinity"
    date := "2026-10-02" },
  { key := "note-plot-card"
    title := "Design note: the Prime plot card"
    date := "2026-10-04" },
  { key := "note-foreign-default"
    title := "Design note: no foreign system as Prime's default"
    date := "2026-10-04" }
]

/-! ## Questions -/

def questions : List Question := [
  { id := "set-profile"
    title := "Set-theory profile of the extensional face"
    summary := "Which set theory, if any, gives the set face its laws. No set theory is selected." },
  { id := "anti-foundation"
    title := "Anti-foundation view"
    summary := "When two pointed graphs picture the same set: Foundation, Aczel, Scott, \
      Finsler or Boffa, compared on a finite menu of eleven pictures and by general criteria. \
      Recovery on the menu compares those pictures; it is not an embedding of the material sets."
    ledger := some { assumptions := none
                     ledger := `Mettapedia.SetTheory.Profiles.AntiFoundationLedger
                     proof := `Mettapedia.SetTheory.Profiles.antiFoundationLedger }
    facts := [cites [`Mettapedia.SetTheory.AntiFoundation.GeneralReadouts.finite_menu_does_not_embed_material_sets]] },
  { id := "demand"
    title := "Demand strategy"
    summary := "When a discarded or copied computation runs: eagerly, lazily with sharing, or \
      by resampling. Observers read outcome bags, sets, counts, faults and draws, or ordered \
      traces of answers, effects and faults."
    facts := [cites [`Mettapedia.GSLT.Dynamics.OrderedDemand.eagerTrace_eq_lazyTrace_iff,
      `Mettapedia.GSLT.Dynamics.OrderedDemand.lazyTrace_eq_resampledTrace_iff,
      `Mettapedia.GSLT.Dynamics.OrderedDemand.bag_agreement_of_ordered]] },
  { id := "demand-scope"
    title := "Scope of the demand strategy"
    summary := "Whether one evaluation strategy holds for every program, or strategies are \
      bubbles carved inside the strategy-free rewrite relation." },
  { id := "causal-rung"
    title := "Causal rung"
    summary := "Which equivalence identifies two causal models over a GSLT: association, \
      intervention or counterfactual." },
  { id := "equality-route"
    title := "Equality that proofs can use, in the Megalodon HOTG profile"
    summary := "The signature's equality has an introduction, extensionality, and no \
      elimination. Three routes give the identity of sets a rule of substitution." },
  { id := "lambda-rho-observers"
    title := "Observer class of the λ-to-ρ compiler"
    summary := "For which observers the compiler from name-passing λ through scoped π to \
      core ρ preserves and reflects behaviour." },
  { id := "foundation-order"
    title := "Order of the foundation"
    summary := "Whether a decidable core comes first, with extensions carrying evidence, or \
      the strongest theory comes first, with decidable fragments carved inside it." },
  { id := "observed-readout"
    title := "Equivalence of running things read in the set face"
    summary := "Which equivalence the set face sees of an observed contextual execution: \
      ordinary bisimilarity with agreeing present readings, observed bisimilarity, the hyperset \
      value of the observed execution, the quotient by observed behaviour, or the constructed \
      material member family. Declared atomic observations are part of the value. A full cover \
      carries the value and every formula over exactly."
    facts := [cites [`Mettapedia.GSLT.ContextualObservedCoalgebraTransport.value_preservation,
      `Mettapedia.GSLT.ContextualObservedCoalgebraTransport.formula_preservation_reflection]] },
  { id := "semantic-shape"
    title := "Shape of Prime's semantics"
    summary := "Whether Prime is a dependent type theory with a model, or a trinity of \
      extensional, intensional and operational faces." }
]

/-! ## Options -/

def setProfileNodes : List Node := [
  { id := "megalodon-hotg"
    question := "set-profile"
    title := "Megalodon HOTG"
    summary := "Higher-order Tarski-Grothendieck as Megalodon and Egal present it: \
      extensionality, empty set, union, power set, separation, replacement, membership \
      induction, a least-universe operator and a global choice operator. The abstract \
      ledger reads replacement as a functional relation; Megalodon's signature and the C \
      profile take it as an operator on functions."
    cProfile := some "megalodon-hotg"
    ledger := some { assumptions := some `Mettapedia.SetTheory.Profiles.MegalodonAssumptions
                     ledger := `Mettapedia.SetTheory.Profiles.MegalodonLedger
                     proof := `Mettapedia.SetTheory.Profiles.megalodonLedger }
    standings := [
      { standing := .rejectedAsDefault
        evidence := [
          .decision "2026-10-04"
            "If there is even ONE reason why Megalodon's HOTG may not be the ideal setting, \
            then this must be QUARANTINED. It cannot be our 'running draft' and any showcases \
            are fake."
            "quarantine-brief-20261004",
          .argument "foundation-contract-20260926" "HOTG is an independently selected theory"
            "Before Prime's native set theory is selected, the choice must be recorded and \
            justified; no such record exists for HOTG.",
          .argument "options-20260929" "S4. The strong top"
            "HOTG or hypersets as the single strong top was assessed at 63 per cent, below the \
            adoption threshold, and left open.",
          .argument "note-foreign-default" "Adopting a foreign default imports its limits"
            "Taken as the default, HOTG brought foundation against hypersets, classical logic \
            through Diaconescu's argument, pairs that need choice, and the least-universe \
            operator, none of them selected.",
          cites [`Mettapedia.SetTheory.Profiles.lem_of_choice,
            `Mettapedia.SetTheory.Profiles.noQuineAtom_of_induction,
            `Mettapedia.SetTheory.Profiles.unorderedPair_of_choice]] },
      { standing := .admittedAsBubble
        evidence := [
          .decision "2026-10-04"
            "Reimplementing Megalodon HOTG in MeTTa/CeTTa in an integrated way is cool. We \
            should perhaps preserve this as an explicit Megalodon profile."
            "quarantine-brief-20261004",
          .decision "2026-10-04"
            "a weaker set theory could host this bubble cleanly, so it could be valuable to \
            preserve some of it in some obviously-not-default location."
            "quarantine-brief-20261004",
          .fixture "prime" "theory_profiles/isolation" ["[hol]", "[megalodon-hotg]", "[set:of]"],
          cites [`Mettapedia.TypeTheory.MaterialSets.Hypersets.HSet.wellFoundedPartEquivZFSet,
            `Mettapedia.SetTheory.Profiles.wellFoundedPart_memInduction]] }] },
  { id := "hyperset-family"
    question := "set-profile"
    title := "Hyperset profile"
    summary := "The set-forming principles with a Quine atom and without membership \
      induction. Aczel's hypersets are a carrier; hypersets outermost, with well-founded sets \
      inside, is the stated direction, not a selection."
    ledger := some { assumptions := some `Mettapedia.SetTheory.Profiles.HypersetAssumptions
                     ledger := `Mettapedia.SetTheory.Profiles.HypersetLedger
                     proof := `Mettapedia.SetTheory.Profiles.hypersetLedger }
    facts := [cites [`Mettapedia.SetTheory.Profiles.hset_hasQuineAtom,
      `Mettapedia.SetTheory.Profiles.hset_refutes_memInduction]] },
  { id := "bare-logic"
    question := "set-profile"
    title := "Bare logic"
    summary := "No set principle: the empty theory of extensional higher-order logic. The C \
      draft's logical checking environment selects no set constants and no set axioms."
    cProfile := some "hol"
    ledger := some { assumptions := some `Mettapedia.SetTheory.Profiles.BareAssumptions
                     ledger := `Mettapedia.SetTheory.Profiles.BareLedger
                     proof := `Mettapedia.SetTheory.Profiles.bareLedger }
    theory := some `Mettapedia.SetTheory.Profiles.bareTheory
    facts := [cites [`Mettapedia.SetTheory.Profiles.bare_implication_refl]] }
]

def antiFoundationNodes : List Node := [
  { id := "foundation", question := "anti-foundation", title := "Foundation"
    summary := "Only well-founded pictures denote sets; membership induction holds."
    denotation := some `Mettapedia.SetTheory.AntiFoundation.denoteFoundation },
  { id := "afa", question := "anti-foundation", title := "Aczel's anti-foundation axiom"
    summary := "Every picture denotes a set, and bisimilar pictures denote the same set."
    denotation := some `Mettapedia.SetTheory.AntiFoundation.denoteAFA, membership := some `Mettapedia.SetTheory.AntiFoundation.aMem },
  { id := "safa", question := "anti-foundation", title := "Scott's anti-foundation axiom"
    summary := "Pictures with isomorphic unfoldings denote the same set."
    denotation := some `Mettapedia.SetTheory.AntiFoundation.denoteSAFA, membership := some `Mettapedia.SetTheory.AntiFoundation.sMem },
  { id := "fafa", question := "anti-foundation", title := "Finsler's anti-foundation axiom"
    summary := "Pictures with isomorphic pointed downsets denote the same set."
    denotation := some `Mettapedia.SetTheory.AntiFoundation.denoteFAFA, membership := some `Mettapedia.SetTheory.AntiFoundation.fMem },
  { id := "bafa", question := "anti-foundation", title := "Boffa's anti-foundation axiom"
    summary := "Every weakly extensional picture is exact; there are many Quine atoms."
    denotation := some `Mettapedia.SetTheory.AntiFoundation.denoteBAFA, membership := some `Mettapedia.SetTheory.AntiFoundation.bMem }
]

def demandNodes : List Node := [
  { id := "eager", question := "demand", title := "Eager evaluation"
    summary := "A discarded argument runs; a copied computation runs once."
    standings := [
      { standing := .admittedAsBubble
        evidence := [.decision "2026-10-03"
          "We have discussed having eager and lazy bubbles … ways to say 'eval this context \
          eagerly'."
          "note-plot-card"] }] },
  { id := "lazy", question := "demand", title := "Lazy evaluation with sharing"
    summary := "A discarded argument never runs; a copied computation runs once and is shared."
    standings := [
      { standing := .admittedAsBubble
        evidence := [.decision "2026-10-03"
          "We have discussed having eager and lazy bubbles … ways to say 'eval this context \
          eagerly'."
          "note-plot-card"] }] },
  { id := "resample", question := "demand", title := "Resampling (call by name)"
    summary := "A discarded argument never runs; each use of a copied computation draws again."
    standings := [
      { standing := .admittedAsBubble
        evidence := [
          .argument "abduction-report-20261005" "Where the intervention sits decides the query"
            "Whether a random step after an intervention is re-drawn or retained decides the \
            counterfactual query: the re-drawn reading is identified by unit-resolved data and \
            differs from the retained one. Callers must say which reading they take.",
          .argument "note-plot-card" "eager and resample are commitments carved inside it"
            "The top is the strategy-free rewrite relation with its set value; lazy, eager and \
            resampling evaluation are commitments carved inside it.",
          cites [`Mettapedia.GSLT.Dynamics.DemandAgreement.lazyShared_eq_resampledUses_iff,
            `Mettapedia.GSLT.Distinction.DemandStrategies.exact_translations,
            `Mettapedia.GSLT.Distinction.DemandStrategies.sharing_requires_purity]] }] }
]

def demandScopeNodes : List Node := [
  { id := "laziness-global", question := "demand-scope", title := "Laziness as one global rule"
    summary := "One evaluation strategy for every program; laziness everywhere is the case \
      ruled out."
    standings := [
      { standing := .rejected
        evidence := [.decision "2026-10-03"
          "We have discussed having eager and lazy bubbles … ways to say 'eval this context \
          eagerly'."
          "note-plot-card"] }] },
  { id := "strategy-bubbles", question := "demand-scope", title := "Strategies as bubbles"
    summary := "The top is the strategy-free rewrite relation with its set value; eager, lazy \
      and resampling evaluation are commitments carved inside it."
    standings := [
      { standing := .selected
        evidence := [.decision "2026-10-03"
          "We have discussed having eager and lazy bubbles … ways to say 'eval this context \
          eagerly'."
          "note-plot-card"] }] }
]

def causalNodes : List Node := [
  { id := "association", question := "causal-rung", title := "Association"
    summary := "Reduction bisimilarity with the base observations: the model is watched." },
  { id := "intervention", question := "causal-rung", title := "Intervention"
    summary := "Contextual equivalence: one intervention before any step, then watching." },
  { id := "counterfactual", question := "causal-rung", title := "Counterfactual"
    summary := "Saturated equivalence: interventions at any reached state, the state retained." }
]

def equalityRouteNodes : List Node := [
  { id := "r1-rule", question := "equality-route", title := "R1: substitution as a rule"
    summary := "A theory adopts the rule eq-subst of higher-order logic: an equation at any \
      carrier rewrites a proposition. Nothing else is assumed." },
  { id := "r2-leibniz", question := "equality-route", title := "R2: Leibniz identity"
    summary := "Identity is defined as Leibniz defines it, and sets with the same members are \
      identical by the axiom same-ext." },
  { id := "r3-carrier-laws", question := "equality-route", title := "R3: laws per carrier"
    summary := "The signature's equality with reflexivity and the substitution axiom \
      subst@set, declared again for every carrier." }
]

def lambdaRhoNodes : List Node := [
  { id := "public-observers", question := "lambda-rho-observers", title := "Public observers"
    summary := "Receivers on public result channels."
    facts := [cites [
      `Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingSpine.native_may_return_iff,
      `Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingSpine.accessibility_iff]] },
  { id := "region-observers", question := "lambda-rho-observers", title := "Region-bounded observers"
    summary := "Contexts that send, receive and compare only names of a region disjoint from \
      the compiler's private names." },
  { id := "reflective-observers", question := "lambda-rho-observers", title := "Reflective observers"
    summary := "Unrestricted ρ contexts, which can take quoted names apart."
    facts := [cites [
      `Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoQuotedCompilerObserverControls.unused_scope_quoted_observer_boundary]] }
]

def observedReadoutNodes : List Node := [
  { id := "present-readings-bisimilarity", question := "observed-readout"
    title := "Bisimilarity with agreeing present readings"
    summary := "Ordinary bisimilarity of the execution, together with agreement of the declared \
      readings at the present state." },
  { id := "observed-bisimilarity", question := "observed-readout"
    title := "Observed bisimilarity"
    summary := "One relation that is a complete-future bisimulation and preserves every declared \
      observation." },
  { id := "material-value", question := "observed-readout"
    title := "Material value"
    summary := "The hyperset decoration of the observed execution graph, declared atoms \
      included." },
  { id := "observed-quotient", question := "observed-readout"
    title := "Quotient by observed behaviour"
    summary := "The contextual family of states up to observed bisimilarity, with its own \
      coalgebra and atoms." },
  { id := "material-members", question := "observed-readout"
    title := "Material member family"
    summary := "The constructed family of material members with a class face and its decoder." }
]

def designNodes : List Node := [
  { id := "decidable-core-first", question := "foundation-order", title := "A decidable core first"
    summary := "A decidable core, with stronger principles added as extensions that carry \
      evidence."
    standings := [
      { standing := .rejected
        evidence := [
          .decision "2026-09-29"
            "If you try to make the decidable fragment core and then try to just have \
            evidence-carrying extension, I think you got it backwards."
            "note-carve-out",
          .argument "options-20260929" "Top-down carve-out"
            "A decidable core plus evidence-carrying extensions is the rejected, backwards shape."] }] },
  { id := "top-down-carve-out", question := "foundation-order", title := "Top-down carve-out"
    summary := "The foundation is the strongest, most open theory; decidable and pragmatic \
      fragments are carved inside it, and their good properties are theorems about them."
    standings := [
      { standing := .selected
        evidence := [
          .decision "2026-09-29"
            "If you try to make the decidable fragment core and then try to just have \
            evidence-carrying extension, I think you got it backwards."
            "note-carve-out",
          .argument "options-20260929" "Negative reading, the carve-out forced"
            "Every internally realised carve-out is proper, and its verdict on the diagonal \
            term is outside the fragment."] }] },
  { id := "dtt-plus-model", question := "semantic-shape", title := "A dependent type theory plus a model"
    summary := "Prime as a dependent type theory, with its meaning given by one model."
    standings := [
      { standing := .rejected
        evidence := [
          .decision "2026-09-22" "Prime isn't just 'blabla DTT only'. We are seeking a trinity."
            "note-trinity",
          .decision "2026-10-02"
            "you forgot the trinity of extensional, intensional, and operational sides of the \
            semantics/math."
            "note-trinity",
          .argument "options-20260929" "(A) is the bottom-up shape"
            "With minimal commitments at the root every strength arrives as an axiom package \
            over a decidable core; the type theory's own checker as the trust root was assessed \
            at 42 per cent."] }] },
  { id := "trinity", question := "semantic-shape", title := "The semantic trinity"
    summary := "Extensional, intensional and operational faces, none of them the whole; the \
      set face is the strong, ambient side."
    standings := [
      { standing := .selected
        evidence := [
          .decision "2026-09-22" "Prime isn't just 'blabla DTT only'. We are seeking a trinity."
            "note-trinity"] }] }
]

/-! ## Arrows -/

def arrows : List Arrow := [
  { id := "hotg-well-founded-part"
    source := "megalodon-hotg", target := "hyperset-family", kind := .equivalence
    grades := [.preserved]
    summary := "Well-founded sets are the well-founded part of the hyperset carrier: that part \
      of HSet is equivalent to ZFSet with membership preserved and reflected, and membership \
      induction holds there. The universe and choice operators are not interpreted."
    evidence := [cites [
      `Mettapedia.TypeTheory.MaterialSets.Hypersets.HSet.wellFoundedPartEquivZFSet,
      `Mettapedia.SetTheory.Profiles.wellFoundedPart_mem_iff_zfSet,
      `Mettapedia.SetTheory.Profiles.wellFoundedPart_memInduction,
      `Mettapedia.SetTheory.Profiles.zfSet_memInduction]]
    contract := {
      entries := [
        .keeps (.formulas .atomic)
          [`Mettapedia.TypeTheory.MaterialSets.Hypersets.HSet.wellFoundedPartEquivZFSet_mem_iff,
           `Mettapedia.SetTheory.Profiles.wellFoundedPart_mem_iff_zfSet]
          "membership of the well-founded hypersets against ZFSet",
        .unknownAt (.formulas .bounded),
        .unknownAt (.commitment .choice),
        .unknownAt (.commitment .universes)] } },
  { id := "bafa-view-fafa", source := "bafa", target := "fafa", kind := .observationalQuotient
    grades := [.factors, .lossy]
    summary := "Finsler's value of a picture is a function of Boffa's; two loops, and the two \
      ends of a two-cycle, are one Finsler atom and two Boffa pictures."
    evidence := [cites [`Mettapedia.SetTheory.AntiFoundation.factors_bafa_fafa,
      `Mettapedia.SetTheory.AntiFoundation.fiber_fafa_bafa,
      `Mettapedia.SetTheory.AntiFoundation.fiber_fafa_bafa_cycle]]
    contract := {
      entries := [
        .loses .distinctions
          [`Mettapedia.SetTheory.AntiFoundation.not_factors_fafa_bafa]
          "on the finite menu of pictures"] } },
  { id := "fafa-view-safa", source := "fafa", target := "safa", kind := .observationalQuotient
    grades := [.factors, .lossy]
    summary := "Scott's value is a function of Finsler's; the Finsler nodes n1 and n2 are one \
      set for Scott."
    evidence := [cites [`Mettapedia.SetTheory.AntiFoundation.factors_fafa_safa,
      `Mettapedia.SetTheory.AntiFoundation.fiber_safa_fafa]]
    contract := {
      entries := [
        .loses .distinctions
          [`Mettapedia.SetTheory.AntiFoundation.not_factors_safa_fafa]
          "on the finite menu of pictures"] } },
  { id := "safa-view-afa", source := "safa", target := "afa", kind := .observationalQuotient
    grades := [.factors, .lossy]
    summary := "Aczel's value is a function of Scott's; the Scott nodes are one set for Aczel."
    evidence := [cites [`Mettapedia.SetTheory.AntiFoundation.factors_safa_afa,
      `Mettapedia.SetTheory.AntiFoundation.fiber_afa_safa]]
    contract := {
      entries := [
        .loses .distinctions
          [`Mettapedia.SetTheory.AntiFoundation.not_factors_afa_safa]
          "on the finite menu of pictures"] } },
  { id := "afa-view-foundation", source := "afa", target := "foundation", kind := .observationalQuotient
    grades := [.factors, .lossy]
    summary := "Foundation's value is a function of Aczel's; the nest and the loop are one \
      refusal for Foundation and two sets for Aczel."
    evidence := [cites [`Mettapedia.SetTheory.AntiFoundation.factors_afa_found,
      `Mettapedia.SetTheory.AntiFoundation.fiber_found_afa]]
    contract := {
      entries := [
        .loses .distinctions
          [`Mettapedia.SetTheory.AntiFoundation.not_factors_found_afa]
          "on the finite menu of pictures"] } },
  { id := "safa-restricts-to-afa", source := "safa", target := "afa", kind := .restriction
    map := some `Mettapedia.SetTheory.AntiFoundation.afaToSafa
    grades := [.preserved]
    summary := "Restricted to the image of Aczel's sets, Scott's carrier on the menu is Aczel's: membership preserved and reflected, injectively."
    evidence := [cites [`Mettapedia.SetTheory.AntiFoundation.afaToSafa_mem,
      `Mettapedia.SetTheory.AntiFoundation.afaToSafa_inj]]
    contract := {
      entries := [
        .keeps (.formulas .atomic)
          [`Mettapedia.SetTheory.AntiFoundation.afaToSafa_mem,
           `Mettapedia.SetTheory.AntiFoundation.afaToSafa_inj]
          "membership of the menu's sets, injectively"] } },
  { id := "fafa-restricts-to-safa", source := "fafa", target := "safa", kind := .restriction
    map := some `Mettapedia.SetTheory.AntiFoundation.safaToFafa
    grades := [.preserved]
    summary := "Restricted to the image of Scott's sets, Finsler's carrier on the menu is Scott's: membership preserved and reflected, injectively."
    evidence := [cites [`Mettapedia.SetTheory.AntiFoundation.safaToFafa_mem,
      `Mettapedia.SetTheory.AntiFoundation.safaToFafa_inj]]
    contract := {
      entries := [
        .keeps (.formulas .atomic)
          [`Mettapedia.SetTheory.AntiFoundation.safaToFafa_mem,
           `Mettapedia.SetTheory.AntiFoundation.safaToFafa_inj]
          "membership of the menu's sets, injectively"] } },
  { id := "bafa-restricts-to-fafa", source := "bafa", target := "fafa", kind := .restriction
    map := some `Mettapedia.SetTheory.AntiFoundation.fafaToBafa
    grades := [.preserved]
    summary := "Restricted to the image of Finsler's sets, Boffa's carrier on the menu is Finsler's: membership preserved and reflected, injectively."
    evidence := [cites [`Mettapedia.SetTheory.AntiFoundation.fafaToBafa_mem,
      `Mettapedia.SetTheory.AntiFoundation.fafaToBafa_inj]]
    contract := {
      entries := [
        .keeps (.formulas .atomic)
          [`Mettapedia.SetTheory.AntiFoundation.fafaToBafa_mem,
           `Mettapedia.SetTheory.AntiFoundation.fafaToBafa_inj]
          "membership of the menu's sets, injectively"] } },
  { id := "eager-in-lazy", source := "eager", target := "lazy", kind := .interpretation
    grades := [.exact]
    summary := "Force the discarded argument: outcomes, faults and draws are kept, for every \
      weighting of the readings."
    evidence := [cites [`Mettapedia.GSLT.Distinction.DemandStrategies.exact_translations]]
    contract := {
      entries := [
        .keeps .distinctions
          [`Mettapedia.GSLT.Distinction.DemandStrategies.exact_translations]
          "all five readings, for every weighting",
        .keeps (.evidence .cost)
          [`Mettapedia.GSLT.Distinction.DemandStrategies.exact_translations]
          "draws"] } },
  { id := "lazy-in-eager", source := "lazy", target := "eager", kind := .interpretation
    grades := [.exact]
    summary := "Drop the discarded argument: distortion zero for every weighting."
    evidence := [cites [`Mettapedia.GSLT.Distinction.DemandStrategies.exact_translations]]
    contract := {
      entries := [
        .keeps .distinctions
          [`Mettapedia.GSLT.Distinction.DemandStrategies.exact_translations]
          "all five readings, for every weighting",
        .keeps (.evidence .cost)
          [`Mettapedia.GSLT.Distinction.DemandStrategies.exact_translations]
          "draws"] } },
  { id := "resample-in-lazy", source := "resample", target := "lazy", kind := .interpretation
    grades := [.exact]
    summary := "Draw twice: distortion zero for every weighting."
    evidence := [cites [`Mettapedia.GSLT.Distinction.DemandStrategies.exact_translations]]
    contract := {
      entries := [
        .keeps .distinctions
          [`Mettapedia.GSLT.Distinction.DemandStrategies.exact_translations]
          "all five readings, for every weighting",
        .keeps (.evidence .cost)
          [`Mettapedia.GSLT.Distinction.DemandStrategies.exact_translations]
          "draws"] } },
  { id := "lazy-in-resample", source := "lazy", target := "resample", kind := .interpretation
    grades := [.exact]
    summary := "Draw once and share: distortion zero for every weighting."
    evidence := [cites [`Mettapedia.GSLT.Distinction.DemandStrategies.exact_translations]]
    contract := {
      entries := [
        .keeps .distinctions
          [`Mettapedia.GSLT.Distinction.DemandStrategies.exact_translations]
          "all five readings, for every weighting",
        .keeps (.evidence .cost)
          [`Mettapedia.GSLT.Distinction.DemandStrategies.exact_translations]
          "draws"] } },
  { id := "eager-through-lazy-to-resample", source := "eager", target := "resample", kind := .interpretation
    grades := [.exact]
    summary := "The composite of two exact routes is exact, by graded functoriality."
    evidence := [cites [`Mettapedia.GSLT.Distinction.DemandStrategies.eager_through_lazy_to_resample]]
    contract := {
      entries := [
        .keeps .distinctions
          [`Mettapedia.GSLT.Distinction.DemandStrategies.eager_through_lazy_to_resample]
          "all five readings, for every weighting"] } },
  { id := "eager-as-lazy-default", source := "eager", target := "lazy", kind := .unclassified
    grades := [.defect "w(bag) + w(count) + w(draws), attained when some computation has other \
      than one answer; w(draws) alone when every computation has exactly one answer"]
    summary := "The same program under the other strategy, on computations that answer and do \
      not fault. The defect depends on the observer's weights; the agreement on outcome sets \
      and faults does not."
    evidence := [cites [`Mettapedia.GSLT.Distinction.DemandStrategies.eager_lazy_defect,
      `Mettapedia.GSLT.Distinction.DemandStrategies.deterministic_eager_lazy,
      `Mettapedia.GSLT.Distinction.DemandStrategies.weights_control]]
    contract := {
      entries := [
        .loses .distinctions
          [`Mettapedia.GSLT.Distinction.DemandStrategies.discard_witness]
          "bags, counts and draws of a discarded computation with other than one answer",
        .loses (.evidence .cost)
          [`Mettapedia.GSLT.Distinction.DemandStrategies.deterministic_eager_lazy]
          "draws, even with one answer"] } },
  { id := "counterfactual-refines-intervention", source := "counterfactual",
    target := "intervention", kind := .observationalQuotient
    grades := [.ordered]
    summary := "Agreement at the counterfactual rung implies agreement at the interventional \
      rung; the interventional distance is at most the counterfactual one."
    evidence := [cites [`Mettapedia.GSLT.Causality.Hierarchy.agree_of_le,
      `Mettapedia.GSLT.Causality.Hierarchy.agree_intervention_of_counterfactual,
      `Mettapedia.GSLT.Causality.Hierarchy.interventional_le_counterfactual]]
    contract := {
      entries := [
        .loses .distinctions
          [`Mettapedia.GSLT.Causality.Hierarchy.ResponseTypes.ladder_strict]
          "the mixed and the fixed populations"] } },
  { id := "intervention-refines-association", source := "intervention",
    target := "association", kind := .observationalQuotient
    grades := [.ordered]
    summary := "Agreement at the interventional rung implies agreement at the associational \
      rung; the passive distance is at most the interventional one."
    evidence := [cites [`Mettapedia.GSLT.Causality.Hierarchy.agree_of_le,
      `Mettapedia.GSLT.Causality.Hierarchy.agree_association_of_intervention,
      `Mettapedia.GSLT.Causality.Hierarchy.passiveDistance_le_interventional]]
    contract := {
      entries := [
        .loses .distinctions
          [`Mettapedia.GSLT.Causality.Hierarchy.ResponseTypes.ladder_strict]
          "a population treatment would help and an inert one"] } },
  { id := "r2-in-r1", source := "r2-leibniz", target := "r1-rule", kind := .interpretation
    grades := [.ungraded]
    summary := "R2's axiom same-ext, with same unfolded, is the statement identical, which R1 \
      proves from extensionality."
    evidence := [.fixture "prime" "profiles/megalodon_hotg/scoped/equality_routes"
      ["[(r1 identical (assumes (extensionality)) (proof 37) (term 602))]"]]
    contract := { entries := [.unknownAt .laws "shown by a fixture, not by a theorem"] } },
  { id := "r3-in-r1", source := "r3-carrier-laws", target := "r1-rule", kind := .interpretation
    grades := [.ungraded]
    summary := "R3's two laws at set are eq-refl and subst, which R1 proves; subst assumes \
      nothing beyond the rule."
    evidence := [.fixture "prime" "profiles/megalodon_hotg/scoped/equality_routes"
      ["[eq-refl]", "[(r1 subst (assumes ()) (proof 14) (term 179))]"]]
    contract := { entries := [.unknownAt .laws "shown by a fixture, not by a theorem"] } },
  { id := "public-in-region", source := "public-observers", target := "region-observers",
    kind := .unclassified, grades := [.ungraded]
    summary := "A receiver on a public result channel is bounded by a region that excludes \
      the compiler's private names."
    evidence := [.argument "spine-module" "The observers are public result-channel receivers"
      "The spine's observers are public result-channel receivers; quoted implementation \
      structure and arbitrary target contexts are additional observations."]
    contract := { entries := [.unknownAt .distinctions] } },
  { id := "observed-in-value", source := "observed-bisimilarity", target := "material-value",
    kind := .observationalQuotient, grades := [.exactKernel .kernel]
    summary := "Two states have the same material value exactly when they are observed \
      bisimilar, and a formula holds of a state exactly when it holds of its value."
    evidence := [cites [`Mettapedia.GSLT.ContextualObservedCoalgebra.value_eq_iff,
      `Mettapedia.GSLT.ContextualObservedCoalgebra.material_formula_iff]]
    contract := {
      entries := [
        .keeps .distinctions
          [`Mettapedia.GSLT.ContextualObservedCoalgebra.value_eq_iff]
          "exactly observed bisimilarity"] } },
  { id := "observed-in-quotient", source := "observed-bisimilarity",
    target := "observed-quotient", kind := .observationalQuotient,
    grades := [.exactKernel .kernel, .exactKernel .quotient, .exactKernel .readout]
    summary := "The projection onto the quotient is onto, identifies exactly the observed \
      bisimilar states, and keeps the material value; on the quotient observed bisimilarity is \
      equality and the value is injective."
    evidence := [cites [`Mettapedia.GSLT.ContextualObservedCoalgebraQuotient.projection_eq_iff,
      `Mettapedia.GSLT.ContextualObservedCoalgebraQuotient.projection_cover,
      `Mettapedia.GSLT.ContextualObservedCoalgebraQuotient.observed_bisimilar_iff_eq,
      `Mettapedia.GSLT.ContextualObservedCoalgebraQuotient.quotientValue_injective,
      `Mettapedia.GSLT.ContextualObservedCoalgebraQuotient.value_square]]
    contract := {
      entries := [
        .keeps .distinctions
          [`Mettapedia.GSLT.ContextualObservedCoalgebraQuotient.projection_eq_iff]
          "exactly observed bisimilarity",
        .unknownAt (.evidence .occurrences)] } },
  { id := "observed-in-members", source := "observed-bisimilarity",
    target := "material-members", kind := .observationalQuotient,
    grades := [.exactKernel .kernel, .exactKernel .quotient, .exactKernel .readout]
    summary := "The member and class observations are onto and identify exactly the observed \
      bisimilar states; the class value is injective and equals the material value along the \
      class observation."
    evidence := [cites [`Mettapedia.GSLT.ContextualObservedMaterialFamily.observation_eq_iff,
      `Mettapedia.GSLT.ContextualObservedMaterialFamily.classObservation_eq_iff,
      `Mettapedia.GSLT.ContextualObservedMaterialFamily.observation_cover,
      `Mettapedia.GSLT.ContextualObservedMaterialFamily.classObservedBisimilar_iff_eq,
      `Mettapedia.GSLT.ContextualObservedMaterialFamily.classValue_injective,
      `Mettapedia.GSLT.ContextualObservedMaterialFamily.classValue_square,
      `Mettapedia.GSLT.ContextualObservedMaterialFamily.observation_value]]
    contract := {
      entries := [
        .keeps .distinctions
          [`Mettapedia.GSLT.ContextualObservedMaterialFamily.observation_eq_iff]
          "exactly observed bisimilarity",
        .unknownAt (.evidence .occurrences)] } },
  { id := "observed-refines-present", source := "observed-bisimilarity",
    target := "present-readings-bisimilarity", kind := .observationalQuotient, grades := [.ungraded]
    summary := "Observed bisimilar states are ordinarily bisimilar and agree on every declared \
      atom."
    evidence := [cites [`Mettapedia.GSLT.ContextualObservedCoalgebra.observed_bisimilar_forgets_atoms,
      `Mettapedia.GSLT.ContextualObservedCoalgebra.observed_bisimilar_atoms]]
    contract := {
      entries := [
        .loses .distinctions
          [`Mettapedia.GSLT.ContextualObservedCoalgebraControls.Late.ordinary_bisimilar,
           `Mettapedia.GSLT.ContextualObservedCoalgebraControls.Late.same_present_atoms,
           `Mettapedia.GSLT.ContextualObservedCoalgebraControls.Late.complete_observed_values_differ]
          "a reading after context transport"] } },
  { id := "region-in-reflective", source := "region-observers", target := "reflective-observers",
    kind := .unclassified, grades := [.ungraded]
    summary := "A region-bounded context is a ρ context."
    evidence := [.argument "spine-module" "Quoted implementation"
      "Quoted implementation structure and arbitrary target contexts are observations beyond \
      the public ones."]
    contract := { entries := [.unknownAt .distinctions] } }
]

/-! ## Observers -/

def observers : List Observer := [
  { id := "classical-forced", title := "Excluded middle forced by the profile's principles"
    reads := "Whether the profile's own principles yield excluded middle. Classical strength \
      is to be recorded per theorem, not imported through a default."
    kind := .«theorem», desideratum := true },
  { id := "quine-atom", title := "A Quine atom"
    reads := "Whether some set equals its own singleton."
    kind := .«theorem» },
  { id := "pairs-without-choice", title := "Unordered pairs without a choice operator"
    reads := "Whether the profile's own signature forms unordered pairs without a choice \
      operator."
    kind := .«theorem» },
  { id := "same-set", title := "Same set"
    reads := "Whether the view's denotation identifies the two pictures."
    kind := .«theorem», identifies := true },
  { id := "outcome-bag", title := "Outcome bags, counts and draws"
    reads := "The bag of outcomes of a test program, their number and the number of draws."
    kind := .«theorem» },
  { id := "outcome-set", title := "Outcome sets and faults"
    reads := "The set of outcomes of a test program and whether it faults."
    kind := .«theorem» },
  { id := "ordered-trace", title := "Ordered trace"
    reads := "The ordered answers, committed effects and faults of a run."
    kind := .«theorem» },
  { id := "strategy-observations-kept", title := "Every strategy's observations kept"
    reads := "Whether what one strategy shows a program stays available under the design."
    kind := .«theorem», desideratum := true },
  { id := "rung-identifies", title := "Rung agreement"
    reads := "Whether the rung's equivalence identifies the two populations."
    kind := .«theorem», identifies := true },
  { id := "rests-on", title := "What a proof rests on"
    reads := "The laws and axioms a route's proof of a statement rests on, as the C draft \
      prints them."
    kind := .fixture },
  { id := "quoted-code", title := "Quoted compiler output"
    reads := "Whether an observer tells apart the compiled code of two structurally equal \
      sources."
    kind := .argument },
  { id := "internal-decision", title := "Equality decided by one of the language's terms"
    reads := "Whether a term of a language whose terms run on terms decides the language's \
      own equality, and on which fragment."
    kind := .«theorem» },
  { id := "readout-identifies", title := "Identified by the readout"
    reads := "Whether the equivalence identifies the two states of an observed execution."
    kind := .«theorem», identifies := true },
  { id := "cost-face", title := "Cost of running"
    reads := "Whether two programs that reach one value are told apart by what running them \
      costs."
    kind := .fixture, desideratum := true }
]

/-! ## Witnesses -/

def setProfileWitnesses : List Witness := [
  { id := "diaconescu", observer := "classical-forced"
    left := "megalodon-hotg", right := "hyperset-family"
    case := "The power set of the power set of the empty set, separated by a proposition into \
      two subsets whose chosen elements decide it."
    leftVerdict := {
      reading := "Excluded middle follows from extensionality, separation, empty set, power \
        set and the choice operator."
      evidence := [.«theorem» [
        { declaration := `Mettapedia.SetTheory.Profiles.lem_of_choice, binds := [`eps, `choice] },
        { declaration := `Mettapedia.SetTheory.Profiles.megalodonLedger }]] }
    rightVerdict := {
      reading := "The profile has no choice operator, so the argument has nothing to start \
        from. That excluded middle is underivable from its principles is not proved."
      evidence := [
        .«theorem» [{ declaration := `Mettapedia.SetTheory.Profiles.hypersetLedger
                      avoids := [`eps, `choice] }],
        .argument "diaconescu-module" "It does not show that excluded middle is underivable"
          "The control shows where the argument uses substitutive equality; it does not show \
          that excluded middle is underivable from the other principles."] } },
  { id := "quine-against-induction", observer := "quine-atom"
    left := "megalodon-hotg", right := "hyperset-family"
    case := "Aczel's atom Ω = {Ω}."
    leftVerdict := {
      reading := "No Quine atom: membership induction refutes it."
      evidence := [cites [`Mettapedia.SetTheory.Profiles.noQuineAtom_of_induction,
        `Mettapedia.SetTheory.Profiles.megalodonLedger]] }
    rightVerdict := {
      reading := "Ω is a Quine atom of HSet, and membership induction fails there."
      evidence := [cites [`Mettapedia.SetTheory.Profiles.hset_hasQuineAtom,
        `Mettapedia.SetTheory.Profiles.hset_refutes_memInduction,
        `Mettapedia.SetTheory.Profiles.quineAtom_refutes_induction]] } },
  { id := "quine-atom-hotg-bare", observer := "quine-atom"
    left := "megalodon-hotg", right := "bare-logic"
    case := "The statement x = {x}, that some set equals its own singleton."
    leftVerdict := {
      reading := "Refuted: membership induction rules out every Quine atom."
      evidence := [cites [`Mettapedia.SetTheory.Profiles.noQuineAtom_of_induction,
        `Mettapedia.SetTheory.Profiles.megalodonLedger]] }
    rightVerdict := {
      reading := "Not stated: the profile has no membership vocabulary, so it neither proves \
        nor refutes a Quine atom; the C draft leaves set forms uninterpreted under the logical \
        profile."
      evidence := [
        .argument "bare-theory-module" "The institution has no membership vocabulary"
          "The bare profile's institution has no membership vocabulary; the Megalodon and \
          hyperset principle sets are not sentences of it.",
        .fixture "prime" "theory_profiles/isolation" ["[hol]", "[set:of]", "[set:known-proposition]"]] } },
  { id := "quine-atom-hyperset-bare", observer := "quine-atom"
    left := "hyperset-family", right := "bare-logic"
    case := "The statement x = {x}, that some set equals its own singleton."
    leftVerdict := {
      reading := "Holds: Aczel's atom Ω = {Ω} is a Quine atom of HSet, and the profile's ledger \
        derives a self-member."
      evidence := [cites [`Mettapedia.SetTheory.Profiles.hset_hasQuineAtom,
        `Mettapedia.SetTheory.Profiles.hypersetLedger]] }
    rightVerdict := {
      reading := "Not stated: the profile has no membership vocabulary; the C draft leaves set \
        forms uninterpreted under the logical profile."
      evidence := [
        .argument "bare-theory-module" "The institution has no membership vocabulary"
          "The bare profile's institution has no membership vocabulary; the Megalodon and \
          hyperset principle sets are not sentences of it.",
        .fixture "prime" "theory_profiles/isolation" ["[hol]", "[set:of]", "[set:known-proposition]"]] } },
  { id := "pairing-replacement", observer := "pairs-without-choice"
    left := "megalodon-hotg", right := "hyperset-family"
    case := "The pair {a, b} as the image of the separated power set of the power set of the \
      empty set: under replacement by an operator on functions, as Megalodon's signature has \
      it, and under replacement by a functional relation."
    leftVerdict := {
      reading := "The signature has no pairing law and its replacement takes a function, so \
        the pair is written with the choice operator, and the ordered pair rests on the \
        choice law. That pairs need choice there is not proved."
      evidence := [
        .«theorem» [{ declaration := `Mettapedia.SetTheory.Profiles.unorderedPair_of_choice
                      binds := [`eps, `choice] }],
        .fixture "prime" "profiles/megalodon_hotg/scoped/curriculum_naproche"
          ["[EpsI]", "[UPair]", "[(type-face kpair-inj (cites (kpair-inj-first kpair-inj-second)) (rests-on (separationLaw replacementLaw powerLaw extensionality EpsI emptyLaw)))]"]] }
    rightVerdict := {
      reading := "Empty set, power set, separation and replacement by a functional relation \
        give unordered pairs, with no choice operator and no host choice."
      evidence := [.«theorem» [
        { declaration := `Mettapedia.SetTheory.Profiles.unorderedPair, avoids := [`eps, `choice],
          choiceFree := true },
        { declaration := `Mettapedia.SetTheory.Profiles.hypersetLedger }]] } }
]

/-- A fibre witness between two anti-foundation views. -/
def fibreWitness (id left right case leftReading rightReading : String)
    (declarations : List Name) : Witness :=
  { id, observer := "same-set", left, right, case
    leftVerdict := { reading := leftReading, evidence := [cites declarations] }
    rightVerdict := { reading := rightReading, evidence := [cites declarations] } }

def antiFoundationWitnesses : List Witness := [
  fibreWitness "nest-and-loop" "foundation" "afa" "The nest and the loop."
    "One value: neither has a well-founded picture." "Two sets."
    [`Mettapedia.SetTheory.AntiFoundation.fiber_found_afa,
      `Mettapedia.SetTheory.AntiFoundation.not_factors_found_afa],
  fibreWitness "scott-nodes" "afa" "safa" "The two Scott nodes."
    "One set: the nodes are bisimilar." "Ω against {Ω, s}."
    [`Mettapedia.SetTheory.AntiFoundation.fiber_afa_safa,
      `Mettapedia.SetTheory.AntiFoundation.not_factors_afa_safa],
  fibreWitness "unary-binary-roots" "afa" "safa"
    "The two roots of the Scott-extensional unary/binary graph."
    "One set: the roots are bisimilar, and no Aczel decoration of the graph is injective."
    "Two sets: their unfolding trees are not isomorphic, and on a Scott-extensional graph \
      that isomorphism is equality."
    [`Mettapedia.SetTheory.AntiFoundation.GeneralReadouts.unfolding_kernel_finer_than_bisimulation],
  fibreWitness "finsler-nodes" "safa" "fafa" "The Finsler nodes n1 and n2."
    "One set." "Two sets."
    [`Mettapedia.SetTheory.AntiFoundation.fiber_safa_fafa,
      `Mettapedia.SetTheory.AntiFoundation.not_factors_safa_fafa],
  fibreWitness "finsler-downsets" "afa" "fafa"
    "The Finsler nodes n1 and n2, read through bisimulation and pointed downsets."
    "One set: the nodes are bisimilar, and their unfolding paths correspond."
    "Two sets: no isomorphism of pointed downsets takes n1 to n2."
    [`Mettapedia.SetTheory.AntiFoundation.GeneralReadouts.pointed_downset_finer_than_bisimulation_and_unfolding_paths],
  fibreWitness "two-loops" "fafa" "bafa" "Two copies of the loop."
    "One Quine atom." "Two Quine atoms."
    [`Mettapedia.SetTheory.AntiFoundation.fiber_fafa_bafa,
      `Mettapedia.SetTheory.AntiFoundation.not_factors_fafa_bafa],
  fibreWitness "two-cycle" "fafa" "bafa" "The two ends of a two-cycle."
    "One Quine atom." "Two exact pictures."
    [`Mettapedia.SetTheory.AntiFoundation.fiber_fafa_bafa_cycle]
]

def demandWitnesses : List Witness := [
  { id := "coin-discard", observer := "outcome-bag", left := "eager", right := "lazy"
    case := "Discarding a coin, against forcing it and then returning."
    leftVerdict := { reading := "Alike: both draw the coin, giving one result per outcome."
                     evidence := [cites [`Mettapedia.GSLT.Distinction.DemandStrategies.coin_witness]] }
    rightVerdict := { reading := "Different in bags, counts and draws, alike in sets and faults."
                      evidence := [cites [`Mettapedia.GSLT.Distinction.DemandStrategies.coin_witness,
                        `Mettapedia.GSLT.Distinction.DemandStrategies.discard_witness]] } },
  { id := "absent-and-fault", observer := "outcome-set", left := "eager", right := "lazy"
    case := "Discarding a computation with no outcome, and discarding a faulting one."
    leftVerdict := { reading := "No outcome for the first; a fault for the second."
                     evidence := [cites [`Mettapedia.GSLT.Distinction.DemandStrategies.absent_and_fault_witnesses]] }
    rightVerdict := { reading := "One answer and no fault for both: the discarded computation \
                        never runs."
                      evidence := [cites [`Mettapedia.GSLT.Distinction.DemandStrategies.absent_and_fault_witnesses]] } },
  { id := "copy-coin", observer := "outcome-set", left := "lazy", right := "resample"
    case := "Copying a coin, and copying a computation that answers twice."
    leftVerdict := { reading := "One shared draw: the two components always agree."
                     evidence := [cites [`Mettapedia.GSLT.Distinction.DemandStrategies.copy_witnesses,
                       `Mettapedia.GSLT.Distinction.DemandStrategies.sharing_requires_purity]] }
    rightVerdict := { reading := "Two draws: different outcome sets for the coin, different bags \
                        with the same set for the repeated answer."
                      evidence := [cites [`Mettapedia.GSLT.Distinction.DemandStrategies.copy_witnesses]] } },
  { id := "coin-discard-resample", observer := "outcome-bag", left := "eager", right := "resample"
    case := "Discarding a coin."
    leftVerdict := { reading := "Two outcomes, one per side of the coin, and one draw."
                     evidence := [cites [`Mettapedia.GSLT.Distinction.DemandStrategies.eager_resample_coin,
                       `Mettapedia.GSLT.Distinction.DemandStrategies.discard_bags_eager_resample_iff]] }
    rightVerdict := { reading := "One outcome and no draw: the discarded coin never runs."
                      evidence := [cites [`Mettapedia.GSLT.Distinction.DemandStrategies.eager_resample_coin,
                        `Mettapedia.GSLT.Distinction.DemandStrategies.eager_resample_heads]] } },
  { id := "unused-effect", observer := "ordered-trace", left := "eager", right := "lazy"
    case := "Discarding a computation whose answer follows a committed effect."
    leftVerdict := { reading := "The effect is committed."
                     evidence := [cites [`Mettapedia.GSLT.Dynamics.OrderedDemand.Controls.unused_effect_control]] }
    rightVerdict := { reading := "The effect is never committed, although the answer-bag law \
                        licenses the discard."
                      evidence := [cites [`Mettapedia.GSLT.Dynamics.OrderedDemand.Controls.unused_effect_control]] } },
  { id := "repeated-effect", observer := "ordered-trace", left := "lazy", right := "resample"
    case := "Using twice a computation whose answer follows a committed effect."
    leftVerdict := { reading := "The effect is committed once."
                     evidence := [cites [`Mettapedia.GSLT.Dynamics.OrderedDemand.Controls.repeated_effect_control]] }
    rightVerdict := { reading := "The effect is committed twice, although the answer-bag law \
                        licenses resampling."
                      evidence := [cites [`Mettapedia.GSLT.Dynamics.OrderedDemand.Controls.repeated_effect_control]] } },
  { id := "global-laziness", observer := "strategy-observations-kept"
    left := "laziness-global", right := "strategy-bubbles"
    case := "Discarding a computation whose answer follows an effect, and discarding a coin."
    leftVerdict := { reading := "Lost: one lazy rule never commits the effect and gives other \
                       bags, counts and draws than eager evaluation, so the eager observations \
                       are unavailable."
                     evidence := [cites [`Mettapedia.GSLT.Dynamics.OrderedDemand.Controls.unused_effect_control,
                       `Mettapedia.GSLT.Distinction.DemandStrategies.coin_witness]] }
    rightVerdict := { reading := "Kept: every strategy is interpretable in every other with \
                        distortion zero, by forcing, dropping, pairing and sharing."
                      evidence := [cites [`Mettapedia.GSLT.Distinction.DemandStrategies.exact_translations,
                        `Mettapedia.GSLT.Distinction.DemandStrategies.eager_through_lazy_to_resample]] } }
]

def causalWitnesses : List Witness := [
  { id := "would-help-and-inert", observer := "rung-identifies"
    left := "association", right := "intervention"
    case := "A population that treatment would help, against an inert one."
    leftVerdict := { reading := "Identified: watched without intervention they agree."
                     evidence := [cites [`Mettapedia.GSLT.Causality.Hierarchy.ResponseTypes.association_wouldHelp_inert,
                       `Mettapedia.GSLT.Causality.Hierarchy.ResponseTypes.ladder_strict]] }
    rightVerdict := { reading := "Kept apart: treating separates them."
                      evidence := [cites [`Mettapedia.GSLT.Causality.Hierarchy.ResponseTypes.not_intervention_wouldHelp_inert,
                        `Mettapedia.GSLT.Causality.Hierarchy.ResponseTypes.treatedShowsEffect_not_passive]] } },
  { id := "mixed-and-fixed", observer := "rung-identifies"
    left := "intervention", right := "counterfactual"
    case := "Half helped and half hurt, against half always and half never showing the effect."
    leftVerdict := { reading := "Identified: every single intervention gives the same possible \
                       outcomes."
                     evidence := [cites [`Mettapedia.GSLT.Causality.Hierarchy.ResponseTypes.intervention_mixed_fixed,
                       `Mettapedia.GSLT.Causality.Hierarchy.ResponseTypes.ladder_strict]] }
    rightVerdict := { reading := "Kept apart: some drawn individual of the first would show the \
                        effect if treated and not if untreated."
                      evidence := [cites [`Mettapedia.GSLT.Causality.Hierarchy.ResponseTypes.not_counterfactual_mixed_fixed,
                        `Mettapedia.GSLT.Causality.Hierarchy.ResponseTypes.necessaryAndSufficient_not_interventional]] } }
]

/-- A witness between two equality routes, read from the fixture's printed rows. -/
def routeWitness (id left right case leftReading rightReading leftRow rightRow : String) :
    Witness :=
  { id, observer := "rests-on", left, right, case
    pending := [
      `Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.MegalodonHOTG.TwinExtensional.subst_fails,
      `Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.MegalodonHOTG.TwinExtensional.same_ext_fails]
    leftVerdict := { reading := leftReading
                     evidence := [.fixture "prime" "profiles/megalodon_hotg/scoped/equality_routes"
                       [leftRow]] }
    rightVerdict := { reading := rightReading
                      evidence := [.fixture "prime" "profiles/megalodon_hotg/scoped/equality_routes"
                        [rightRow]] } }

def equalityRouteWitnesses : List Witness := [
  routeWitness "identical-r1-r2" "r1-rule" "r2-leibniz"
    "identical: sets with the same members satisfy the same predicates."
    "Rests on extensionality alone; 37 symbols checked."
    "Rests on the axiom same-ext; 18 symbols checked."
    "[(r1 identical (assumes (extensionality)) (proof 37) (term 602))]"
    "[(r2 identical (assumes (same-ext)) (proof 18) (term 252))]",
  routeWitness "rewrite-r1-r3" "r1-rule" "r3-carrier-laws"
    "rewrite: a = b and a ∈ X give b ∈ X."
    "Rests on nothing beyond the rule."
    "Rests on the axiom subst@set."
    "[(r1 rewrite (assumes ()) (proof 18) (term 204))]"
    "[(r3 rewrite (assumes (subst@set)) (proof 26) (term 370))]",
  routeWitness "symmetric-r2-r3" "r2-leibniz" "r3-carrier-laws"
    "symmetric: a = b gives b = a."
    "Rests on nothing: Leibniz identity is symmetric by logic."
    "Rests on subst@set and extensionality."
    "[(r2 symmetric (assumes ()) (proof 18) (term 145))]"
    "[(r3 symmetric (assumes (subst@set extensionality)) (proof 26) (term 295))]"
]

def lambdaRhoWitnesses : List Witness := [
  { id := "quoted-allocation-region", observer := "quoted-code"
    left := "region-observers", right := "reflective-observers"
    case := "ν.0 and 0 are structurally equal π sources; the compiler emits allocation code for \
      the first and inaction for the second, and a ρ test receives on the quoted code."
    leftVerdict := {
      reading := "Not shown to tell them apart: the test needs the compiler's private \
        allocation code. Adequacy for region-bounded observers is not yet a theorem."
      evidence := [
        .argument "spine-report-20261005" "The quoted-observer counterexample"
          "The quoted-observer counterexample separates implementations at the π-to-ρ \
          boundary; unrestricted reflective contextual equivalence is not claimed.",
        .argument "quoted-controls-module" "This is a boundary for observing compiler code"
          "The counterexample concerns observing compiler code, not unrestricted lambda \
          contextual equivalence."] }
    rightVerdict := {
      reading := "Tells them apart: the allocation quote answers the test and the inaction \
        quote cannot."
      evidence := [cites [
        `Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoQuotedCompilerObserverControls.unused_scope_quoted_observer_boundary]] } },
  { id := "quoted-allocation-public", observer := "quoted-code"
    left := "public-observers", right := "reflective-observers"
    case := "The same two compiled processes."
    leftVerdict := {
      reading := "Not shown to tell them apart: a receiver on a public result channel does not \
        take quoted implementation code apart."
      evidence := [.argument "spine-module" "The observers are public result-channel receivers"
        "The spine's adequacy theorems are stated for public result-channel receivers."] }
    rightVerdict := {
      reading := "Tells them apart."
      evidence := [cites [
        `Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoQuotedCompilerObserverControls.unused_scope_quoted_observer_boundary]] } }
]

def designWitnesses : List Witness := [
  { id := "diagonal", observer := "internal-decision"
    left := "decidable-core-first", right := "top-down-carve-out"
    case := "The diagonal term built from a term that decides equality, in a bubble whose \
      terms run on terms and which has two unequal terms."
    leftVerdict := {
      reading := "A core whose terms run on terms has no term deciding its full equality, so \
        such a core cannot itself be the decidable part."
      evidence := [cites [`Mettapedia.GSLT.Reflection.ReflectiveBubble.no_internal_total_decision]] }
    rightVerdict := {
      reading := "Every internally realised decision covers a proper fragment, and its verdict \
        on the diagonal term is outside that fragment."
      evidence := [cites [`Mettapedia.GSLT.Reflection.ReflectiveBubble.fragment_ne_univ,
        `Mettapedia.GSLT.Reflection.ReflectiveBubble.diagonal_verdict_outside]] } },
  { id := "two-reversals", observer := "cost-face"
    left := "dtt-plus-model", right := "trinity"
    case := "rev l and rev-onto nil l on lists of numbers."
    leftVerdict := {
      reading := "One: the type face proves rev l = rev-onto nil l, the set face proves it for \
        every list, and a model gives the two one value."
      evidence := [.fixture "prime" "trinity/reverse.intensional" ["[rev-is-rev-onto]"],
        .fixture "prime" "trinity/reverse.extensional" ["[rev-is-rev-onto]"]] }
    rightVerdict := {
      reading := "Two: the operational face counts 1, 3, 6 and 10 firings for rev on lists of \
        length 0 to 3, against 1, 2, 3 and 4 for the reversal onto an accumulator."
      evidence := [.fixture "prime" "trinity/reverse.operational" ["[(1 3 6 10)]", "[(1 2 3 4)]"]] }
    pending := [`Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Reverse.cost_not_from_set,
      `Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Reverse.reversalTriangle_loses] }
]

def observedReadoutWitnesses : List Witness := [
  { id := "late-reading", observer := "readout-identifies"
    left := "present-readings-bisimilarity", right := "material-value"
    case := "Two initial states of a growing execution whose present readings agree; a reading \
      after context transport differs."
    leftVerdict := {
      reading := "Identified: the states are ordinarily bisimilar and agree on every present \
        reading."
      evidence := [cites [`Mettapedia.GSLT.ContextualObservedCoalgebraControls.Late.same_present_atoms,
        `Mettapedia.GSLT.ContextualObservedCoalgebraControls.Late.ordinary_bisimilar]] }
    rightVerdict := {
      reading := "Kept apart: their complete observed values differ already at the initial \
        context."
      evidence := [cites [
        `Mettapedia.GSLT.ContextualObservedCoalgebraControls.Late.complete_observed_values_differ]] } }
]

/-! ## The graph -/

/-- The options explored for Prime, with their arrows, observers and witnesses. -/
def primeOptions : Graph where
  documents := documents ++ [ContextChoices.report] ++ CarveOuts.documents ++
    [CarveOutSites.report, CarveOutSheaves.report, CarveOutSheafPowers.report,
      CarveOutSheafPowers.finalCoalgebraPaper, WeightAlgebras.report, WeightAlgebras.descriptorLibrary,
      OpenTower.report]
  questions := questions ++ ContextChoices.questions ++ CarveOuts.questions ++
    CarveOutSites.questions ++ CarveOutSheaves.questions ++ CarveOutSheafPowers.questions ++
    [WeightAlgebras.question] ++ OpenTower.questions ++ ReviewDigest.questions
  nodes := setProfileNodes ++ antiFoundationNodes ++ demandNodes ++ demandScopeNodes ++
    causalNodes ++ equalityRouteNodes ++ lambdaRhoNodes ++ observedReadoutNodes ++ designNodes ++
    ContextChoices.nodes ++ CarveOuts.allNodes ++ CarveOutSites.nodes ++ CarveOutSheaves.nodes ++
    CarveOutSheafPowers.nodes ++ WeightAlgebras.nodes ++ OpenTower.nodes ++ ReviewDigest.nodes
  arrows := arrows ++ ContextChoices.arrows ++ CarveOuts.arrows ++ CarveOutSites.arrows ++
    CarveOutSheaves.arrows ++ CarveOutSheafPowers.arrows ++ WeightAlgebras.arrows ++
    OpenTower.arrows ++ ReviewDigest.arrows
  observers := observers ++ ContextChoices.observers ++ CarveOuts.observers ++
    CarveOutSites.observers ++ CarveOutSheaves.observers ++ CarveOutSheafPowers.observers ++
    WeightAlgebras.observers ++ OpenTower.observers ++ ReviewDigest.observers
  witnesses := setProfileWitnesses ++ antiFoundationWitnesses ++ demandWitnesses ++
    causalWitnesses ++ equalityRouteWitnesses ++ lambdaRhoWitnesses ++ observedReadoutWitnesses ++
    designWitnesses ++ ContextChoices.witnesses ++ CarveOuts.witnesses ++ CarveOutSites.witnesses ++
    CarveOutSheaves.witnesses ++ CarveOutSheafPowers.witnesses ++ WeightAlgebras.witnesses ++
    WeightAlgebras.surveyWitnesses ++ WeightAlgebras.targetWitnesses ++
    OpenTower.witnesses ++ ReviewDigest.witnesses
  obligations := CarveOutSheafPowers.obligations
  fixturePins := ReplayPins.fixturePins
  frontierTargets := FrontierMap.targets

theorem primeOptions_wellFormed : primeOptions.wellFormed = true := by
  decide +kernel

/-- **Check one.** Every option ruled out, as a whole or as a default, carries a
witness. -/
theorem primeOptions_rejectedWitnessed : primeOptions.rejectedWitnessed = true := by
  decide +kernel

/-- **Check two, positive control.** The logical profile is not an option ruled out.
The C draft leaves `set:` forms uninterpreted in a space that selects no set theory,
and its internal type and declaration services then use this logical core. -/
theorem logical_profile_admissible : primeOptions.defaultsAdmissible ["hol"] = true := by
  decide +kernel

/-- **Check two, negative control.** The Megalodon HOTG profile as a default is
refused. -/
theorem hotg_profile_refused_as_default :
    primeOptions.defaultsAdmissible ["megalodon-hotg"] = false := by
  decide +kernel

/-! ## Kinds and contracts -/

/-- **Contracts.** Every entry that says an arrow preserves something, or does not,
cites declarations; every entry marked unknown cites none. -/
theorem primeOptions_contractsCited : primeOptions.contractsCited = true := by
  decide +kernel

/-- **Observational quotients.** None claims to preserve first-order formulas without a
cited theorem. -/
theorem primeOptions_quotientsHonest : primeOptions.quotientsHonest = true := by
  decide +kernel

/-- No preservation claim is contradicted by a counterexample recorded for the same
passage. -/
theorem primeOptions_contractsConsistent : primeOptions.contractsConsistent = true := by
  decide +kernel

/-- Every arrow claiming to forget a distinction names a counterexample in its contract. -/
theorem primeOptions_lossyCounterexampled : primeOptions.lossyCounterexampled = true := by
  decide +kernel

/-- **Negative control.** A record claiming that the two-valued reading at a point
preserves bounded formulas. It cites the transfer theorem for positive bounded
formulas, which proves less than the claim. -/
def pointReadingClaim : Arrow where
  id := "points-preserve-bounded"
  source := "double-negation-part"
  target := "two-valued-points"
  kind := .observationalQuotient
  grades := [.factors]
  summary := "Claimed: a point's two-valued reading preserves every bounded formula."
  evidence := [cites [``Mettapedia.SetTheory.CarveOuts.HeytingValued.Point.holds_eval_iff_of_positive]]
  contract := { entries := [
    .keeps (.formulas .bounded)
      [``Mettapedia.SetTheory.CarveOuts.HeytingValued.Point.holds_eval_iff_of_positive]] }

/-- The graph with the bad record added. -/
def withPointReadingClaim : Graph :=
  { primeOptions with arrows := primeOptions.arrows ++ [pointReadingClaim] }

/-- The bad record is refused: the free point's bounded-universal gap, recorded on the
same passage, contradicts it. -/
theorem pointReadingClaim_refused :
    withPointReadingClaim.contractConflicts =
      [("points-preserve-bounded", .formulas .bounded,
        [``Mettapedia.SetTheory.CarveOuts.HeytingValued.free_point_ball_gap])] := by
  decide +kernel

theorem pointReadingClaim_inconsistent : withPointReadingClaim.contractsConsistent = false := by
  decide +kernel

/-! ## Named hypotheses and refutations -/

/-! ## Replay pins -/

/-- Every fixture the registry cites has a replay pin. -/
theorem primeOptions_fixturesPinned : primeOptions.fixturesPinned = true := by
  decide +kernel

/-- **Negative control.** A witness citing a fixture that has no replay pin. -/
def withUnpinnedFixture : Graph :=
  { primeOptions with
    witnesses := primeOptions.witnesses.map fun witness =>
      if witness.id == "equal-supports" then
        { witness with
          rightVerdict := { witness.rightVerdict with
            evidence := witness.rightVerdict.evidence ++
              [.fixture "c-draft" "tests/prime/causal/unpinned_control.metta" []] } }
      else witness }

/-- The unpinned fixture is refused. -/
theorem unpinnedFixture_refused : withUnpinnedFixture.fixturesPinned = false := by
  decide +kernel

/-- Proved obligations cite declarations, and open ones cite none. -/
theorem primeOptions_obligationsCited : primeOptions.obligationsCited = true := by
  decide +kernel

/-- No option is conditional on a hypothesis the registry records as refuted. -/
theorem primeOptions_hypothesesUnrefuted : primeOptions.hypothesesUnrefuted = true := by
  decide +kernel

/-- **Negative control.** The small-map option as first recorded: conditional on (R) for
`Type`-valued sheaves on Cantor space, with the ledger that assumes it. -/
def withTypeRepresentabilityAssumed : Graph :=
  { primeOptions with
    nodes := primeOptions.nodes.map fun node =>
      if node.id == "cantor-sheaf-small-maps" then
        { node with
          ledger := some CarveOutSheaves.conditionalCoalgebraLedger
          hypotheses := node.hypotheses ++
            [{ name := ``CarveOutSheaves.CantorTypeRepresentability
               conditions := "the basic small-map axioms" }] }
      else node }

/-- The record is refused: the registry records the hypothesis as refuted, by the theorem that
every map is small on these sheaves and no small map is universal. -/
theorem typeRepresentabilityAssumed_refused :
    withTypeRepresentabilityAssumed.refutedHypotheses =
      [("cantor-sheaf-small-maps", ``CarveOutSheaves.CantorTypeRepresentability,
        [``Mettapedia.SetTheory.CarveOuts.Sheaves.cantor_sheaf_not_representable])] := by
  decide +kernel

end Mettapedia.Languages.MeTTa.PrimeOptions
