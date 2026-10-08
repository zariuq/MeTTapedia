import Mettapedia.GSLT.Distinction.OptionGraph
import Mettapedia.SetTheory.OpenTower.Hosting
import Mettapedia.SetTheory.OpenTower.Stability
import Mettapedia.SetTheory.OpenTower.NoIsolatedCompletion
import Mettapedia.TypeTheory.IndexedUniverseAdequacy
import Mettapedia.GSLT.Logic.ObserverPresheafControls
import Mettapedia.Logic.TheoryModel.Basic
import Mettapedia.Logic.FinitaryRuleSystem.DirectedUnion
import Mettapedia.Logic.Metaphysics.UltrainfinitismCore
import Mettapedia.Logic.StoneGunkDuality
import Mettapedia.SetTheory.CarveOuts.WellFoundedBubble

/-!
# Open towers of set stages, placed in the option graph

Seven questions, with their options, arrows, contracts and witnesses.

* **What an open tower is** (`open-tower-kind`): an internal tower of closed sets in one level
  under a named supply of inaccessibles; the external schema of embeddings between universe
  levels; a generated enclosure tower; a proof-theoretic progression. The first two are built;
  the last two are recorded without facts from this module.
* **Limits** (`open-tower-limit`): the union of the ω-tower against its closure.
* **Hosting** (`open-tower-hosting`): a stage as a model of an exactly named derivation
  system, componentwise enclosure of its model codes in a later stage, and a first-order set
  model. The coded interpretation agrees through each type's decoding bijection; a single
  internal code for the whole interpretation and internal consistency remain separate.
* **Stability** (`open-tower-stability`): what survives the inclusion of an earlier stage into
  a later one.
* **The strength of the top** (`open-tower-top`): a greatest stage, a strongest completion
  reachable by one sentence, a cofinal extensible family, one fixed model, a linear open tower, or
  a plural family of admitted theories. The review digest proposed this question separately as
  the strength of the top; it is the same question and is merged here. Its "greatest consistent
  theory" is recorded in the one form refuted, a completion isolated by one sentence.
* **Perspectives** (`open-tower-perspectives`): three statements of openness, kept as separate
  options, with the one equivalence that holds between two of them: for Boolean algebras, no
  terminal refinement stage and no principal perspective are the same property.
* **The hosted system** (`open-tower-hosted-system`): the higher-order derivation system of the
  seven set laws, which every stage hosts. Hosting is an interpretation of that system in a stage:
  a stage exists, so the system is consistent relative to the host. No arithmetized consistency
  statement and no conservativity are claimed.

Boundaries are recorded as unknowns, not as preservation claims: whether the union of the
ω-tower satisfies Replacement is open, and the eventual theory is consistent but not shown
complete.

`graph` is the local graph; `graph_wellFormed`, `witnesses_kernelChecked`, `contracts_cited`,
`quotients_honest`, `contracts_consistent`, `lossy_counterexampled` and `rejected_witnessed`
check it, and `identifications` lists the two pairs it proves to be the same. Host choice
enters through the replacement operation of the set model and through
Mathlib's cardinal arithmetic; the choice-free tower is recorded as a fact of the internal
option.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeOptions.OpenTower

open Lean (Name)
open Mettapedia.GSLT.Distinction.OptionGraph

/-- The report that records the arguments. -/
def report : Document where
  key := "open-tower-of-stages-report-20261006"
  title := "Open towers of set stages: what they are, hosting, stability and the top"
  date := "2026-10-06"

/-- The named supply of inaccessibles that the internal tower is conditional on. -/
def cofinalInaccessibles : NamedHypothesis where
  name := ``Mettapedia.Logic.HOL.Embedding.ZFSetUniverseClosure.CofinalInaccessibles
  conditions := "Every theorem of the internal tower: cofinally many inaccessible cardinals at \
    the level of the sets"

/-! ## Questions -/

def questions : List Question := [
  { id := "open-tower-kind"
    title := "What an open tower of set stages is"
    summary := "Four constructions share the name: an internal tower of closed sets in one level \
      under a named supply of inaccessibles, the external schema of embeddings between universe \
      levels, a generated enclosure tower of declared codes, and a proof-theoretic progression \
      of consistency or reflection extensions. None is renamed as another." },
  { id := "open-tower-limit"
    title := "The limit of the ω-tower"
    summary := "Whether the union of the ω-tower is itself a stage, and what it models." },
  { id := "open-tower-hosting"
    title := "How a later stage hosts an earlier one"
    summary := "A stage as a model of an exactly named derivation system with closed falsity \
      empty; its type codes, operation codes and individual truth fibres enclosed in a later \
      stage, with external decoding agreement; a first-order set model of ZFC." },
  { id := "open-tower-stability"
    title := "What survives growth from one stage to a later one"
    summary := "Truth of formulas along the inclusion of an earlier stage into a later one, and \
      the eventual theory of the tower: deductively closed, consistent and containing ZFC; \
      whether it is complete is open."
    facts := [cites [``Mettapedia.SetTheory.OpenTower.Stability.eventualTheory_closed,
      ``Mettapedia.SetTheory.OpenTower.Stability.eventualTheory_consistent,
      ``Mettapedia.SetTheory.OpenTower.Stability.mem_eventualTheory_iff_free,
      ``Mettapedia.SetTheory.OpenTower.Stability.zfc_subset_eventualTheory,
      ``Mettapedia.SetTheory.OpenTower.Stability.infinity_eventual_not_initial]] },
  { id := "open-tower-top"
    title := "Strength of the top"
    summary := "Whether the top is a greatest stage, a strongest theory reached from the base by \
      one sentence, one fixed model, a linear open tower, a plural family of admitted theories \
      with interpretation arrows, or a cofinal, directed, extensible family of stages that no \
      set exhausts. 'Strongest' names an order: constructor capability, interpretability, \
      proof-theoretic strength or model strength."
    facts := [cites [``Mettapedia.TypeTheory.IndexedUniverseAdequacy.no_final_stage,
      ``Mettapedia.TypeTheory.IndexedUniverseAdequacy.finite_support_has_strict_host,
      ``Mettapedia.GSLT.AdmissibleContextCongruence.ObserverPresheafControls.OracleTower.oracleTower_strict,
      ``Mettapedia.Logic.TheoryModel.subset_theoryOf_iff]] },
  { id := "open-tower-hosted-system"
    title := "The system a stage hosts"
    summary := "The higher-order derivation system of the seven set laws, with its proofs \
      retained." },
  { id := "open-tower-perspectives"
    title := "Three statements of openness"
    summary := "No terminal stage of a tower of sets, no isolated completion of a theory, and no \
      principal point of a space of perspectives. Only the last two are joined by a theorem, for \
      Boolean algebras." }
]

/-! ## Options -/

def nodes : List Node := [
  { id := "internal-set-tower", question := "open-tower-kind"
    title := "Internal tower of closed sets"
    summary := "Closed sets in one level of ZFSet: least closed sets around each stage, an \
      ordinal-indexed continuation, directed, cofinal, without a greatest stage. The tower is \
      choice-free when enclosures are supplied as data and replacement is stated relationally."
    hypotheses := [cofinalInaccessibles]
    facts := [cites [``Mettapedia.SetTheory.OpenTower.InternalTower.stage_ssubset_of_lt,
      ``Mettapedia.SetTheory.OpenTower.InternalTower.no_terminal_stage,
      ``Mettapedia.SetTheory.OpenTower.InternalTower.stages_directed,
      ``Mettapedia.SetTheory.OpenTower.InternalTower.no_small_cofinal_family,
      ``Mettapedia.SetTheory.OpenTower.InternalTower.ordinalStage_unbounded,
      ``Mettapedia.SetTheory.OpenTower.InternalTower.closed_empty],
      .«theorem» [
        { declaration :=
          ``Mettapedia.SetTheory.OpenTower.InternalTower.Enclosures.relStage_mem_of_lt,
          choiceFree := true },
        { declaration :=
            ``Mettapedia.SetTheory.OpenTower.InternalTower.Enclosures.relStage_independent,
          choiceFree := true },
        { declaration := ``Mettapedia.SetTheory.OpenTower.InternalTower.hullRel_closedRel,
          choiceFree := true },
        { declaration := ``Mettapedia.SetTheory.OpenTower.Stability.bounded_absolute,
          choiceFree := true }]] },
  { id := "external-level-schema", question := "open-tower-kind"
    title := "External schema across universe levels"
    summary := "The membership-preserving embedding of each level into the next, whose image is \
      a closed set containing ω and elementarily equivalent to the lower level. Each statement \
      sees finitely many levels; the levels are not terms."
    facts := [cites [``Mettapedia.SetTheory.OpenTower.ExternalTower.liftEmbedding_mem_iff,
      ``Mettapedia.SetTheory.OpenTower.ExternalTower.image_is_set,
      ``Mettapedia.SetTheory.OpenTower.ExternalTower.image_closed,
      ``Mettapedia.SetTheory.OpenTower.ExternalTower.not_seen_whole_at_same_level,
      ``Mettapedia.SetTheory.OpenTower.ExternalTower.exists_closed_omega_succ,
      ``Mettapedia.SetTheory.OpenTower.ExternalTower.exists_nested_closed_omega]] },
  { id := "generated-enclosure-tower", question := "open-tower-kind"
    title := "Generated enclosure tower"
    summary := "The closure of declared codes under declared operations, decoded coherently. \
      Weaker than closure under every small family of the ambient level." },
  { id := "proof-theoretic-progression", question := "open-tower-kind"
    title := "Proof-theoretic progression"
    summary := "Extensions of a theory by consistency or reflection principles along presented \
      well-orders. A separate track from enlarging set carriers." },
  { id := "union-of-tower", question := "open-tower-limit"
    title := "The union of the ω-tower"
    summary := "The set of members of all stages of the ω-tower. It models Zermelo set theory with \
      choice; whether it satisfies Replacement is open."
    hypotheses := [cofinalInaccessibles]
    facts := [cites [``Mettapedia.SetTheory.OpenTower.InternalTower.towerUnion_not_closed,
      ``Mettapedia.SetTheory.OpenTower.ZFCStages.towerUnion_zclosed,
      ``Mettapedia.SetTheory.OpenTower.ZFCStages.towerUnion_models_zc]] },
  { id := "closure-of-union", question := "open-tower-limit"
    title := "The ω-th stage"
    summary := "The least closed set around the union of the ω-tower."
    hypotheses := [cofinalInaccessibles]
    facts := [cites [``Mettapedia.SetTheory.OpenTower.InternalTower.limitStage_closed,
      ``Mettapedia.SetTheory.OpenTower.InternalTower.stage_mem_limitStage,
      ``Mettapedia.SetTheory.OpenTower.InternalTower.towerUnion_ne_limitStage]] },
  { id := "stage-model", question := "open-tower-hosting"
    title := "A stage as a model of the seven set laws"
    summary := "The standard higher-order model over the members of a closed set containing ∅. \
      Every retained proof from the seven set laws is interpreted, and closed falsity is empty."
    facts := [cites [``Mettapedia.SetTheory.OpenTower.Hosting.Stage.theory_valid,
      ``Mettapedia.SetTheory.OpenTower.Hosting.Stage.theoremSection,
      ``Mettapedia.SetTheory.OpenTower.Hosting.Stage.falsity_empty,
      ``Mettapedia.SetTheory.OpenTower.Hosting.Stage.consistent]] },
  { id := "internal-copy", question := "open-tower-hosting"
    title := "Model component codes in a later stage"
    summary := "Type codes, coded operations and truth fibres of the stage model are members of \
      every later closed set containing the stage; terms are interpreted by graph lambda and \
      application. Whole-interpretation coding and internal consistency are separate obligations."
    facts := [cites [``Mettapedia.SetTheory.OpenTower.Hosting.Stage.internal_copy,
      ``Mettapedia.SetTheory.OpenTower.Hosting.Stage.consistent_from_internal_copy,
      ``Mettapedia.SetTheory.OpenTower.Hosting.tower_hosting,
      ``Mettapedia.SetTheory.OpenTower.Hosting.external_hosting]] },
  { id := "first-order-set-model", question := "open-tower-hosting"
    title := "A first-order set model of ZFC"
    summary := "The members of a closed set containing ω, as a structure for the first-order \
      language of set theory, with consistency in the Foundation library's calculus."
    facts := [cites [``Mettapedia.SetTheory.OpenTower.ZFCStages.closed_models_zfc,
      ``Mettapedia.SetTheory.OpenTower.ZFCStages.stage_models_zfc,
      ``Mettapedia.SetTheory.OpenTower.ZFCStages.zfc_consistent_of_stage,
      ``Mettapedia.SetTheory.OpenTower.ZFCStages.image_models_zfc,
      ``Mettapedia.SetTheory.OpenTower.ZFCStages.zfc_consistent_of_image]] },
  { id := "earlier-stage", question := "open-tower-stability"
    title := "Truth at an earlier stage"
    summary := "Formulas read among the members of an earlier stage." },
  { id := "later-stage", question := "open-tower-stability"
    title := "Truth at a later stage"
    summary := "Formulas read among the members of a later stage, which includes the earlier \
      one transitively." },
  { id := "greatest-stage", question := "open-tower-top"
    title := "A greatest stage"
    summary := "A closed set including every closed set."
    standings := [{
      standing := .rejected,
      evidence := [cites [``Mettapedia.SetTheory.OpenTower.InternalTower.not_exists_greatest_stage]]
    }]
    hypotheses := [cofinalInaccessibles] },
  { id := "strongest-completion", question := "open-tower-top"
    title := "A strongest theory reached by one sentence"
    summary := "A completion of a base theory isolated by a single sentence over it: the form in \
      which a greatest consistent theory above the base is refuted."
    standings := [{
      standing := .rejected,
      evidence := [cites [
        ``Mettapedia.SetTheory.OpenTower.NoIsolatedCompletion.no_isolated_completion,
        ``Mettapedia.SetTheory.OpenTower.NoIsolatedCompletion.lindenbaum_noTerminalStage]]
    }] },
  { id := "cofinal-extensible-family", question := "open-tower-top"
    title := "A cofinal, directed, extensible family of stages"
    summary := "The class of stages: every set lies in a stage, any two sets lie in one stage, \
      every set-indexed family lies in one stage, and no set-indexed family is cofinal."
    hypotheses := [cofinalInaccessibles]
    facts := [cites [``Mettapedia.SetTheory.OpenTower.InternalTower.exists_stage_containing,
      ``Mettapedia.SetTheory.OpenTower.InternalTower.stages_directed,
      ``Mettapedia.SetTheory.OpenTower.InternalTower.small_family_bounded,
      ``Mettapedia.SetTheory.OpenTower.InternalTower.no_small_cofinal_family]] },
  { id := "one-fixed-model", question := "open-tower-top"
    title := "One fixed model"
    summary := "A single model, for example HOTG with ambient hypersets, as the top. A model is \
      one perspective: a point of the space of completions." },
  { id := "linear-open-tower", question := "open-tower-top"
    title := "A linear open tower"
    summary := "Stages U0 < U1 < …, each modelling the last, with no final stage."
    facts := [cites [``Mettapedia.TypeTheory.IndexedUniverseAdequacy.no_final_stage]] },
  { id := "plural-admitted-family", question := "open-tower-top"
    title := "A plural family of admitted theories"
    summary := "Stages related by interpretation arrows with contracts: directed within a \
      compatible family, joined across incompatible families only by interpretations into a host \
      that keeps their memberships apart; no terminal stage."
    facts := [cites [``Mettapedia.Logic.FinitaryRuleSystem.directedUnion_noBottom,
      ``Mettapedia.Logic.FinitaryRuleSystem.Canary.splitUnion_not_noBottom,
      ``Mettapedia.SetTheory.CarveOuts.not_acc_of_quine]] },
  { id := "seven-law-hol-system", question := "open-tower-hosted-system"
    title := "The derivation system of the seven set laws"
    summary := "Higher-order derivations from the seven HOTG set laws, retained as proof terms." },
  { id := "no-terminal-set-stage", question := "open-tower-perspectives"
    title := "No terminal stage of the tower of sets"
    summary := "Every closed set is a member of a later closed set."
    hypotheses := [cofinalInaccessibles]
    facts := [cites [
      ``Mettapedia.SetTheory.OpenTower.NoIsolatedCompletion.closedSets_noTerminalStage]] },
  { id := "no-terminal-refinement-stage", question := "open-tower-perspectives"
    title := "No terminal refinement stage"
    summary := "In a Boolean algebra, every nonzero element strictly refines to another nonzero \
      element; for Δ₁ extensions of IΣ₁, every consistent sentence over the theory is strictly \
      implied by another consistent one."
    facts := [cites [
      ``Mettapedia.SetTheory.OpenTower.NoIsolatedCompletion.lindenbaum_noTerminalStage,
      ``Mettapedia.SetTheory.OpenTower.NoIsolatedCompletion.bool_has_terminalStage]] },
  { id := "no-principal-perspective", question := "open-tower-perspectives"
    title := "No principal perspective"
    summary := "The space of perspectives has no isolated point: the Stone space of an atomless \
      algebra, the completions of an arithmetic theory, the free ultrafilters on the stage \
      indices."
    facts := [cites [``Mettapedia.SetTheory.OpenTower.NoIsolatedCompletion.no_isolated_completion,
      ``Mettapedia.SetTheory.OpenTower.NoIsolatedCompletion.completions_nonempty,
      ``Mettapedia.SetTheory.OpenTower.NoIsolatedCompletion.free_ultrafilter_not_isolated]] }
]

/-! ## Arrows -/

def arrows : List Arrow := [
  { id := "level-image-as-stage", source := "external-level-schema"
    target := "internal-set-tower"
    kind := .interpretation
    grades := [.preserved]
    summary := "One level read as the set of its lifts one level up: a closed set containing ω, \
      bounding every lifted stage of the lower internal tower."
    evidence := [cites [``Mettapedia.SetTheory.OpenTower.ExternalTower.image_closed,
      ``Mettapedia.SetTheory.OpenTower.ExternalTower.lift_stage_mem_image,
      ``Mettapedia.SetTheory.OpenTower.ExternalTower.image_members_in_closed_members]]
    contract := {
      entries := [
        .keeps (.formulas .firstOrder)
          [``Mettapedia.SetTheory.OpenTower.ExternalTower.image_elementarilyEquivalent]
          "first-order sentences of membership and equality; the lift is an isomorphism onto \
          the members of the image",
        .keeps .laws [``Mettapedia.Logic.HOL.Embedding.ZFSetLiftedUniverseClosure.closed_lift_iff,
          ``Mettapedia.SetTheory.OpenTower.ExternalTower.lift_stage]
          "closedness is preserved and reflected; least closed sets commute with the lift under \
          the inaccessibility hypothesis at both levels",
        .unknownAt (.commitment .choice) "a choice-free code for the image set"] } },
  { id := "union-closes-to-limit", source := "union-of-tower"
    target := "closure-of-union"
    kind := .interpretation
    grades := [.preserved]
    summary := "The union of the ω-tower is a member of the ω-th stage, which contains every \
      stage."
    evidence := [cites [``Mettapedia.SetTheory.OpenTower.InternalTower.stage_mem_limitStage,
      ``Mettapedia.SetTheory.OpenTower.InternalTower.limitStage_closed]]
    contract := {
      entries := [
        .keeps .distinctions [
          ``Mettapedia.SetTheory.OpenTower.InternalTower.towerUnion_ne_limitStage]
          "the union and the ω-th stage are different sets",
        .unknownAt (.formulas .firstOrder)
          "first-order replacement instances in the union of the ω-tower"] } },
  { id := "internal-copy-decodes", source := "internal-copy"
    target := "stage-model"
    kind := .interpretation
    grades := [.preserved]
    summary := "The coded interpretation of a term in the later stage decodes to its denotation \
      in the stage model."
    evidence := [cites [``Mettapedia.SetTheory.OpenTower.Hosting.decode_interpret,
      ``Mettapedia.SetTheory.OpenTower.Hosting.Stage.decode_interpret_stage]]
    contract := {
      entries := [
        .keeps (.formulas .higherOrder)
          [``Mettapedia.SetTheory.OpenTower.Hosting.Stage.decode_interpret_stage]
          "every term and formula of the seven-law signature, at every coded valuation",
        .keeps .verdicts [``Mettapedia.SetTheory.OpenTower.Hosting.Stage.theorem_fibre,
          ``Mettapedia.SetTheory.OpenTower.Hosting.Stage.falsity_fibre]
          "theorems have the inhabited fibre and closed falsity the empty fibre",
        .unknownAt .distinctions
          "one set coding satisfaction for all formulas at once, which needs a coding of the \
          syntax"] } },
  { id := "internal-copy-is-stage-model", source := "stage-model"
    target := "internal-copy"
    kind := .equivalence
    grades := [.exactKernel .extension]
    summary := "The componentwise coded interpretation agrees with the stage model through each \
      type: on every term and coded valuation, the coded interpretation decodes to the model's \
      denotation."
    evidence := [cites [``Mettapedia.SetTheory.OpenTower.Hosting.Stage.decode_interpret_stage,
      ``Mettapedia.SetTheory.OpenTower.Hosting.Stage.decode_codedConstants]]
    contract := {
      entries := [
        .keeps (.formulas .higherOrder)
          [``Mettapedia.SetTheory.OpenTower.Hosting.Stage.decode_interpret_stage]
          "every term and formula of the seven-law signature, at every coded valuation; decoding \
          is a bijection at each type, so every valuation of the model is reached",
        .unknownAt .distinctions
          "one set coding satisfaction for all formulas at once, which needs a coding of the \
          syntax"] } },
  { id := "earlier-into-later", source := "later-stage"
    target := "earlier-stage"
    kind := .restriction
    grades := [.preserved]
    summary := "The earlier stage is a transitive subset of the later one; truth is read on the \
      smaller carrier."
    evidence := [cites [``Mettapedia.SetTheory.OpenTower.InternalTower.stage_subset_of_le,
      ``Mettapedia.SetTheory.OpenTower.Stability.membershipEmbedding]]
    contract := {
      entries := [
        .keeps (.formulas .bounded)
          [``Mettapedia.SetTheory.OpenTower.Stability.bounded_absolute,
          ``Mettapedia.SetTheory.OpenTower.Stability.stage_bounded_absolute]
          "bounded formulas with parameters in the earlier stage, preserved and reflected",
        .loses (.formulas .firstOrder)
          [``Mettapedia.SetTheory.OpenTower.Stability.weakInfinity_changes,
          ``Mettapedia.SetTheory.OpenTower.Stability.infinity_changes]
          "an unbounded sentence false at the first stage over ∅ and true at the next"] } },
  { id := "stage-hosts-hol-system", source := "seven-law-hol-system"
    target := "stage-model"
    kind := .interpretation
    grades := [.ungraded]
    summary := "The derivation system interpreted in a stage, a closed set containing ∅: if the \
      stage exists, every derivation is interpreted and closed falsity has none, so the system \
      is consistent relative to the host. Along the tower and across levels its type codes, \
      operation codes and individual truth fibres belong to the next stage."
    evidence := [cites [``Mettapedia.SetTheory.OpenTower.Hosting.Stage.consistent,
      ``Mettapedia.SetTheory.OpenTower.Hosting.Stage.internal_copy,
      ``Mettapedia.SetTheory.OpenTower.Hosting.tower_hosting,
      ``Mettapedia.SetTheory.OpenTower.Hosting.external_hosting]]
    contract := {
      entries := [
        .keeps .laws [``Mettapedia.SetTheory.OpenTower.Hosting.Stage.theory_valid]
          "the seven set laws hold in the stage",
        .keeps .verdicts [``Mettapedia.SetTheory.OpenTower.Hosting.Stage.consistent,
          ``Mettapedia.SetTheory.OpenTower.Hosting.Stage.falsity_empty]
          "no derivation of closed falsity, given the stage",
        .keeps (.evidence .witnesses) [``Mettapedia.SetTheory.OpenTower.Hosting.Stage.internal_copy,
          ``Mettapedia.SetTheory.OpenTower.Hosting.tower_hosting,
          ``Mettapedia.SetTheory.OpenTower.Hosting.external_hosting]
          "each type code, operation code and individual truth fibre belongs to the next stage",
        .unknownAt .distinctions
          "a single internal code for the whole model, syntax and proof interpretation",
        .unknownAt .verdicts
          "no arithmetized consistency statement Con(T) is stated or proved: consistency is \
          relative to the host and the stage",
        .unknownAt .distinctions
          "no conservativity: nothing true in the stage is shown derivable in the system"] } },
  { id := "plural-family-to-fixed-model", source := "plural-admitted-family"
    target := "one-fixed-model"
    kind := .observationalQuotient
    grades := [.ungraded]
    summary := "Choosing one model is choosing a point of the space of perspectives: what holds \
      at every perspective holds at the chosen one; which independent sentences the point \
      decides is not recorded."
    evidence := [cites [``Mettapedia.Logic.Metaphysics.ultraTrue_all_iff,
      ``Mettapedia.Logic.Metaphysics.ultraTrue_exists_iff,
      ``Mettapedia.Logic.Metaphysics.openFamily_iff_not_precise,
      ``Mettapedia.Foundations.Gunk.isGunky_iff_perfect_stoneSpace,
      ``Mettapedia.SetTheory.OpenTower.NoIsolatedCompletion.completions_perfect,
      ``Mettapedia.SetTheory.OpenTower.NoIsolatedCompletion.no_isolated_completion]]
    contract := {
      entries := [
        .keeps .verdicts [``Mettapedia.Logic.Metaphysics.ultraTrue_all_iff]
          "what holds at every perspective holds at the chosen one",
        .unknownAt .distinctions "which independent sentences the chosen point decides"] } },
  { id := "refinement-is-perspective", source := "no-terminal-refinement-stage"
    target := "no-principal-perspective"
    kind := .equivalence
    grades := [.exactKernel .extension]
    summary := "For a Boolean algebra, a refinement tower of nonzero elements without a terminal \
      stage is exactly a Stone space without an isolated point."
    evidence := [cites [
      ``Mettapedia.SetTheory.OpenTower.NoIsolatedCompletion.noTerminalStage_iff_perfect]]
    contract := {
      entries := [
        .keeps .verdicts
          [``Mettapedia.SetTheory.OpenTower.NoIsolatedCompletion.noTerminalStage_iff_perfect]
          "for every Boolean algebra, its perspectives the points of its Stone space",
        .unknownAt .distinctions
          "a comparison with the tower of sets, which is a different order, and with the free \
          ultrafilters on the stage indices, which are not given as the Stone space of an \
          algebra"] } }
]

/-! ## Observers and witnesses -/

def observers : List Observer := [
  { id := "limit-is-stage", title := "The limit is a stage"
    reads := "Whether the set is closed under union, power set and replacement."
    kind := .«theorem» },
  { id := "unbounded-sentence-preserved", title := "An unbounded sentence keeps its truth value"
    reads := "Whether the sentence `some nonempty set has no member-maximal element` has the \
      same truth value at the two stages."
    kind := .«theorem» },
  { id := "common-upper-stage", title := "A common upper stage"
    reads := "Whether two stages, one with Foundation and one with a Quine atom, need a \
      consistent stage above both on one membership relation."
    kind := .«theorem» },
  { id := "level-bounded", title := "One set bounds the stages of a level"
    reads := "Whether a single set has every stage of a level as a member."
    kind := .«theorem» },
  { id := "first-stage-model", title := "A model at the first stage"
    reads := "Whether the option's model of its theory exists at the first stage of the ω-tower \
      over ∅, where every set is hereditarily finite."
    kind := .«theorem» },
  { id := "realized-at-arithmetic", title := "Realized over arithmetic"
    reads := "Whether the option exists for a consistent Δ₁ extension of IΣ₁."
    kind := .«theorem» },
  { id := "greatest-element", title := "A greatest element"
    reads := "Whether the option has a top: a stage including every stage, or a strongest \
      theory reached by one sentence."
    kind := .«theorem» }
]

def witnesses : List Witness := [
  { id := "union-not-a-stage", observer := "limit-is-stage"
    left := "union-of-tower", right := "closure-of-union"
    case := "The ω-tower over any set, under the inaccessibility hypothesis."
    leftVerdict := {
      reading := "Refuted: replacement along the finite ordinals collects every stage into one \
        member of the union."
      evidence := [cites [``Mettapedia.SetTheory.OpenTower.InternalTower.towerUnion_not_closed]] }
    rightVerdict := {
      reading := "Holds: the least closed set around the union."
      evidence := [cites [``Mettapedia.SetTheory.OpenTower.InternalTower.limitStage_closed]] } },
  { id := "weak-infinity-changes", observer := "unbounded-sentence-preserved"
    left := "earlier-stage", right := "later-stage"
    case := "The first two stages of the ω-tower over ∅."
    leftVerdict := {
      reading := "False: the first stage consists of hereditarily finite sets."
      evidence := [cites [
        ``Mettapedia.SetTheory.OpenTower.Stability.weakInfinity_false_at_stage_zero,
        ``Mettapedia.SetTheory.OpenTower.Stability.stage_zero_hereditarilyFinite]] }
    rightVerdict := {
      reading := "True: the first stage is a member without a member-maximal element."
      evidence := [cites [
        ``Mettapedia.SetTheory.OpenTower.Stability.weakInfinity_true_at_later_stage]] } },
  { id := "no-top-stage", observer := "greatest-element"
    left := "greatest-stage", right := "cofinal-extensible-family"
    case := "Closed sets of one level, under the inaccessibility hypothesis."
    leftVerdict := {
      reading := "Refuted: the least closed set around a greatest one would contain it."
      evidence := [cites [
        ``Mettapedia.SetTheory.OpenTower.InternalTower.not_exists_greatest_stage]] }
    rightVerdict := {
      reading := "Holds without a top: directed, every set-indexed family bounded, no set-indexed \
        family cofinal."
      evidence := [cites [``Mettapedia.SetTheory.OpenTower.InternalTower.stages_directed,
        ``Mettapedia.SetTheory.OpenTower.InternalTower.no_small_cofinal_family]] } },
  { id := "no-strongest-completion", observer := "greatest-element"
    left := "strongest-completion", right := "cofinal-extensible-family"
    case := "A consistent Δ₁ extension of IΣ₁, and the closed sets of one level."
    leftVerdict := {
      reading := "Refuted: every consistent sentence over the theory is strictly implied by \
        another consistent one, so no completion is isolated."
      evidence := [cites [
        ``Mettapedia.SetTheory.OpenTower.NoIsolatedCompletion.lindenbaum_noTerminalStage,
        ``Mettapedia.SetTheory.OpenTower.NoIsolatedCompletion.no_isolated_completion]] }
    rightVerdict := {
      reading := "Holds without a top: every closed set is a member of a later one."
      evidence := [cites [
        ``Mettapedia.SetTheory.OpenTower.NoIsolatedCompletion.closedSets_noTerminalStage]] } },
  { id := "lower-level-bounded-above", observer := "level-bounded"
    left := "internal-set-tower", right := "external-level-schema"
    case := "The ordinal-indexed tower of closed sets of one level, under the inaccessibility \
      hypothesis."
    leftVerdict := {
      reading := "Not bounded: no set of the level contains every stage."
      evidence := [cites [``Mettapedia.SetTheory.OpenTower.InternalTower.ordinalStage_unbounded]] }
    rightVerdict := {
      reading := "Bounded one level up: the lift of every stage is a member of the image of the \
        level, which is a set there."
      evidence := [cites [``Mettapedia.SetTheory.OpenTower.ExternalTower.lift_ordinalStage_mem_image,
        ``Mettapedia.SetTheory.OpenTower.ExternalTower.image_is_set]] } },
  { id := "first-stage-not-zfc", observer := "first-stage-model"
    left := "stage-model", right := "first-order-set-model"
    case := "The first stage of the ω-tower over ∅, under the inaccessibility hypothesis."
    leftVerdict := {
      reading := "A model: the stage models the seven set laws, with closed falsity empty."
      evidence := [cites [``Mettapedia.SetTheory.OpenTower.Hosting.tower_hosting]] }
    rightVerdict := {
      reading := "Not a model of ZFC: the axiom of infinity fails at the first stage and holds \
        from the next on."
      evidence := [cites [``Mettapedia.SetTheory.OpenTower.Stability.infinity_changes,
        ``Mettapedia.SetTheory.OpenTower.Stability.stage_zero_hereditarilyFinite]] } },
  { id := "first-stage-copy-not-zfc", observer := "first-stage-model"
    left := "internal-copy", right := "first-order-set-model"
    case := "The first stage of the ω-tower over ∅, under the inaccessibility hypothesis."
    leftVerdict := {
      reading := "Present: the codes, operations and truth fibres of its model are members of the \
        next stage."
      evidence := [cites [``Mettapedia.SetTheory.OpenTower.Hosting.tower_hosting]] }
    rightVerdict := {
      reading := "Not a model of ZFC: the axiom of infinity fails at the first stage."
      evidence := [cites [``Mettapedia.SetTheory.OpenTower.Stability.infinity_changes]] } },
  { id := "no-top-linear-stage", observer := "greatest-element"
    left := "greatest-stage", right := "linear-open-tower"
    case := "Closed sets of one level, and a linear tower of universe stages."
    leftVerdict := {
      reading := "Refuted: the least closed set around a greatest one would contain it."
      evidence := [cites [
        ``Mettapedia.SetTheory.OpenTower.InternalTower.not_exists_greatest_stage]] }
    rightVerdict := {
      reading := "Holds without a top: no stage is final, and every finite set of stages has a \
        strictly larger host."
      evidence := [cites [``Mettapedia.TypeTheory.IndexedUniverseAdequacy.no_final_stage,
        ``Mettapedia.TypeTheory.IndexedUniverseAdequacy.finite_support_has_strict_host]] } },
  { id := "no-strongest-linear-stage", observer := "greatest-element"
    left := "strongest-completion", right := "linear-open-tower"
    case := "A consistent Δ₁ extension of IΣ₁, and a linear tower of universe stages."
    leftVerdict := {
      reading := "Refuted: no completion is isolated."
      evidence := [cites [
        ``Mettapedia.SetTheory.OpenTower.NoIsolatedCompletion.no_isolated_completion]] }
    rightVerdict := {
      reading := "Holds without a top: no stage is final."
      evidence := [cites [``Mettapedia.TypeTheory.IndexedUniverseAdequacy.no_final_stage]] } },
  { id := "a-completion-exists", observer := "realized-at-arithmetic"
    left := "strongest-completion", right := "one-fixed-model"
    case := "A consistent Δ₁ extension of IΣ₁."
    leftVerdict := {
      reading := "Not realized: no completion is reached by one sentence over the theory."
      evidence := [cites [
        ``Mettapedia.SetTheory.OpenTower.NoIsolatedCompletion.no_isolated_completion]] }
    rightVerdict := {
      reading := "Realized: the space of completions is nonempty, and each completion is one \
        fixed perspective."
      evidence := [cites [
        ``Mettapedia.SetTheory.OpenTower.NoIsolatedCompletion.completions_nonempty]] } },
  { id := "foundation-vs-quine", observer := "common-upper-stage"
    left := "plural-admitted-family", right := "linear-open-tower"
    case := "A stage with Foundation and a stage with a Quine atom, on one membership relation."
    leftVerdict := {
      reading := "Not needed: a Quine atom is not accessible, so the well-founded part and the \
        hypersets stay apart and are joined by interpretation."
      evidence := [cites [``Mettapedia.SetTheory.CarveOuts.not_acc_of_quine]] }
    rightVerdict := {
      reading := "Needed: a linear tower puts both on one membership, and in the canary rule \
        system a union that is not directed derives falsity."
      evidence := [cites [``Mettapedia.Logic.FinitaryRuleSystem.Canary.splitUnion_not_noBottom]] } }
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

theorem lossy_counterexampled : graph.lossyCounterexampled = true := by
  decide +kernel

/-- Every rejected option carries a witness. -/
theorem rejected_witnessed : graph.rejectedWitnessed = true := by
  decide +kernel

/-- **The two comparisons**: the componentwise coded interpretation agrees with the stage model,
and for Boolean algebras
no terminal refinement stage is no principal perspective. -/
theorem identifications : graph.equivalences = [
    ("stage-model", "internal-copy"),
    ("no-terminal-refinement-stage", "no-principal-perspective")] := by
  decide +kernel

end Mettapedia.Languages.MeTTa.PrimeOptions.OpenTower
