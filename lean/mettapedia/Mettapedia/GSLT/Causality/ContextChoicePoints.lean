import Mettapedia.GSLT.Causality.ContextOperatorsControls
import Mettapedia.GSLT.Causality.ContextOperatorsWeighted
import Mettapedia.GSLT.Causality.StructuralModels
import Mettapedia.GSLT.Causality.AdaptiveContexts
import Mettapedia.GSLT.Causality.AbstractionControls
import Mettapedia.GSLT.Causality.ProbabilitiesOfCausation
import Mettapedia.GSLT.Distinction.DemandStrategies
import Mettapedia.GSLT.Distinction.Probabilistic
import Mettapedia.GSLT.Distinction.HistoryObserverControls

/-!
# Choice points of the context operators: what each restriction keeps and loses

Each design choice is a pair: the general top and a restricted option.  For
each pair this module records

* **the embedding**: the restricted option as a bubble inside the top, with
  its guarantee proved as a theorem about the bubble;
* **the separating witness**: a concrete case the restricted option cannot
  express or cannot distinguish;
* **the evidence kind** of each part: `«theorem»` (checked by the kernel),
  `fixture` (a test of the C implementation with an expected output),
  `argument` (a written argument) or `decision`.

For every part whose evidence is a theorem, the record's conjunction
(`explicitDo_record`, `strategy_record`, `provenance_record`,
`firstClass_record`, `region_record`, `weights_record`, `structural_record`,
`gradedIdentity_record`) states the embedding's guarantee and the witness
together, assembled from the theorems named in the table `records`.  The
names in the table are resolved when this module is compiled.

| choice | restricted option | general top |
|---|---|---|
| 0 | explicit `do` (one assignment) | `do` derived from binding override |
| 1 | one global evaluation strategy | strategy as a bubble |
| 2 | forgetful readouts | readouts that keep provenance |
| 3 | contexts only at the meta level | first-class contexts |
| 4 | region-bounded interventions | unrestricted interventions |
| 5 | possibility | weights |
| 6 | one causal calculus in the kernel | causal theories as bubbles |
| 7 | one fixed equality | graded identity |

Choice 0 has two directions.  On values over finitely many keys the two
presentations have the same plug maps, so the choice evaporates on the ladder.
Over infinitely many keys explicit assignments reach further, so the chains
are the bubble.  On computations explicit `do` is eager, a bubble inside
derived `do` whose guarantee is that every binding is drawn once, and the
override law fails for it exactly off the discarding line of
`DemandAgreement`.

Choice 3 records one part as an argument.  The proved separation is relative
to the model: no meta-level intervention on the given model behaves like the
adaptive program (`AdaptiveContexts.adaptive_not_meta`), while a different model
does (`AdaptiveContexts.adaptive_reencoded`).  The stronger claim, that an
observer restricted to meta-level contexts cannot state the adaptive query as
a formula, depends on what the observer may read: when the covariate the
policy reads is an observation, a saturated formula can branch on it, choose
the regime per branch, and so express the query; when it is not, the policy
is beyond the formula.  That dependence is recorded as an argument, not as a
theorem.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ContextChoicePoints

open Mettapedia.GSLT
open Mettapedia.GSLT.MinimalEnablingContext
open Mettapedia.GSLT.AdmissibleContextCongruence
open Mettapedia.GSLT.Distinction
open Mettapedia.GSLT.Causality.Hierarchy
open Mettapedia.GSLT.Causality.ContextOperators
open Mettapedia.GSLT.Causality.ContextBindings
open Mettapedia.GSLT.Causality.ContextBindings.OverrideAction

/-! ## The records -/

/-- The evidence for one part of a record. -/
inductive Evidence where
  /-- A theorem checked by the kernel. -/
  | «theorem»
  /-- A test of the C implementation with an expected output. -/
  | fixture
  /-- A written argument. -/
  | argument
  /-- A decision. -/
  | decision
  deriving DecidableEq, Repr

/-- **A choice point**: the restricted option, the general top, the theorems
that embed the restricted option as a bubble with its guarantee, and the
witnesses of what it loses, each with its evidence. -/
structure Record where
  number : ℕ
  restricted : String
  general : String
  embedding : List Lean.Name
  embeddingEvidence : List Evidence
  witness : List Lean.Name
  witnessEvidence : List Evidence
  /-- The C fixtures that exhibit the choice, as paths in the implementation's
  test tree. -/
  fixtures : List String
  /-- Statements recorded as arguments, verbatim. -/
  arguments : List String
  deriving Repr

/-- **The table of choice points.** -/
def records : List Record :=
  [ { number := 0
      restricted := "explicit do: one simultaneous assignment"
      general := "do derived from binding override (ctx:bind, newest wins)"
      embedding := [``ContextBindings.OverrideAction.bindingPlug_equiv_assign,
        ``ContextBindings.OverrideAction.explicit_derived_agree,
        ``ContextBindings.OverrideAction.explicit_derived_interventionalDistance,
        ``ContextBindings.OverrideAction.explicit_derived_counterfactualDistance,
        ``ContextBindings.explicitAnswers_doBinding, ``ContextBindings.derivedAnswers_doBinding,
        ``ContextBindings.explicitDraws_doBinding, ``ContextBindings.explicit_eq_derived_of_read]
      embeddingEvidence := [.«theorem», .fixture]
      witness := [``ContextBindings.explicit_eq_derived_iff,
        ``ContextBindings.explicit_derived_support_iff, ``ContextBindings.explicit_override_iff,
        ``ContextBindings.derived_override,
        ``ContextOperatorsControls.Store.explicit_beyond_derived]
      witnessEvidence := [.«theorem», .fixture]
      fixtures := ["tests/prime/causal/structural_model.metta",
        "tests/prime/causal/composition_regions.metta"]
      arguments := [] },
    { number := 1
      restricted := "one global evaluation strategy"
      general := "evaluation strategy as a bubble"
      embedding := [``Dynamics.DemandAgreement.strategies_agree_iff,
        ``Dynamics.DemandAgreement.strategies_agree_support_iff,
        ``Distinction.DemandStrategies.deterministic_eager_lazy,
        ``Distinction.DemandStrategies.exact_translations]
      embeddingEvidence := [.«theorem», .fixture]
      witness := [``Dynamics.DemandAgreement.coin_uses,
        ``Dynamics.DemandAgreement.discard_atLeastOne_fails_on_coin,
        ``Distinction.DemandStrategies.sharing_requires_purity]
      witnessEvidence := [.«theorem», .fixture]
      fixtures := ["tests/prime/demand/bubbles.metta"]
      arguments := [] },
    { number := 2
      restricted := "forgetful readouts"
      general := "readouts that keep provenance (the retained unit, the occurrence)"
      embedding := [``Hierarchy.agree_of_le,
        ``AbstractionControls.Forgetful.passive_isometry,
        ``AbstractionControls.Forgetful.commutes_at_mixed]
      embeddingEvidence := [.«theorem»]
      witness := [``Hierarchy.ResponseTypes.ladder_strict,
        ``AbstractionControls.Forgetful.collapses_mixed_fixed,
        ``Hierarchy.ResponseTypes.not_counterfactual_mixed_fixed,
        ``ContextOperatorsControls.Retention.mixed_fixed_retention,
        ``Distinction.HistoryObserverControls.kind_bisimilar_not_eq,
        ``Distinction.HistoryObserverControls.no_matcher_recovers_occurrences]
      witnessEvidence := [.«theorem», .fixture]
      fixtures := ["tests/prime/causal/twin_experiment.metta",
        "tests/prime/shared_cause_probability.metta"]
      arguments := [] },
    { number := 3
      restricted := "contexts only at the meta level"
      general := "first-class contexts"
      embedding := [``AdaptiveContexts.internal_do_eq_external, ``AdaptiveContexts.embed_impose,
        ``AdaptiveContexts.moves_embed, ``AdaptiveContexts.moves_of_embed,
        ``AdaptiveContexts.shows_embed,
        ``AdaptiveContexts.constant_policy_regime_independent]
      embeddingEvidence := [.«theorem»]
      witness := [``AdaptiveContexts.flip_regime_depends, ``AdaptiveContexts.adaptive_not_meta,
        ``AdaptiveContexts.adaptive_reencoded]
      witnessEvidence := [.«theorem», .fixture, .argument]
      fixtures := ["tests/prime/causal/adaptive_policy.metta"]
      arguments := ["The separation is relative to the model: no meta-level intervention " ++
        "on the given model behaves like the adaptive program, and a different model does. " ++
        "Whether an observer with meta-level contexts only can state the adaptive query as " ++
        "a formula depends on whether the covariate the policy reads is an observation; " ++
        "this dependence is not proved."] },
    { number := 4
      restricted := "region-bounded interventions"
      general := "unrestricted interventions"
      embedding := [``ContextBindings.OverrideAction.regionDerived_mono,
        ``ContextBindings.OverrideAction.agree_of_region_le,
        ``ContextBindings.OverrideAction.interventionalDistance_region_mono,
        ``ContextBindings.OverrideAction.counterfactualDistance_region_mono,
        ``ContextOperators.agree_of_unwinding,
        ``ContextOperatorsControls.OneShot.masked_noninterference,
        ``ContextOperatorsControls.OneShot.region_noninterference]
      embeddingEvidence := [.«theorem»]
      witness := [``ContextOperatorsControls.OneShot.region_witness]
      witnessEvidence := [.«theorem», .fixture]
      fixtures := ["tests/prime/causal/composition_regions.metta"]
      arguments := [] },
    { number := 5
      restricted := "possibility"
      general := "weights"
      embedding := [``WeightedResponseTypes.erase_agree_of_weightedAgree,
        ``WeightedResponseTypes.necessaryAndSufficient_erase_iff,
        ``Distinction.Probabilistic.ProbabilisticSystem.support_eq_boolean_image]
      embeddingEvidence := [.«theorem»]
      witness := [``WeightedResponseTypes.erasure_strict,
        ``WeightedResponseTypes.equalSupport_control,
        ``Hierarchy.ResponseTypes.monotonicity_not_identifying,
        ``WeightedResponseTypes.monotonicity_identifies_with_weights,
        ``Distinction.Probabilistic.Causal.support_does_not_transport_pns]
      witnessEvidence := [.«theorem»]
      fixtures := []
      arguments := [] },
    { number := 6
      restricted := "one causal calculus in the kernel"
      general := "causal theories as bubbles of the GSLT top"
      embedding := [``StructuralModels.exists_unique_solution,
        ``StructuralModels.surgery_exists_unique_solution,
        ``StructuralModels.run_reaches_solution, ``StructuralModels.step_self_iff]
      embeddingEvidence := [.«theorem»]
      witness := [``StructuralModels.copyLoop_two_solutions,
        ``StructuralModels.negLoop_no_solution, ``StructuralModels.negLoop_never_settles,
        ``StructuralModels.copyLoop_not_recursive, ``StructuralModels.negLoop_not_recursive]
      witnessEvidence := [.«theorem», .fixture, .argument]
      fixtures := ["tests/prime/causal/structural_model.metta",
        "tests/prime/causal/feedback.metta"]
      arguments := ["Halpern's nonrecursive models with a unique solution for every " ++
        "setting form a class between the recursive models and all models; no model of " ++
        "that intermediate class is exhibited here."] },
    { number := 7
      restricted := "one fixed equality"
      general := "graded identity: three rung equalities and their distances"
      embedding := [``Hierarchy.agree_of_le, ``AdmissibleClass.relEquiv_of_equiv,
        ``Hierarchy.interventionalDistance_eq_zero_iff,
        ``Distinction.saturatedCrisp_logicalDistance_eq_zero_iff,
        ``Hierarchy.interventional_le_counterfactual]
      embeddingEvidence := [.«theorem»]
      witness := [``Hierarchy.ResponseTypes.ladder_strict,
        ``AbstractionControls.ResponseGraded.passiveDistance_wouldHelp_inert,
        ``AbstractionControls.ResponseGraded.interventionalDistance_wouldHelp_inert,
        ``AbstractionControls.ResponseGraded.interventionalDistance_mixed_fixed,
        ``AbstractionControls.ResponseGraded.counterfactualDistance_mixed_fixed]
      witnessEvidence := [.«theorem»]
      fixtures := []
      arguments := [] } ]

theorem records_length : records.length = 8 := rfl

/-! ## The records as theorems -/

section Records

open Mettapedia.GSLT.Dynamics.DemandAgreement

/-- **Choice 0.**  On values the two presentations have one ladder; on
computations the explicit, eager `do` keeps the override law exactly when the
shadowed computation has one answer or the newer none, while derived `do`
always keeps it; over infinitely many keys explicit assignments separate what
chains cannot. -/
theorem explicitDo_record :
    (∀ {S : GSLT} {Key Value : Type} [DecidableEq Key] (O : OverrideAction S Key Value)
        (observations : ContextualRules.Observations S) (region : Set Key) (rung : Rung)
        (left right : S.Term),
        Agree (O.regionExplicit region) observations rung left right ↔
          Agree (O.regionDerived region) observations rung left right) ∧
      (∀ {Key α : Type} [DecidableEq Key] (key : Key) (computation : Multiset α) (uses : ℕ),
        explicitAnswers (doBinding key computation) (List.replicate uses key) =
            derivedAnswers (doBinding key computation) (List.replicate uses key) ↔
          1 ≤ uses ∨ computation.card = 1) ∧
      (∀ {Key α : Type} [DecidableEq Key] (key : Key) (older newer : Multiset α) (body : List Key),
        explicitAnswers (graft (doBinding key newer) (doBinding key older)) body =
            explicitAnswers (doBinding key newer) body ↔
          older.card = 1 ∨ newer = 0) ∧
      (∀ {Key α : Type} [DecidableEq Key] (key : Key) (older newer : Multiset α) (body : List Key),
        derivedAnswers (graft (doBinding key newer) (doBinding key older)) body =
          derivedAnswers (doBinding key newer) body) ∧
      (Agree ((ContextOperatorsControls.Store.storeAction ℕ Bool).regionDerived Set.univ)
          ContextOperatorsControls.Store.everyKeyTrue .counterfactual
          ContextOperatorsControls.Store.allFalse ContextOperatorsControls.Store.trueAtZero ∧
        ¬ Agree (⊤ : AdmissibleClass (ContextOperatorsControls.Store.storeAction ℕ Bool).explicitRules)
          ContextOperatorsControls.Store.everyKeyTrue .intervention
          ContextOperatorsControls.Store.allFalse ContextOperatorsControls.Store.trueAtZero) :=
  ⟨fun O observations region rung left right =>
      O.explicit_derived_agree observations region rung left right,
    fun key computation uses => explicit_eq_derived_iff key computation uses,
    fun key older newer body => explicit_override_iff key older newer body,
    fun key older newer body => derived_override key older newer body,
    ContextOperatorsControls.Store.explicit_beyond_derived⟩

/-- **Choice 1.**  The three strategies agree exactly on the discarding and
copying lines, and the coin separates them off those lines. -/
theorem strategy_record :
    (∀ (α : Type) (uses : ℕ) (computation : Multiset α),
        eagerShared uses computation = lazyShared uses computation ∧
            lazyShared uses computation = resampledUses uses computation ↔
          (1 ≤ uses ∨ computation.card = 1) ∧ (uses ≤ 1 ∨ computation.card ≤ 1)) ∧
      (eagerShared 0 coinBag ≠ lazyShared 0 coinBag ∧
        (eagerShared 0 coinBag).toFinset = (lazyShared 0 coinBag).toFinset ∧
          (lazyShared 2 coinBag).toFinset ≠ (resampledUses 2 coinBag).toFinset) :=
  ⟨fun _ uses computation => strategies_agree_iff uses computation, coin_uses⟩

open Mettapedia.GSLT.Causality.AbstractionControls
open Mettapedia.GSLT.Causality.AbstractionControls.ResponseGraded
open Mettapedia.GSLT.Causality.Hierarchy.ResponseTypes

/-- **Choice 2.**  Forgetting response types keeps every passive answer and
loses a rung-3 answer: the forgotten mixed and fixed populations are at
counterfactual distance zero, while the populations themselves differ on
whether treatment is necessary and sufficient for some unit; the twin built
from the shared draw tells them apart, the experiment does not. -/
theorem provenance_record (discount : ℝ) (discount_nonneg : 0 ≤ discount)
    (discount_le_one : discount ≤ 1) :
    (∀ left right : Stage,
        passiveDistance readings discount discount_nonneg discount_le_one
            (Forgetful.forget left) (Forgetful.forget right) =
          passiveDistance readings discount discount_nonneg discount_le_one left right) ∧
      counterfactualDistance everyIntervention readings discount discount_nonneg discount_le_one
          (Forgetful.forget mixed) (Forgetful.forget fixed) = 0 ∧
      (everyIntervention.saturated quantities).sat necessaryAndSufficient mixed ∧
      ¬ (everyIntervention.saturated quantities).sat necessaryAndSufficient fixed ∧
      ContextOperatorsControls.Retention.experimentSet mixedIndividuals =
          ContextOperatorsControls.Retention.experimentSet fixedIndividuals ∧
        ContextOperatorsControls.Retention.twinSet mixedIndividuals ≠
          ContextOperatorsControls.Retention.twinSet fixedIndividuals :=
  ⟨Forgetful.passive_isometry discount discount_nonneg discount_le_one,
    Forgetful.collapses_mixed_fixed discount discount_nonneg discount_le_one,
    mixed_sat_necessaryAndSufficient, fixed_not_sat_necessaryAndSufficient,
    ContextOperatorsControls.Retention.mixed_fixed_retention⟩

/-- **Choice 3.**  Meta-level interventions are the constant policies; their
guarantee is that the regime does not depend on the unit; the adaptive policy
is no meta-level intervention on the same model, and is one on a re-encoded
model. -/
theorem firstClass_record :
    (∀ (individuals : List (Bool × Response)) (treatment : Option Bool),
        AdaptiveContexts.Stage.population individuals (fun _ => treatment) =
          AdaptiveContexts.impose treatment (.population individuals fun _ => none)) ∧
      (∀ {individuals : List (Bool × Response)} {treatment : Option Bool} {natural : Bool}
          {response : Response} {imposed : Option Bool},
        AdaptiveContexts.Moves (.population individuals fun _ => treatment)
            (.individual natural response imposed) → imposed = treatment) ∧
      (∀ treatment : Option Bool,
        ¬ ReductionBisimilar AdaptiveContexts.quantities
          (AdaptiveContexts.embed (impose treatment (.population AdaptiveContexts.twoUnits none)))
          (.population AdaptiveContexts.twoUnits AdaptiveContexts.flip)) ∧
      ReductionBisimilar AdaptiveContexts.quantities
        (.population AdaptiveContexts.twoUnits AdaptiveContexts.flip)
        (AdaptiveContexts.embed (.population AdaptiveContexts.reencodedUnits none)) :=
  ⟨AdaptiveContexts.internal_do_eq_external,
    fun step => AdaptiveContexts.constant_policy_regime_independent step,
    AdaptiveContexts.adaptive_not_meta, AdaptiveContexts.adaptive_reencoded⟩

open ContextOperatorsControls.OneShot in
/-- **Choice 4.**  A smaller region gives a smaller class, and the region's
contexts cannot separate a pair that a context outside the region separates. -/
theorem region_record :
    (∀ {region region' : Set Switch}, region ⊆ region' →
        (oneShotAction Switch Bool).regionDerived region ≤
          (oneShotAction Switch Bool).regionDerived region') ∧
      (∀ rung, Agree ((oneShotAction Switch Bool).regionDerived {Switch.open_}) (shows Switch Bool) rung
        (.pending gatedLaw secretOn) (.pending gatedLaw secretOff)) ∧
      ¬ Agree (⊤ : AdmissibleClass (oneShotAction Switch Bool).derivedRules) (shows Switch Bool)
        .intervention (.pending gatedLaw secretOn) (.pending gatedLaw secretOff) :=
  ⟨fun sub => (oneShotAction Switch Bool).regionDerived_mono sub, region_cannot_separate,
    global_separates⟩

open Mettapedia.GSLT.Causality.WeightedResponseTypes in
/-- **Choice 5.**  Erasure maps the weighted ladder to the possibilistic one
and keeps the positivity of the probability of necessity and sufficiency; two
populations with equal supports agree at every possibilistic rung and at no
weighted rung. -/
theorem weights_record :
    (∀ (rung : Rung) {population population' : Mettapedia.InformationTheory.Prob Individual},
        WeightedAgree rung population population' →
          Agree everyIntervention quantities rung (erase population none) (erase population' none)) ∧
      (∀ population : Mettapedia.InformationTheory.Prob Individual,
        ladder.sat necessaryAndSufficient (erase population none) ↔ 0 < pns population) ∧
      ((∀ rung, Agree everyIntervention quantities rung (erase mostlyHelped none)
          (erase mostlyAlways none)) ∧
        ∀ rung, ¬ WeightedAgree rung mostlyHelped mostlyAlways) :=
  ⟨fun rung _ _ agree => erase_agree_of_weightedAgree rung agree, necessaryAndSufficient_erase_iff,
    erasure_strict⟩

open Mettapedia.GSLT.Causality.StructuralModels in
/-- **Choice 6.**  Recursive models have exactly one solution, before and after
every intervention; copying feedback has two and negating feedback none, and
neither is recursive; all are terms of one GSLT. -/
theorem structural_record :
    (∀ {Key Value : Type} {mechanisms : Mechanisms Key Value}, Recursive mechanisms →
        ∀ assignment : Key → Option Value, Nonempty (Key → Value) →
          ∃! store, IsSolution (surgery assignment mechanisms) store) ∧
      (IsSolution copyLoop (fun _ => false) ∧ IsSolution copyLoop (fun _ => true) ∧
        (fun _ : Cell => false) ≠ fun _ => true) ∧
      (∀ store, ¬ IsSolution negLoop store) ∧
      (Recursive copyLoop → False) ∧ (Recursive negLoop → False) :=
  ⟨fun recursive assignment ⟨seed⟩ => surgery_exists_unique_solution recursive assignment seed,
    copyLoop_two_solutions, negLoop_no_solution, copyLoop_not_recursive, negLoop_not_recursive⟩

/-- **Choice 7.**  The rung equalities refine one another and contain the
equations; they are strict, and graded: the populations that would be helped
and the inert one are at passive distance zero and interventional distance at
least the square of the discount; the mixed and the fixed populations are at
interventional distance zero and counterfactual distance at least that. -/
theorem gradedIdentity_record (discount : ℝ) (discount_nonneg : 0 ≤ discount)
    (discount_le_one : discount ≤ 1) :
    ((Agree everyIntervention quantities .association wouldHelp inert ∧
          ¬ Agree everyIntervention quantities .intervention wouldHelp inert) ∧
        (Agree everyIntervention quantities .intervention mixed fixed ∧
          ¬ Agree everyIntervention quantities .counterfactual mixed fixed)) ∧
      passiveDistance readings discount discount_nonneg discount_le_one wouldHelp inert = 0 ∧
      discount * discount ≤
        interventionalDistance everyIntervention readings discount discount_nonneg discount_le_one
          wouldHelp inert ∧
      interventionalDistance everyIntervention readings discount discount_nonneg discount_le_one
          mixed fixed = 0 ∧
      discount * discount ≤
        counterfactualDistance everyIntervention readings discount discount_nonneg discount_le_one
          mixed fixed :=
  ⟨ladder_strict, passiveDistance_wouldHelp_inert discount discount_nonneg discount_le_one,
    interventionalDistance_wouldHelp_inert discount discount_nonneg discount_le_one,
    interventionalDistance_mixed_fixed discount discount_nonneg discount_le_one,
    counterfactualDistance_mixed_fixed discount discount_nonneg discount_le_one⟩

end Records

end Mettapedia.GSLT.Causality.ContextChoicePoints
