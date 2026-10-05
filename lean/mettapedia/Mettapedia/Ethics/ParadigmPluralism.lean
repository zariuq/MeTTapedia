import Mettapedia.GSLT.Logic.Views
import Mettapedia.Ethics.ChoicePointParadigms
import Mettapedia.Ethics.MoralParadigmEquivalence

/-!
# Ethical paradigms as plural views

The deontic, utilitarian and target-centered virtue paradigms of
`Mettapedia.Ethics.MoralParadigmEquivalence` translate into one another with
the same judgments.  This module asks the pluralist questions of
`Mettapedia.GSLT.Logic.Views` about them: what each translation keeps
(a `Factors` statement), what it forgets (a `NonTrivialFiber`), whether some
paradigm is privileged, and whether learners in the three paradigms converge.

**Every paradigm can serve as the pivot; none is lossless.**
* Going through any pivot and back keeps the judgment (`roundTrips_exact`),
  but the round trip is not the identity: utilities lose their magnitude
  (`utility_roundTrip_forgets_magnitude`), rule sets and virtue sets are
  replaced by the canonical ones (`deontic_roundTrip_forgets_rules`,
  `virtue_roundTrip_forgets_virtues`).
* Every translation of the library factors through the judgment, so each
  translation into a paradigm identifies distinct sources
  (`library_translations_forget`).
* At a single case, whatever the translation, no paradigm hosts all others
  without loss (`no_lossless_pivot`): there are only finitely many deontic or
  virtue theories and infinitely many utility theories, and a utility theory
  with a permissible verdict has utility zero, while two different rule sets
  are permissible.  Each paradigm hosts itself (`hostsWithoutLoss_self`).

**Views over the choice-point language.**  On the rescue specimen of
`Mettapedia.Ethics.ChoicePointParadigms`, the deontic verdict and the value
verdict are incomparable views of the cases: one deontic verdict carries two
values (`deontic_forgets_value`) and one value carries two deontic verdicts
(`value_forgets_deontic`), so neither is finest (`no_finest_rescue_view`).
They agree on which act is excluded (`excluded_commonCoarsening`); that this is
a property of the specimen and not of the two views is shown by a prohibited
good (`excluded_not_common_in_general`).  Over agents, every type the action
fragment generates gives two different programs the same evaluation, and
agent-centered virtue separates them (`act_level_forgets_possession`): two
policies evaluated alike need not be one.

**Convergence given a common basis of evaluation.**  A learner holds a prior
order on its hypotheses and conjectures, after each labelled case, the first
hypothesis that agrees with every label so far: identification by enumeration
(Gold, "Language identification in the limit", 1967).
* If some hypothesis agrees with the target on the whole stream, the learner's
  conjecture is eventually constant at the first such hypothesis
  (`conjecture_eventually`).
* **The common basis.**  If several learners, in different paradigms, are
  corrected by one target evaluation that each can express, and every case is
  presented, then from some stage on each learner holds one hypothesis, and
  all of these have the target as their evaluation (`common_basis_converges`).
  What converges is the evaluation: two priors in one paradigm reach two
  different hypotheses with one evaluation
  (`rescue_limits_differ_evaluations_agree`).
* **Control without the common basis.**  Learners corrected by different
  targets reach different evaluations and disagree from some stage on forever
  at a case where the targets differ (`without_common_basis_disagree`).
* **Finite stages.**  Before the data decide, learners with different priors
  disagree (`rescue_stage_zero_divergence`).
* The rescue specimen: a utilitarian learner whose prior starts with a
  short-horizon score, a deontic learner whose prior starts with prohibiting
  nothing, and a virtue learner whose prior starts with courage give three
  different verdicts on crossing in an emergency at stage zero, and all three
  converge to the rescue judgment (`rescue_converges`).  Corrected by the
  short-horizon score instead, the utilitarian learner disagrees with the
  virtue learner forever on that act (`rescue_without_common_basis`).
-/

set_option autoImplicit false

namespace Mettapedia.Ethics.ParadigmPluralism

open Filter
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GSLT.ViewPluralism
open Mettapedia.Ethics
open Mettapedia.Ethics.MoralParadigmEquivalence

universe uAgent uSituation uAction

/-! ## Routes through a pivot -/

section Routes

variable {Agent : Type uAgent} {Situation : Type uSituation} {Action : Type uAction}

/-- **Going through any pivot and back keeps the judgment.** -/
theorem roundTrips_exact :
    (∀ source : UtilityTheory Agent Situation Action,
      JudgmentEquivalent source.toDeontic.toUtility.judgment source.judgment ∧
        JudgmentEquivalent source.toTargetVirtue.toUtility.judgment source.judgment) ∧
      (∀ source : DeterminateDeonticTheory Agent Situation Action,
        JudgmentEquivalent source.toUtility.toDeontic.judgment source.judgment ∧
          JudgmentEquivalent source.toTargetVirtue.toDeontic.judgment source.judgment) ∧
      (∀ source : DeterminateTargetVirtueTheory Agent Situation Action,
        JudgmentEquivalent source.toDeontic.toTargetVirtue.judgment source.judgment ∧
          JudgmentEquivalent source.toUtility.toTargetVirtue.judgment source.judgment) :=
  ⟨fun source => ⟨source.toDeontic.toUtility_exact.trans source.toDeontic_exact,
      source.toTargetVirtue.toUtility_exact.trans source.toTargetVirtue_exact⟩,
    fun source => ⟨source.toUtility.toDeontic_exact.trans source.toUtility_exact,
      source.toTargetVirtue.toDeontic_exact.trans source.toTargetVirtue_exact⟩,
    fun source => ⟨source.toDeontic.toTargetVirtue_exact.trans source.toDeontic_exact,
      source.toUtility.toTargetVirtue_exact.trans source.toUtility_exact⟩⟩

end Routes

/-! ### Specimens at a single case -/

/-- Utility seven at the single case. -/
def sevenEverywhere : UtilityTheory Unit Unit Unit := ⟨fun _ _ _ => 7⟩

/-- Utility one at the single case. -/
def oneEverywhere : UtilityTheory Unit Unit Unit := ⟨fun _ _ _ => 1⟩

theorem utilityTheory_ext {first second : UtilityTheory Unit Unit Unit}
    (same : first.utility () () () = second.utility () () ()) : first = second := by
  cases first
  cases second
  congr
  funext agent situation action
  cases agent
  cases situation
  cases action
  exact same

theorem utilityToMoralValue_eq_permissible_iff (value : ℤ) :
    utilityToMoralValue value = .MorallyPermissible ↔ value = 0 := by
  unfold utilityToMoralValue
  split_ifs with positive negative <;> simp <;> omega

/-- The rule set with a single rule: everything is permitted. -/
def permissionOnlyTheory : DeonticTheory Unit Unit Unit where
  rules := {⟨.Permission, fun _ _ _ => True⟩}

theorem permissionOnly_supportsVerdict_iff (verdict : MoralValueAttribute) :
    permissionOnlyTheory.SupportsVerdict () () () verdict ↔ verdict = .MorallyPermissible := by
  constructor
  · rintro ⟨rule, member, -, force⟩
    obtain rfl : rule = ⟨.Permission, fun _ _ _ => True⟩ := member
    exact force.symm
  · rintro rfl
    exact ⟨_, Set.mem_singleton _, trivial, rfl⟩

/-- Permitting everything by one rule, as a determinate theory. -/
def permissionOnly : DeterminateDeonticTheory Unit Unit Unit where
  theory := permissionOnlyTheory
  determinate := fun _ _ _ => ⟨.MorallyPermissible,
    (permissionOnly_supportsVerdict_iff _).mpr rfl,
    fun _ supports => (permissionOnly_supportsVerdict_iff _).mp supports⟩

theorem permissionOnly_judgment : permissionOnly.judgment () () () = .MorallyPermissible :=
  (permissionOnly.supportsVerdict_iff_judgment_eq () () () _).mp
    ((permissionOnly_supportsVerdict_iff _).mpr rfl)

/-- The canonical rule set for the same judgment. -/
def permittedCanonically : DeterminateDeonticTheory Unit Unit Unit :=
  DeterminateDeonticTheory.ofJudgment fun _ _ _ => .MorallyPermissible

theorem permissionOnly_ne_canonical : permissionOnly ≠ permittedCanonically := by
  intro same
  have obligation : DeonticTheory.classifierRule (fun _ _ _ => .MorallyPermissible) .MorallyGood ∈
      permissionOnly.theory.rules := by
    rw [same]
    exact ⟨_, rfl⟩
  have forces := congrArg DeonticRule.force
    (show _ = (⟨.Permission, fun _ _ _ => True⟩ : DeonticRule Unit Unit Unit) from obligation)
  simp [DeonticTheory.classifierRule, moralValueToDeontic] at forces

/-- One virtue, the neutral one, whose target is the act being permissible. -/
def neutralOnlyTheory : TargetVirtueTheory Unit Unit Unit where
  included := {.MorallyPermissible}
  spec := TargetVirtueTheory.classifierVirtue fun _ _ _ => .MorallyPermissible

theorem neutralOnly_supportsVerdict_iff (verdict : MoralValueAttribute) :
    neutralOnlyTheory.SupportsVerdict () () () verdict ↔ verdict = .MorallyPermissible := by
  constructor
  · rintro ⟨virtue, member, -, valence⟩
    obtain rfl : virtue = .MorallyPermissible := member
    exact valence.symm
  · rintro rfl
    exact ⟨.MorallyPermissible, Set.mem_singleton _, ⟨trivial, trivial, rfl⟩, rfl⟩

def neutralOnly : DeterminateTargetVirtueTheory Unit Unit Unit where
  theory := neutralOnlyTheory
  determinate := fun _ _ _ => ⟨.MorallyPermissible,
    (neutralOnly_supportsVerdict_iff _).mpr rfl,
    fun _ supports => (neutralOnly_supportsVerdict_iff _).mp supports⟩

/-- **A round trip loses the magnitude of utilities.** -/
theorem utility_roundTrip_forgets_magnitude : sevenEverywhere.toDeontic.toUtility ≠ sevenEverywhere := by
  intro same
  have value := congrArg (fun theory : UtilityTheory Unit Unit Unit => theory.utility () () ()) same
  have judged := UtilityTheory.toDeontic_exact sevenEverywhere () () ()
  simp only [DeterminateDeonticTheory.toUtility, UtilityTheory.ofJudgment, judged] at value
  simp [sevenEverywhere, UtilityTheory.judgment, utilityToMoralValue, moralValueToUtility] at value

/-- **A round trip replaces a rule set by the canonical one.** -/
theorem deontic_roundTrip_forgets_rules : permissionOnly.toUtility.toDeontic ≠ permissionOnly := by
  intro same
  have canonical : permissionOnly.toUtility.toDeontic = permittedCanonically := by
    change DeterminateDeonticTheory.ofJudgment permissionOnly.toUtility.judgment = _
    congr 1
    funext agent situation action
    cases agent
    cases situation
    cases action
    rw [DeterminateDeonticTheory.toUtility_exact, permissionOnly_judgment]
  exact permissionOnly_ne_canonical (same.symm.trans canonical)

/-- **A round trip replaces a set of virtues by the canonical one.** -/
theorem virtue_roundTrip_forgets_virtues : neutralOnly.toUtility.toTargetVirtue ≠ neutralOnly := by
  intro same
  have included := congrArg (fun theory => theory.theory.included) same
  have good : MoralValueAttribute.MorallyGood ∈ neutralOnly.toUtility.toTargetVirtue.theory.included :=
    Set.mem_univ _
  rw [included] at good
  cases Set.mem_singleton_iff.mp good

/-- **Every library translation into a paradigm identifies distinct sources.** -/
theorem library_translations_forget :
    ¬ Factors (UtilityTheory.toDeontic (Agent := Unit) (Situation := Unit) (Action := Unit)) id ∧
      ¬ Factors (DeterminateDeonticTheory.toUtility (Agent := Unit) (Situation := Unit)
        (Action := Unit)) id ∧
      ¬ Factors (UtilityTheory.toTargetVirtue (Agent := Unit) (Situation := Unit)
        (Action := Unit)) id := by
  have sameJudgment : sevenEverywhere.judgment = oneEverywhere.judgment := by
    funext agent situation action
    simp [sevenEverywhere, oneEverywhere, UtilityTheory.judgment, utilityToMoralValue]
  have distinct : sevenEverywhere ≠ oneEverywhere := fun same => by
    have := congrArg (fun theory : UtilityTheory Unit Unit Unit => theory.utility () () ()) same
    simp [sevenEverywhere, oneEverywhere] at this
  have sameDeontic : permissionOnly.judgment = permittedCanonically.judgment := by
    funext agent situation action
    cases agent
    cases situation
    cases action
    rw [permissionOnly_judgment]
    exact (DeterminateDeonticTheory.ofJudgment_judgmentEquivalent
      (fun _ _ _ => .MorallyPermissible) () () ()).symm
  exact ⟨fun factors => distinct (factors.constantOnFibers _ _
      (congrArg DeterminateDeonticTheory.ofJudgment sameJudgment)),
    fun factors => permissionOnly_ne_canonical (factors.constantOnFibers _ _
      (congrArg UtilityTheory.ofJudgment sameDeontic)),
    fun factors => distinct (factors.constantOnFibers _ _
      (congrArg DeterminateTargetVirtueTheory.ofJudgment sameJudgment))⟩

/-! ### No lossless pivot at a single case -/

/-- The three paradigms. -/
inductive Paradigm
  | deontic
  | utilitarian
  | virtue
  deriving DecidableEq

/-- A paradigm's theories over given agents, situations and actions. -/
abbrev Paradigm.Theory (Agent : Type) (Situation : Type) (Action : Type) : Paradigm → Type
  | .deontic => DeterminateDeonticTheory Agent Situation Action
  | .utilitarian => UtilityTheory Agent Situation Action
  | .virtue => DeterminateTargetVirtueTheory Agent Situation Action

/-- A theory's judgment, in each paradigm. -/
noncomputable def Paradigm.judgment {Agent Situation Action : Type} :
    (paradigm : Paradigm) → paradigm.Theory Agent Situation Action → MoralJudgment Agent Situation Action
  | .deontic => DeterminateDeonticTheory.judgment
  | .utilitarian => UtilityTheory.judgment
  | .virtue => DeterminateTargetVirtueTheory.judgment

/-- `pivot` **hosts `source` without loss** at a single case: some translation
keeps every judgment and lets the source theory be recovered. -/
def HostsWithoutLoss (pivot source : Paradigm) : Prop :=
  ∃ translate : source.Theory Unit Unit Unit → pivot.Theory Unit Unit Unit,
    Factors translate id ∧ ∀ theory, pivot.judgment (translate theory) = source.judgment theory

theorem hostsWithoutLoss_self (paradigm : Paradigm) : HostsWithoutLoss paradigm paradigm :=
  ⟨id, ⟨id, fun _ => rfl⟩, fun _ => rfl⟩

theorem finite_deonticAttribute : Finite DeonticAttribute :=
  Finite.of_injective
    (fun tag : DeonticAttribute => match tag with
      | .Obligation => (0 : Fin 3) | .Prohibition => 1 | .Permission => 2)
    (by intro first second same; cases first <;> cases second <;> first | rfl | cases same)

theorem finite_moralValueAttribute : Finite MoralValueAttribute :=
  Finite.of_injective
    (fun value : MoralValueAttribute => match value with
      | .MorallyGood => (0 : Fin 3) | .MorallyBad => 1 | .MorallyPermissible => 2)
    (by intro first second same; cases first <;> cases second <;> first | rfl | cases same)

theorem finite_characterValence : Finite TargetCenteredVirtue.CharacterValence :=
  Finite.of_injective
    (fun valence : TargetCenteredVirtue.CharacterValence => match valence with
      | .virtue => (0 : Fin 3) | .vice => 1 | .neutral => 2)
    (by intro first second same; cases first <;> cases second <;> first | rfl | cases same)

/-- **There are finitely many deontic theories at a single case.** -/
theorem finite_deontic : Finite (DeterminateDeonticTheory Unit Unit Unit) := by
  have := finite_deonticAttribute
  have : Finite (DeonticRule Unit Unit Unit) :=
    Finite.of_injective (fun rule : DeonticRule Unit Unit Unit => (rule.force, rule.guard))
      (by
        rintro ⟨force, guard⟩ ⟨force', guard'⟩ same
        cases same
        rfl)
  exact Finite.of_injective (fun theory : DeterminateDeonticTheory Unit Unit Unit =>
      theory.theory.rules)
    (by
      rintro ⟨⟨rules⟩, determinate⟩ ⟨⟨rules'⟩, determinate'⟩ same
      cases same
      rfl)

/-- **There are finitely many virtue theories at a single case.** -/
theorem finite_virtue : Finite (DeterminateTargetVirtueTheory Unit Unit Unit) := by
  have := finite_moralValueAttribute
  have := finite_characterValence
  have : Finite (TargetCenteredVirtue.VirtueSpec Unit Unit Unit MoralValueAttribute) :=
    Finite.of_injective
      (fun spec : TargetCenteredVirtue.VirtueSpec Unit Unit Unit MoralValueAttribute =>
        (spec.valence, spec.field, spec.basis, spec.mode, spec.target))
      (by
        rintro ⟨valence, field, basis, nonempty, mode, target⟩
          ⟨valence', field', basis', nonempty', mode', target'⟩ same
        simp only [Prod.mk.injEq] at same
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := same
        rfl)
  exact Finite.of_injective (fun theory : DeterminateTargetVirtueTheory Unit Unit Unit =>
      (theory.theory.included, theory.theory.spec))
    (by
      rintro ⟨⟨included, spec⟩, determinate⟩ ⟨⟨included', spec'⟩, determinate'⟩ same
      simp only [Prod.mk.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      rfl)

/-- **There are infinitely many utility theories at a single case.** -/
theorem infinite_utility : Infinite (UtilityTheory Unit Unit Unit) :=
  Infinite.of_injective (fun value : ℤ => (⟨fun _ _ _ => value⟩ : UtilityTheory Unit Unit Unit))
    (fun first second same => by
      have := congrArg (fun theory : UtilityTheory Unit Unit Unit => theory.utility () () ()) same
      exact this)

theorem injective_of_factors_id {A : Type*} {B : Type*} {translate : A → B}
    (factors : Factors translate id) : Function.Injective translate :=
  fun first second same => factors.constantOnFibers first second same

/-- **At a single case no paradigm is a lossless pivot**: for each paradigm,
some other paradigm has no judgment-preserving translation into it from which
its theories can be recovered. -/
theorem no_lossless_pivot (pivot : Paradigm) : ∃ source, ¬ HostsWithoutLoss pivot source := by
  cases pivot
  · refine ⟨.utilitarian, fun ⟨translate, factors, _⟩ => ?_⟩
    have := finite_deontic
    have := infinite_utility
    exact not_injective_infinite_finite translate (injective_of_factors_id factors)
  · refine ⟨.deontic, fun ⟨translate, factors, keeps⟩ => ?_⟩
    have zero : ∀ theory : DeterminateDeonticTheory Unit Unit Unit,
        theory.judgment () () () = .MorallyPermissible →
          (translate theory).utility () () () = 0 := by
      intro theory permissible
      have judged := congrFun (congrFun (congrFun (keeps theory) ()) ()) ()
      change utilityToMoralValue ((translate theory).utility () () ()) =
        theory.judgment () () () at judged
      rw [permissible] at judged
      exact (utilityToMoralValue_eq_permissible_iff _).mp judged
    have canonicalPermissible : permittedCanonically.judgment () () () = .MorallyPermissible :=
      DeterminateDeonticTheory.ofJudgment_judgmentEquivalent _ () () ()
    apply permissionOnly_ne_canonical
    apply injective_of_factors_id factors
    exact utilityTheory_ext ((zero _ permissionOnly_judgment).trans
      (zero _ canonicalPermissible).symm)
  · refine ⟨.utilitarian, fun ⟨translate, factors, _⟩ => ?_⟩
    have := finite_virtue
    have := infinite_utility
    exact not_injective_infinite_finite translate (injective_of_factors_id factors)

/-! ## Views over the choice-point language -/

section ChoicePoints

open Mettapedia.Ethics.ChoicePointParadigms
open Mettapedia.Languages.ChoicePoints (did scene)
open Turing.ToPartrec

/-- A case of the rescue specimen. -/
abbrev RescueCase := RescueSituation × RescueAction

/-- The deontic verdict on a rescue case, for one agent. -/
noncomputable def deonticView (agent : Code) (case : RescueCase) : DeonticAttribute :=
  deonticVerdict 2 rescueViolation agent (situationIndex case.1) (actionIndex case.2)

/-- The value verdict on a rescue case, for one agent. -/
noncomputable def valueView (agent : Code) (case : RescueCase) : MoralValueAttribute :=
  valueVerdict 2 rescueIdeal rescueViolation agent (situationIndex case.1) (actionIndex case.2)

theorem valueView_eq (agent : Code) (case : RescueCase) :
    valueView agent case = rescueJudgment () case.1 case.2 :=
  rescue_value_verdict agent () case.1 case.2

/-- **One deontic verdict, two values**: crossing and waiting in an emergency
are both permitted, and only crossing is good. -/
def deontic_forgets_value (agent : Code) : NonTrivialFiber (deonticView agent) (valueView agent) where
  left := (.emergency, .cross)
  right := (.emergency, .wait)
  sameShadow := (rescue_deontic_verdict agent).2.2.1.trans (rescue_deontic_verdict agent).2.2.2.symm
  differentValue := by
    rw [valueView_eq, valueView_eq]
    decide

/-- **One value, two deontic verdicts**: waiting is permissible in both
situations, obligatory in the ordinary one and merely permitted in an
emergency. -/
def value_forgets_deontic (agent : Code) : NonTrivialFiber (valueView agent) (deonticView agent) where
  left := (.ordinary, .wait)
  right := (.emergency, .wait)
  sameShadow := by
    rw [valueView_eq, valueView_eq]
    rfl
  differentValue := by
    change deonticVerdict 2 rescueViolation agent 0 0 ≠ deonticVerdict 2 rescueViolation agent 1 0
    rw [(rescue_deontic_verdict agent).2.1, (rescue_deontic_verdict agent).2.2.2]
    decide

/-- The two verdicts as a family of views of the rescue cases. -/
inductive Verdict
  | deontic
  | value
  deriving DecidableEq

abbrev Verdict.Carrier : Verdict → Type
  | .deontic => DeonticAttribute
  | .value => MoralValueAttribute

noncomputable def rescueViews (agent : Code) : (verdict : Verdict) → RescueCase → verdict.Carrier
  | .deontic => deonticView agent
  | .value => valueView agent

/-- **Neither verdict is finest on the rescue cases.** -/
theorem no_finest_rescue_view (agent : Code) (verdict : Verdict) :
    ¬ Finest (rescueViews agent) verdict := by
  cases verdict
  · exact not_finest_of_fiber _ .value (deontic_forgets_value agent)
  · exact not_finest_of_fiber _ .deontic (value_forgets_deontic agent)

/-- The deontic verdicts of the four rescue cases. -/
theorem deonticView_eq (agent : Code) (case : RescueCase) :
    deonticView agent case =
      match case with
      | (.ordinary, .cross) => .Prohibition
      | (.ordinary, .wait) => .Obligation
      | (.emergency, _) => .Permission := by
  obtain ⟨ordinaryCross, ordinaryWait, emergencyCross, emergencyWait⟩ := rescue_deontic_verdict agent
  rcases case with ⟨_ | _, _ | _⟩
  · exact ordinaryWait
  · exact ordinaryCross
  · exact emergencyWait
  · exact emergencyCross

/-- **The two verdicts agree on which act is excluded** in the rescue
specimen: being bad is a common coarsening. -/
theorem excluded_commonCoarsening (agent : Code) :
    CommonCoarsening (rescueViews agent) fun case => valueView agent case = .MorallyBad
  | .deontic => ⟨fun verdict => verdict = .Prohibition, fun case => by
      change (deonticView agent case = _) = (valueView agent case = _)
      rw [deonticView_eq, valueView_eq]
      rcases case with ⟨_ | _, _ | _⟩ <;> simp [rescueJudgment]⟩
  | .value => ⟨fun value => value = .MorallyBad, fun _ => rfl⟩

/-- **The agreement is a property of the specimen**: with an outcome that is
both ideal and a violation, the deontic verdict prohibits an act whose value
is good. -/
theorem excluded_not_common_in_general (agent : Code) :
    deonticVerdict 2 (fun world => world = did 0 0) agent 0 0 = .Prohibition ∧
      valueVerdict 2 (fun world => world = did 0 0) (fun world => world = did 0 0) agent 0 0 =
        .MorallyGood :=
  ⟨(DeonticSemantics.verdict_eq_prohibition_iff _ _ _).mpr (conflict_prohibited_good agent).2,
    (ValueSemantics.verdict_eq_good_iff _ _ _).mpr (conflict_prohibited_good agent).1⟩

/-- What the action fragment lets one observe of an agent: every generated
type at every scene. -/
def actLevel (agent : Code) : ℕ → (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop) → ℕ → Prop :=
  fun actionCount predicate situation => generatedDiamond actionCount predicate (scene agent situation)

/-- **Two agents evaluated alike by every act-level type, separated by
agent-centered virtue.** -/
def act_level_forgets_possession :
    NonTrivialFiber actLevel
      (HostVirtuePossession.HostPossesses VirtuePossessionUndecidability.faithfulReport) :=
  NonTrivialFiber.ofProp (a := Code.id) (b := Code.zero')
    (funext fun actionCount => funext fun predicate => funext fun situation =>
      propext (possession_not_act_level.1 actionCount predicate situation))
    possession_not_act_level.2.1 possession_not_act_level.2.2

end ChoicePoints

/-! ## Convergence given a common basis of evaluation -/

section Enumeration

variable {Case : Type*} {Value : Type*} [DecidableEq Value] {Hypothesis : Type*}

/-- The conjecture of a learner after `stage` labelled cases: the first
hypothesis of its prior that agrees with every label so far. -/
def conjecture (prior : List Hypothesis) (readout : Hypothesis → Case → Value)
    (stream : ℕ → Case) (target : Case → Value) (stage : ℕ) : Option Hypothesis :=
  prior.find? fun hypothesis => decide (∀ k < stage, readout hypothesis (stream k) = target (stream k))

/-- **Identification by enumeration**: if some hypothesis of the prior agrees
with the target on the whole stream, the conjecture is eventually constant at
such a hypothesis. -/
theorem conjecture_eventually (prior : List Hypothesis) (readout : Hypothesis → Case → Value)
    (stream : ℕ → Case) (target : Case → Value)
    (realizable : ∃ hypothesis ∈ prior, ∀ k, readout hypothesis (stream k) = target (stream k)) :
    ∃ limit ∈ prior, (∀ k, readout limit (stream k) = target (stream k)) ∧
      ∀ᶠ stage in atTop, conjecture prior readout stream target stage = some limit := by
  induction prior with
  | nil =>
      obtain ⟨_, member, -⟩ := realizable
      cases member
  | cons first rest ih =>
      by_cases agrees : ∀ k, readout first (stream k) = target (stream k)
      · refine ⟨first, List.mem_cons_self, agrees, Eventually.of_forall fun stage => ?_⟩
        exact List.find?_cons_of_pos (decide_eq_true fun k _ => agrees k)
      · simp only [not_forall] at agrees
        obtain ⟨refuted, differs⟩ := agrees
        obtain ⟨hypothesis, member, hypothesisAgrees⟩ := realizable
        have inRest : hypothesis ∈ rest := by
          rcases List.mem_cons.mp member with same | inRest
          · subst same
            exact absurd (hypothesisAgrees refuted) differs
          · exact inRest
        obtain ⟨limit, limitMember, limitAgrees, eventually⟩ :=
          ih ⟨hypothesis, inRest, hypothesisAgrees⟩
        refine ⟨limit, List.mem_cons_of_mem _ limitMember, limitAgrees, ?_⟩
        filter_upwards [eventually, eventually_gt_atTop refuted] with stage same later
        unfold conjecture at same ⊢
        rw [List.find?_cons_of_neg]
        · exact same
        · simp only [decide_eq_true_eq, not_forall]
          exact ⟨refuted, later, differs⟩

/-- With a stream that presents every case, the limit's evaluation is the
target. -/
theorem conjecture_converges (prior : List Hypothesis) (readout : Hypothesis → Case → Value)
    (stream : ℕ → Case) (covers : ∀ case, ∃ k, stream k = case) (target : Case → Value)
    (realizable : ∃ hypothesis ∈ prior, readout hypothesis = target) :
    ∃ limit ∈ prior, readout limit = target ∧
      ∀ᶠ stage in atTop, conjecture prior readout stream target stage = some limit := by
  obtain ⟨hypothesis, member, same⟩ := realizable
  obtain ⟨limit, limitMember, agrees, eventually⟩ :=
    conjecture_eventually prior readout stream target ⟨hypothesis, member, fun k => by rw [same]⟩
  refine ⟨limit, limitMember, funext fun case => ?_, eventually⟩
  obtain ⟨k, rfl⟩ := covers case
  exact agrees k

/-- **Convergence given a common basis of evaluation.**  Learners in several
paradigms, each with its own hypotheses, readout and prior, corrected by one
target that each can express on a stream presenting every case: from some
stage on every learner holds one hypothesis, and every such hypothesis has the
target as its evaluation. -/
theorem common_basis_converges {ι : Type*} [Finite ι] {Hypothesis : ι → Type*}
    (prior : ∀ i, List (Hypothesis i)) (readout : ∀ i, Hypothesis i → Case → Value)
    (stream : ℕ → Case) (covers : ∀ case, ∃ k, stream k = case) (target : Case → Value)
    (realizable : ∀ i, ∃ hypothesis ∈ prior i, readout i hypothesis = target) :
    ∃ limit : ∀ i, Hypothesis i, (∀ i, limit i ∈ prior i ∧ readout i (limit i) = target) ∧
      ∀ᶠ stage in atTop, ∀ i, conjecture (prior i) (readout i) stream target stage = some (limit i) := by
  choose limit member same eventually using fun i =>
    conjecture_converges (prior i) (readout i) stream covers target (realizable i)
  exact ⟨limit, fun i => ⟨member i, same i⟩, eventually_all.mpr eventually⟩

/-- **Control without the common basis.**  Two learners corrected by targets
that differ at a case presented in the stream disagree on it from some stage
on, forever. -/
theorem without_common_basis_disagree {Hypothesis' : Type*}
    (prior : List Hypothesis) (readout : Hypothesis → Case → Value)
    (prior' : List Hypothesis') (readout' : Hypothesis' → Case → Value)
    (stream : ℕ → Case) (covers : ∀ case, ∃ k, stream k = case)
    (target target' : Case → Value)
    (realizable : ∃ hypothesis ∈ prior, readout hypothesis = target)
    (realizable' : ∃ hypothesis ∈ prior', readout' hypothesis = target')
    {case : Case} (differ : target case ≠ target' case) :
    ∀ᶠ stage in atTop, ∀ hypothesis hypothesis',
      conjecture prior readout stream target stage = some hypothesis →
        conjecture prior' readout' stream target' stage = some hypothesis' →
          readout hypothesis case ≠ readout' hypothesis' case := by
  obtain ⟨limit, -, same, eventually⟩ :=
    conjecture_converges prior readout stream covers target realizable
  obtain ⟨limit', -, same', eventually'⟩ :=
    conjecture_converges prior' readout' stream covers target' realizable'
  filter_upwards [eventually, eventually'] with stage held held' hypothesis hypothesis' first second
  rw [held, Option.some_inj] at first
  rw [held', Option.some_inj] at second
  subst first
  subst second
  rw [same, same']
  exact differ

/-- Before any label, a learner conjectures the head of its prior. -/
theorem conjecture_zero (first : Hypothesis) (rest : List Hypothesis)
    (readout : Hypothesis → Case → Value) (stream : ℕ → Case) (target : Case → Value) :
    conjecture (first :: rest) readout stream target 0 = some first :=
  List.find?_cons_of_pos (decide_eq_true fun _ bound => absurd bound (Nat.not_lt_zero _))

end Enumeration

/-! ### The rescue specimen -/

section Rescue

/-- The rescue judgment, as an evaluation of cases. -/
def rescueTarget (case : RescueCase) : MoralValueAttribute :=
  rescueJudgment () case.1 case.2

/-- Every case of the rescue specimen, in turn. -/
def rescueStream (k : ℕ) : RescueCase :=
  match k % 4 with
  | 0 => (.ordinary, .wait)
  | 1 => (.ordinary, .cross)
  | 2 => (.emergency, .wait)
  | _ => (.emergency, .cross)

theorem rescueStream_covers (case : RescueCase) : ∃ k, rescueStream k = case := by
  rcases case with ⟨_ | _, _ | _⟩
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩

/-- A short-horizon score: crossing costs, waiting costs nothing. -/
def shortHorizon : UtilityTheory Unit RescueSituation RescueAction where
  utility _ _ action := match action with
    | .cross => -1
    | .wait => 0

/-- Utilities that rank crossing in an emergency at seven. -/
def rescueSeven : UtilityTheory Unit RescueSituation RescueAction where
  utility _ situation action := match situation, action with
    | .emergency, .cross => 7
    | .ordinary, .cross => -1
    | _, .wait => 0

/-- The same ranking with crossing in an emergency at one. -/
def rescueOne : UtilityTheory Unit RescueSituation RescueAction :=
  UtilityTheory.ofJudgment rescueJudgment

/-- Courage: crossing is good whatever the situation. -/
def courageJudgment : MoralJudgment Unit RescueSituation RescueAction
  | _, _, .cross => .MorallyGood
  | _, _, .wait => .MorallyPermissible

/-- The utilitarian learner's prior: the short-horizon score first. -/
def utilitarianPrior : List (UtilityTheory Unit RescueSituation RescueAction) :=
  [shortHorizon, rescueSeven]

/-- The deontic learner's prior: prohibiting nothing first. -/
noncomputable def deonticPrior : List (DeterminateDeonticTheory Unit RescueSituation RescueAction) :=
  [DeterminateDeonticTheory.ofJudgment fun _ _ _ => .MorallyPermissible, rescueDeonticTheory]

/-- The virtue learner's prior: courage first. -/
def virtuePrior : List (DeterminateTargetVirtueTheory Unit RescueSituation RescueAction) :=
  [DeterminateTargetVirtueTheory.ofJudgment courageJudgment, rescueVirtueTheory]

/-- The three paradigms' priors over the rescue specimen. -/
noncomputable def rescuePrior :
    (paradigm : Paradigm) → List (paradigm.Theory Unit RescueSituation RescueAction)
  | .deontic => deonticPrior
  | .utilitarian => utilitarianPrior
  | .virtue => virtuePrior

/-- Each paradigm's evaluation of a rescue case. -/
noncomputable def rescueReadout (paradigm : Paradigm)
    (theory : paradigm.Theory Unit RescueSituation RescueAction) (case : RescueCase) :
    MoralValueAttribute :=
  paradigm.judgment theory () case.1 case.2

theorem rescueSeven_readout : rescueReadout .utilitarian rescueSeven = rescueTarget := by
  funext case
  rcases case with ⟨_ | _, _ | _⟩ <;> rfl

theorem rescueOne_readout : rescueReadout .utilitarian rescueOne = rescueTarget :=
  funext fun case => UtilityTheory.ofJudgment_judgmentEquivalent rescueJudgment () case.1 case.2

/-- Each paradigm can express the rescue judgment within its prior. -/
theorem rescue_realizable (paradigm : Paradigm) :
    ∃ theory ∈ rescuePrior paradigm, rescueReadout paradigm theory = rescueTarget := by
  cases paradigm
  · exact ⟨rescueDeonticTheory, by simp [rescuePrior, deonticPrior], funext fun case =>
      DeterminateDeonticTheory.ofJudgment_judgmentEquivalent rescueJudgment () case.1 case.2⟩
  · exact ⟨rescueSeven, by simp [rescuePrior, utilitarianPrior], rescueSeven_readout⟩
  · exact ⟨rescueVirtueTheory, by simp [rescuePrior, virtuePrior], funext fun case =>
      DeterminateTargetVirtueTheory.ofJudgment_judgmentEquivalent rescueJudgment () case.1 case.2⟩

/-- **The three paradigms' learners converge to the rescue judgment.** -/
theorem rescue_converges :
    ∃ limit : ∀ paradigm : Paradigm, paradigm.Theory Unit RescueSituation RescueAction,
      (∀ paradigm, limit paradigm ∈ rescuePrior paradigm ∧
        rescueReadout paradigm (limit paradigm) = rescueTarget) ∧
      ∀ᶠ stage in atTop, ∀ paradigm,
        conjecture (rescuePrior paradigm) (rescueReadout paradigm) rescueStream rescueTarget stage =
          some (limit paradigm) :=
  have : Finite Paradigm :=
    Finite.of_injective (fun paradigm : Paradigm => match paradigm with
      | .deontic => (0 : Fin 3) | .utilitarian => 1 | .virtue => 2)
      (by intro first second same; cases first <;> cases second <;> first | rfl | cases same)
  common_basis_converges rescuePrior rescueReadout rescueStream rescueStream_covers rescueTarget
    rescue_realizable

/-- **At stage zero the three learners give three verdicts on crossing in an
emergency**: bad for the short-horizon score, permissible for prohibiting
nothing, good for courage. -/
theorem rescue_stage_zero_divergence :
    (∃ theory, conjecture (rescuePrior .utilitarian) (rescueReadout .utilitarian) rescueStream
        rescueTarget 0 = some theory ∧
      rescueReadout .utilitarian theory (.emergency, .cross) = .MorallyBad) ∧
    (∃ theory, conjecture (rescuePrior .deontic) (rescueReadout .deontic) rescueStream
        rescueTarget 0 = some theory ∧
      rescueReadout .deontic theory (.emergency, .cross) = .MorallyPermissible) ∧
    (∃ theory, conjecture (rescuePrior .virtue) (rescueReadout .virtue) rescueStream
        rescueTarget 0 = some theory ∧
      rescueReadout .virtue theory (.emergency, .cross) = .MorallyGood) :=
  ⟨⟨_, conjecture_zero _ _ _ _ _, rfl⟩,
    ⟨_, conjecture_zero _ _ _ _ _,
      DeterminateDeonticTheory.ofJudgment_judgmentEquivalent _ () _ _⟩,
    ⟨_, conjecture_zero _ _ _ _ _,
      DeterminateTargetVirtueTheory.ofJudgment_judgmentEquivalent _ () _ _⟩⟩

/-- **Without the common basis**: the utilitarian learner corrected by the
short-horizon score and the virtue learner corrected by the rescue judgment
disagree on crossing in an emergency from some stage on, forever. -/
theorem rescue_without_common_basis :
    ∀ᶠ stage in atTop, ∀ theory theory',
      conjecture (rescuePrior .utilitarian) (rescueReadout .utilitarian) rescueStream
          (rescueReadout .utilitarian shortHorizon) stage = some theory →
        conjecture (rescuePrior .virtue) (rescueReadout .virtue) rescueStream rescueTarget stage =
          some theory' →
          rescueReadout .utilitarian theory (.emergency, .cross) ≠
            rescueReadout .virtue theory' (.emergency, .cross) :=
  without_common_basis_disagree _ _ _ _ rescueStream rescueStream_covers _ _
    ⟨shortHorizon, by simp [rescuePrior, utilitarianPrior], rfl⟩
    (rescue_realizable .virtue) (case := (.emergency, .cross)) (by decide)

/-- **What converges is the evaluation**: two utilitarian priors that list the
same two rankings in opposite orders reach two different theories with one
evaluation. -/
theorem rescue_limits_differ_evaluations_agree :
    rescueSeven ≠ rescueOne ∧
      rescueReadout .utilitarian rescueSeven = rescueReadout .utilitarian rescueOne ∧
      (∀ᶠ stage in atTop, conjecture [rescueSeven, rescueOne] (rescueReadout .utilitarian)
          rescueStream rescueTarget stage = some rescueSeven) ∧
      ∀ᶠ stage in atTop, conjecture [rescueOne, rescueSeven] (rescueReadout .utilitarian)
          rescueStream rescueTarget stage = some rescueOne := by
  refine ⟨fun same => ?_, rescueSeven_readout.trans rescueOne_readout.symm,
    Eventually.of_forall fun stage => List.find?_cons_of_pos (decide_eq_true fun k _ => by
      rw [rescueSeven_readout]),
    Eventually.of_forall fun stage => List.find?_cons_of_pos (decide_eq_true fun k _ => by
      rw [rescueOne_readout])⟩
  have := congrArg (fun theory : UtilityTheory Unit RescueSituation RescueAction =>
    theory.utility () .emergency .cross) same
  simp [rescueSeven, rescueOne, UtilityTheory.ofJudgment, rescueJudgment, moralValueToUtility] at this

end Rescue

/-! ## Axiom audit -/

#print axioms roundTrips_exact
#print axioms utility_roundTrip_forgets_magnitude
#print axioms deontic_roundTrip_forgets_rules
#print axioms virtue_roundTrip_forgets_virtues
#print axioms library_translations_forget
#print axioms no_lossless_pivot
#print axioms no_finest_rescue_view
#print axioms excluded_commonCoarsening
#print axioms excluded_not_common_in_general
#print axioms act_level_forgets_possession
#print axioms conjecture_eventually
#print axioms common_basis_converges
#print axioms without_common_basis_disagree
#print axioms rescue_converges
#print axioms rescue_stage_zero_divergence
#print axioms rescue_without_common_basis
#print axioms rescue_limits_differ_evaluations_agree

end Mettapedia.Ethics.ParadigmPluralism
