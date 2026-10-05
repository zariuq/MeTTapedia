import Mettapedia.GSLT.Distinction.GradedCongruence
import Mettapedia.GSLT.Distinction.Isometry

/-!
# Pearl's ladder over a GSLT: association, intervention, counterfactual

A causal model here is a term of a GSLT whose interventions are the contexts of
an admissible class (`AdmissibleClass`), observed through a set of base
observations.  The three rungs of Pearl's ladder are three equivalences that
the library already has, read causally.

* **Association** (`Agree _ _ .association`): reduction bisimilarity with the
  base observations.  No intervention is made; the model is only watched.
* **Intervention** (`Agree _ _ .intervention`): the contextual equivalence.
  An intervention is applied once, before any step, and the intervened model
  is then watched.  This is one regime per question, as in the interventional
  distributions `P(y | do(x))`.
* **Counterfactual** (`Agree _ _ .counterfactual`): the saturated relative
  equivalence.  An intervention may be applied to any state the run has
  reached, and the state is retained, so two different interventions can be
  tried on the same drawn individual.  This is the joint across regimes of
  one unit, as in `P(y_x, y'_x')`.

**The ladder.**  Higher rungs refine lower ones (`agree_of_le`), and each rung
is an equivalence (`agree_equivalence`).  Rung two is the largest relation
inside rung one that every intervention preserves (`intervention_largest`);
rung three is the coarsest reduction bisimulation that every intervention
preserves (`counterfactual_iff_exists`).

**The ladder of languages.**  A formula of the unintervened (passive) system
read after an intervention (`underIntervention`) is a formula of the saturated
system in which an intervention other than the identity occurs only at the
root (`sat_underIntervention`).  Rung one is agreement on passive formulas,
rung two on formulas "intervene once, then watch", and rung three on all
saturated formulas, where different interventions may sit in different
conjuncts beneath one step (`agree_association_iff`, `agree_intervention_iff`,
`agree_counterfactual_iff`, under finite branching).  This mirrors the
symbolic languages of Bareinboim, Correa, Ibeling and Icard (*On Pearl's
Hierarchy and the Foundations of Causal Inference*, Definition 8): one
subscript per term at layer two, mixed subscripts at layer three.

**Strictness, on one GSLT** (`ResponseTypes`).  Individuals carry a natural
treatment and one of the four response types of a binary outcome to a binary
treatment; a population first draws an individual, who then responds to the
treatment imposed so far.
* A population that would be helped by treatment and an inert one agree at
  rung one and are separated by treating (`ladder_strict`).  The query "the
  effect shows under treatment" is not a passive query
  (`treatedShowsEffect_not_passive`), and rung one is not preserved by
  interventions (`association_not_closedUnder`).
* A population half helped and half hurt and a population half always and
  half never showing the effect agree at rung two and are separated at rung
  three.  The separating formula (`necessaryAndSufficient`) says that some
  drawn individual would show the effect if treated and would not if
  untreated: the probability of necessity and sufficiency is positive.  It is
  not a rung-two query (`necessaryAndSufficient_not_interventional`).

The abstract precedent for rungs two and three is the frozen-release control
(`SaturatedControls.FrozenRelease`); the example here is the causal one.

**Comparison with the causal hierarchy theorem.**  Bareinboim et al. call a
layer collapsed at a model when agreement at the lower layer with that model
forces agreement at the higher one (Definition 10), and prove that collapse
has measure zero (Theorem 1).  The separations here are the existential form
on one GSLT, together with the inexpressibility of the two queries; the
genericity form is a statement about a class of GSLTs and is not claimed.

**Graded ladder.**  With graded base observations the three rungs are the zero
kernels of three distances, ordered pointwise
(`passiveDistance_le_interventional`, `interventional_le_counterfactual`):
the passive logical distance, its supremum over the admissible interventions,
and the saturated logical distance.  The identity is an observation-preserving
functional bisimulation from the passive to the saturated system
(`passiveEmbedding`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.Hierarchy

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.MinimalEnablingContext
open Mettapedia.GSLT.AdmissibleContextCongruence
open Mettapedia.GSLT.Distinction

universe uS uContext uRule uAtom uObs

/-! ## The rungs -/

/-- The three rungs of the ladder. -/
inductive Rung where
  | association
  | intervention
  | counterfactual
  deriving DecidableEq

namespace Rung

/-- The height of a rung. -/
def height : Rung → ℕ
  | association => 0
  | intervention => 1
  | counterfactual => 2

instance : LE Rung := ⟨fun lower upper => lower.height ≤ upper.height⟩

end Rung

section Ladder

variable {S : GSLT.{uS}} {rules : ContextualRules.{uContext, uRule} S}
  (A : AdmissibleClass rules) (observations : ContextualRules.Observations.{uAtom} S)

/-- **Agreement of two models at a rung.**  Association is reduction
bisimilarity with the base observations; intervention is the contextual
equivalence (one intervention, before any step); counterfactual is the
saturated relative equivalence (an intervention at any reached state). -/
def Agree : Rung → S.Term → S.Term → Prop
  | .association => ReductionBisimilar observations
  | .intervention => A.ContextualEquiv observations
  | .counterfactual => A.RelEquiv observations

theorem agree_intervention_of_counterfactual {left right : S.Term}
    (agree : Agree A observations .counterfactual left right) :
    Agree A observations .intervention left right :=
  A.contextualEquiv_of_relEquiv observations agree

theorem agree_association_of_intervention {left right : S.Term}
    (agree : Agree A observations .intervention left right) :
    Agree A observations .association left right :=
  A.reductionBisimilar_of_contextualEquiv observations agree

/-- **Higher rungs refine lower ones.** -/
theorem agree_of_le {lower upper : Rung} (le : lower ≤ upper) {left right : S.Term}
    (agree : Agree A observations upper left right) : Agree A observations lower left right := by
  have heights : lower.height ≤ upper.height := le
  cases lower <;> cases upper
  · exact agree
  · exact agree_association_of_intervention A observations agree
  · exact agree_association_of_intervention A observations
      (agree_intervention_of_counterfactual A observations agree)
  · exact absurd heights (by decide)
  · exact agree
  · exact agree_intervention_of_counterfactual A observations agree
  · exact absurd heights (by decide)
  · exact absurd heights (by decide)
  · exact agree

/-- Each rung is an equivalence. -/
theorem agree_equivalence : ∀ rung : Rung, Equivalence (Agree A observations rung)
  | .association =>
      ⟨fun term => reductionBisimilar_of_equiv observations (S.equations.iseqv.refl term),
        fun related => reductionBisimilar_symm observations related,
        fun first second => reductionBisimilar_trans observations first second⟩
  | .intervention =>
      ⟨fun _ _ _ => reductionBisimilar_of_equiv observations (S.equations.iseqv.refl _),
        fun related _ admissible => reductionBisimilar_symm observations (related admissible),
        fun first second _ admissible =>
          reductionBisimilar_trans observations (first admissible) (second admissible)⟩
  | .counterfactual => A.relEquiv_equivalence observations

/-- Rung two is preserved by every intervention. -/
theorem intervention_closedUnder : A.ClosedUnder (Agree A observations .intervention) :=
  A.contextualEquiv_closedUnder observations

/-- Rung three is preserved by every intervention. -/
theorem counterfactual_closedUnder : A.ClosedUnder (Agree A observations .counterfactual) :=
  A.relEquiv_closedUnder observations

/-- **Rung two is the largest relation inside rung one that every intervention
preserves.** -/
theorem intervention_largest {relation : S.Term → S.Term → Prop}
    (closed : A.ClosedUnder relation)
    (contained : ∀ ⦃left right⦄, relation left right → Agree A observations .association left right)
    {left right : S.Term} (related : relation left right) :
    Agree A observations .intervention left right :=
  A.contextualEquiv_largest observations closed contained related

/-- **Rung three is the coarsest reduction bisimulation that every intervention
preserves.** -/
theorem counterfactual_iff_exists {left right : S.Term} :
    Agree A observations .counterfactual left right ↔
      ∃ relation, IsReductionBisimulation observations relation ∧ A.ClosedUnder relation ∧
        relation left right :=
  A.relEquiv_iff_exists observations

/-! ## The ladder of languages -/

/-- **The passive system**: the unintervened steps of the GSLT, one label, with
the base observations. -/
def passive : System.{uAtom, 0} S :=
  System.ofObserved ⟨observations.Atom, observations.observes⟩ observations.observes_resp

theorem passive_bisimilar_iff (left right : S.Term) :
    (passive observations).Bisimilar left right ↔ Agree A observations .association left right :=
  System.ofObserved_bisimilar_iff _ _ left right

/-- **A passive formula read after an intervention**, as a formula of the
saturated system: atoms are read through the intervention and the first steps
are taken in it; beneath the first step the intervention is the identity. -/
def underIntervention :
    {context : rules.Context // A.Admissible context} →
      Formula (passive observations).Atom (passive observations).Label →
        Formula (A.saturated observations).Atom (A.saturated observations).Label
  | _, .top => .top
  | context, .atom atom => .atom (atom, context)
  | context, .conj left right =>
      .conj (underIntervention context left) (underIntervention context right)
  | context, .neg inner => .neg (underIntervention context inner)
  | context, .dia _ inner =>
      .dia context (underIntervention ⟨rules.identity, A.identity_mem⟩ inner)

/-- The formula read after an intervention holds at a model exactly when the
passive formula holds at the intervened model. -/
theorem sat_underIntervention :
    ∀ (formula : Formula (passive observations).Atom (passive observations).Label)
      (context : {context : rules.Context // A.Admissible context}) (term : S.Term),
      (A.saturated observations).sat (underIntervention A observations context formula) term ↔
        (passive observations).sat formula (rules.plug context.1 term)
  | .top, _, _ => Iff.rfl
  | .atom _, _, _ => Iff.rfl
  | .conj left right, context, term =>
      and_congr (sat_underIntervention left context term) (sat_underIntervention right context term)
  | .neg inner, context, term => not_congr (sat_underIntervention inner context term)
  | .dia _ inner, context, term => by
      constructor
      · rintro ⟨target, step, holds⟩
        exact ⟨target, step, ((passive observations).sat_resp inner
          (rules.plug_identity target)).mp ((sat_underIntervention inner _ target).mp holds)⟩
      · rintro ⟨target, step, holds⟩
        exact ⟨target, step, (sat_underIntervention inner _ target).mpr
          (((passive observations).sat_resp inner (rules.plug_identity target)).mpr holds)⟩

/-- Models agreeing at rung one satisfy the same passive formulas. -/
theorem passive_sat_iff_of_agree {left right : S.Term}
    (agree : Agree A observations .association left right)
    (formula : Formula (passive observations).Atom (passive observations).Label) :
    (passive observations).sat formula left ↔ (passive observations).sat formula right :=
  (passive observations).logicallyEquivalent_of_bisimilar
    ((passive_bisimilar_iff A observations left right).mpr agree) formula

/-- Models agreeing at rung two satisfy the same formulas "intervene once, then
watch". -/
theorem sat_underIntervention_iff_of_agree {left right : S.Term}
    (agree : Agree A observations .intervention left right)
    (context : {context : rules.Context // A.Admissible context})
    (formula : Formula (passive observations).Atom (passive observations).Label) :
    (A.saturated observations).sat (underIntervention A observations context formula) left ↔
      (A.saturated observations).sat (underIntervention A observations context formula) right := by
  rw [sat_underIntervention, sat_underIntervention]
  exact passive_sat_iff_of_agree A observations (agree context.2) formula

/-- **Rung one is agreement on passive formulas**, under finite branching. -/
theorem agree_association_iff (finite : (passive observations).ImageFiniteModulo)
    (left right : S.Term) :
    Agree A observations .association left right ↔
      (passive observations).LogicallyEquivalent left right :=
  (passive_bisimilar_iff A observations left right).symm.trans
    ((passive observations).logicallyEquivalent_iff_bisimilar finite left right).symm

/-- **Rung two is agreement on the formulas "intervene once, then watch"**,
under finite branching of the passive system. -/
theorem agree_intervention_iff (finite : (passive observations).ImageFiniteModulo)
    (left right : S.Term) :
    Agree A observations .intervention left right ↔
      ∀ (context : {context : rules.Context // A.Admissible context})
        (formula : Formula (passive observations).Atom (passive observations).Label),
        ((A.saturated observations).sat (underIntervention A observations context formula) left ↔
          (A.saturated observations).sat (underIntervention A observations context formula)
            right) := by
  constructor
  · exact fun agree => sat_underIntervention_iff_of_agree A observations agree
  · intro formulas context admissible
    apply (passive_bisimilar_iff A observations _ _).mp
    apply (passive observations).bisimilar_of_logicallyEquivalent finite
    intro formula
    have same := formulas ⟨context, admissible⟩ formula
    rwa [sat_underIntervention, sat_underIntervention] at same

/-- **Rung three is agreement on all saturated formulas**, under finite
branching of the saturated system. -/
theorem agree_counterfactual_iff (finite : (A.saturated observations).ImageFiniteModulo)
    (left right : S.Term) :
    Agree A observations .counterfactual left right ↔
      (A.saturated observations).LogicallyEquivalent left right :=
  ((A.saturated observations).logicallyEquivalent_iff_bisimilar finite left right).symm

end Ladder

/-! ## The graded ladder -/

section Graded

variable {S : GSLT.{uS}} {rules : ContextualRules.{uContext, uRule} S}
  (A : AdmissibleClass rules) (base : GradedObservations.{uS, uObs} S) (discount : ℝ)
  (discount_nonneg : 0 ≤ discount) (discount_le_one : discount ≤ 1)

/-- The passive distance: the logical distance of the unintervened steps. -/
noncomputable def passiveDistance (left right : S.Term) : ℝ :=
  (GradedSystem.stepping S base discount discount_nonneg discount_le_one).logicalDistance left right

/-- The interventional distance: the largest passive distance after one
admissible intervention. -/
noncomputable def interventionalDistance (left right : S.Term) : ℝ :=
  ⨆ context : {context : rules.Context // A.Admissible context},
    passiveDistance base discount discount_nonneg discount_le_one
      (rules.plug context.1 left) (rules.plug context.1 right)

/-- The counterfactual distance: the logical distance of the saturated system. -/
noncomputable def counterfactualDistance (left right : S.Term) : ℝ :=
  (saturatedGraded A base discount discount_nonneg discount_le_one).logicalDistance left right

/-- A step under the identity intervention is a step. -/
theorem step_plug_identity_iff {term target : S.Term} :
    S.Step (rules.plug rules.identity term) target ↔ S.Step term target := by
  constructor
  · intro step
    obtain ⟨target', step', equivalent⟩ := S.rewrites_resp_left (rules.plug_identity term) step
    exact S.rewrites_resp_right step' (S.equations.iseqv.symm equivalent)
  · intro step
    obtain ⟨target', step', equivalent⟩ :=
      S.rewrites_resp_left (S.equations.iseqv.symm (rules.plug_identity term)) step
    exact S.rewrites_resp_right step' (S.equations.iseqv.symm equivalent)

/-- **The identity embeds the passive system into the saturated one**: it is an
observation-preserving functional bisimulation, reading each observation and
taking each step under the identity intervention. -/
def passiveEmbedding :
    ObservationBisimulation (GradedSystem.stepping S base discount discount_nonneg discount_le_one)
      (saturatedGraded A base discount discount_nonneg discount_le_one) where
  mapTerm := id
  mapEquiv := fun equivalent => equivalent
  atom observation := (observation, ⟨rules.identity, A.identity_mem⟩)
  label _ := ⟨rules.identity, A.identity_mem⟩
  discount_eq := rfl
  value_map observation term := base.value_resp observation (rules.plug_identity term)
  mapAct _ _ _ step := step_plug_identity_iff.mpr step
  liftAct _ _ target step := ⟨target, step_plug_identity_iff.mp step, S.equations.iseqv.refl _⟩

theorem passiveDistance_le_counterfactual (left right : S.Term) :
    passiveDistance base discount discount_nonneg discount_le_one left right ≤
      counterfactualDistance A base discount discount_nonneg discount_le_one left right :=
  (passiveEmbedding A base discount discount_nonneg discount_le_one).logicalDistance_le_map left right

theorem passiveDistance_nonneg (left right : S.Term) :
    0 ≤ passiveDistance base discount discount_nonneg discount_le_one left right :=
  GradedSystem.logicalDistance_nonneg _ left right

theorem bddAbove_interventional (left right : S.Term) :
    BddAbove (Set.range fun context : {context : rules.Context // A.Admissible context} =>
      passiveDistance base discount discount_nonneg discount_le_one
        (rules.plug context.1 left) (rules.plug context.1 right)) :=
  ⟨1, by
    rintro _ ⟨context, rfl⟩
    exact GradedSystem.logicalDistance_le_one _ _ _⟩

/-- Each intervened passive distance is below the interventional distance. -/
theorem passiveDistance_plug_le_interventional {context : rules.Context}
    (admissible : A.Admissible context) (left right : S.Term) :
    passiveDistance base discount discount_nonneg discount_le_one
        (rules.plug context left) (rules.plug context right) ≤
      interventionalDistance A base discount discount_nonneg discount_le_one left right :=
  le_ciSup (bddAbove_interventional A base discount discount_nonneg discount_le_one left right)
    ⟨context, admissible⟩

/-- **The passive distance is below the interventional one.** -/
theorem passiveDistance_le_interventional (left right : S.Term) :
    passiveDistance base discount discount_nonneg discount_le_one left right ≤
      interventionalDistance A base discount discount_nonneg discount_le_one left right := by
  have bound := passiveDistance_plug_le_interventional A base discount discount_nonneg
    discount_le_one A.identity_mem left right
  unfold passiveDistance at bound ⊢
  rwa [GradedSystem.logicalDistance_resp_left _ (rules.plug_identity left),
    GradedSystem.logicalDistance_resp_right _ _ (rules.plug_identity right)] at bound

/-- **The interventional distance is below the counterfactual one.** -/
theorem interventional_le_counterfactual (left right : S.Term) :
    interventionalDistance A base discount discount_nonneg discount_le_one left right ≤
      counterfactualDistance A base discount discount_nonneg discount_le_one left right := by
  have : Nonempty {context : rules.Context // A.Admissible context} :=
    ⟨⟨rules.identity, A.identity_mem⟩⟩
  refine ciSup_le fun context => ?_
  exact (passiveDistance_le_counterfactual A base discount discount_nonneg discount_le_one _ _).trans
    (saturatedGraded_logicalDistance_plug_le A context.2 left right)

/-- **The zero kernel of the interventional distance**: every admissible
intervention leaves the models at passive distance zero. -/
theorem interventionalDistance_eq_zero_iff (left right : S.Term) :
    interventionalDistance A base discount discount_nonneg discount_le_one left right = 0 ↔
      ∀ ⦃context : rules.Context⦄, A.Admissible context →
        passiveDistance base discount discount_nonneg discount_le_one
          (rules.plug context left) (rules.plug context right) = 0 := by
  have : Nonempty {context : rules.Context // A.Admissible context} :=
    ⟨⟨rules.identity, A.identity_mem⟩⟩
  constructor
  · intro zero context admissible
    exact le_antisymm ((passiveDistance_plug_le_interventional A base discount discount_nonneg
      discount_le_one admissible left right).trans_eq zero) (passiveDistance_nonneg _ _ _ _ _ _)
  · intro each
    refine le_antisymm (ciSup_le fun context => (each context.2).le) ?_
    exact (passiveDistance_nonneg _ _ _ _ _ _).trans
      (passiveDistance_le_interventional A base discount discount_nonneg discount_le_one left right)

end Graded

/-! ## Strictness: response types -/

namespace ResponseTypes

/-- The four ways a binary outcome can respond to a binary treatment. -/
inductive Response where
  | never
  | helped
  | hurt
  | always
  deriving DecidableEq

/-- The outcome of a response type under a treatment. -/
def Response.outcome : Response → Bool → Bool
  | .never, _ => false
  | .helped, treated => treated
  | .hurt, treated => !treated
  | .always, _ => true

/-- A stage of an experiment on a population. -/
inductive Stage where
  /-- A population before an individual is drawn: each individual's natural
  treatment and response type, and the treatment imposed so far. -/
  | population (individuals : List (Bool × Response)) (imposed : Option Bool)
  /-- A drawn individual: natural treatment, response type, imposed treatment. -/
  | individual (natural : Bool) (response : Response) (imposed : Option Bool)
  /-- The record of a finished individual: treatment received, outcome. -/
  | record (treated effect : Bool)
  deriving DecidableEq

/-- An experiment draws an individual, who then responds to the treatment
imposed, or to its natural treatment if none was imposed. -/
inductive Moves : Stage → Stage → Prop where
  | draw {individuals : List (Bool × Response)} {imposed : Option Bool} {natural : Bool}
      {response : Response} :
      (natural, response) ∈ individuals →
        Moves (.population individuals imposed) (.individual natural response imposed)
  | respond {natural : Bool} {response : Response} {imposed : Option Bool} :
      Moves (.individual natural response imposed)
        (.record (imposed.getD natural) (response.outcome (imposed.getD natural)))

/-- **The response-type GSLT.** -/
abbrev responseGSLT : GSLT where
  Term := Stage
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := Moves
  rewrites_resp_left := by
    intro source source' target equal step
    subst equal
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst equal
    exact step

/-- Impose a treatment, or nothing.  A later imposition overrides an earlier
one; a record is past, and imposing on it changes nothing. -/
def impose (treatment : Option Bool) : Stage → Stage
  | .population individuals imposed => .population individuals (treatment.or imposed)
  | .individual natural response imposed => .individual natural response (treatment.or imposed)
  | .record treated effect => .record treated effect

/-- **Interventions**: impose a treatment, or nothing. -/
abbrev interventions : ContextualRules responseGSLT where
  Context := Option Bool
  identity := none
  compose outer inner := outer.or inner
  plug := impose
  plug_identity term := by cases term <;> rfl
  plug_compose outer inner term := by cases outer <;> cases term <;> rfl
  plug_resp _ := by
    intro left right equal
    subst equal
    rfl
  Rule := Unit
  fires _ := Moves
  fires_resp_left := by
    intro _ left right target equal fires
    subst equal
    exact ⟨target, fires, rfl⟩
  fires_resp_right := by
    intro _ source target target' fires equal
    subst equal
    exact fires
  fires_step := fun fires => fires

/-- Every intervention is admissible. -/
abbrev everyIntervention : AdmissibleClass interventions := ⊤

/-- The two measured quantities. -/
inductive Quantity where
  | treatment
  | effect
  deriving DecidableEq

/-- A record shows its treatment and its effect; nothing else shows anything. -/
def shows : Quantity → Stage → Prop
  | .treatment, .record treated _ => treated = true
  | .effect, .record _ effect => effect = true
  | _, .population _ _ => False
  | _, .individual _ _ _ => False

/-- The measured quantities as observations. -/
abbrev quantities : ContextualRules.Observations responseGSLT where
  Atom := Quantity
  observes := shows
  observes_resp := by
    intro _ left right equal
    subst equal
    exact Iff.rfl

theorem moves_of_step {source target : Stage} (step : responseGSLT.Step source target) :
    Moves source target := step

/-! ### Rung one is strictly coarser than rung two -/

/-- Treatment would help, but nobody is treated. -/
abbrev wouldHelp : Stage := .population [(false, .helped)] none

/-- Treatment does nothing. -/
abbrev inert : Stage := .population [(false, .never)] none

/-- The pairs identified when nothing is imposed. -/
def untreatedMatch (left right : Stage) : Prop :=
  left = right ∨ (left = wouldHelp ∧ right = inert) ∨
    (left = .individual false .helped none ∧ right = .individual false .never none)

theorem untreatedMatch_isReductionBisimulation :
    IsReductionBisimulation quantities untreatedMatch := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro left right (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) left' step
    · exact ⟨left', step, Or.inl rfl⟩
    · cases moves_of_step step with
      | draw member =>
          simp only [List.mem_singleton, Prod.mk.injEq] at member
          obtain ⟨rfl, rfl⟩ := member
          exact ⟨_, Moves.draw (List.mem_singleton.mpr rfl), Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
    · cases moves_of_step step
      exact ⟨_, Moves.respond, Or.inl rfl⟩
  · rintro left right (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) right' step
    · exact ⟨right', step, Or.inl rfl⟩
    · cases moves_of_step step with
      | draw member =>
          simp only [List.mem_singleton, Prod.mk.injEq] at member
          obtain ⟨rfl, rfl⟩ := member
          exact ⟨_, Moves.draw (List.mem_singleton.mpr rfl), Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
    · cases moves_of_step step
      exact ⟨_, Moves.respond, Or.inl rfl⟩
  · rintro left right (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) atom
    · exact Iff.rfl
    · cases atom <;> exact Iff.rfl
    · cases atom <;> exact Iff.rfl

/-- **Untreated, the two populations look alike.** -/
theorem association_wouldHelp_inert :
    Agree everyIntervention quantities .association wouldHelp inert :=
  ⟨untreatedMatch, untreatedMatch_isReductionBisimulation, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩

/-- **Treated, they do not.** -/
theorem not_passive_treated :
    ¬ ReductionBisimilar quantities (impose (some true) wouldHelp) (impose (some true) inert) := by
  rintro ⟨relation, ⟨⟨forward, _⟩, atoms⟩, related⟩
  obtain ⟨drawn, drawStep, drawnRelated⟩ := forward related
    (Moves.draw (List.mem_singleton.mpr rfl) :
      Moves (.population [(false, .helped)] (some true)) (.individual false .helped (some true)))
  cases moves_of_step drawStep with
  | draw member =>
      simp only [List.mem_singleton, Prod.mk.injEq] at member
      obtain ⟨rfl, rfl⟩ := member
      obtain ⟨final, finalStep, finalRelated⟩ := forward drawnRelated
        (Moves.respond : Moves (.individual false .helped (some true))
          (.record true true))
      cases moves_of_step finalStep
      have shown : false = true := (atoms finalRelated .effect).mp rfl
      exact Bool.false_ne_true shown

theorem not_intervention_wouldHelp_inert :
    ¬ Agree everyIntervention quantities .intervention wouldHelp inert := by
  intro agree
  have contextual : everyIntervention.ContextualEquiv quantities wouldHelp inert := agree
  exact not_passive_treated
    (contextual (AdmissibleClass.top_admissible (rules := interventions) (some true)))

/-- **Rung one is not preserved by interventions.** -/
theorem association_not_closedUnder :
    ¬ everyIntervention.ClosedUnder (Agree everyIntervention quantities .association) := by
  intro closed
  exact not_passive_treated
    (closed (AdmissibleClass.top_admissible (rules := interventions) (some true))
      association_wouldHelp_inert)

/-- "Treat, then after two steps the effect shows." -/
def treatedShowsEffect :
    Formula (everyIntervention.saturated quantities).Atom
      (everyIntervention.saturated quantities).Label :=
  underIntervention everyIntervention quantities ⟨some true, AdmissibleClass.top_admissible _⟩
    (.dia () (.dia () (.atom Quantity.effect)))

theorem wouldHelp_sat_treatedShowsEffect :
    (everyIntervention.saturated quantities).sat treatedShowsEffect wouldHelp := by
  rw [treatedShowsEffect, sat_underIntervention]
  exact ⟨.individual false .helped (some true), Moves.draw (List.mem_singleton.mpr rfl),
    .record true true, Moves.respond, rfl⟩

theorem inert_not_sat_treatedShowsEffect :
    ¬ (everyIntervention.saturated quantities).sat treatedShowsEffect inert := by
  rw [treatedShowsEffect, sat_underIntervention]
  rintro ⟨drawn, drawStep, final, finalStep, shown⟩
  cases moves_of_step drawStep with
  | draw member =>
      simp only [List.mem_singleton, Prod.mk.injEq] at member
      obtain ⟨rfl, rfl⟩ := member
      cases moves_of_step finalStep
      exact Bool.false_ne_true shown

/-- **The effect of treatment is not a passive query**: no passive formula
agrees with it at every model. -/
theorem treatedShowsEffect_not_passive :
    ¬ ∃ formula : Formula (passive quantities).Atom (passive quantities).Label,
        ∀ term, (passive quantities).sat formula term ↔
          (everyIntervention.saturated quantities).sat treatedShowsEffect term := by
  rintro ⟨formula, same⟩
  apply inert_not_sat_treatedShowsEffect
  apply (same inert).mp
  apply (passive_sat_iff_of_agree everyIntervention quantities association_wouldHelp_inert
    formula).mp
  exact (same wouldHelp).mpr wouldHelp_sat_treatedShowsEffect

/-! ### Rung two is strictly coarser than rung three -/

/-- Half helped and half hurt by treatment, nobody treated. -/
abbrev mixedIndividuals : List (Bool × Response) := [(false, .helped), (false, .hurt)]

/-- Half always and half never showing the effect, nobody treated. -/
abbrev fixedIndividuals : List (Bool × Response) := [(false, .always), (false, .never)]

abbrev mixed : Stage := .population mixedIndividuals none

abbrev fixed : Stage := .population fixedIndividuals none

/-- The fixed response type with the same outcome under a treatment. -/
def fixedCounterpart (treated : Bool) (response : Response) : Response :=
  if response.outcome treated then .always else .never

/-- The mixed response type with the same outcome under a treatment. -/
def mixedCounterpart (treated : Bool) (response : Response) : Response :=
  if response.outcome treated = treated then .helped else .hurt

theorem fixedCounterpart_outcome (treated : Bool) (response : Response) :
    (fixedCounterpart treated response).outcome treated = response.outcome treated := by
  cases response <;> cases treated <;> rfl

theorem mixedCounterpart_outcome (treated : Bool) (response : Response) :
    (mixedCounterpart treated response).outcome treated = response.outcome treated := by
  cases response <;> cases treated <;> rfl

theorem fixedCounterpart_mem (treated : Bool) (response : Response) :
    (false, fixedCounterpart treated response) ∈ fixedIndividuals := by
  unfold fixedCounterpart
  split <;> simp

theorem mixedCounterpart_mem (treated : Bool) (response : Response) :
    (false, mixedCounterpart treated response) ∈ mixedIndividuals := by
  unfold mixedCounterpart
  split <;> simp

/-- The pairs identified when one treatment is imposed before the draw. -/
def experimentMatch (left right : Stage) : Prop :=
  left = right ∨
    (∃ imposed, left = .population mixedIndividuals imposed ∧
      right = .population fixedIndividuals imposed) ∨
    (∃ imposed response response', left = .individual false response imposed ∧
      right = .individual false response' imposed ∧
      response.outcome (imposed.getD false) = response'.outcome (imposed.getD false))

theorem experimentMatch_isReductionBisimulation :
    IsReductionBisimulation quantities experimentMatch := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro left right (rfl | ⟨imposed, rfl, rfl⟩ | ⟨imposed, response, response', rfl, rfl, same⟩)
      left' step
    · exact ⟨left', step, Or.inl rfl⟩
    · cases moves_of_step step with
      | @draw _ _ natural response member =>
          have natural_false : natural = false := by
            simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
            rcases member with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rfl
          subst natural_false
          exact ⟨_, Moves.draw (fixedCounterpart_mem (imposed.getD false) response),
            Or.inr (Or.inr ⟨imposed, response, _, rfl, rfl,
              (fixedCounterpart_outcome _ _).symm⟩)⟩
    · cases moves_of_step step
      refine ⟨_, Moves.respond, Or.inl ?_⟩
      rw [same]
  · rintro left right (rfl | ⟨imposed, rfl, rfl⟩ | ⟨imposed, response, response', rfl, rfl, same⟩)
      right' step
    · exact ⟨right', step, Or.inl rfl⟩
    · cases moves_of_step step with
      | @draw _ _ natural response' member =>
          have natural_false : natural = false := by
            simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
            rcases member with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rfl
          subst natural_false
          exact ⟨_, Moves.draw (mixedCounterpart_mem (imposed.getD false) response'),
            Or.inr (Or.inr ⟨imposed, _, response', rfl, rfl, mixedCounterpart_outcome _ _⟩)⟩
    · cases moves_of_step step
      refine ⟨_, Moves.respond, Or.inl ?_⟩
      rw [same]
  · rintro left right (rfl | ⟨imposed, rfl, rfl⟩ | ⟨imposed, response, response', rfl, rfl, -⟩)
      atom
    · exact Iff.rfl
    · cases atom <;> exact Iff.rfl
    · cases atom <;> exact Iff.rfl

/-- **Under every single treatment regime, the two populations look alike.** -/
theorem intervention_mixed_fixed :
    Agree everyIntervention quantities .intervention mixed fixed := by
  intro context _
  exact ⟨experimentMatch, experimentMatch_isReductionBisimulation,
    Or.inr (Or.inl ⟨context.or none, rfl, rfl⟩)⟩

/-- Read the effect, with nothing further imposed. -/
def effectShown : (everyIntervention.saturated quantities).Atom :=
  (.effect, ⟨none, AdmissibleClass.top_admissible _⟩)

/-- Impose a treatment. -/
def treat (treatment : Bool) : (everyIntervention.saturated quantities).Label :=
  ⟨some treatment, AdmissibleClass.top_admissible _⟩

/-- Take a step with nothing imposed. -/
def proceed : (everyIntervention.saturated quantities).Label :=
  ⟨none, AdmissibleClass.top_admissible _⟩

/-- **Some drawn individual would show the effect if treated, and would not
show it if untreated**: the probability of necessity and sufficiency is
positive.  Two different interventions sit beneath one step. -/
def necessaryAndSufficient :
    Formula (everyIntervention.saturated quantities).Atom
      (everyIntervention.saturated quantities).Label :=
  .dia proceed
    (.conj (.dia (treat true) (.atom effectShown))
      (.dia (treat false) (.neg (.atom effectShown))))

theorem mixed_sat_necessaryAndSufficient :
    (everyIntervention.saturated quantities).sat necessaryAndSufficient mixed :=
  ⟨.individual false .helped none, Moves.draw (by simp),
    ⟨.record true true, Moves.respond, rfl⟩,
    ⟨.record false false, Moves.respond, Bool.false_ne_true⟩⟩

theorem fixed_not_sat_necessaryAndSufficient :
    ¬ (everyIntervention.saturated quantities).sat necessaryAndSufficient fixed := by
  rintro ⟨drawn, drawStep, ⟨treated, treatedStep, treatedShows⟩,
    ⟨untreated, untreatedStep, untreatedHides⟩⟩
  cases moves_of_step drawStep with
  | draw member =>
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
      rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · cases moves_of_step untreatedStep
        exact untreatedHides rfl
      · cases moves_of_step treatedStep
        exact Bool.false_ne_true treatedShows

/-- **Across treatment regimes on one drawn individual, they differ.** -/
theorem not_counterfactual_mixed_fixed :
    ¬ Agree everyIntervention quantities .counterfactual mixed fixed := by
  intro agree
  have same := (everyIntervention.saturated quantities).logicallyEquivalent_of_bisimilar agree
    necessaryAndSufficient
  exact fixed_not_sat_necessaryAndSufficient (same.mp mixed_sat_necessaryAndSufficient)

/-- **The probability of necessity and sufficiency is not a rung-two query**:
no formula "intervene once, then watch" agrees with it at every model. -/
theorem necessaryAndSufficient_not_interventional :
    ¬ ∃ (context : {context : interventions.Context // everyIntervention.Admissible context})
        (formula : Formula (passive quantities).Atom (passive quantities).Label),
        ∀ term, (everyIntervention.saturated quantities).sat
            (underIntervention everyIntervention quantities context formula) term ↔
          (everyIntervention.saturated quantities).sat necessaryAndSufficient term := by
  rintro ⟨context, formula, same⟩
  apply fixed_not_sat_necessaryAndSufficient
  apply (same fixed).mp
  apply (sat_underIntervention_iff_of_agree everyIntervention quantities intervention_mixed_fixed
    context formula).mp
  exact (same mixed).mpr mixed_sat_necessaryAndSufficient

/-! ### Monotonicity does not identify the query on this ladder -/

/-- No individual is hurt by treatment. -/
def Monotone (individuals : List (Bool × Response)) : Prop :=
  ∀ individual ∈ individuals, individual.2 ≠ .hurt

/-- Helped, always and never, nobody treated. -/
abbrev monotoneIndividuals : List (Bool × Response) :=
  [(false, .helped), (false, .always), (false, .never)]

/-- Pairs of stages of two populations whose individuals realize the same
outcomes under each treatment. -/
def sameRealizations (individuals individuals' : List (Bool × Response))
    (left right : Stage) : Prop :=
  left = right ∨
    (∃ imposed, left = .population individuals imposed ∧
      right = .population individuals' imposed) ∨
    (∃ imposed response response', left = .individual false response imposed ∧
      right = .individual false response' imposed ∧
      response.outcome (imposed.getD false) = response'.outcome (imposed.getD false))

/-- **Populations of naturally untreated individuals whose realized outcomes
agree under each treatment agree at rung two.** -/
theorem sameRealizations_isReductionBisimulation {individuals individuals' : List (Bool × Response)}
    (untreated : ∀ individual ∈ individuals, individual.1 = false)
    (untreated' : ∀ individual ∈ individuals', individual.1 = false)
    (forth : ∀ treated : Bool, ∀ individual ∈ individuals,
      ∃ individual' ∈ individuals', individual'.2.outcome treated = individual.2.outcome treated)
    (back : ∀ treated : Bool, ∀ individual' ∈ individuals',
      ∃ individual ∈ individuals, individual.2.outcome treated = individual'.2.outcome treated) :
    IsReductionBisimulation quantities (sameRealizations individuals individuals') := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro left right (rfl | ⟨imposed, rfl, rfl⟩ | ⟨imposed, response, response', rfl, rfl, same⟩)
      left' step
    · exact ⟨left', step, Or.inl rfl⟩
    · cases moves_of_step step with
      | @draw _ _ natural response member =>
          have natural_false : natural = false := untreated _ member
          subst natural_false
          obtain ⟨⟨natural', response'⟩, member', outcome⟩ :=
            forth (imposed.getD false) _ member
          have natural'_false : natural' = false := untreated' _ member'
          subst natural'_false
          exact ⟨_, Moves.draw member',
            Or.inr (Or.inr ⟨imposed, response, response', rfl, rfl, outcome.symm⟩)⟩
    · cases moves_of_step step
      refine ⟨_, Moves.respond, Or.inl ?_⟩
      rw [same]
  · rintro left right (rfl | ⟨imposed, rfl, rfl⟩ | ⟨imposed, response, response', rfl, rfl, same⟩)
      right' step
    · exact ⟨right', step, Or.inl rfl⟩
    · cases moves_of_step step with
      | @draw _ _ natural response' member' =>
          have natural_false : natural = false := untreated' _ member'
          subst natural_false
          obtain ⟨⟨natural, response⟩, member, outcome⟩ :=
            back (imposed.getD false) _ member'
          have natural_false : natural = false := untreated _ member
          subst natural_false
          exact ⟨_, Moves.draw member,
            Or.inr (Or.inr ⟨imposed, response, response', rfl, rfl, outcome⟩)⟩
    · cases moves_of_step step
      refine ⟨_, Moves.respond, Or.inl ?_⟩
      rw [same]
  · rintro left right (rfl | ⟨imposed, rfl, rfl⟩ | ⟨imposed, response, response', rfl, rfl, -⟩)
      atom
    · exact Iff.rfl
    · cases atom <;> exact Iff.rfl
    · cases atom <;> exact Iff.rfl

theorem intervention_monotone_fixed :
    Agree everyIntervention quantities .intervention (.population monotoneIndividuals none) fixed := by
  intro context _
  exact ⟨sameRealizations monotoneIndividuals fixedIndividuals,
    sameRealizations_isReductionBisimulation (by decide) (by decide) (by decide) (by decide),
    Or.inr (Or.inl ⟨context.or none, rfl, rfl⟩)⟩

theorem monotone_sat_necessaryAndSufficient :
    (everyIntervention.saturated quantities).sat necessaryAndSufficient
      (.population monotoneIndividuals none) :=
  ⟨.individual false .helped none, Moves.draw (by simp),
    ⟨.record true true, Moves.respond, rfl⟩,
    ⟨.record false false, Moves.respond, Bool.false_ne_true⟩⟩

/-- **Monotonicity does not identify the query at rung two here.**  Two
populations with no individual hurt by treatment agree at rung two and differ
on whether some individual would show the effect exactly when treated.  The
ladder's observers are possibilistic: they see which outcomes are possible in
each regime, not how often, and the classical identification under
monotonicity subtracts frequencies. -/
theorem monotonicity_not_identifying :
    Monotone monotoneIndividuals ∧ Monotone fixedIndividuals ∧
      Agree everyIntervention quantities .intervention (.population monotoneIndividuals none) fixed ∧
      (everyIntervention.saturated quantities).sat necessaryAndSufficient
        (.population monotoneIndividuals none) ∧
      ¬ (everyIntervention.saturated quantities).sat necessaryAndSufficient fixed :=
  ⟨by unfold Monotone; decide, by unfold Monotone; decide, intervention_monotone_fixed,
    monotone_sat_necessaryAndSufficient,
    fixed_not_sat_necessaryAndSufficient⟩

/-! ### The ladder is strict -/

/-- **The ladder is strict on the response-type GSLT.** -/
theorem ladder_strict :
    (Agree everyIntervention quantities .association wouldHelp inert ∧
        ¬ Agree everyIntervention quantities .intervention wouldHelp inert) ∧
      (Agree everyIntervention quantities .intervention mixed fixed ∧
        ¬ Agree everyIntervention quantities .counterfactual mixed fixed) :=
  ⟨⟨association_wouldHelp_inert, not_intervention_wouldHelp_inert⟩,
    ⟨intervention_mixed_fixed, not_counterfactual_mixed_fixed⟩⟩

end ResponseTypes

end Mettapedia.GSLT.Causality.Hierarchy
