import Mettapedia.GSLT.Causality.Abstraction

/-!
# Controls for the causal ladder and for causal abstraction

* **Gauge.**  A low-level process `ready → done` whose interventions change
  nothing, and a high-level copy carrying an unobservable gauge bit that
  interventions flip.  Embedding with the gauge off, and sending each
  intervention to itself, commutes with interventions up to counterfactual
  distance zero (`Gauge.commutes`), so it is a causal abstraction
  (`Gauge.abstraction`) and an isometry of the counterfactual distance
  (`Gauge.isometry`).  The square does not commute up to the equations
  (`Gauge.not_square`), and no functional bisimulation of the saturated
  systems has this term map and these intervention labels
  (`Gauge.no_saturatedMap`).  The functional reading of "commutes with
  interventions" is strictly stronger than the causal one.

* **Graded rungs on the response-type GSLT** (`ResponseGraded`).  With the
  measured quantities read as indicators and a positive discount `δ`, the
  population that would be helped and the inert one are at passive distance
  zero and at interventional distance at least `δ²`
  (`passiveDistance_wouldHelp_inert`, `interventionalDistance_wouldHelp_inert`);
  the mixed and the fixed populations are at interventional distance zero and
  at counterfactual distance at least `δ²` (`interventionalDistance_mixed_fixed`,
  `counterfactualDistance_mixed_fixed`).  The second bound is the value gap of
  the graded form of the necessity-and-sufficiency query.

* **Forgetful.**  Replace each individual's response type by the constant
  type with the same realized outcome under the treatment currently imposed.
  This is a passive map on every term, intervened or not
  (`Forgetful.passiveMap`).  At the mixed population it commutes with every
  intervention up to counterfactual distance zero
  (`Forgetful.commutes_at_mixed`): an exact transformation of that population.
  At a drawn individual it does not (`Forgetful.not_commutes_at_individual`),
  so it is not a causal abstraction (`Forgetful.not_causalAbstraction`).  It
  identifies the mixed and the fixed populations, which the low level
  separates counterfactually (`Forgetful.collapses_mixed_fixed`), and no
  functional bisimulation of the saturated systems, with any vocabulary, has
  this term map (`Forgetful.no_saturatedMap`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.AbstractionControls

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.MinimalEnablingContext
open Mettapedia.GSLT.AdmissibleContextCongruence
open Mettapedia.GSLT.Distinction
open Mettapedia.GSLT.Causality.Hierarchy
open Mettapedia.GSLT.Causality.Abstraction

/-! ## Gauge: a causal abstraction that is not a saturated map -/

namespace Gauge

/-- The two phases of a process. -/
inductive Phase where
  | ready
  | done
  deriving DecidableEq

/-- The low level: a process that finishes. -/
abbrev lowGSLT : GSLT where
  Term := Phase
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites source target := source = .ready ∧ target = .done
  rewrites_resp_left := by
    intro _ _ target equal step
    subst equal
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro _ _ _ step equal
    subst equal
    exact step

/-- The high level: the same process with a gauge bit, kept by the step. -/
abbrev highGSLT : GSLT where
  Term := Bool × Phase
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites source target := source.2 = .ready ∧ target = (source.1, .done)
  rewrites_resp_left := by
    intro _ _ target equal step
    subst equal
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro _ _ _ step equal
    subst equal
    exact step

/-- Low-level interventions: switches that act on nothing. -/
abbrev lowRules : ContextualRules lowGSLT where
  Context := Bool
  identity := false
  compose outer inner := xor outer inner
  plug _ term := term
  plug_identity _ := rfl
  plug_compose _ _ _ := rfl
  plug_resp _ := fun equal => equal
  Rule := Unit
  fires _ := lowGSLT.rewrites
  fires_resp_left := by
    intro _ _ _ target equal fires
    subst equal
    exact ⟨target, fires, rfl⟩
  fires_resp_right := by
    intro _ _ _ _ fires equal
    subst equal
    exact fires
  fires_step := fun fires => fires

/-- High-level interventions: switches that flip the gauge. -/
abbrev highRules : ContextualRules highGSLT where
  Context := Bool
  identity := false
  compose outer inner := xor outer inner
  plug context term := (xor context term.1, term.2)
  plug_identity term := by
    rcases term with ⟨gauge, phase⟩
    cases gauge <;> rfl
  plug_compose outer inner term := by
    rcases term with ⟨gauge, phase⟩
    cases outer <;> cases inner <;> cases gauge <;> rfl
  plug_resp _ := by
    intro _ _ equal
    subst equal
    rfl
  Rule := Unit
  fires _ := highGSLT.rewrites
  fires_resp_left := by
    intro _ _ _ target equal fires
    subst equal
    exact ⟨target, fires, rfl⟩
  fires_resp_right := by
    intro _ _ _ _ fires equal
    subst equal
    exact fires
  fires_step := fun fires => fires

/-- Whether the process is done, as a reading. -/
def lowReadings : GradedObservations lowGSLT where
  Atom := Unit
  value _ phase := if phase = .done then 1 else 0
  value_nonneg _ _ := by split <;> norm_num
  value_le_one _ _ := by split <;> norm_num
  value_resp _ _ _ equal := by rw [show _ = _ from equal]

/-- Whether the process is done, ignoring the gauge. -/
def highReadings : GradedObservations highGSLT where
  Atom := Unit
  value _ term := if term.2 = .done then 1 else 0
  value_nonneg _ _ := by split <;> norm_num
  value_le_one _ _ := by split <;> norm_num
  value_resp _ _ _ equal := by rw [show _ = _ from equal]

variable (discount : ℝ) (discount_nonneg : 0 ≤ discount) (discount_le_one : discount ≤ 1)

/-- Embed with the gauge off. -/
def passiveMap : PassiveMap lowReadings highReadings discount discount_nonneg discount_le_one where
  mapTerm phase := (false, phase)
  mapEquiv := fun equal => by
    change _ = _ at equal
    subst equal
    rfl
  atom := id
  label := id
  discount_eq := rfl
  value_map _ _ := rfl
  mapAct _ _ _ step := ⟨step.1, by rw [step.2]⟩
  liftAct _ _ _ step := ⟨.done, ⟨step.1, rfl⟩, step.2.symm⟩

/-- Send each switch to the same switch. -/
def sameSwitch : InterventionMap (⊤ : AdmissibleClass lowRules) (⊤ : AdmissibleClass highRules) where
  map context := context
  admissible _ := AdmissibleClass.top_admissible _

/-- **The gauge is invisible**: terms with the same phase lie in a graded
bisimulation of the high-level saturated system. -/
theorem samePhase_isGradedBisimulation :
    (saturatedGraded (⊤ : AdmissibleClass highRules) highReadings discount discount_nonneg
      discount_le_one).IsGradedBisimulation fun first second => first.2 = second.2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro first second same label first' step
    change (xor label.1 first.1, first.2).2 = .ready ∧ first' = ((xor label.1 first.1, first.2).1, .done)
      at step
    refine ⟨((xor label.1 second.1, second.2).1, .done), ⟨?_, rfl⟩, ?_⟩
    · change second.2 = .ready
      rw [← same]
      exact step.1
    · rw [step.2]
  · intro first second same label second' step
    change (xor label.1 second.1, second.2).2 = .ready ∧
      second' = ((xor label.1 second.1, second.2).1, .done) at step
    refine ⟨((xor label.1 first.1, first.2).1, .done), ⟨?_, rfl⟩, ?_⟩
    · change first.2 = .ready
      rw [same]
      exact step.1
    · rw [step.2]
  · intro first second same atom
    change (if (xor atom.2.1 first.1, first.2).2 = Phase.done then (1 : ℝ) else 0) =
      if (xor atom.2.1 second.1, second.2).2 = Phase.done then 1 else 0
    simp only [same]

/-- **The square commutes up to counterfactual distance zero.** -/
theorem commutes ⦃context : Bool⦄ (_admissible : (⊤ : AdmissibleClass lowRules).Admissible context)
    (term : Phase) :
    counterfactualDistance (⊤ : AdmissibleClass highRules) highReadings discount discount_nonneg
        discount_le_one ((passiveMap discount discount_nonneg discount_le_one).mapTerm
          (lowRules.plug context term))
        (highRules.plug (sameSwitch.map context)
          ((passiveMap discount discount_nonneg discount_le_one).mapTerm term)) = 0 :=
  GradedSystem.logicalDistance_eq_zero_of_gradedBisimilar _
    ⟨_, samePhase_isGradedBisimulation discount discount_nonneg discount_le_one, rfl⟩

/-- **The gauge embedding is a causal abstraction.** -/
def abstraction :
    CausalAbstraction (⊤ : AdmissibleClass lowRules) (⊤ : AdmissibleClass highRules) lowReadings
      highReadings discount discount_nonneg discount_le_one where
  passiveMap := passiveMap discount discount_nonneg discount_le_one
  intervention := sameSwitch
  commutes := commutes discount discount_nonneg discount_le_one

/-- **It is an isometry of the counterfactual distance.** -/
theorem isometry (left right : Phase) :
    counterfactualDistance (⊤ : AdmissibleClass highRules) highReadings discount discount_nonneg
        discount_le_one (false, left) (false, right) =
      counterfactualDistance (⊤ : AdmissibleClass lowRules) lowReadings discount discount_nonneg
        discount_le_one left right :=
  (abstraction discount discount_nonneg discount_le_one).counterfactualDistance_map
    (fun observation => ⟨observation, rfl⟩)
    (fun label => ⟨⟨label.1, AdmissibleClass.top_admissible _⟩, rfl⟩) left right

/-- **The square does not commute up to the equations.** -/
theorem not_square :
    ¬ ∀ ⦃context : Bool⦄, (⊤ : AdmissibleClass lowRules).Admissible context → ∀ term : Phase,
      highGSLT.Equiv ((passiveMap discount discount_nonneg discount_le_one).mapTerm
          (lowRules.plug context term))
        (highRules.plug (sameSwitch.map context)
          ((passiveMap discount discount_nonneg discount_le_one).mapTerm term)) := by
  intro square
  have equal : ((false, Phase.ready) : Bool × Phase) = (true, .ready) :=
    square (AdmissibleClass.top_admissible (rules := lowRules) true) .ready
  exact Bool.false_ne_true (congrArg Prod.fst equal)

/-- **No functional bisimulation of the saturated systems has the gauge
embedding as its term map and the same switches as its labels.** -/
theorem no_saturatedMap :
    ¬ ∃ map : SaturatedMap (⊤ : AdmissibleClass lowRules) (⊤ : AdmissibleClass highRules)
        lowReadings highReadings discount discount_nonneg discount_le_one,
      (∀ phase, map.mapTerm phase = (false, phase)) ∧ ∀ label, (map.label label).1 = label.1 := by
  rintro ⟨map, mapTerm_eq, label_eq⟩
  let flip : {context : Bool // (⊤ : AdmissibleClass lowRules).Admissible context} :=
    ⟨true, AdmissibleClass.top_admissible _⟩
  have image : highGSLT.Step (highRules.plug (map.label flip).1 (map.mapTerm .ready))
      (map.mapTerm .done) := map.mapAct flip (⟨rfl, rfl⟩ : lowGSLT.Step .ready .done)
  rw [label_eq flip, mapTerm_eq, mapTerm_eq] at image
  exact Bool.false_ne_true (congrArg Prod.fst image.2)

end Gauge

/-! ## Graded rungs on the response-type GSLT -/

namespace ResponseGraded

open Mettapedia.GSLT.Causality.Hierarchy.ResponseTypes

/-- The measured quantities as indicator readings. -/
def reading : Quantity → Stage → ℝ
  | .treatment, .record treated _ => if treated then 1 else 0
  | .effect, .record _ effect => if effect then 1 else 0
  | _, .population _ _ => 0
  | _, .individual _ _ _ => 0

/-- The indicator readings as graded observations. -/
def readings : GradedObservations responseGSLT where
  Atom := Quantity
  value := reading
  value_nonneg quantity stage := by
    cases quantity <;> cases stage <;> simp only [reading] <;> (try split_ifs) <;> norm_num
  value_le_one quantity stage := by
    cases quantity <;> cases stage <;> simp only [reading] <;> (try split_ifs) <;> norm_num
  value_resp _ _ _ equal := by rw [show _ = _ from equal]

variable (discount : ℝ) (discount_nonneg : 0 ≤ discount) (discount_le_one : discount ≤ 1)

/-- The saturated graded system of the response-type GSLT. -/
noncomputable abbrev saturatedSystem :=
  saturatedGraded everyIntervention readings discount discount_nonneg discount_le_one

/-- The effect, read with nothing further imposed. -/
def effectNow : (saturatedSystem discount discount_nonneg discount_le_one).observations.Atom :=
  ((Quantity.effect, ⟨none, AdmissibleClass.top_admissible _⟩) :
    Quantity × {context : Option Bool // everyIntervention.Admissible context})

/-- Impose a treatment, or nothing, as a label. -/
def under (treatment : Option Bool) :
    (saturatedSystem discount discount_nonneg discount_le_one).dynamics.Label :=
  ⟨treatment, AdmissibleClass.top_admissible _⟩

theorem eval_effectNow (treated effect : Bool) :
    (saturatedSystem discount discount_nonneg discount_le_one).eval
        (.atom (effectNow discount discount_nonneg discount_le_one)) (.record treated effect) =
      if effect then 1 else 0 := rfl

/-- **A diamond at a drawn individual** is the discounted value at its record. -/
theorem eval_dia_individual (treatment : Option Bool)
    (inner : (saturatedSystem discount discount_nonneg discount_le_one).Formula)
    (natural : Bool) (response : Response) (imposed : Option Bool) :
    (saturatedSystem discount discount_nonneg discount_le_one).eval
        (.dia (under discount discount_nonneg discount_le_one treatment) inner)
        (.individual natural response imposed) =
      discount * (saturatedSystem discount discount_nonneg discount_le_one).eval inner
        (.record ((treatment.or imposed).getD natural)
          (response.outcome ((treatment.or imposed).getD natural))) := by
  have steps : {target | Moves (.individual natural response (treatment.or imposed)) target} =
      {.record ((treatment.or imposed).getD natural)
        (response.outcome ((treatment.or imposed).getD natural))} := by
    ext target
    constructor
    · intro step
      cases step
      exact Set.mem_singleton _
    · intro member
      rw [Set.mem_singleton_iff.mp member]
      exact Moves.respond
  change discount * sSup ((saturatedSystem discount discount_nonneg discount_le_one).eval inner ''
    {target | Moves (.individual natural response (treatment.or imposed)) target}) = _
  rw [steps, Set.image_singleton, csSup_singleton]

/-- **A diamond at a one-individual population.** -/
theorem eval_dia_single (treatment : Option Bool)
    (inner : (saturatedSystem discount discount_nonneg discount_le_one).Formula)
    (natural : Bool) (response : Response) (imposed : Option Bool) :
    (saturatedSystem discount discount_nonneg discount_le_one).eval
        (.dia (under discount discount_nonneg discount_le_one treatment) inner)
        (.population [(natural, response)] imposed) =
      discount * (saturatedSystem discount discount_nonneg discount_le_one).eval inner
        (.individual natural response (treatment.or imposed)) := by
  have steps : {target | Moves (.population [(natural, response)] (treatment.or imposed)) target} =
      {.individual natural response (treatment.or imposed)} := by
    ext target
    constructor
    · intro step
      cases step with
      | draw member =>
          simp only [List.mem_singleton, Prod.mk.injEq] at member
          obtain ⟨rfl, rfl⟩ := member
          exact Set.mem_singleton _
    · intro member
      rw [Set.mem_singleton_iff.mp member]
      exact Moves.draw (List.mem_singleton.mpr rfl)
  change discount * sSup ((saturatedSystem discount discount_nonneg discount_le_one).eval inner ''
    {target | Moves (.population [(natural, response)] (treatment.or imposed)) target}) = _
  rw [steps, Set.image_singleton, csSup_singleton]

/-- **A diamond at a two-individual population.** -/
theorem eval_dia_pair (treatment : Option Bool)
    (inner : (saturatedSystem discount discount_nonneg discount_le_one).Formula)
    (first second : Bool × Response) (imposed : Option Bool) :
    (saturatedSystem discount discount_nonneg discount_le_one).eval
        (.dia (under discount discount_nonneg discount_le_one treatment) inner)
        (.population [first, second] imposed) =
      discount * max ((saturatedSystem discount discount_nonneg discount_le_one).eval inner
          (.individual first.1 first.2 (treatment.or imposed)))
        ((saturatedSystem discount discount_nonneg discount_le_one).eval inner
          (.individual second.1 second.2 (treatment.or imposed))) := by
  have steps : {target | Moves (.population [first, second] (treatment.or imposed)) target} =
      {.individual first.1 first.2 (treatment.or imposed),
        .individual second.1 second.2 (treatment.or imposed)} := by
    ext target
    constructor
    · intro step
      cases step with
      | @draw _ _ natural response member =>
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact Moves.draw (by simp)
      · exact Moves.draw (by simp)
  change discount * sSup ((saturatedSystem discount discount_nonneg discount_le_one).eval inner ''
    {target | Moves (.population [first, second] (treatment.or imposed)) target}) = _
  rw [steps, Set.image_pair, csSup_pair]

/-! ### Rung one against rung two -/

/-- A graded bisimulation of the passive system, from a reduction bisimulation
that relates only terms with equal readings. -/
theorem passiveDistance_eq_zero_of_isReductionBisimulation {relation : Stage → Stage → Prop}
    (bisimulation : IsReductionBisimulation quantities relation)
    (readings_eq : ∀ ⦃left right⦄, relation left right → ∀ quantity,
      reading quantity left = reading quantity right)
    {left right : Stage} (related : relation left right) :
    passiveDistance readings discount discount_nonneg discount_le_one left right = 0 :=
  GradedSystem.logicalDistance_eq_zero_of_gradedBisimilar _
    ⟨relation, ⟨fun _ _ held _ _ step => bisimulation.1.1 held step,
      fun _ _ held _ _ step => bisimulation.1.2 held step,
      fun _ _ held quantity => readings_eq held quantity⟩, related⟩

/-- **The helped and the inert populations are at passive distance zero.** -/
theorem passiveDistance_wouldHelp_inert :
    passiveDistance readings discount discount_nonneg discount_le_one wouldHelp inert = 0 :=
  passiveDistance_eq_zero_of_isReductionBisimulation discount discount_nonneg discount_le_one
    untreatedMatch_isReductionBisimulation
    (by
      rintro left right (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) quantity
      · rfl
      · cases quantity <;> rfl
      · cases quantity <;> rfl)
    (Or.inr (Or.inl ⟨rfl, rfl⟩))

/-- "After two passive steps the effect shows", in the saturated system. -/
def twoStepsEffect : (saturatedSystem discount discount_nonneg discount_le_one).Formula :=
  .dia (under discount discount_nonneg discount_le_one none)
    (.dia (under discount discount_nonneg discount_le_one none)
      (.atom (effectNow discount discount_nonneg discount_le_one)))

/-- **Treated, the helped and the inert populations are at interventional
distance at least `δ²`.** -/
theorem interventionalDistance_wouldHelp_inert :
    discount * discount ≤
      interventionalDistance everyIntervention readings discount discount_nonneg discount_le_one
        wouldHelp inert := by
  refine le_trans ?_ (passiveDistance_plug_le_interventional everyIntervention readings discount
    discount_nonneg discount_le_one (AdmissibleClass.top_admissible (rules := interventions)
      (some true)) wouldHelp inert)
  let probe : (GradedSystem.stepping responseGSLT readings discount discount_nonneg
      discount_le_one).Formula := .dia () (.dia () (.atom Quantity.effect))
  have translated : (passiveEmbedding everyIntervention readings discount discount_nonneg
      discount_le_one).translate probe = twoStepsEffect discount discount_nonneg discount_le_one :=
    rfl
  have atHelped := (passiveEmbedding everyIntervention readings discount discount_nonneg
    discount_le_one).eval_translate probe (impose (some true) wouldHelp)
  have atInert := (passiveEmbedding everyIntervention readings discount discount_nonneg
    discount_le_one).eval_translate probe (impose (some true) inert)
  rw [translated] at atHelped atInert
  change (saturatedSystem discount discount_nonneg discount_le_one).eval
      (.dia (under discount discount_nonneg discount_le_one none)
        (.dia (under discount discount_nonneg discount_le_one none)
          (.atom (effectNow discount discount_nonneg discount_le_one))))
      (.population [(false, .helped)] (some true)) = _ at atHelped
  change (saturatedSystem discount discount_nonneg discount_le_one).eval
      (.dia (under discount discount_nonneg discount_le_one none)
        (.dia (under discount discount_nonneg discount_le_one none)
          (.atom (effectNow discount discount_nonneg discount_le_one))))
      (.population [(false, .never)] (some true)) = _ at atInert
  rw [eval_dia_single, eval_dia_individual] at atHelped atInert
  change discount * (discount * 1) = _ at atHelped
  change discount * (discount * 0) = _ at atInert
  have bound := GradedSystem.abs_eval_sub_le_logicalDistance
    (GradedSystem.stepping responseGSLT readings discount discount_nonneg discount_le_one) probe
    (impose (some true) wouldHelp) (impose (some true) inert)
  rw [← atHelped, ← atInert, mul_one, mul_zero, mul_zero, sub_zero,
    abs_of_nonneg (mul_nonneg discount_nonneg discount_nonneg)] at bound
  exact bound

/-! ### Rung two against rung three -/

/-- **The mixed and the fixed populations are at interventional distance
zero.** -/
theorem interventionalDistance_mixed_fixed :
    interventionalDistance everyIntervention readings discount discount_nonneg discount_le_one
      mixed fixed = 0 :=
  (interventionalDistance_eq_zero_iff everyIntervention readings discount discount_nonneg
    discount_le_one mixed fixed).mpr fun context _ =>
      passiveDistance_eq_zero_of_isReductionBisimulation discount discount_nonneg discount_le_one
        experimentMatch_isReductionBisimulation
        (by
          rintro left right (rfl | ⟨imposed, rfl, rfl⟩ | ⟨imposed, response, response', rfl, rfl, -⟩)
            quantity
          · rfl
          · cases quantity <;> rfl
          · cases quantity <;> rfl)
        (Or.inr (Or.inl ⟨context.or none, rfl, rfl⟩))

/-- The graded form of "some drawn individual would show the effect if
treated and would not if untreated". -/
def necessaryAndSufficientGraded :
    (saturatedSystem discount discount_nonneg discount_le_one).Formula :=
  .dia (under discount discount_nonneg discount_le_one none)
    (.conj
      (.dia (under discount discount_nonneg discount_le_one (some true))
        (.atom (effectNow discount discount_nonneg discount_le_one)))
      (.dia (under discount discount_nonneg discount_le_one (some false))
        (.neg (.atom (effectNow discount discount_nonneg discount_le_one)))))

theorem eval_necessaryAndSufficientGraded_mixed :
    (saturatedSystem discount discount_nonneg discount_le_one).eval
        (necessaryAndSufficientGraded discount discount_nonneg discount_le_one) mixed =
      discount * discount := by
  rw [necessaryAndSufficientGraded, eval_dia_pair]
  simp only [GradedSystem.eval_conj, GradedSystem.eval_neg, eval_dia_individual]
  change discount * max (min (discount * 1) (discount * (1 - 0)))
    (min (discount * 0) (discount * (1 - 1))) = discount * discount
  rw [mul_one, sub_zero, mul_one, mul_zero, sub_self, mul_zero, min_self, min_self,
    max_eq_left discount_nonneg]

theorem eval_necessaryAndSufficientGraded_fixed :
    (saturatedSystem discount discount_nonneg discount_le_one).eval
        (necessaryAndSufficientGraded discount discount_nonneg discount_le_one) fixed = 0 := by
  rw [necessaryAndSufficientGraded, eval_dia_pair]
  simp only [GradedSystem.eval_conj, GradedSystem.eval_neg, eval_dia_individual]
  change discount * max (min (discount * 1) (discount * (1 - 1)))
    (min (discount * 0) (discount * (1 - 0))) = 0
  simp only [mul_one, sub_self, mul_zero, sub_zero]
  rw [min_eq_right discount_nonneg, min_eq_left discount_nonneg, max_self, mul_zero]

/-- **Across treatment regimes on one drawn individual, the mixed and the
fixed populations are at counterfactual distance at least `δ²`.** -/
theorem counterfactualDistance_mixed_fixed :
    discount * discount ≤
      counterfactualDistance everyIntervention readings discount discount_nonneg discount_le_one
        mixed fixed := by
  have bound := GradedSystem.abs_eval_sub_le_logicalDistance
    (saturatedSystem discount discount_nonneg discount_le_one)
    (necessaryAndSufficientGraded discount discount_nonneg discount_le_one) mixed fixed
  rw [eval_necessaryAndSufficientGraded_mixed, eval_necessaryAndSufficientGraded_fixed, sub_zero,
    abs_of_nonneg (mul_nonneg discount_nonneg discount_nonneg)] at bound
  exact bound

end ResponseGraded

/-! ## Forgetful: exact on a population, not a causal abstraction -/

namespace Forgetful

open Mettapedia.GSLT.Causality.Hierarchy.ResponseTypes
open ResponseGraded

/-- Settle an individual's response type to the constant type with the same
realized outcome under the treatment imposed. -/
def settle (imposed : Option Bool) (individual : Bool × Response) : Bool × Response :=
  (individual.1, fixedCounterpart (imposed.getD individual.1) individual.2)

/-- **Forget response types**, keeping realized outcomes. -/
def forget : Stage → Stage
  | .population individuals imposed => .population (individuals.map (settle imposed)) imposed
  | .individual natural response imposed =>
      .individual natural (fixedCounterpart (imposed.getD natural) response) imposed
  | .record treated effect => .record treated effect

variable (discount : ℝ) (discount_nonneg : 0 ≤ discount) (discount_le_one : discount ≤ 1)

/-- **Forgetting is a passive map on every term**, intervened or not. -/
def passiveMap : PassiveMap readings readings discount discount_nonneg discount_le_one where
  mapTerm := forget
  mapEquiv := fun equal => by
    change _ = _ at equal
    subst equal
    rfl
  atom := id
  label := id
  discount_eq := rfl
  value_map quantity stage := by cases stage <;> cases quantity <;> rfl
  mapAct _ _ _ step := by
    cases moves_of_step step with
    | @draw individuals imposed natural response member =>
        exact Moves.draw (List.mem_map.mpr ⟨(natural, response), member, rfl⟩)
    | @respond natural response imposed =>
        have responds := Moves.respond (natural := natural)
          (response := fixedCounterpart (imposed.getD natural) response) (imposed := imposed)
        rw [fixedCounterpart_outcome] at responds
        exact responds
  liftAct _ source _ step := by
    cases source with
    | population individuals imposed =>
        cases moves_of_step step with
        | draw member =>
            obtain ⟨⟨natural, response⟩, member', settled⟩ := List.mem_map.mp member
            simp only [settle, Prod.mk.injEq] at settled
            obtain ⟨rfl, rfl⟩ := settled
            exact ⟨.individual natural response imposed, Moves.draw member', rfl⟩
    | individual natural response imposed =>
        cases moves_of_step step
        refine ⟨_, Moves.respond, ?_⟩
        change Stage.record _ _ = Stage.record _ _
        rw [fixedCounterpart_outcome]
    | record treated effect => cases moves_of_step step

/-- **Forgetting is exact at rung one**: an isometry of the passive distance. -/
theorem passive_isometry (left right : Stage) :
    passiveDistance readings discount discount_nonneg discount_le_one (forget left) (forget right) =
      passiveDistance readings discount discount_nonneg discount_le_one left right :=
  (passiveMap discount discount_nonneg discount_le_one).logicalDistance_map
    (fun quantity => ⟨quantity, rfl⟩) (fun label => ⟨label, rfl⟩) left right

/-- Populations equal up to order are at counterfactual distance zero. -/
theorem population_perm_zero {first second : List (Bool × Response)} (perm : first.Perm second)
    (imposed : Option Bool) :
    counterfactualDistance everyIntervention readings discount discount_nonneg discount_le_one
      (.population first imposed) (.population second imposed) = 0 := by
  let related : Stage → Stage → Prop := fun left right => left = right ∨
    ∃ (individuals individuals' : List (Bool × Response)) (setting : Option Bool),
      individuals.Perm individuals' ∧ left = .population individuals setting ∧
        right = .population individuals' setting
  have bisimulation :
      (saturatedSystem discount discount_nonneg discount_le_one).IsGradedBisimulation related := by
    refine ⟨?_, ?_, ?_⟩
    · rintro left right (rfl | ⟨individuals, individuals', setting, perm', rfl, rfl⟩) label left'
        step
      · exact ⟨left', step, Or.inl rfl⟩
      · change Moves (.population individuals (label.1.or setting)) left' at step
        cases step with
        | draw member =>
            exact ⟨_, (Moves.draw (perm'.mem_iff.mp member) :
              Moves (.population individuals' (label.1.or setting)) _), Or.inl rfl⟩
    · rintro left right (rfl | ⟨individuals, individuals', setting, perm', rfl, rfl⟩) label right'
        step
      · exact ⟨right', step, Or.inl rfl⟩
      · change Moves (.population individuals' (label.1.or setting)) right' at step
        cases step with
        | draw member =>
            exact ⟨_, (Moves.draw (perm'.mem_iff.mpr member) :
              Moves (.population individuals (label.1.or setting)) _), Or.inl rfl⟩
    · rintro left right (rfl | ⟨individuals, individuals', setting, perm', rfl, rfl⟩) atom
      · rfl
      · obtain ⟨quantity, label⟩ := atom
        cases quantity <;> rfl
  exact GradedSystem.logicalDistance_eq_zero_of_gradedBisimilar _
    ⟨related, bisimulation, Or.inr ⟨first, second, imposed, perm, rfl, rfl⟩⟩

/-- **At the mixed population forgetting commutes with every intervention**, up
to counterfactual distance zero: an exact transformation of that population. -/
theorem commutes_at_mixed (context : Option Bool) :
    counterfactualDistance everyIntervention readings discount discount_nonneg discount_le_one
      (forget (impose context mixed)) (impose context (forget mixed)) = 0 := by
  cases context with
  | none => exact population_perm_zero discount discount_nonneg discount_le_one (List.Perm.refl _) none
  | some treated =>
      cases treated
      · exact population_perm_zero discount discount_nonneg discount_le_one (by decide) (some false)
      · exact population_perm_zero discount discount_nonneg discount_le_one (by decide) (some true)

/-- An individual helped by treatment, untreated. -/
abbrev helpedIndividual : Stage := .individual false .helped none

/-- **At a drawn individual forgetting does not commute with treating.** -/
theorem not_commutes_at_individual (positive : 0 < discount) :
    counterfactualDistance everyIntervention readings discount discount_nonneg discount_le_one
      (forget (impose (some true) helpedIndividual))
      (impose (some true) (forget helpedIndividual)) ≠ 0 := by
  intro zero
  have same := eval_eq_of_logicalDistance_eq_zero
    (saturatedSystem discount discount_nonneg discount_le_one) zero
    (.dia (under discount discount_nonneg discount_le_one none)
      (.atom (effectNow discount discount_nonneg discount_le_one)))
  change (saturatedSystem discount discount_nonneg discount_le_one).eval
      (.dia (under discount discount_nonneg discount_le_one none)
        (.atom (effectNow discount discount_nonneg discount_le_one)))
      (.individual false .always (some true)) =
    (saturatedSystem discount discount_nonneg discount_le_one).eval
      (.dia (under discount discount_nonneg discount_le_one none)
        (.atom (effectNow discount discount_nonneg discount_le_one)))
      (.individual false .never (some true)) at same
  rw [eval_dia_individual, eval_dia_individual] at same
  change discount * 1 = discount * 0 at same
  linarith

/-- **Forgetting is not a causal abstraction** with interventions sent to
themselves. -/
theorem not_causalAbstraction (positive : 0 < discount) :
    ¬ ∃ abstraction : CausalAbstraction everyIntervention everyIntervention readings readings
        discount discount_nonneg discount_le_one,
      (∀ stage, abstraction.passiveMap.mapTerm stage = forget stage) ∧
        ∀ context, abstraction.intervention.map context = context := by
  rintro ⟨abstraction, mapTerm_eq, map_eq⟩
  have square := abstraction.commutes
    (AdmissibleClass.top_admissible (rules := interventions) (some true)) helpedIndividual
  rw [mapTerm_eq, mapTerm_eq, map_eq] at square
  exact not_commutes_at_individual discount discount_nonneg discount_le_one positive square

/-- **Forgetting identifies the mixed and the fixed populations.** -/
theorem collapses_mixed_fixed :
    counterfactualDistance everyIntervention readings discount discount_nonneg discount_le_one
      (forget mixed) (forget fixed) = 0 :=
  population_perm_zero discount discount_nonneg discount_le_one (by decide) none

/-- **No functional bisimulation of the saturated systems, with any vocabulary,
has forgetting as its term map**: it would keep the counterfactual distance of
the mixed and the fixed populations, which forgetting collapses. -/
theorem no_saturatedMap (positive : 0 < discount) :
    ¬ ∃ map : SaturatedMap everyIntervention everyIntervention readings readings discount
        discount_nonneg discount_le_one,
      ∀ stage, map.mapTerm stage = forget stage := by
  rintro ⟨map, mapTerm_eq⟩
  have bound := map.logicalDistance_le_map mixed fixed
  rw [mapTerm_eq, mapTerm_eq] at bound
  have collapsed := collapses_mixed_fixed discount discount_nonneg discount_le_one
  have separated := counterfactualDistance_mixed_fixed discount discount_nonneg discount_le_one
  unfold counterfactualDistance at collapsed separated
  nlinarith [mul_pos positive positive]

end Forgetful

end Mettapedia.GSLT.Causality.AbstractionControls
