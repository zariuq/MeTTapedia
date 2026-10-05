import Mettapedia.GSLT.Causality.Hierarchy
import Mettapedia.GSLT.Distinction.SpanTransport

/-!
# Causal abstraction: observation-preserving maps congruent with interventions

A low-level and a high-level causal model are GSLTs with admissible classes of
interventions and graded base observations (`Causality.Hierarchy`).  A map
between them has two parts:

* a **passive map** (`PassiveMap`): an observation-preserving functional
  bisimulation of the unintervened systems (`ObservationBisimulation`), with a
  translation `τ` of the observations;
* an **intervention map** (`InterventionMap`): each admissible low-level
  intervention goes to an admissible high-level one.

The question is what "the map commutes with interventions" should mean.  There
are three candidate squares, from strongest to weakest.

* **Commuting up to the high-level equations** (`saturate`).  Then the map is
  an observation-preserving functional bisimulation of the two saturated
  systems: every intervened step lands exactly on the image of the low-level
  target.
* **Commuting up to zero high-level counterfactual distance**
  (`CausalAbstraction`).  This is the definition adopted here.  Under it every
  saturated formula transports (`CausalAbstraction.eval_translate`), so the map
  never loses a counterfactual distinction
  (`CausalAbstraction.counterfactualDistance_le`), and with surjective
  translations it is an isometry of the counterfactual distance
  (`CausalAbstraction.counterfactualDistance_map`).  The square, for one
  intervention, is exactly the congruence of the relation "map, then
  counterfactual equivalence" for that intervention and its image
  (`commutes_iff_congruent`, through `SpanTransport.Congruent`).
* **No square at all**: a passive map only.  It is exact at rung one and
  nothing more.

The first implies the second (`CausalAbstraction.ofSquare`), and a functional
bisimulation of the saturated systems whose vocabulary is `τ × ω`, with `ω`
compatible with composition and both translations surjective, also gives the
second (`commutes_of_saturatedMap`).  So the answer to "is causal abstraction
an observation-preserving map congruent with contexts" is: yes, when
congruence is taken relationally, modulo the high-level counterfactual
equivalence; the functional reading is strictly stronger and the passive one
strictly weaker.  The controls exhibit both gaps.

* `Gauge`: an unobservable high-level gauge that interventions flip.  The
  square holds up to counterfactual distance zero, so this is a causal
  abstraction and an isometry, but no functional bisimulation of the saturated
  systems with that intervention map exists, and the square fails up to the
  equations.
* `Forgetful`, on the response-type GSLT: replace each individual's response
  type by the constant type with the same realized outcome.  This is a passive
  map on every term, intervened or not, and at the mixed population it commutes
  with every intervention up to counterfactual distance zero (an exact
  transformation in the sense of Rubenstein et al., *Causal Consistency of
  Structural Equation Models*, Definition 3).  At a drawn individual it does
  not commute, and it collapses individuals the low level separates; so no
  functional bisimulation of the saturated systems has this term map.  This is
  the gap Beckers and Halpern (*Abstracting Causal Models*, Definition 3.5 and
  Theorem 3.8) close by asking for compatibility at every exogenous setting.

**Reading.**  An exact transformation commutes with interventions on the
distribution of the population; a uniform transformation in the sense of
Beckers and Halpern commutes at every unit.  Over a GSLT the units are the
retained states of a run, and the square is required at every one of them.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.Abstraction

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.MinimalEnablingContext
open Mettapedia.GSLT.AdmissibleContextCongruence
open Mettapedia.GSLT.Distinction
open Mettapedia.GSLT.Causality.Hierarchy

universe uS uT uC uR uC' uR' uO uO' uA uL uV

/-! ## Intervention maps, passive maps, saturated maps -/

/-- **A translation of interventions**: each admissible low-level intervention
goes to an admissible high-level one. -/
structure InterventionMap {S : GSLT.{uS}} {T : GSLT.{uT}}
    {rulesS : ContextualRules.{uC, uR} S} {rulesT : ContextualRules.{uC', uR'} T}
    (A : AdmissibleClass rulesS) (B : AdmissibleClass rulesT) where
  map : rulesS.Context → rulesT.Context
  admissible : ∀ {context : rulesS.Context}, A.Admissible context → B.Admissible (map context)

/-- The translation on the labels of the saturated systems. -/
def InterventionMap.label {S : GSLT.{uS}} {T : GSLT.{uT}}
    {rulesS : ContextualRules.{uC, uR} S} {rulesT : ContextualRules.{uC', uR'} T}
    {A : AdmissibleClass rulesS} {B : AdmissibleClass rulesT} (ω : InterventionMap A B) :
    {context : rulesS.Context // A.Admissible context} →
      {context : rulesT.Context // B.Admissible context} :=
  fun context => ⟨ω.map context.1, ω.admissible context.2⟩

/-- **A passive map**: an observation-preserving functional bisimulation between
the unintervened systems. -/
abbrev PassiveMap {S : GSLT.{uS}} {T : GSLT.{uT}} (baseS : GradedObservations.{uS, uO} S)
    (baseT : GradedObservations.{uT, uO'} T) (discount : ℝ) (discount_nonneg : 0 ≤ discount)
    (discount_le_one : discount ≤ 1) :=
  ObservationBisimulation (GradedSystem.stepping S baseS discount discount_nonneg discount_le_one)
    (GradedSystem.stepping T baseT discount discount_nonneg discount_le_one)

/-- **A saturated map**: an observation-preserving functional bisimulation
between the saturated systems. -/
abbrev SaturatedMap {S : GSLT.{uS}} {T : GSLT.{uT}}
    {rulesS : ContextualRules.{uC, uR} S} {rulesT : ContextualRules.{uC', uR'} T}
    (A : AdmissibleClass rulesS) (B : AdmissibleClass rulesT)
    (baseS : GradedObservations.{uS, uO} S) (baseT : GradedObservations.{uT, uO'} T)
    (discount : ℝ) (discount_nonneg : 0 ≤ discount) (discount_le_one : discount ≤ 1) :=
  ObservationBisimulation (saturatedGraded A baseS discount discount_nonneg discount_le_one)
    (saturatedGraded B baseT discount discount_nonneg discount_le_one)

/-- Formula values agree at distance zero. -/
theorem eval_eq_of_logicalDistance_eq_zero {S : GSLT.{uS}}
    (Q : GradedSystem.{uS, uA, uL, uV} S) {left right : S.Term}
    (zero : Q.logicalDistance left right = 0) (formula : Q.Formula) :
    Q.eval formula left = Q.eval formula right := by
  have bound := Q.abs_eval_sub_le_logicalDistance formula left right
  rw [zero] at bound
  exact sub_eq_zero.mp (abs_nonpos_iff.mp bound)

section Transport

variable {S : GSLT.{uS}} {T : GSLT.{uT}}
  {rulesS : ContextualRules.{uC, uR} S} {rulesT : ContextualRules.{uC', uR'} T}
  {A : AdmissibleClass rulesS} {B : AdmissibleClass rulesT}
  {baseS : GradedObservations.{uS, uO} S} {baseT : GradedObservations.{uT, uO'} T}
  {discount : ℝ} {discount_nonneg : 0 ≤ discount} {discount_le_one : discount ≤ 1}

/-! ## Commuting up to the equations: a saturated map -/

/-- **A square commuting up to the high-level equations makes the passive map a
saturated map**, with observations `τ × ω` and labels `ω`. -/
def saturate (passiveMap : PassiveMap baseS baseT discount discount_nonneg discount_le_one)
    (ω : InterventionMap A B)
    (square : ∀ ⦃context : rulesS.Context⦄, A.Admissible context → ∀ term : S.Term,
      T.Equiv (passiveMap.mapTerm (rulesS.plug context term))
        (rulesT.plug (ω.map context) (passiveMap.mapTerm term))) :
    SaturatedMap A B baseS baseT discount discount_nonneg discount_le_one where
  mapTerm := passiveMap.mapTerm
  mapEquiv := passiveMap.mapEquiv
  atom observation := (passiveMap.atom observation.1, ω.label observation.2)
  label := ω.label
  discount_eq := rfl
  value_map observation term := by
    change baseT.value (passiveMap.atom observation.1)
        (rulesT.plug (ω.map observation.2.1) (passiveMap.mapTerm term)) =
      baseS.value observation.1 (rulesS.plug observation.2.1 term)
    rw [← baseT.value_resp _ (square observation.2.2 term)]
    exact passiveMap.value_map observation.1 (rulesS.plug observation.2.1 term)
  mapAct context term target step := by
    have image : T.Step (passiveMap.mapTerm (rulesS.plug context.1 term))
        (passiveMap.mapTerm target) := passiveMap.mapAct () step
    obtain ⟨target', step', equivalent⟩ := T.rewrites_resp_left (square context.2 term) image
    exact T.rewrites_resp_right step' (T.equations.iseqv.symm equivalent)
  liftAct context term target' step := by
    obtain ⟨middle, step', equivalent⟩ :=
      T.rewrites_resp_left (T.equations.iseqv.symm (square context.2 term)) step
    obtain ⟨target, sourceStep, close⟩ := passiveMap.liftAct () step'
    exact ⟨target, sourceStep, T.equations.iseqv.trans close (T.equations.iseqv.symm equivalent)⟩

/-! ## From a saturated map to the square up to counterfactual distance zero -/

/-- **A saturated map with vocabulary `τ × ω` commutes with every admissible
intervention up to zero high-level counterfactual distance**, when `ω` is
compatible with composition and both translations are surjective.  The pair
`f (C[t])`, `ω(C)[f t]` lies in a graded bisimulation of the high-level
saturated system: after any further intervention both step to images of the
same low-level steps. -/
theorem commutes_of_saturatedMap
    (map : SaturatedMap A B baseS baseT discount discount_nonneg discount_le_one)
    (ω : InterventionMap A B) (reading : baseS.Atom → baseT.Atom)
    (reading_eq : ∀ observation context, (map.atom (observation, context)).1 = reading observation)
    (context_eq : ∀ observation context,
      (map.atom (observation, context)).2.1 = ω.map context.1)
    (label_eq : ∀ context, (map.label context).1 = ω.map context.1)
    (compose_eq : ∀ ⦃outer inner : rulesS.Context⦄, A.Admissible outer → A.Admissible inner →
      ∀ term, T.Equiv (rulesT.plug (ω.map (rulesS.compose outer inner)) term)
        (rulesT.plug (ω.map outer) (rulesT.plug (ω.map inner) term)))
    (readingSurjective : Function.Surjective reading)
    (labelSurjective : Function.Surjective ω.label)
    {context : rulesS.Context} (admissible : A.Admissible context) (term : S.Term) :
    counterfactualDistance B baseT discount discount_nonneg discount_le_one
      (map.mapTerm (rulesS.plug context term)) (rulesT.plug (ω.map context) (map.mapTerm term)) =
        0 := by
  let related : T.Term → T.Term → Prop := fun first second => T.Equiv first second ∨
    ∃ inner, A.Admissible inner ∧ ∃ source, first = map.mapTerm (rulesS.plug inner source) ∧
      second = rulesT.plug (ω.map inner) (map.mapTerm source)
  have forthSquare : ∀ {inner : rulesS.Context}, A.Admissible inner → ∀ (source : S.Term)
      (outer : {context : rulesS.Context // A.Admissible context}) {first' : T.Term},
      T.Step (rulesT.plug (ω.map outer.1) (map.mapTerm (rulesS.plug inner source))) first' →
        ∃ second', T.Step (rulesT.plug (ω.map outer.1)
            (rulesT.plug (ω.map inner) (map.mapTerm source))) second' ∧ T.Equiv first' second' := by
    intro inner innerAdmissible source outer first' step
    have step' : T.Step (rulesT.plug (map.label outer).1 (map.mapTerm (rulesS.plug inner source)))
        first' := by
      rw [label_eq outer]
      exact step
    obtain ⟨lowTarget, lowStep, close⟩ := map.liftAct outer step'
    obtain ⟨composedTarget, composedStep, composedClose⟩ :=
      S.rewrites_resp_left (S.equations.iseqv.symm (rulesS.plug_compose outer.1 inner source))
        lowStep
    have image : T.Step (rulesT.plug (map.label
        ⟨rulesS.compose outer.1 inner, A.compose_mem outer.2 innerAdmissible⟩).1
        (map.mapTerm source)) (map.mapTerm composedTarget) :=
      map.mapAct ⟨rulesS.compose outer.1 inner, A.compose_mem outer.2 innerAdmissible⟩ composedStep
    rw [label_eq ⟨rulesS.compose outer.1 inner, A.compose_mem outer.2 innerAdmissible⟩] at image
    obtain ⟨second', secondStep, secondClose⟩ :=
      T.rewrites_resp_left (compose_eq outer.2 innerAdmissible (map.mapTerm source)) image
    exact ⟨second', secondStep, T.equations.iseqv.trans (T.equations.iseqv.symm close)
      (T.equations.iseqv.trans (map.mapEquiv composedClose) secondClose)⟩
  have backSquare : ∀ {inner : rulesS.Context}, A.Admissible inner → ∀ (source : S.Term)
      (outer : {context : rulesS.Context // A.Admissible context}) {second' : T.Term},
      T.Step (rulesT.plug (ω.map outer.1)
          (rulesT.plug (ω.map inner) (map.mapTerm source))) second' →
        ∃ first', T.Step (rulesT.plug (ω.map outer.1) (map.mapTerm (rulesS.plug inner source)))
            first' ∧ T.Equiv first' second' := by
    intro inner innerAdmissible source outer second' step
    obtain ⟨composedImage, composedImageStep, composedImageClose⟩ :=
      T.rewrites_resp_left
        (T.equations.iseqv.symm (compose_eq outer.2 innerAdmissible (map.mapTerm source))) step
    have step' : T.Step (rulesT.plug (map.label
        ⟨rulesS.compose outer.1 inner, A.compose_mem outer.2 innerAdmissible⟩).1
        (map.mapTerm source)) composedImage := by
      rw [label_eq ⟨rulesS.compose outer.1 inner, A.compose_mem outer.2 innerAdmissible⟩]
      exact composedImageStep
    obtain ⟨lowTarget, lowStep, close⟩ := map.liftAct _ step'
    obtain ⟨filledTarget, filledStep, filledClose⟩ :=
      S.rewrites_resp_left (rulesS.plug_compose outer.1 inner source) lowStep
    have image : T.Step (rulesT.plug (map.label outer).1 (map.mapTerm (rulesS.plug inner source)))
        (map.mapTerm filledTarget) := map.mapAct outer filledStep
    rw [label_eq outer] at image
    exact ⟨_, image, T.equations.iseqv.trans
      (T.equations.iseqv.symm (map.mapEquiv filledClose))
      (T.equations.iseqv.trans close (T.equations.iseqv.symm composedImageClose))⟩
  have bisimulation :
      (saturatedGraded B baseT discount discount_nonneg discount_le_one).IsGradedBisimulation
        related := by
    refine ⟨?_, ?_, ?_⟩
    · rintro first second (equivalent | ⟨inner, innerAdmissible, source, rfl, rfl⟩) label first'
        step
      · obtain ⟨second', secondStep, close⟩ :=
          (saturatedGraded B baseT discount discount_nonneg discount_le_one).dynamics.act_resp_left
            equivalent step
        exact ⟨second', secondStep, Or.inl close⟩
      · obtain ⟨outer, rfl⟩ := labelSurjective label
        obtain ⟨second', secondStep, close⟩ := forthSquare innerAdmissible source outer step
        exact ⟨second', secondStep, Or.inl close⟩
    · rintro first second (equivalent | ⟨inner, innerAdmissible, source, rfl, rfl⟩) label second'
        step
      · obtain ⟨first', firstStep, close⟩ :=
          (saturatedGraded B baseT discount discount_nonneg discount_le_one).dynamics.act_resp_left
            (T.equations.iseqv.symm equivalent) step
        exact ⟨first', firstStep, Or.inl (T.equations.iseqv.symm close)⟩
      · obtain ⟨outer, rfl⟩ := labelSurjective label
        obtain ⟨first', firstStep, close⟩ := backSquare innerAdmissible source outer step
        exact ⟨first', firstStep, Or.inl close⟩
    · rintro first second (equivalent | ⟨inner, innerAdmissible, source, rfl, rfl⟩) atom
      · exact (saturatedGraded B baseT discount discount_nonneg discount_le_one).observations.value_resp
          atom equivalent
      · obtain ⟨highObservation, label⟩ := atom
        obtain ⟨observation, rfl⟩ := readingSurjective highObservation
        obtain ⟨outer, rfl⟩ := labelSurjective label
        let composedContext : {context : rulesS.Context // A.Admissible context} :=
          ⟨rulesS.compose outer.1 inner, A.compose_mem outer.2 innerAdmissible⟩
        have filled : baseT.value (map.atom (observation, outer)).1
            (rulesT.plug (map.atom (observation, outer)).2.1
              (map.mapTerm (rulesS.plug inner source))) =
            baseS.value observation (rulesS.plug outer.1 (rulesS.plug inner source)) :=
          map.value_map (observation, outer) (rulesS.plug inner source)
        rw [reading_eq observation outer, context_eq observation outer] at filled
        have composed : baseT.value (map.atom (observation, composedContext)).1
            (rulesT.plug (map.atom (observation, composedContext)).2.1 (map.mapTerm source)) =
            baseS.value observation (rulesS.plug composedContext.1 source) :=
          map.value_map (observation, composedContext) source
        rw [reading_eq observation composedContext, context_eq observation composedContext]
          at composed
        change baseT.value (reading observation)
            (rulesT.plug (ω.map outer.1) (map.mapTerm (rulesS.plug inner source))) =
          baseT.value (reading observation)
            (rulesT.plug (ω.map outer.1) (rulesT.plug (ω.map inner) (map.mapTerm source)))
        rw [filled, ← baseT.value_resp (reading observation)
          (compose_eq outer.2 innerAdmissible (map.mapTerm source)), composed]
        exact baseS.value_resp observation
          (S.equations.iseqv.symm (rulesS.plug_compose outer.1 inner source))
  exact GradedSystem.logicalDistance_eq_zero_of_gradedBisimilar _
    ⟨related, bisimulation, Or.inr ⟨context, admissible, term, rfl, rfl⟩⟩

end Transport

/-! ## Causal abstractions -/

/-- **A causal abstraction**: a passive map and an intervention map whose
square commutes, at every state and for every admissible intervention, up to
zero high-level counterfactual distance. -/
structure CausalAbstraction {S : GSLT.{uS}} {T : GSLT.{uT}}
    {rulesS : ContextualRules.{uC, uR} S} {rulesT : ContextualRules.{uC', uR'} T}
    (A : AdmissibleClass rulesS) (B : AdmissibleClass rulesT)
    (baseS : GradedObservations.{uS, uO} S) (baseT : GradedObservations.{uT, uO'} T)
    (discount : ℝ) (discount_nonneg : 0 ≤ discount) (discount_le_one : discount ≤ 1) where
  passiveMap : PassiveMap baseS baseT discount discount_nonneg discount_le_one
  intervention : InterventionMap A B
  commutes : ∀ ⦃context : rulesS.Context⦄, A.Admissible context → ∀ term : S.Term,
    counterfactualDistance B baseT discount discount_nonneg discount_le_one
      (passiveMap.mapTerm (rulesS.plug context term))
      (rulesT.plug (intervention.map context) (passiveMap.mapTerm term)) = 0

namespace CausalAbstraction

variable {S : GSLT.{uS}} {T : GSLT.{uT}}
  {rulesS : ContextualRules.{uC, uR} S} {rulesT : ContextualRules.{uC', uR'} T}
  {A : AdmissibleClass rulesS} {B : AdmissibleClass rulesT}
  {baseS : GradedObservations.{uS, uO} S} {baseT : GradedObservations.{uT, uO'} T}
  {discount : ℝ} {discount_nonneg : 0 ≤ discount} {discount_le_one : discount ≤ 1}

/-- **A square commuting up to the equations gives a causal abstraction.** -/
def ofSquare (passiveMap : PassiveMap baseS baseT discount discount_nonneg discount_le_one)
    (ω : InterventionMap A B)
    (square : ∀ ⦃context : rulesS.Context⦄, A.Admissible context → ∀ term : S.Term,
      T.Equiv (passiveMap.mapTerm (rulesS.plug context term))
        (rulesT.plug (ω.map context) (passiveMap.mapTerm term))) :
    CausalAbstraction A B baseS baseT discount discount_nonneg discount_le_one where
  passiveMap := passiveMap
  intervention := ω
  commutes context admissible term := by
    unfold counterfactualDistance
    rw [GradedSystem.logicalDistance_resp_right _ _ (T.equations.iseqv.symm
      (square admissible term))]
    exact GradedSystem.logicalDistance_self _ _

variable (abstraction : CausalAbstraction A B baseS baseT discount discount_nonneg discount_le_one)

/-- An observation read through a translated intervention at an image is the
low-level observation read through the intervention. -/
theorem atom_value (observation : baseS.Atom)
    (context : {context : rulesS.Context // A.Admissible context}) (term : S.Term) :
    baseT.value (abstraction.passiveMap.atom observation)
        (rulesT.plug (abstraction.intervention.map context.1)
          (abstraction.passiveMap.mapTerm term)) =
      baseS.value observation (rulesS.plug context.1 term) := by
  let identity : {context : rulesT.Context // B.Admissible context} :=
    ⟨rulesT.identity, B.identity_mem⟩
  have same := eval_eq_of_logicalDistance_eq_zero
    (saturatedGraded B baseT discount discount_nonneg discount_le_one)
    (abstraction.commutes context.2 term) (.atom (abstraction.passiveMap.atom observation, identity))
  change baseT.value (abstraction.passiveMap.atom observation)
      (rulesT.plug rulesT.identity
        (abstraction.passiveMap.mapTerm (rulesS.plug context.1 term))) =
    baseT.value (abstraction.passiveMap.atom observation)
      (rulesT.plug rulesT.identity (rulesT.plug (abstraction.intervention.map context.1)
        (abstraction.passiveMap.mapTerm term))) at same
  rw [baseT.value_resp _ (rulesT.plug_identity _), baseT.value_resp _ (rulesT.plug_identity _)]
    at same
  rw [← same]
  exact abstraction.passiveMap.value_map observation (rulesS.plug context.1 term)

omit abstraction in
/-- The steps under the identity intervention are the steps. -/
theorem setOf_step_plug_identity (term : T.Term) :
    {target | T.Step (rulesT.plug rulesT.identity term) target} = {target | T.Step term target} :=
  Set.ext fun _ => step_plug_identity_iff

/-- The values of a high-level formula at the steps of an image are its values
at the images of the low-level steps. -/
theorem image_steps (value : T.Term → ℝ)
    (resp : ∀ {first second : T.Term}, T.Equiv first second → value first = value second)
    (term : S.Term) :
    value '' {target | T.Step (abstraction.passiveMap.mapTerm term) target} =
      (fun target => value (abstraction.passiveMap.mapTerm target)) ''
        {target | S.Step term target} := by
  ext number
  constructor
  · rintro ⟨target', step, rfl⟩
    obtain ⟨target, lowStep, close⟩ := abstraction.passiveMap.liftAct () step
    exact ⟨target, lowStep, resp close⟩
  · rintro ⟨target, lowStep, rfl⟩
    exact ⟨_, abstraction.passiveMap.mapAct () lowStep, rfl⟩

/-- **A translated diamond at an image** is the discounted supremum over the
images of the low-level intervened steps. -/
theorem eval_dia (context : {context : rulesS.Context // A.Admissible context})
    (inner : (saturatedGraded B baseT discount discount_nonneg discount_le_one).Formula)
    (term : S.Term) :
    (saturatedGraded B baseT discount discount_nonneg discount_le_one).eval
        (.dia (abstraction.intervention.label context) inner)
        (abstraction.passiveMap.mapTerm term) =
      discount * sSup ((fun target =>
        (saturatedGraded B baseT discount discount_nonneg discount_le_one).eval inner
          (abstraction.passiveMap.mapTerm target)) ''
        {target | S.Step (rulesS.plug context.1 term) target}) := by
  let identity : {context : rulesT.Context // B.Admissible context} :=
    ⟨rulesT.identity, B.identity_mem⟩
  have same := eval_eq_of_logicalDistance_eq_zero
    (saturatedGraded B baseT discount discount_nonneg discount_le_one)
    (abstraction.commutes context.2 term) (.dia identity inner)
  change discount * sSup ((saturatedGraded B baseT discount discount_nonneg discount_le_one).eval
      inner '' {target | T.Step (rulesT.plug rulesT.identity
        (abstraction.passiveMap.mapTerm (rulesS.plug context.1 term))) target}) =
    discount * sSup ((saturatedGraded B baseT discount discount_nonneg discount_le_one).eval
      inner '' {target | T.Step (rulesT.plug rulesT.identity
        (rulesT.plug (abstraction.intervention.map context.1)
          (abstraction.passiveMap.mapTerm term))) target}) at same
  rw [setOf_step_plug_identity, setOf_step_plug_identity] at same
  change discount * sSup ((saturatedGraded B baseT discount discount_nonneg discount_le_one).eval
      inner '' {target | T.Step (rulesT.plug (abstraction.intervention.map context.1)
        (abstraction.passiveMap.mapTerm term)) target}) = _
  rw [← same, abstraction.image_steps _
    (fun equivalent => GradedSystem.eval_resp _ inner equivalent)]

/-- Translate a low-level saturated formula: observations by `τ × ω`,
interventions by `ω`. -/
def translate :
    (saturatedGraded A baseS discount discount_nonneg discount_le_one).Formula →
      (saturatedGraded B baseT discount discount_nonneg discount_le_one).Formula
  | .top => .top
  | .atom observation =>
      .atom (abstraction.passiveMap.atom observation.1, abstraction.intervention.label observation.2)
  | .neg inner => .neg (translate inner)
  | .conj left right => .conj (translate left) (translate right)
  | .shift threshold inner => .shift threshold (translate inner)
  | .dia context inner => .dia (abstraction.intervention.label context) (translate inner)

/-- **Every counterfactual formula transports along a causal abstraction.** -/
theorem eval_translate :
    ∀ (formula : (saturatedGraded A baseS discount discount_nonneg discount_le_one).Formula)
      (term : S.Term),
      (saturatedGraded B baseT discount discount_nonneg discount_le_one).eval
          (abstraction.translate formula) (abstraction.passiveMap.mapTerm term) =
        (saturatedGraded A baseS discount discount_nonneg discount_le_one).eval formula term
  | .top, _ => rfl
  | .atom observation, term => abstraction.atom_value observation.1 observation.2 term
  | .neg inner, term => by
      simp only [translate, GradedSystem.eval_neg, eval_translate inner term]
  | .conj left right, term => by
      simp only [translate, GradedSystem.eval_conj, eval_translate left term,
        eval_translate right term]
  | .shift threshold inner, term => by
      simp only [translate, GradedSystem.eval_shift, eval_translate inner term]
  | .dia context inner, term =>
      (abstraction.eval_dia context (abstraction.translate inner) term).trans (by
        change discount * sSup _ = discount * sSup
          ((saturatedGraded A baseS discount discount_nonneg discount_le_one).eval inner ''
            {target | S.Step (rulesS.plug context.1 term) target})
        congr 2
        exact Set.image_congr fun target _ => eval_translate inner target)

/-- **A causal abstraction loses no counterfactual distinction.** -/
theorem counterfactualDistance_le (left right : S.Term) :
    counterfactualDistance A baseS discount discount_nonneg discount_le_one left right ≤
      counterfactualDistance B baseT discount discount_nonneg discount_le_one
        (abstraction.passiveMap.mapTerm left) (abstraction.passiveMap.mapTerm right) := by
  unfold counterfactualDistance
  refine (saturatedGraded A baseS discount discount_nonneg discount_le_one).logicalDistance_le_iff.mpr
    fun formula => ?_
  rw [← abstraction.eval_translate formula left, ← abstraction.eval_translate formula right]
  exact GradedSystem.abs_eval_sub_le_logicalDistance _ _ _ _

variable (atomSurjective : Function.Surjective abstraction.passiveMap.atom)
  (labelSurjective : Function.Surjective abstraction.intervention.label)

/-- Pull a high-level saturated formula back along surjective translations. -/
noncomputable def pullback :
    (saturatedGraded B baseT discount discount_nonneg discount_le_one).Formula →
      (saturatedGraded A baseS discount discount_nonneg discount_le_one).Formula
  | .top => .top
  | .atom observation =>
      .atom (Function.surjInv atomSurjective observation.1,
        Function.surjInv labelSurjective observation.2)
  | .neg inner => .neg (pullback inner)
  | .conj left right => .conj (pullback left) (pullback right)
  | .shift threshold inner => .shift threshold (pullback inner)
  | .dia label inner => .dia (Function.surjInv labelSurjective label) (pullback inner)

theorem eval_pullback :
    ∀ (formula : (saturatedGraded B baseT discount discount_nonneg discount_le_one).Formula)
      (term : S.Term),
      (saturatedGraded A baseS discount discount_nonneg discount_le_one).eval
          (abstraction.pullback atomSurjective labelSurjective formula) term =
        (saturatedGraded B baseT discount discount_nonneg discount_le_one).eval formula
          (abstraction.passiveMap.mapTerm term)
  | .top, _ => rfl
  | .atom observation, term => by
      have value := abstraction.atom_value (Function.surjInv atomSurjective observation.1)
        (Function.surjInv labelSurjective observation.2) term
      change baseT.value (abstraction.passiveMap.atom (Function.surjInv atomSurjective observation.1))
          (rulesT.plug (abstraction.intervention.label
            (Function.surjInv labelSurjective observation.2)).1
            (abstraction.passiveMap.mapTerm term)) = _ at value
      rw [Function.surjInv_eq atomSurjective, Function.surjInv_eq labelSurjective] at value
      exact value.symm
  | .neg inner, term => by
      simp only [pullback, GradedSystem.eval_neg, eval_pullback inner term]
  | .conj left right, term => by
      simp only [pullback, GradedSystem.eval_conj, eval_pullback left term,
        eval_pullback right term]
  | .shift threshold inner, term => by
      simp only [pullback, GradedSystem.eval_shift, eval_pullback inner term]
  | .dia label inner, term => by
      have unfolded := abstraction.eval_dia (Function.surjInv labelSurjective label) inner term
      change _ = discount * sSup _ at unfolded
      change discount * sSup
          ((saturatedGraded A baseS discount discount_nonneg discount_le_one).eval
            (abstraction.pullback atomSurjective labelSurjective inner) ''
            {target | S.Step (rulesS.plug (Function.surjInv labelSurjective label).1 term) target}) =
        (saturatedGraded B baseT discount discount_nonneg discount_le_one).eval
          (.dia label inner) (abstraction.passiveMap.mapTerm term)
      have relabel : (saturatedGraded B baseT discount discount_nonneg discount_le_one).eval
          (.dia label inner) (abstraction.passiveMap.mapTerm term) =
        (saturatedGraded B baseT discount discount_nonneg discount_le_one).eval
          (.dia (abstraction.intervention.label (Function.surjInv labelSurjective label)) inner)
          (abstraction.passiveMap.mapTerm term) := by
        rw [Function.surjInv_eq labelSurjective label]
      rw [relabel, unfolded]
      congr 2
      exact Set.image_congr fun target _ => eval_pullback inner target

/-- **With surjective translations a causal abstraction is an isometry of the
counterfactual distance.** -/
theorem counterfactualDistance_map (atomSurjective : Function.Surjective abstraction.passiveMap.atom)
    (labelSurjective : Function.Surjective abstraction.intervention.label) (left right : S.Term) :
    counterfactualDistance B baseT discount discount_nonneg discount_le_one
        (abstraction.passiveMap.mapTerm left) (abstraction.passiveMap.mapTerm right) =
      counterfactualDistance A baseS discount discount_nonneg discount_le_one left right := by
  refine le_antisymm ?_ (abstraction.counterfactualDistance_le left right)
  unfold counterfactualDistance
  refine (saturatedGraded B baseT discount discount_nonneg discount_le_one).logicalDistance_le_iff.mpr
    fun formula => ?_
  rw [← abstraction.eval_pullback atomSurjective labelSurjective formula left,
    ← abstraction.eval_pullback atomSurjective labelSurjective formula right]
  exact GradedSystem.abs_eval_sub_le_logicalDistance _ _ _ _

end CausalAbstraction

/-! ## The square is a congruence of the relation "map, then counterfactual equivalence" -/

section Congruence

variable {S : GSLT.{uS}} {T : GSLT.{uT}}
  {rulesS : ContextualRules.{uC, uR} S} {rulesT : ContextualRules.{uC', uR'} T}
  {A : AdmissibleClass rulesS} {B : AdmissibleClass rulesT}
  {baseS : GradedObservations.{uS, uO} S} {baseT : GradedObservations.{uT, uO'} T}
  {discount : ℝ} {discount_nonneg : 0 ≤ discount} {discount_le_one : discount ≤ 1}

/-- **The square for one intervention is exactly the congruence**, for that
intervention and its image, of the relation that maps a low-level term and then
allows any high-level term at counterfactual distance zero. -/
theorem commutes_iff_congruent
    (passiveMap : PassiveMap baseS baseT discount discount_nonneg discount_le_one)
    (ω : InterventionMap A B) {context : rulesS.Context} (admissible : A.Admissible context) :
    (∀ term : S.Term, counterfactualDistance B baseT discount discount_nonneg discount_le_one
        (passiveMap.mapTerm (rulesS.plug context term))
        (rulesT.plug (ω.map context) (passiveMap.mapTerm term)) = 0) ↔
      SpanTransport.Congruent
        (fun (term : S.Term) (image : T.Term) =>
          counterfactualDistance B baseT discount discount_nonneg discount_le_one
            (passiveMap.mapTerm term) image = 0)
        (rulesS.plug context) (rulesT.plug (ω.map context)) := by
  unfold counterfactualDistance
  constructor
  · intro square term image related
    refine le_antisymm ?_ (GradedSystem.logicalDistance_nonneg _ _ _)
    calc (saturatedGraded B baseT discount discount_nonneg discount_le_one).logicalDistance
          (passiveMap.mapTerm (rulesS.plug context term)) (rulesT.plug (ω.map context) image)
        ≤ (saturatedGraded B baseT discount discount_nonneg discount_le_one).logicalDistance
            (passiveMap.mapTerm (rulesS.plug context term))
            (rulesT.plug (ω.map context) (passiveMap.mapTerm term)) +
          (saturatedGraded B baseT discount discount_nonneg discount_le_one).logicalDistance
            (rulesT.plug (ω.map context) (passiveMap.mapTerm term))
            (rulesT.plug (ω.map context) image) :=
          GradedSystem.logicalDistance_triangle _ _ _ _
      _ ≤ 0 + (saturatedGraded B baseT discount discount_nonneg discount_le_one).logicalDistance
            (passiveMap.mapTerm term) image := by
          rw [square term, zero_add, zero_add]
          exact saturatedGraded_logicalDistance_plug_le B (ω.admissible admissible) _ _
      _ = 0 := by rw [related, add_zero]
  · intro congruent term
    exact congruent (GradedSystem.logicalDistance_self _ (passiveMap.mapTerm term))

end Congruence

end Mettapedia.GSLT.Causality.Abstraction
