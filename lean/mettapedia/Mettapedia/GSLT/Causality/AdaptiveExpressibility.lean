import Mettapedia.GSLT.Causality.AdaptiveContexts

/-!
# When a meta-level observer can state the adaptive query

The separation `adaptive_not_meta` is about one model: no constant regime on
`twoUnits` reaches both records that `flip` reaches. The formula-level claim
is different. The contexts stay the meta-level ones (`everyIntervention`: one
imposed treatment for every unit). The language is the Hennessy–Milner
`Formula` of the saturated system of `quantities`, the observer already used
by `Hierarchy`. No new formula type and no new observation predicate are
introduced. `treatmentShown` is the treatment atom of that observer read with
nothing imposed, the same pairing as `effectShown`.

The covariate the policy reads is the drawn unit's natural treatment. On a
record with nothing imposed, `shows .treatment` is that bit.

* **The covariate is an observation.** The saturated formula `adaptiveFormula`
  branches on the treatment atom, then imposes the opposite regime on that
  same unit. At a population with nothing imposed it holds exactly when `flip`
  reaches both the record “treated, effect” and the record “untreated, no
  effect”. `twoUnits` is a population it holds of.
* **The covariate is not an observation.** A formula whose atoms are all
  effect atoms — interventions still allowed, the treatment atom not — cannot
  express that query. Swapping the natural treatments of `twoUnits`, and
  leaving the response types in place, preserves every such formula and
  changes the query.

So, for this observer, the query is expressible exactly when the formula may
read the treatment atom. The single-intervention fragment `underIntervention`
is a different restriction: it cannot branch inside one unit, whether or not
the treatment atom is a passive observation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.AdaptiveExpressibility

open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.AdmissibleContextCongruence
open Mettapedia.GSLT.Causality.Hierarchy
open Mettapedia.GSLT.Causality.Hierarchy.ResponseTypes

/-- The adaptive policy and its two-unit population, named here so the
meta-level stage of `ResponseTypes` stays the ambient `Stage`. -/
abbrev flip := Mettapedia.GSLT.Causality.AdaptiveContexts.flip

abbrev twoUnits := Mettapedia.GSLT.Causality.AdaptiveContexts.twoUnits

/-- The saturated system of every meta-level intervention, observed by
`quantities`. -/
abbrev ladder := everyIntervention.saturated quantities

/-- The treatment atom of `quantities`, read with nothing further imposed. -/
def treatmentShown : ladder.Atom :=
  (.treatment, ⟨none, AdmissibleClass.top_admissible _⟩)

/-- The treatment bit the record shows, or its negation. -/
def literalTreatment : Bool → Formula ladder.Atom ladder.Label
  | false => .neg (.atom treatmentShown)
  | true => .atom treatmentShown

/-- The effect bit, or its negation. -/
def literalEffect : Bool → Formula ladder.Atom ladder.Label
  | true => .atom effectShown
  | false => .neg (.atom effectShown)

/-- Draw one unit, read its natural treatment, and impose one regime on it. -/
def branch (covariate regime effect : Bool) : Formula ladder.Atom ladder.Label :=
  .dia proceed
    (.conj (.dia proceed (literalTreatment covariate)) (.dia (treat regime) (literalEffect effect)))

/-- **The adaptive query as a saturated formula.** One branch for each record
`flip` is asked to reach: a naturally untreated unit that shows the effect if
treated, and a naturally treated unit that hides the effect if untreated. -/
def adaptiveFormula : Formula ladder.Atom ladder.Label :=
  .conj (branch false true true) (branch true false false)

/-- **The covariate is an observation of `quantities`.** On a record reached
with nothing imposed, the treatment atom is the natural treatment. -/
theorem quantities_observe_covariate (natural : Bool) (response : Response) :
    shows .treatment (.record natural (response.outcome natural)) ↔ natural = true := by
  unfold shows
  exact Iff.rfl

theorem sat_treatment_record (treated effect want : Bool) :
    ladder.sat (literalTreatment want) (.record treated effect) ↔ treated = want := by
  cases want with
  | true =>
      change (shows .treatment (.record treated effect) ↔ treated = true)
      unfold shows
      exact Iff.rfl
  | false =>
      change (¬ shows .treatment (.record treated effect) ↔ treated = false)
      unfold shows
      exact Bool.eq_false_iff.symm

theorem sat_effect_record (treated effect want : Bool) :
    ladder.sat (literalEffect want) (.record treated effect) ↔ effect = want := by
  cases want with
  | true =>
      change (shows .effect (.record treated effect) ↔ effect = true)
      unfold shows
      exact Iff.rfl
  | false =>
      change (¬ shows .effect (.record treated effect) ↔ effect = false)
      unfold shows
      exact Bool.eq_false_iff.symm

/-- One branch holds at an unintervened population exactly when some unit has
that natural treatment and that outcome under the imposed regime. -/
theorem sat_branch (individuals : List (Bool × Response)) (covariate regime effect : Bool) :
    ladder.sat (branch covariate regime effect) (.population individuals none) ↔
      ∃ unit ∈ individuals, unit.1 = covariate ∧ unit.2.outcome regime = effect := by
  constructor
  · intro holds
    obtain ⟨drawn, drawStep, naturalBit, regimeBit⟩ := holds
    cases moves_of_step drawStep with
    | @draw _ _ natural response member =>
        obtain ⟨_, respondStep, bit⟩ := naturalBit
        cases moves_of_step respondStep
        obtain ⟨_, respondStep', shown⟩ := regimeBit
        cases moves_of_step respondStep'
        exact ⟨(natural, response), member,
          (sat_treatment_record natural _ covariate).mp bit,
          (sat_effect_record regime _ effect).mp shown⟩
  · rintro ⟨⟨natural, response⟩, member, covariateEq, outcomeEq⟩
    exact ⟨.individual natural response none, Moves.draw member,
      ⟨.record natural (response.outcome natural), Moves.respond,
        (sat_treatment_record natural _ covariate).mpr covariateEq⟩,
      ⟨.record regime (response.outcome regime), Moves.respond,
        (sat_effect_record regime _ effect).mpr outcomeEq⟩⟩

/-- The query `flip` answers: both of its records are reachable. -/
def AdaptiveQuery (individuals : List (Bool × Response)) : Prop :=
  (∃ unit ∈ individuals, unit.1 = false ∧ unit.2.outcome true = true) ∧
    (∃ unit ∈ individuals, unit.1 = true ∧ unit.2.outcome false = false)

theorem flip_imposed (natural : Bool) : (flip natural).getD natural = !natural := rfl

theorem not_eq_true (value : Bool) : (!value) = true ↔ value = false := by
  rw [Bool.not_eq, ← Bool.eq_false_iff]

theorem not_eq_false (value : Bool) : (!value) = false ↔ value = true := by
  rw [Bool.not_eq, Bool.ne_false_iff]

/-- **The formula is the adaptive policy's query.** Both records of `flip`. -/
theorem adaptiveQuery_iff_flip (individuals : List (Bool × Response)) :
    AdaptiveQuery individuals ↔
      Mettapedia.GSLT.Causality.AdaptiveContexts.ReachesRecord
          (.population individuals flip) true true ∧
        Mettapedia.GSLT.Causality.AdaptiveContexts.ReachesRecord
          (.population individuals flip) false false := by
  rw [Mettapedia.GSLT.Causality.AdaptiveContexts.reachesRecord_population_iff,
    Mettapedia.GSLT.Causality.AdaptiveContexts.reachesRecord_population_iff]
  constructor
  · rintro ⟨⟨unit, member, natural, outcome⟩, ⟨unit', member', natural', outcome'⟩⟩
    refine ⟨⟨unit, member, ?_, outcome⟩, ⟨unit', member', ?_, outcome'⟩⟩
    · rw [flip_imposed, not_eq_true]
      exact natural
    · rw [flip_imposed, not_eq_false]
      exact natural'
  · rintro ⟨⟨unit, member, treated, outcome⟩, ⟨unit', member', treated', outcome'⟩⟩
    refine ⟨⟨unit, member, ?_, outcome⟩, ⟨unit', member', ?_, outcome'⟩⟩
    · rw [flip_imposed] at treated
      exact (not_eq_true unit.1).mp treated
    · rw [flip_imposed] at treated'
      exact (not_eq_false unit'.1).mp treated'

/-- **Reading the covariate expresses the query**, at every unintervened
population. -/
theorem adaptiveQuery_expressed (individuals : List (Bool × Response)) :
    ladder.sat adaptiveFormula (.population individuals none) ↔ AdaptiveQuery individuals := by
  unfold adaptiveFormula AdaptiveQuery
  simp only [System.sat, sat_branch]

/-- The population `flip` is stated on. Its natural treatments are observable
as the treatment bits of the unintervened records. -/
abbrev covariateSeen : List (Bool × Response) := twoUnits

/-- The same response types with the natural treatments swapped. -/
def covariateHidden : List (Bool × Response) :=
  [(true, .always), (false, .never)]

theorem seen_query : AdaptiveQuery covariateSeen :=
  ⟨⟨(false, .always), List.mem_cons_self, rfl, rfl⟩,
    ⟨(true, .never), List.mem_cons_of_mem _ List.mem_cons_self, rfl, rfl⟩⟩

theorem hidden_not_query : ¬ AdaptiveQuery covariateHidden := by
  rintro ⟨⟨unit, member, natural, outcome⟩, _⟩
  simp only [covariateHidden, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl
  · cases natural
  · cases outcome

/-- **The expressing population.** `twoUnits` satisfies the formula, and `flip`
reaches both records. -/
theorem seen_satisfies :
    ladder.sat adaptiveFormula (.population covariateSeen none) ∧
      Mettapedia.GSLT.Causality.AdaptiveContexts.ReachesRecord (.population covariateSeen flip) true true ∧
        Mettapedia.GSLT.Causality.AdaptiveContexts.ReachesRecord (.population covariateSeen flip) false false := by
  have query := seen_query
  have records := (adaptiveQuery_iff_flip covariateSeen).mp query
  exact ⟨(adaptiveQuery_expressed covariateSeen).mpr query, records.1, records.2⟩

/-- **The swapped population fails the formula and the query.** -/
theorem hidden_fails :
    ¬ ladder.sat adaptiveFormula (.population covariateHidden none) ∧
      ¬ (Mettapedia.GSLT.Causality.AdaptiveContexts.ReachesRecord (.population covariateHidden flip) true true ∧
          Mettapedia.GSLT.Causality.AdaptiveContexts.ReachesRecord (.population covariateHidden flip) false false) := by
  have notQuery := hidden_not_query
  exact ⟨(adaptiveQuery_expressed covariateHidden).not.mpr notQuery,
    (adaptiveQuery_iff_flip covariateHidden).not.mp notQuery⟩

/-! ## Formulas that cannot read the covariate -/

/-- A formula of the existing language that never reads the treatment atom.
Interventions are still allowed. -/
def EffectOnly : Formula ladder.Atom ladder.Label → Prop
  | .top => True
  | .atom atom => atom.1 = Quantity.effect
  | .conj left right => EffectOnly left ∧ EffectOnly right
  | .neg inner => EffectOnly inner
  | .dia _ inner => EffectOnly inner

/-- The expressing formula reads the treatment atom. -/
theorem adaptiveFormula_reads_covariate : ¬ EffectOnly adaptiveFormula := by
  intro only
  unfold adaptiveFormula branch literalTreatment at only
  obtain ⟨left, _⟩ := only
  simp only [EffectOnly, treatmentShown] at left
  obtain ⟨bad, _⟩ := left
  cases bad

/-- States that show the same effects after the natural treatments are swapped. -/
inductive EffectTwin : Stage → Stage → Prop where
  | seenHidden (imposed : Option Bool) :
      EffectTwin (.population covariateSeen imposed) (.population covariateHidden imposed)
  | hiddenSeen (imposed : Option Bool) :
      EffectTwin (.population covariateHidden imposed) (.population covariateSeen imposed)
  | alwaysSeen (imposed : Option Bool) :
      EffectTwin (.individual false .always imposed) (.individual true .always imposed)
  | alwaysHidden (imposed : Option Bool) :
      EffectTwin (.individual true .always imposed) (.individual false .always imposed)
  | neverSeen (imposed : Option Bool) :
      EffectTwin (.individual true .never imposed) (.individual false .never imposed)
  | neverHidden (imposed : Option Bool) :
      EffectTwin (.individual false .never imposed) (.individual true .never imposed)
  | records (treated treated' effect : Bool) :
      EffectTwin (.record treated effect) (.record treated' effect)

theorem effectTwin_symm {left right : Stage} (rel : EffectTwin left right) :
    EffectTwin right left := by
  cases rel with
  | seenHidden imposed => exact .hiddenSeen imposed
  | hiddenSeen imposed => exact .seenHidden imposed
  | alwaysSeen imposed => exact .alwaysHidden imposed
  | alwaysHidden imposed => exact .alwaysSeen imposed
  | neverSeen imposed => exact .neverHidden imposed
  | neverHidden imposed => exact .neverSeen imposed
  | records treated treated' effect => exact .records treated' treated effect

theorem effectTwin_impose (context : Option Bool) {left right : Stage}
    (rel : EffectTwin left right) : EffectTwin (impose context left) (impose context right) := by
  cases rel with
  | seenHidden imposed => exact .seenHidden (context.or imposed)
  | hiddenSeen imposed => exact .hiddenSeen (context.or imposed)
  | alwaysSeen imposed => exact .alwaysSeen (context.or imposed)
  | alwaysHidden imposed => exact .alwaysHidden (context.or imposed)
  | neverSeen imposed => exact .neverSeen (context.or imposed)
  | neverHidden imposed => exact .neverHidden (context.or imposed)
  | records treated treated' effect => exact .records treated treated' effect

theorem effectTwin_shows_effect {left right : Stage} (rel : EffectTwin left right) :
    shows .effect left ↔ shows .effect right := by
  cases rel <;> simp [shows]

/-- Swap the natural treatment and keep the response type. -/
def swapped (individual : Bool × Response) : Bool × Response :=
  (!individual.1, individual.2)

theorem hidden_mem_of_seen {individual : Bool × Response} (member : individual ∈ covariateSeen) :
    swapped individual ∈ covariateHidden := by
  simp only [covariateSeen, twoUnits, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self

theorem seen_mem_of_hidden {individual : Bool × Response} (member : individual ∈ covariateHidden) :
    swapped individual ∈ covariateSeen := by
  simp only [covariateHidden, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self

theorem effectTwin_step {left right target : Stage} (rel : EffectTwin left right)
    (step : Moves left target) : ∃ target', Moves right target' ∧ EffectTwin target target' := by
  cases rel with
  | seenHidden imposed =>
      cases step with
      | @draw _ _ natural response member =>
          refine ⟨.individual (!natural) response imposed,
            Moves.draw (hidden_mem_of_seen member), ?_⟩
          simp only [covariateSeen, twoUnits, List.mem_cons, List.mem_nil_iff, or_false,
            Prod.mk.injEq] at member
          rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact .alwaysSeen imposed
          · exact .neverSeen imposed
  | hiddenSeen imposed =>
      cases step with
      | @draw _ _ natural response member =>
          refine ⟨.individual (!natural) response imposed,
            Moves.draw (seen_mem_of_hidden member), ?_⟩
          simp only [covariateHidden, List.mem_cons, List.mem_nil_iff, or_false,
            Prod.mk.injEq] at member
          rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact .alwaysHidden imposed
          · exact .neverHidden imposed
  | alwaysSeen imposed =>
      cases step
      exact ⟨.record (imposed.getD true) true, Moves.respond,
        .records (imposed.getD false) (imposed.getD true) true⟩
  | alwaysHidden imposed =>
      cases step
      exact ⟨.record (imposed.getD false) true, Moves.respond,
        .records (imposed.getD true) (imposed.getD false) true⟩
  | neverSeen imposed =>
      cases step
      exact ⟨.record (imposed.getD false) false, Moves.respond,
        .records (imposed.getD true) (imposed.getD false) false⟩
  | neverHidden imposed =>
      cases step
      exact ⟨.record (imposed.getD true) false, Moves.respond,
        .records (imposed.getD false) (imposed.getD true) false⟩
  | records _ _ _ =>
      cases step

/-- Effect-only formulas agree on the swapped populations, at every stage the
swap relates, and under every meta-level intervention. -/
theorem effectOnly_agree (formula : Formula ladder.Atom ladder.Label) :
    EffectOnly formula → ∀ {left right : Stage}, EffectTwin left right →
      (ladder.sat formula left ↔ ladder.sat formula right) := by
  induction formula with
  | top =>
      intro _ _ _ _
      rfl
  | atom atom =>
      intro only _ _ rel
      cases atom with
      | mk quantity context =>
          cases only
          exact effectTwin_shows_effect (effectTwin_impose context.1 rel)
  | conj left right leftIh rightIh =>
      intro only _ _ rel
      obtain ⟨onlyLeft, onlyRight⟩ := only
      constructor
      · intro holds
        exact ⟨(leftIh onlyLeft rel).mp holds.1, (rightIh onlyRight rel).mp holds.2⟩
      · intro holds
        exact ⟨(leftIh onlyLeft rel).mpr holds.1, (rightIh onlyRight rel).mpr holds.2⟩
  | neg inner innerIh =>
      intro only _ _ rel
      exact not_congr (innerIh only rel)
  | dia label inner innerIh =>
      intro only _ _ rel
      constructor
      · intro holds
        obtain ⟨target, step, innerHolds⟩ := holds
        obtain ⟨target', step', related⟩ :=
          effectTwin_step (effectTwin_impose label.1 rel) step
        exact ⟨target', step', (innerIh only related).mp innerHolds⟩
      · intro holds
        obtain ⟨target, step, innerHolds⟩ := holds
        obtain ⟨target', step', related⟩ :=
          effectTwin_step (effectTwin_impose label.1 (effectTwin_symm rel)) step
        exact ⟨target', step', (innerIh only (effectTwin_symm related)).mpr innerHolds⟩

/-- **Without the covariate, the query is not expressible.** Every effect-only
formula agrees on `covariateSeen` and `covariateHidden`, and the query does
not. -/
theorem effectOnly_cannot_express :
    ¬ ∃ formula, EffectOnly formula ∧ ∀ individuals,
        ladder.sat formula (.population individuals none) ↔ AdaptiveQuery individuals := by
  rintro ⟨formula, only, expresses⟩
  have agree := effectOnly_agree formula only (EffectTwin.seenHidden none)
  have holdsSeen := (expresses covariateSeen).mpr seen_query
  have holdsHidden := agree.mp holdsSeen
  exact hidden_not_query ((expresses covariateHidden).mp holdsHidden)

/-- **Expressible exactly when the covariate is readable.** The full language
of `quantities` expresses the query, by a formula that reads the treatment
atom, on the population `twoUnits`. The effect-only formulas of the same
language do not express it; the witness is the swap of that population's
natural treatments. -/
theorem expressible_exactly_when_covariate :
    (ladder.sat adaptiveFormula (.population covariateSeen none) ∧
        ∀ individuals, ladder.sat adaptiveFormula (.population individuals none) ↔
          (Mettapedia.GSLT.Causality.AdaptiveContexts.ReachesRecord (.population individuals flip) true true ∧
            Mettapedia.GSLT.Causality.AdaptiveContexts.ReachesRecord (.population individuals flip) false false)) ∧
      ¬ EffectOnly adaptiveFormula ∧
      ¬ ∃ formula, EffectOnly formula ∧ ∀ individuals,
          ladder.sat formula (.population individuals none) ↔ AdaptiveQuery individuals := by
  refine ⟨⟨(seen_satisfies).1, ?_⟩, adaptiveFormula_reads_covariate, effectOnly_cannot_express⟩
  intro individuals
  exact (adaptiveQuery_expressed individuals).trans (adaptiveQuery_iff_flip individuals)

end Mettapedia.GSLT.Causality.AdaptiveExpressibility
