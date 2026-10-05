import Mettapedia.GSLT.Causality.Hierarchy
import Mettapedia.GSLT.Logic.ObserverDetermination

/-!
# Identifiability on Pearl's ladder: the determination criterion at every rung

A set of experiments is an admissible class `F` inside the class `A` of the
interventions one reasons about.  At a rung, `F` **identifies** everything `A`
distinguishes when agreement at that rung relative to `F` already forces
agreement relative to `A`; since `F ≤ A`, the converse inclusion always holds
(`agree_antitone`).

**The criterion** (`identified_iff`).  At rung two (one intervention, then
watch) and rung three (interventions at any retained state), experiments
`F ≤ A` identify everything `A` distinguishes at that rung exactly when every
intervention of `A` preserves the `F`-relative agreement at that rung.  At rung
three this is `relEquiv_iff_iff_le_determined` read causally
(`counterfactual_identified_iff`); at rung two it rests on rung two being the
largest relation inside association that the class preserves
(`intervention_identified_iff`).

**Rung one is the bottom class** (`agree_bot_iff`).  The bottom admissible
class runs no experiment: its contexts act as the identity up to the equations
(`plug_equiv_of_bot`), and both its higher rungs are association.  So the
rung-one criterion is the criterion for `F = ⊥`: passive observation
identifies everything `A` distinguishes, at rung two or at rung three, exactly
when every intervention of `A` preserves association
(`association_identified_iff`).  Then the whole ladder collapses for `A`
(`collapse_iff`).

**Adding experimental arms** (`sup_generatedBy_identified_iff`,
`not_agree_sup_of_not_preserved`).  Adjoining arms to an experiment changes
nothing at a rung exactly when every new arm preserves the old agreement, and
one new arm that breaks it separates a pair the old experiment identified.

**Counterexamples, one per rung**, on the response-type GSLT of `Hierarchy`.
* Rung one (`rungOne_counterexample`): with no experiment, the population that
  treatment would help and the inert one agree; treating separates them, and
  treating does not preserve association.
* Rung two (`rungTwo_counterexample`): experimenting only by treating
  (`treatArm`), a naturally treated individual whom treatment helps and one who
  always shows the effect agree.  Withholding treatment separates them, and it
  is the arm that breaks the agreement.
* Rung three (`rungThree_counterexample`): with the treatment arm only, a
  naturally treated population half helped and half hurt agrees
  counterfactually with one half always and half never showing the effect.
  With every intervention the two still agree at rung two; the
  necessity-and-sufficiency query separates them at rung three, and
  withholding treatment is again the arm that breaks the agreement.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.Identifiability

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.MinimalEnablingContext
open Mettapedia.GSLT.AdmissibleContextCongruence
open Mettapedia.GSLT.Causality.Hierarchy

universe uS uContext uRule uAtom

section Criterion

variable {S : GSLT.{uS}} {rules : ContextualRules.{uContext, uRule} S}
  (observations : ContextualRules.Observations.{uAtom} S)

/-! ## Agreement respects the equations and is antitone in the class -/

theorem reductionBisimilar_respectsEquations :
    RespectsEquations (ReductionBisimilar observations) :=
  fun _ _ _ _ leftEquivalent rightEquivalent related =>
    reductionBisimilar_trans observations
      (reductionBisimilar_trans observations
        (reductionBisimilar_of_equiv observations (S.equations.iseqv.symm leftEquivalent)) related)
      (reductionBisimilar_of_equiv observations rightEquivalent)

/-- Agreement at every rung is invariant under the equations. -/
theorem agree_respectsEquations (A : AdmissibleClass rules) :
    ∀ rung : Rung, RespectsEquations (Agree A observations rung)
  | .association => reductionBisimilar_respectsEquations observations
  | .intervention => fun _ _ _ _ leftEquivalent rightEquivalent related _ admissible =>
      reductionBisimilar_respectsEquations observations
        (rules.plug_resp _ leftEquivalent) (rules.plug_resp _ rightEquivalent)
        (related admissible)
  | .counterfactual => A.relEquiv_respectsEquations observations

theorem contextualEquiv_antitone {F A : AdmissibleClass rules} (le : F ≤ A) {left right : S.Term}
    (related : A.ContextualEquiv observations left right) :
    F.ContextualEquiv observations left right :=
  fun _ admissible => related (le _ admissible)

/-- **More interventions give a finer agreement, at every rung.** -/
theorem agree_antitone {F A : AdmissibleClass rules} (le : F ≤ A) :
    ∀ (rung : Rung) {left right : S.Term},
      Agree A observations rung left right → Agree F observations rung left right
  | .association, _, _, related => related
  | .intervention, _, _, related => contextualEquiv_antitone observations le related
  | .counterfactual, _, _, related => AdmissibleClass.relEquiv_antitone observations le related

/-- Rungs two and three are preserved by every intervention of their class. -/
theorem agree_closedUnder (A : AdmissibleClass rules) {rung : Rung}
    (above : rung ≠ .association) : A.ClosedUnder (Agree A observations rung) := by
  cases rung with
  | association => exact absurd rfl above
  | intervention => exact intervention_closedUnder A observations
  | counterfactual => exact counterfactual_closedUnder A observations

/-! ## The criterion at rungs two and three -/

/-- **The determination criterion at rung two.**  Experiments `F ≤ A`
identify everything `A` distinguishes with one intervention exactly when every
intervention of `A` preserves the `F`-relative interventional agreement. -/
theorem intervention_identified_iff {F A : AdmissibleClass rules} (le : F ≤ A) :
    (∀ left right, Agree A observations .intervention left right ↔
        Agree F observations .intervention left right) ↔
      ∀ ⦃context : rules.Context⦄, A.Admissible context →
        Preserves context (Agree F observations .intervention) := by
  constructor
  · intro same context admissible left right related
    exact (same _ _).mp
      (intervention_closedUnder A observations admissible ((same _ _).mpr related))
  · intro preserved left right
    exact ⟨agree_antitone observations le .intervention,
      intervention_largest A observations
        (fun _ _ _ admissible related => preserved admissible related)
        (fun _ _ related => agree_association_of_intervention F observations related)⟩

/-- **The determination criterion at rung three**: the extension criterion
`relEquiv_iff_iff_le_determined`, read causally. -/
theorem counterfactual_identified_iff {F A : AdmissibleClass rules} (le : F ≤ A) :
    (∀ left right, Agree A observations .counterfactual left right ↔
        Agree F observations .counterfactual left right) ↔
      ∀ ⦃context : rules.Context⦄, A.Admissible context →
        Preserves context (Agree F observations .counterfactual) :=
  (AdmissibleClass.relEquiv_iff_iff_le_determined observations le).trans
    ⟨fun below context admissible => below context admissible,
      fun preserved _ admissible => preserved admissible⟩

/-- **The determination criterion, at rungs two and three.** -/
theorem identified_iff {F A : AdmissibleClass rules} (le : F ≤ A) {rung : Rung}
    (above : rung ≠ .association) :
    (∀ left right, Agree A observations rung left right ↔ Agree F observations rung left right) ↔
      ∀ ⦃context : rules.Context⦄, A.Admissible context →
        Preserves context (Agree F observations rung) := by
  cases rung with
  | association => exact absurd rfl above
  | intervention => exact intervention_identified_iff observations le
  | counterfactual => exact counterfactual_identified_iff observations le

/-! ## Rung one is the bottom class -/

/-- A context of the bottom class acts as the identity, up to the equations. -/
theorem plug_equiv_of_bot {context : rules.Context}
    (admissible : (⊥ : AdmissibleClass rules).Admissible context) (term : S.Term) :
    S.Equiv (rules.plug context term) term := by
  have generated : AdmissibleClass.GeneratedBy (∅ : Set rules.Context) context :=
    (bot_le : (⊥ : AdmissibleClass rules) ≤ AdmissibleClass.generatedBy ∅) context admissible
  clear admissible
  induction generated with
  | identity => exact rules.plug_identity term
  | generator member => exact absurd member (Set.notMem_empty _)
  | compose _ _ outer inner =>
      exact S.equations.iseqv.trans (rules.plug_compose _ _ term)
        (S.equations.iseqv.trans (rules.plug_resp _ inner) outer)

/-- Association is itself a reduction bisimulation. -/
theorem isReductionBisimulation_reductionBisimilar :
    IsReductionBisimulation observations (ReductionBisimilar observations) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro left right ⟨relation, bisimulation, related⟩ left' step
    obtain ⟨right', step', related'⟩ := bisimulation.1.1 related step
    exact ⟨right', step', relation, bisimulation, related'⟩
  · rintro left right ⟨relation, bisimulation, related⟩ right' step
    obtain ⟨left', step', related'⟩ := bisimulation.1.2 related step
    exact ⟨left', step', relation, bisimulation, related'⟩
  · rintro left right ⟨relation, bisimulation, related⟩ atom
    exact bisimulation.2 related atom

/-- The bottom class preserves association. -/
theorem bot_closedUnder_association :
    (⊥ : AdmissibleClass rules).ClosedUnder (ReductionBisimilar observations) :=
  fun _ _ _ admissible related =>
    reductionBisimilar_respectsEquations observations
      (S.equations.iseqv.symm (plug_equiv_of_bot admissible _))
      (S.equations.iseqv.symm (plug_equiv_of_bot admissible _)) related

/-- **Rung one is every rung of the bottom class**: with no experiment,
intervening and counterfactual agreement are association. -/
theorem agree_bot_iff (rung : Rung) (left right : S.Term) :
    Agree (⊥ : AdmissibleClass rules) observations rung left right ↔
      ReductionBisimilar observations left right := by
  cases rung with
  | association => exact Iff.rfl
  | intervention =>
      exact ⟨agree_association_of_intervention ⊥ observations,
        fun related _ admissible => bot_closedUnder_association observations admissible related⟩
  | counterfactual =>
      exact ⟨fun related => agree_association_of_intervention ⊥ observations
          (agree_intervention_of_counterfactual ⊥ observations related),
        fun related => (⊥ : AdmissibleClass rules).relEquiv_of_isReductionBisimulation observations
          (isReductionBisimulation_reductionBisimilar observations)
          (bot_closedUnder_association observations) related⟩

/-- **The determination criterion at rung one.**  Passive observation
identifies everything the class `A` distinguishes at a higher rung exactly
when every intervention of `A` preserves association.  It is `identified_iff`
for the bottom class. -/
theorem association_identified_iff (A : AdmissibleClass rules) {rung : Rung}
    (above : rung ≠ .association) :
    (∀ left right, Agree A observations rung left right ↔
        Agree A observations .association left right) ↔
      ∀ ⦃context : rules.Context⦄, A.Admissible context →
        Preserves context (Agree A observations .association) := by
  have bottom := identified_iff observations (bot_le : (⊥ : AdmissibleClass rules) ≤ A) above
  constructor
  · intro same context admissible left right related
    have same' : ∀ left right, Agree A observations rung left right ↔
        Agree (⊥ : AdmissibleClass rules) observations rung left right :=
      fun left right => (same left right).trans (agree_bot_iff observations rung left right).symm
    exact (agree_bot_iff observations rung _ _).mp
      (bottom.mp same' admissible ((agree_bot_iff observations rung _ _).mpr related))
  · intro preserved left right
    have preserved' : ∀ ⦃context : rules.Context⦄, A.Admissible context →
        Preserves context (Agree (⊥ : AdmissibleClass rules) observations rung) :=
      fun _ admissible _ _ related => (agree_bot_iff observations rung _ _).mpr
        (preserved admissible ((agree_bot_iff observations rung _ _).mp related))
    exact (bottom.mpr preserved' left right).trans (agree_bot_iff observations rung left right)

/-- **Collapse of the ladder.**  Association already forces counterfactual
agreement for `A` exactly when every intervention of `A` preserves
association. -/
theorem collapse_iff (A : AdmissibleClass rules) :
    A.ClosedUnder (Agree A observations .association) ↔
      ∀ left right, Agree A observations .association left right →
        Agree A observations .counterfactual left right := by
  constructor
  · intro closed left right related
    exact A.relEquiv_of_isReductionBisimulation observations
      (isReductionBisimulation_reductionBisimilar observations) closed related
  · intro collapse context left right admissible related
    exact agree_association_of_intervention A observations
      (agree_intervention_of_counterfactual A observations
        (counterfactual_closedUnder A observations admissible (collapse left right related)))

/-! ## Adding experimental arms -/

/-- **Adding arms.**  Adjoining a set of interventions to the experiments `F`
leaves agreement at rung two or three unchanged exactly when every adjoined
intervention preserves it. -/
theorem sup_generatedBy_identified_iff (F : AdmissibleClass rules) (added : Set rules.Context)
    {rung : Rung} (above : rung ≠ .association) :
    (∀ left right, Agree (F ⊔ AdmissibleClass.generatedBy added) observations rung left right ↔
        Agree F observations rung left right) ↔
      ∀ context ∈ added, Preserves context (Agree F observations rung) := by
  refine (identified_iff observations le_sup_left above).trans ⟨?_, ?_⟩
  · intro preserved context member
    exact preserved ((le_sup_right : AdmissibleClass.generatedBy added ≤ F ⊔ _) context
      (AdmissibleClass.generator_mem member))
  · intro preserved context admissible
    have below : F ⊔ AdmissibleClass.generatedBy added ≤
        AdmissibleClass.admissibleFor (Agree F observations rung)
          (agree_respectsEquations observations F rung) :=
      sup_le (fun _ admissible' _ _ related =>
          agree_closedUnder observations F above admissible' related)
        (AdmissibleClass.generatedBy_le_iff.mpr fun _ member => preserved _ member)
    exact below context admissible

/-- **One breaking arm separates.**  An adjoined intervention that sends a
pair to an `F`-inequivalent pair separates that pair once adjoined. -/
theorem not_agree_sup_of_not_preserved (F : AdmissibleClass rules) {added : Set rules.Context}
    {context : rules.Context} (member : context ∈ added) {rung : Rung}
    (above : rung ≠ .association) {left right : S.Term}
    (separated : ¬ Agree F observations rung (rules.plug context left) (rules.plug context right)) :
    ¬ Agree (F ⊔ AdmissibleClass.generatedBy added) observations rung left right := by
  intro related
  exact separated (agree_antitone observations le_sup_left rung
    (agree_closedUnder observations _ above
      ((le_sup_right : AdmissibleClass.generatedBy added ≤ F ⊔ _) context
        (AdmissibleClass.generator_mem member)) related))

end Criterion

/-! ## Counterexamples on the response-type GSLT -/

namespace ResponseControls

open Mettapedia.GSLT.Causality.Hierarchy.ResponseTypes

/-- **Experiments that only treat**: the class generated by imposing treatment. -/
def treatArm : AdmissibleClass interventions :=
  AdmissibleClass.generatedBy {some true}

theorem treatArm_admissible_iff {context : Option Bool} :
    treatArm.Admissible context ↔ context = none ∨ context = some true := by
  constructor
  · intro generated
    have closed : ∀ {setting : interventions.Context},
        AdmissibleClass.GeneratedBy (rules := interventions) {some true} setting →
          setting = none ∨ setting = some true := by
      intro setting generated
      induction generated with
      | identity => exact Or.inl rfl
      | generator member => exact Or.inr member
      | compose _ _ outer inner =>
          rcases outer with rfl | rfl <;> rcases inner with rfl | rfl <;> decide
    exact closed generated
  · rintro (rfl | rfl)
    · exact treatArm.identity_mem
    · exact AdmissibleClass.generator_mem rfl

/-! ### Matching populations by outcomes -/

/-- Stages of two populations whose individuals are matched, keeping the
natural treatment, so that matched individuals show the same outcome under
every allowed regime. -/
def outcomeMatch (allowed : Option Bool → Prop) (individuals individuals' : List (Bool × Response))
    (left right : Stage) : Prop :=
  left = right ∨
    (∃ imposed, allowed imposed ∧ left = .population individuals imposed ∧
      right = .population individuals' imposed) ∨
    (∃ imposed natural response response', allowed imposed ∧
      left = .individual natural response imposed ∧ right = .individual natural response' imposed ∧
      ∀ setting, allowed setting →
        response.outcome (setting.getD natural) = response'.outcome (setting.getD natural))

/-- Every individual of the first population has a match in the second. -/
def Matched (allowed : Option Bool → Prop) (individuals individuals' : List (Bool × Response)) :
    Prop :=
  ∀ natural response, (natural, response) ∈ individuals →
    ∃ response', (natural, response') ∈ individuals' ∧ ∀ setting, allowed setting →
      response.outcome (setting.getD natural) = response'.outcome (setting.getD natural)

theorem outcomeMatch_isReductionBisimulation {allowed : Option Bool → Prop}
    {individuals individuals' : List (Bool × Response)}
    (forth : Matched allowed individuals individuals')
    (back : Matched allowed individuals' individuals) :
    IsReductionBisimulation quantities (outcomeMatch allowed individuals individuals') := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro left right (rfl | ⟨imposed, allowedImposed, rfl, rfl⟩ |
        ⟨imposed, natural, response, response', allowedImposed, rfl, rfl, same⟩) left' step
    · exact ⟨left', step, Or.inl rfl⟩
    · cases moves_of_step step with
      | @draw _ _ natural response member =>
          obtain ⟨response', member', same⟩ := forth natural response member
          exact ⟨_, Moves.draw member', Or.inr (Or.inr ⟨imposed, natural, response, response',
            allowedImposed, rfl, rfl, same⟩)⟩
    · cases moves_of_step step
      refine ⟨_, Moves.respond, Or.inl ?_⟩
      rw [same imposed allowedImposed]
  · rintro left right (rfl | ⟨imposed, allowedImposed, rfl, rfl⟩ |
        ⟨imposed, natural, response, response', allowedImposed, rfl, rfl, same⟩) right' step
    · exact ⟨right', step, Or.inl rfl⟩
    · cases moves_of_step step with
      | @draw _ _ natural response' member' =>
          obtain ⟨response, member, same⟩ := back natural response' member'
          exact ⟨_, Moves.draw member, Or.inr (Or.inr ⟨imposed, natural, response, response',
            allowedImposed, rfl, rfl, fun setting allowedSetting =>
              (same setting allowedSetting).symm⟩)⟩
    · cases moves_of_step step
      refine ⟨_, Moves.respond, Or.inl ?_⟩
      rw [same imposed allowedImposed]
  · rintro left right (rfl | ⟨imposed, -, rfl, rfl⟩ |
        ⟨imposed, natural, response, response', -, rfl, rfl, -⟩) atom
    · exact Iff.rfl
    · cases atom <;> exact Iff.rfl
    · cases atom <;> exact Iff.rfl

theorem outcomeMatch_closedUnder {F : AdmissibleClass interventions}
    {allowed : Option Bool → Prop} {individuals individuals' : List (Bool × Response)}
    (stable : ∀ ⦃context : Option Bool⦄, F.Admissible context →
      ∀ setting, allowed setting → allowed (context.or setting)) :
    F.ClosedUnder (outcomeMatch allowed individuals individuals') := by
  rintro context left right admissible (rfl | ⟨imposed, allowedImposed, rfl, rfl⟩ |
      ⟨imposed, natural, response, response', allowedImposed, rfl, rfl, same⟩)
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨context.or imposed, stable admissible imposed allowedImposed, rfl, rfl⟩)
  · exact Or.inr (Or.inr ⟨context.or imposed, natural, response, response',
      stable admissible imposed allowedImposed, rfl, rfl, same⟩)

/-- Under one regime, every individual matches a constant individual. -/
theorem matched_toConstant (setting : Option Bool) (natural : Bool)
    {individuals : List (Bool × Response)}
    (naturals : ∀ individual ∈ individuals, individual.1 = natural) :
    Matched (· = setting) individuals [(natural, .always), (natural, .never)] := by
  intro natural' response member
  obtain rfl : natural' = natural := naturals _ member
  refine ⟨fixedCounterpart (setting.getD natural') response, ?_, ?_⟩
  · unfold fixedCounterpart
    split <;> simp
  · rintro _ rfl
    exact (fixedCounterpart_outcome _ _).symm

/-- Under one regime, every individual matches one helped or hurt by
treatment. -/
theorem matched_toMixed (setting : Option Bool) (natural : Bool)
    {individuals : List (Bool × Response)}
    (naturals : ∀ individual ∈ individuals, individual.1 = natural) :
    Matched (· = setting) individuals [(natural, .helped), (natural, .hurt)] := by
  intro natural' response member
  obtain rfl : natural' = natural := naturals _ member
  refine ⟨mixedCounterpart (setting.getD natural') response, ?_, ?_⟩
  · unfold mixedCounterpart
    split <;> simp
  · rintro _ rfl
    exact (mixedCounterpart_outcome _ _).symm

/-- The regimes reachable with the treatment arm leave a naturally treated
individual treated. -/
def KeepsTreated (setting : Option Bool) : Prop :=
  setting.getD true = true

theorem keepsTreated_stable ⦃context : Option Bool⦄ (admissible : treatArm.Admissible context)
    (setting : Option Bool) (kept : KeepsTreated setting) : KeepsTreated (context.or setting) := by
  rcases treatArm_admissible_iff.mp admissible with rfl | rfl
  · exact kept
  · rfl

/-- Naturally treated individuals matched by their outcome under treatment. -/
theorem matched_keepsTreated {individuals individuals' : List (Bool × Response)}
    (treated : ∀ individual ∈ individuals, individual.1 = true)
    (cover : ∀ response, (true, response) ∈ individuals →
      ∃ response', (true, response') ∈ individuals' ∧
        response'.outcome true = response.outcome true) :
    Matched KeepsTreated individuals individuals' := by
  intro natural response member
  obtain rfl : natural = true := treated _ member
  obtain ⟨response', member', same⟩ := cover response member
  refine ⟨response', member', fun setting kept => ?_⟩
  change setting.getD true = true at kept
  rw [kept]
  exact same.symm

/-- With the treatment arm only, naturally treated populations matched by
their outcome under treatment agree counterfactually. -/
theorem treatArm_counterfactual {individuals individuals' : List (Bool × Response)}
    (treated : ∀ individual ∈ individuals, individual.1 = true)
    (treated' : ∀ individual ∈ individuals', individual.1 = true)
    (cover : ∀ response, (true, response) ∈ individuals →
      ∃ response', (true, response') ∈ individuals' ∧
        response'.outcome true = response.outcome true)
    (cover' : ∀ response', (true, response') ∈ individuals' →
      ∃ response, (true, response) ∈ individuals ∧ response.outcome true = response'.outcome true) :
    Agree treatArm quantities .counterfactual (.population individuals none)
      (.population individuals' none) :=
  treatArm.relEquiv_of_isReductionBisimulation quantities
    (outcomeMatch_isReductionBisimulation (matched_keepsTreated treated cover)
      (matched_keepsTreated treated' cover'))
    (outcomeMatch_closedUnder keepsTreated_stable) (Or.inr (Or.inl ⟨none, rfl, rfl, rfl⟩))

/-! ### Rung one -/

/-- **Rung one.**  With no experiment the population that treatment would help
and the inert one agree; with every intervention they do not, and treating
does not preserve association. -/
theorem rungOne_counterexample :
    Agree (⊥ : AdmissibleClass interventions) quantities .intervention wouldHelp inert ∧
      ¬ Agree everyIntervention quantities .intervention wouldHelp inert ∧
      ¬ Preserves (rules := interventions) (some true)
        (Agree everyIntervention quantities .association) :=
  ⟨(agree_bot_iff quantities .intervention _ _).mpr association_wouldHelp_inert,
    not_intervention_wouldHelp_inert,
    fun preserves => not_passive_treated (preserves association_wouldHelp_inert)⟩

/-! ### Rung two -/

/-- A naturally treated individual whom treatment helps. -/
abbrev treatedHelped : Stage := .population [(true, .helped)] none

/-- A naturally treated individual who always shows the effect. -/
abbrev treatedAlways : Stage := .population [(true, .always)] none

theorem treatArm_counterfactual_helped_always :
    Agree treatArm quantities .counterfactual treatedHelped treatedAlways := by
  refine treatArm_counterfactual (by simp) (by simp) ?_ ?_
  · intro response member
    simp only [List.mem_singleton, Prod.mk.injEq, true_and] at member
    subst member
    exact ⟨.always, by simp, rfl⟩
  · intro response member
    simp only [List.mem_singleton, Prod.mk.injEq, true_and] at member
    subst member
    exact ⟨.helped, by simp, rfl⟩

/-- **Withholding treatment separates them.** -/
theorem not_intervention_helped_always :
    ¬ Agree everyIntervention quantities .intervention treatedHelped treatedAlways := by
  intro agree
  obtain ⟨relation, ⟨⟨forward, _⟩, atoms⟩, related⟩ :=
    agree (AdmissibleClass.top_admissible (rules := interventions) (some false))
  obtain ⟨drawn, drawStep, drawnRelated⟩ := forward related
    (Moves.draw (List.mem_singleton.mpr rfl) :
      Moves (.population [(true, .helped)] (some false)) (.individual true .helped (some false)))
  cases moves_of_step drawStep with
  | draw member =>
      simp only [List.mem_singleton, Prod.mk.injEq] at member
      obtain ⟨rfl, rfl⟩ := member
      obtain ⟨final, finalStep, finalRelated⟩ := forward drawnRelated
        (Moves.respond : Moves (.individual true .helped (some false)) (.record false false))
      cases moves_of_step finalStep
      have shown : false = true := (atoms finalRelated .effect).mpr rfl
      exact Bool.false_ne_true shown

/-- **Rung two.**  Experimenting only by treating, a naturally treated
individual whom treatment helps and one who always shows the effect agree;
with every intervention they do not, and withholding treatment is the arm that
breaks the agreement. -/
theorem rungTwo_counterexample :
    Agree treatArm quantities .intervention treatedHelped treatedAlways ∧
      ¬ Agree everyIntervention quantities .intervention treatedHelped treatedAlways ∧
      ¬ Preserves (rules := interventions) (some false)
        (Agree treatArm quantities .intervention) := by
  have agreeF : Agree treatArm quantities .intervention treatedHelped treatedAlways :=
    agree_intervention_of_counterfactual treatArm quantities treatArm_counterfactual_helped_always
  refine ⟨agreeF, not_intervention_helped_always, fun preserves => ?_⟩
  have identified := (intervention_identified_iff quantities
    (le_top : treatArm ≤ everyIntervention)).mpr (by
      intro context _
      rcases context with _ | _ | _
      · exact fun _ _ related =>
          intervention_closedUnder treatArm quantities treatArm.identity_mem related
      · exact preserves
      · exact fun _ _ related => intervention_closedUnder treatArm quantities
          (AdmissibleClass.generator_mem rfl) related)
  exact not_intervention_helped_always ((identified _ _).mpr agreeF)

/-! ### Rung three -/

/-- Naturally treated, half helped and half hurt by treatment. -/
abbrev treatedMixed : Stage := .population [(true, .helped), (true, .hurt)] none

/-- Naturally treated, half always and half never showing the effect. -/
abbrev treatedFixed : Stage := .population [(true, .always), (true, .never)] none

theorem treatArm_counterfactual_mixed_fixed :
    Agree treatArm quantities .counterfactual treatedMixed treatedFixed := by
  refine treatArm_counterfactual (by simp) (by simp) ?_ ?_
  · intro response member
    simp only [List.mem_cons, Prod.mk.injEq, true_and, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨.always, by simp, rfl⟩
    · exact ⟨.never, by simp, rfl⟩
  · intro response member
    simp only [List.mem_cons, Prod.mk.injEq, true_and, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨.helped, by simp, rfl⟩
    · exact ⟨.hurt, by simp, rfl⟩

/-- Under every single regime the two naturally treated populations look
alike. -/
theorem intervention_treatedMixed_treatedFixed :
    Agree everyIntervention quantities .intervention treatedMixed treatedFixed := by
  intro context _
  exact ⟨outcomeMatch (· = context.or none) [(true, .helped), (true, .hurt)]
      [(true, .always), (true, .never)],
    outcomeMatch_isReductionBisimulation (matched_toConstant _ true (by simp))
      (matched_toMixed _ true (by simp)),
    Or.inr (Or.inl ⟨context.or none, rfl, rfl, rfl⟩)⟩

theorem treatedMixed_sat_necessaryAndSufficient :
    (everyIntervention.saturated quantities).sat necessaryAndSufficient treatedMixed :=
  ⟨.individual true .helped none, Moves.draw (by simp),
    ⟨.record true true, Moves.respond, rfl⟩,
    ⟨.record false false, Moves.respond, Bool.false_ne_true⟩⟩

theorem treatedFixed_not_sat_necessaryAndSufficient :
    ¬ (everyIntervention.saturated quantities).sat necessaryAndSufficient treatedFixed := by
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

theorem not_counterfactual_treatedMixed_treatedFixed :
    ¬ Agree everyIntervention quantities .counterfactual treatedMixed treatedFixed := by
  intro agree
  have same := (everyIntervention.saturated quantities).logicallyEquivalent_of_bisimilar agree
    necessaryAndSufficient
  exact treatedFixed_not_sat_necessaryAndSufficient
    (same.mp treatedMixed_sat_necessaryAndSufficient)

/-- **Rung three.**  With the treatment arm only, the naturally treated
population half helped and half hurt agrees counterfactually with the one half
always and half never showing the effect.  With every intervention they still
agree at rung two, they differ at rung three, and withholding treatment is the
arm that breaks the counterfactual agreement. -/
theorem rungThree_counterexample :
    Agree treatArm quantities .counterfactual treatedMixed treatedFixed ∧
      Agree everyIntervention quantities .intervention treatedMixed treatedFixed ∧
      ¬ Agree everyIntervention quantities .counterfactual treatedMixed treatedFixed ∧
      ¬ Preserves (rules := interventions) (some false)
        (Agree treatArm quantities .counterfactual) := by
  refine ⟨treatArm_counterfactual_mixed_fixed, intervention_treatedMixed_treatedFixed,
    not_counterfactual_treatedMixed_treatedFixed, fun preserves => ?_⟩
  have identified := (counterfactual_identified_iff quantities
    (le_top : treatArm ≤ everyIntervention)).mpr (by
      intro context _
      rcases context with _ | _ | _
      · exact fun _ _ related =>
          counterfactual_closedUnder treatArm quantities treatArm.identity_mem related
      · exact preserves
      · exact fun _ _ related => counterfactual_closedUnder treatArm quantities
          (AdmissibleClass.generator_mem rfl) related)
  exact not_counterfactual_treatedMixed_treatedFixed
    ((identified _ _).mpr treatArm_counterfactual_mixed_fixed)

end ResponseControls

end Mettapedia.GSLT.Causality.Identifiability
