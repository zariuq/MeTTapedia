import Mettapedia.OSLF.Framework.InitialModalSchema

/-!
# Initial syntax and exact replay do not imply consistency

The free OSLF formula algebra and the least rule closure solve two structural
problems: they give syntax without accidental equations and derivability
without extra rule applications.  Neither construction constrains which rules
an author may supply.  Consequently, exact replay is compatible with both a
consistent empty calculus and a calculus containing a direct rule for bottom.

This module records that boundary as executable positive and negative
controls.  Consistency begins only after a rule set is shown sound in a model
that does not satisfy bottom.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.InitialityConsistencySeparation

open Mettapedia.OSLF.Formula
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.InitialModalSchema
open Mettapedia.Logic
open Mettapedia.GSLT.LanguageDef.KernelAuthority

/-! ## Consistency is a property of the authored rules -/

/-- Syntactic consistency relative to the distinguished OSLF bottom formula. -/
def Consistent (rules : List OSLFFormula → OSLFFormula → Prop) : Prop :=
  ¬ Derives rules .bot

/-- A calculus with no rule applications. -/
def emptyRules : List OSLFFormula → OSLFFormula → Prop :=
  fun _ _ => False

/-- Positive control: least closure adds no theorem when there are no rules. -/
theorem emptyRules_consistent : Consistent emptyRules := by
  intro derivesBottom
  exact Derives.least (fun _ => False)
    (by intro _ _ impossible _; exact impossible.elim) derivesBottom

/-- The deliberately inconsistent one-rule calculus `──────── / ⊥`. -/
def bottomRules : List OSLFFormula → OSLFFormula → Prop :=
  fun hypotheses conclusion => hypotheses = [] ∧ conclusion = .bot

/-- Negative control: least closure faithfully retains an authored bottom
rule; leastness is not consistency. -/
theorem bottomRules_derives_bottom : Derives bottomRules .bot := by
  refine Derives.node (rules := bottomRules) [] OSLFFormula.bot ?_ ?_
  · exact ⟨rfl, rfl⟩
  · simp

theorem bottomRules_inconsistent : ¬ Consistent bottomRules :=
  fun consistent => consistent bottomRules_derives_bottom

/-! ## Exact replay also retains an inconsistent rule -/

/-- A complete decidable witness for the direct bottom rule. -/
def bottomRuleWitness : RuleWitness bottomRules where
  W := Unit
  isInstance := fun _ hypotheses conclusion =>
    decide (hypotheses = [] ∧ conclusion = .bot)
  sound := by
    intro _ hypotheses conclusion accepted
    change decide (hypotheses = [] ∧ conclusion = OSLFFormula.bot) = true at accepted
    change hypotheses = [] ∧ conclusion = OSLFFormula.bot
    exact of_decide_eq_true accepted
  complete := by
    intro hypotheses conclusion rule
    change hypotheses = [] ∧ conclusion = OSLFFormula.bot at rule
    exact ⟨(), decide_eq_true rule⟩

abbrev bottomChecker := replayChecker bottomRuleWitness

def bottomCertificate : Derivation OSLFFormula bottomRuleWitness.W :=
  .node .bot () 0 Fin.elim0

/-- Exact checking means exact agreement with the authored rules—even when
those rules derive bottom. -/
theorem bottomCertificate_accepted :
    bottomChecker.check .bot bottomCertificate = true := by
  decide +kernel

theorem bottomChecker_exact :
    bottomChecker.Authority (Derives bottomRules) :=
  replayChecker_authority bottomRuleWitness

/-! ## A separating model is the missing consistency ingredient -/

/-- The ordinary local rule-soundness obligation used by
`replay_sound_in_every_model`. -/
def RulesSound (rules : List OSLFFormula → OSLFFormula → Prop)
    (meaning : OSLFFormula → Prop) : Prop :=
  ∀ hypotheses conclusion, rules hypotheses conclusion →
    (∀ hypothesis ∈ hypotheses, meaning hypothesis) → meaning conclusion

/-- No interpretation that rejects bottom can validate the direct bottom
rule.  This is precisely why consistency requires an independent model, not
only initial syntax or exact replay. -/
theorem bottomRules_not_sound_in_bottom_rejecting_model
    (meaning : OSLFFormula → Prop) (rejectsBottom : ¬ meaning .bot) :
    ¬ RulesSound bottomRules meaning := by
  intro sound
  exact rejectsBottom (sound [] .bot ⟨rfl, rfl⟩ (by simp))

/-! ## Independent model qualification -/

/-- A semantic qualification of an authored rule set.  Its meaning predicate
is supplied independently of certificate replay; every rule preserves that
meaning, and the distinguished bottom formula is not meaningful.

This is the additional datum needed to turn exact syntactic replay into a
consistency result. -/
structure ModelQualification
    (rules : List OSLFFormula → OSLFFormula → Prop) where
  Meaning : OSLFFormula → Prop
  rulesSound : RulesSound rules Meaning
  rejectsBottom : ¬ Meaning .bot

/- The record states the mathematical qualification obligations.  As with an
arbitrary semantic structure, it does not establish the historical provenance
of a concrete `Meaning`; that must be justified by the profile supplying it. -/

namespace ModelQualification

variable {rules : List OSLFFormula → OSLFFormula → Prop}

/-- Every derivable formula is valid in an independently supplied sound
model.  This is leastness of derivability, not a property of a checker. -/
theorem derives_sound (qualification : ModelQualification rules)
    {formula : OSLFFormula} (derivation : Derives rules formula) :
    qualification.Meaning formula :=
  Derives.least qualification.Meaning qualification.rulesSound derivation

/-- A bottom-rejecting model of all authored rules separates bottom from the
least rule closure. -/
theorem consistent (qualification : ModelQualification rules) :
    Consistent rules := by
  intro derivesBottom
  exact qualification.rejectsBottom
    (qualification.derives_sound derivesBottom)

/-- Any sound checker for derivability rejects every purported certificate
of bottom once the rule set has an independent bottom-rejecting model.
Certificate completeness is unnecessary for this rejection direction. -/
theorem checker_rejects_bottom
    {Certificate : Type*}
    (checker : Checker OSLFFormula Certificate)
    (checkerSound : checker.Sound (Derives rules))
    (qualification : ModelQualification rules)
    (certificate : Certificate) :
    checker.check .bot certificate = false := by
  cases accepted : checker.check .bot certificate with
  | false => rfl
  | true =>
      exact False.elim (qualification.rejectsBottom
        (qualification.derives_sound
          (checkerSound .bot certificate accepted)))

/-- Exact replay authority is more than enough for universal bottom
certificate rejection once semantic qualification is present. -/
theorem authority_rejects_bottom
    {Certificate : Type*}
    (checker : Checker OSLFFormula Certificate)
    (authority : checker.Authority (Derives rules))
    (qualification : ModelQualification rules)
    (certificate : Certificate) :
    checker.check .bot certificate = false :=
  checker_rejects_bottom checker authority.sound qualification certificate

end ModelQualification

/-! ### Positive and adversarial controls -/

 /-- An empty reduction relation for the positive semantic control. -/
def emptyRelation : Pattern → Pattern → Prop :=
  fun _ _ => False

/-- An atom interpretation in which no atomic proposition holds. -/
def emptyAtoms : AtomSem :=
  fun _ _ => False

/-- Genuine OSLF satisfaction in the empty relation/atom model. -/
def emptyModelMeaning (formula : OSLFFormula) : Prop :=
  ∀ state, sem emptyRelation emptyAtoms formula state

/-- Positive semantic canary: top holds at every state. -/
theorem emptyModelMeaning_top : emptyModelMeaning .top := by
  intro state
  trivial

/-- Negative semantic canary: an uninterpreted atom does not hold at every
state. -/
theorem emptyModelMeaning_atom_not :
    ¬ emptyModelMeaning (.atom "uninterpreted") := by
  intro meaningful
  exact meaningful (.fvar "state")

/-- The empty calculus has a concrete OSLF model qualification.  There are no
rules whose soundness must be established, and OSLF bottom is false at every
state. -/
def emptyRulesQualification : ModelQualification emptyRules where
  Meaning := emptyModelMeaning
  rulesSound := by
    intro _ _ impossible _
    exact impossible.elim
  rejectsBottom := by
    intro meaningful
    exact meaningful (.fvar "state")

/-- A deliberately small executable checker for the empty calculus. -/
def emptyChecker : Checker OSLFFormula Unit where
  check := fun _ _ => false

/-- The always-rejecting checker is exact for the empty calculus because the
least closure of an empty rule set contains no formulas. -/
theorem emptyChecker_exact :
    emptyChecker.Authority (Derives emptyRules) where
  sound := by
    intro claim certificate accepted
    simp [emptyChecker] at accepted
  complete := by
    intro claim derives
    exact (Derives.least (fun _ => False)
      (by intro _ _ impossible _; exact impossible.elim) derives).elim

/-- Positive executable control: every certificate is rejected for bottom in
the independently qualified empty calculus. -/
theorem emptyChecker_rejects_bottom (certificate : Unit) :
    emptyChecker.check .bot certificate = false :=
  emptyRulesQualification.authority_rejects_bottom
    emptyChecker emptyChecker_exact certificate

/-- Negative control: the direct-bottom calculus cannot carry an independent
model qualification.  Exact replay did not manufacture one. -/
theorem bottomRules_has_no_modelQualification :
    ¬ Nonempty (ModelQualification bottomRules) := by
  rintro ⟨qualification⟩
  exact qualification.rejectsBottom
    (qualification.derives_sound bottomRules_derives_bottom)

/-- The two structural universal properties coexist with inconsistency:
formula syntax still distinguishes top from bottom, and replay remains exact,
while the authored calculus derives bottom. -/
theorem initiality_and_exact_replay_do_not_imply_consistency :
    (¬ Identifies formulas .top .bot) ∧
      bottomChecker.Authority (Derives bottomRules) ∧
      Derives bottomRules .bot :=
  ⟨formulas_distinguishes_top_bot, bottomChecker_exact,
    bottomRules_derives_bottom⟩

#print axioms emptyRules_consistent
#print axioms bottomRules_derives_bottom
#print axioms bottomCertificate_accepted
#print axioms bottomChecker_exact
#print axioms bottomRules_not_sound_in_bottom_rejecting_model
#print axioms ModelQualification.derives_sound
#print axioms ModelQualification.consistent
#print axioms ModelQualification.checker_rejects_bottom
#print axioms ModelQualification.authority_rejects_bottom
#print axioms emptyModelMeaning_top
#print axioms emptyModelMeaning_atom_not
#print axioms emptyChecker_exact
#print axioms emptyChecker_rejects_bottom
#print axioms bottomRules_has_no_modelQualification
#print axioms initiality_and_exact_replay_do_not_imply_consistency

end Mettapedia.OSLF.Framework.InitialityConsistencySeparation
