import Mettapedia.GSLT.Compilation.Uniform.QueryRulesOnTheStep
import Mettapedia.OSLF.MeTTaIL.NoncontextualPremiseCheck

/-!
# Closure of the ordered data fragment

A query returns data on data, and the next match retains both the data in
the earlier bindings and the vector tails already matched. If a right side
uses only rests that its left side matches as vector tails, the authored
step preserves the whole ordered data carrier. This condition gives a
uniform carrier for the executable compiler.

A variable matched against an ordinary argument need not hold a vector.
Using such a value in a rest position may leave an open rest in the result.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Compilation.Uniform.OrderedDataCarrier

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec (matchPattern_sound BindingsExtends mergeBindings_subsumed_left)
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
  (Step engineBasePremises step_iff_rootStep_of_noncontextualRules check_noncontextualRules_iff)
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (matchPatternForRule_eq_syntactic)
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution (applyBindingsForRuleUsing_empty_eq_applyBindings)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions (RuleWithCondition)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic (Tm)
open OrderedMatching
open QueryPremises (Flows DataRows mem_premises_cons mem_query arguments_data)

variable {relEnv : RelationEnv} {language : LanguageDef} {inputs : String → ℕ → Bool}

private theorem data_after_premises (dataRows : DataRows relEnv language)
    {rests bound last : List String} {premises : List Premise}
    (flows : Flows inputs rests bound premises last) :
    ∀ {seed final : Bindings}, DataOn seed → Settled seed rests →
      final ∈ applyPremisesWithEnv relEnv language premises seed →
      DataOn final ∧ Settled final rests := by
  induction flows with
  | nil =>
      intro seed final onData settled found
      have same : final = seed := by simpa [applyPremisesWithEnv] using found
      subst final
      exact ⟨onData, settled⟩
  | @query bound last relation arguments premises orderedArguments _ staysSettled flows ih =>
      intro seed final onData settled found
      obtain ⟨next, asked, later⟩ := (mem_premises_cons ..).mp found
      obtain ⟨row, offered, extension, matched, merged⟩ := mem_query.mp asked
      have rowData := dataRows relation _ row offered
        (instanceList_data onData _ orderedArguments fun rest inside => settled rest (staysSettled rest inside))
      have retained : BindingsExtends seed next := fun _ _ held => mergeBindings_subsumed_left merged held
      exact ih (DataOn.merge merged onData (arguments_data orderedArguments rowData matched))
        (settled.extends_ retained) later

/-- The compiled source has a uniform data carrier when every result rest
is captured as a vector rest on the left. No mode law is needed for closure. -/
theorem carrier {program : List (RuleWithCondition ℕ Tm)}
    (compiled : QueryRulesOnTheStep.compile inputs language = .ok program)
    (dataRows : DataRows relEnv language)
    (rests : ∀ rule ∈ language.rewrites, ∀ rest ∈ restNames rule.right, rest ∈ restNames rule.left) :
    QueryRulesOnTheStep.DataCarrier relEnv language (fun term => isData term = true) where
  data := fun _ data => data
  closed := by
    intro before after data stepped
    have wellFormed (rule : RewriteRule) (member : rule ∈ language.rewrites) :
        QueryPremises.QueryRule inputs rule :=
      ((QueryRulesOnTheStep.compile_origins compiled).1 rule member).elim fun _ found => found.2.source
    rw [step_iff_rootStep_of_noncontextualRules fun rule member => by
      obtain ⟨_, flows, _⟩ := (wellFormed rule member).flows
      exact flows.noncontextual] at stepped
    obtain ⟨rule, member, initial, matched, final, found, made⟩ := stepped
    rw [matchPatternForRule_eq_syntactic] at matched
    have shape := wellFormed rule member
    obtain ⟨_, flows, _⟩ := shape.flows
    have related := matchPattern_sound matched
    obtain ⟨_, settled⟩ := match_binds rule.left shape.left related
    obtain ⟨finalData, finalSettled⟩ := data_after_premises dataRows flows
      (match_data rule.left shape.left data related) settled found
    have applied := (applyBindingsForRuleUsing_empty_eq_applyBindings rule final shape.aligned).symm.trans made
    rw [← applied]
    exact instance_data finalData rule.right shape.right fun rest memberOfRest =>
      finalSettled rest (rests rule member rest memberOfRest)

namespace Controls

def counterexampleRule : RewriteRule :=
  { name := "unmatched-rest"
    typeContext := []
    premises := []
    left := .apply "A" [.fvar "tail"]
    right := .collection .vec [] (some "tail") }

def counterexample : LanguageDef :=
  { LanguageDef.empty "unmatched-result-rest" with rewrites := [counterexampleRule] }

def ordinaryArgument : Pattern := .apply "A" [.apply "unit" []]

def openResult : Pattern := .collection .vec [] (some "tail")

theorem compiled_counterexample :
    (match QueryRulesOnTheStep.compile (fun _ _ => true) counterexample with
      | .ok _ => true
      | .error _ => false) = true := by
  decide +kernel

theorem counterexample_steps :
    Step (engineBasePremises RelationEnv.empty) counterexample ordinaryArgument openResult := by
  change Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing RelationEnv.empty
    counterexample ordinaryArgument openResult
  apply (Mettapedia.OSLF.Framework.TypeSynthesis.mem_rootFrontier_iff_langReducesUsing
    RelationEnv.empty counterexample ((check_noncontextualRules_iff _).mp (by decide +kernel))
    ordinaryArgument openResult).mp
  decide +kernel

theorem data_is_not_closed :
    isData ordinaryArgument = true ∧ isData openResult = false ∧
      Step (engineBasePremises RelationEnv.empty) counterexample ordinaryArgument openResult :=
  ⟨rfl, rfl, counterexample_steps⟩

end Controls

#print axioms carrier
#print axioms Controls.data_is_not_closed

end Mettapedia.GSLT.Compilation.Uniform.OrderedDataCarrier
