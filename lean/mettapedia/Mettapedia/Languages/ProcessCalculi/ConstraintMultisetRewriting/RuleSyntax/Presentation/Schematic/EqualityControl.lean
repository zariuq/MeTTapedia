import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic.Knowledge

/-!
# Control: the relation environment must add nothing to the builtin equality

The theorems of the presentation with unknowns ask the relation environment to add no tuple to the builtin
equality (`noEq`). Without that, the guards are no longer decided by the equality: the environment
`eqEverything` relates every pair, and with it the rule `failingGuard` (guard `4 = 5`, make `6`) steps from the
empty store (`failingGuard_steps`), while `RuleSyntax.step` admits no firing of it there (`failingGuard_refused`)
and the presentation under an environment that adds nothing to the equality does not step
(`failingGuard_no_step`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic.EqualityControl

open Mettapedia.Logic.LP
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv premiseStepWithEnv builtinRelationTuples matchRelationArgument)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises PremiseAt PremisesAt StepAt)
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (matchPatternForRule matchPatternForRule_eq_syntactic)
open Mettapedia.OSLF.Framework.TypeSynthesis (langSemanticReducesUsing)
open Interface (Frames)
open NamesOnTheStep (Expr)
open Presentation.Schematic.Examples (sym)
open Presentation.Schematic.Controls (emptyState)
open Presentation.Schematic.Knowledge (mem_relationQuery)

/-- **A relation environment that relates every pair by the equality.** -/
def eqEverything : RelationEnv where
  tuples relation arguments := if relation = "eq" then [arguments] else []

/-- **Guard `4 = 5`, make `6`**: a ground rule of the fragment whose guard fails. -/
def failingGuard : SRule := ⟨PUnit.unit, ⟨[], [], [], [.equal (sym 4) (sym 5)], [sym 6]⟩, []⟩

/-- The program of that rule. -/
def failingProgram : List SRule := [failingGuard]

theorem failingGuard_fragment : ∀ r ∈ failingProgram, RangeRestrictedPositive r := by
  intro r member
  rw [List.mem_singleton.mp member]
  refine ⟨rfl, rfl, fun t inWritten z vars => ?_⟩
  simp only [written, failingGuard, List.map_nil, List.flatMap_cons, List.flatMap_nil, checkTerms,
    List.nil_append, List.append_nil, List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at inWritten
  rcases inWritten with rfl | rfl | rfl <;> exact absurd vars not_mem_vars_const

/-- **With an environment that relates every pair, the failing guard passes**, and the presented language steps
from the empty store to `{6}`. -/
theorem failingGuard_steps :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.Step (engineBasePremises eqEverything) (presentSchematic failingProgram)
      (storeCode []) (storeCode [.sym 6]) := by
  let initial : Bindings := [("rest", .collection .hashBag [] none)]
  have matched : initial ∈ matchPatternForRule (presentSchematic failingProgram) (schematicRewrite 0 failingGuard)
      (storeCode []) := by
    rw [matchPatternForRule_eq_syntactic, matchPattern_iff_matchRel]
    exact .collection (by decide) .nilRest
  have found :
      initial.find? (·.1 == "rest") = some ("rest", .collection .hashBag (([] : List Expr).map rowCode) none) := by
    simp [initial]
  have selfFour : [] ∈ matchRelationArgument initial (termCode (sym 4)) (rowCode (.sym 4)) := by
    rw [matchRelationArgument_other initial _ (fun _ different => by simp [termCode, sym] at different),
      matchPattern_iff_matchRel]
    exact matchRel_self_rowCode (.sym 4)
  have selfFive : [] ∈ matchRelationArgument initial (termCode (sym 5)) (rowCode (.sym 5)) := by
    rw [matchRelationArgument_other initial _ (fun _ different => by simp [termCode, sym] at different),
      matchPattern_iff_matchRel]
    exact matchRel_self_rowCode (.sym 5)
  have premise : initial ∈ premiseStepWithEnv eqEverything (presentSchematic failingProgram) initial
      (equationPremise (sym 4, sym 5)) := by
    refine mem_relationQuery.mpr ⟨[rowCode (.sym 4), rowCode (.sym 5)], ?_, [], ?_, mergeBindings_nil initial⟩
    · simp only [List.map_cons, List.map_nil]
      rw [show termCode (sym 4) = rowCode (.sym 4) from rfl, show termCode (sym 5) = rowCode (.sym 5) from rfl,
        applyBindings_rowCode, applyBindings_rowCode]
      exact List.mem_append_right _ (by simp [eqEverything])
    · exact mem_matchRelationArgs_cons.mpr ⟨[], selfFour, initial, mergeBindings_nil initial, [],
        mem_matchRelationArgs_one.mpr ⟨selfFive, initial, mergeBindings_nil initial⟩, mergeBindings_nil []⟩
  refine ⟨1, .rule (List.mem_singleton_self _) matched (.cons (premiseAt_engine_iff.mpr premise) (.nil initial)) ?_⟩
  rw [applyBindingsForRule_schematic]
  exact right_instantiated initial (fun _ => .sym 0) [sym 6] [] found fun p inProduce z vars => by
    rw [List.mem_singleton.mp inProduce] at vars
    exact absurd vars not_mem_vars_const

/-- **Under an environment that adds nothing to the equality, the presented language does not step there.** -/
theorem failingGuard_no_step {relEnv : RelationEnv} (noEq : ∀ args, relEnv.tuples "eq" args = []) (target : Pattern) :
    ¬ langSemanticReducesUsing relEnv (presentSchematic failingProgram) (storeCode []) target := by
  intro step
  obtain ⟨r, member, θ, rest, fires, -⟩ := (semanticStep_storeCode_iff noEq failingGuard_fragment).mp step
  rw [List.mem_singleton.mp member] at fires
  have equal := fires.equations (sym 4, sym 5) (List.mem_append_right _ (by simp [failingGuard, guardOf]))
  exact absurd (Expr.sym.inj equal) (by decide)

/-- **`RuleSyntax.step` admits no firing of the failing guard at the empty store.** -/
theorem failingGuard_refused :
    ¬ ∃ g : Firing ℕ E {r | r ∈ failingProgram} emptyState.frame,
      (schematicStep ℕ failingProgram).Admits (s := emptyState) g := by
  rintro ⟨g, admitted⟩
  obtain ⟨-, -, -, solvable, checks, -⟩ := (admits_iff g).mp admitted
  obtain ⟨σ, solved⟩ := (Frames.ofSubstitution_solvable_iff A _).mp solvable
  have isRule : g.rule = failingGuard := List.mem_singleton.mp g.member
  obtain ⟨rule, member, ext, opening, selection, seen⟩ := g
  obtain rfl : rule = failingGuard := isRule
  have holds := checks (Check.map opening.applyTerm (.equal (sym 4) (sym 5))) (List.mem_singleton_self _)
    PUnit.unit σ solved
  have equal : σ.applyTerm (opening.applyTerm (sym 4)) = σ.applyTerm (opening.applyTerm (sym 5)) := holds
  exact absurd (RowConstant.sym.inj (Term.const.inj equal)) (by decide)

#print axioms failingGuard_fragment
#print axioms failingGuard_steps
#print axioms failingGuard_no_step
#print axioms failingGuard_refused

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic.EqualityControl
