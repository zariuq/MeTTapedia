import Mettapedia.GSLT.LanguageDef.IRRunView
import Mettapedia.OSLF.MeTTaIL.MatchSpec

/-!
# Equation-bearing canary for representation run views

This four-constant presentation has no rewrites and two authored equations,
`A = B` and `C = D`.  Its run protocol recognizes only `B` and returns `C`.
Consequently the raw run relation cannot connect `A` to `D`, while the sole
semantic run view must connect them by `E ; Run ; E`.

The example is deliberately independent of any process calculus or parser.
It checks that equality belongs to the generic representation interface
rather than being recovered by a language-specific implementation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IRRunViewEquationCanary

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.IRPass
open Mettapedia.GSLT.LanguageDef.IRRunView
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.Syntax

private def resultSort : TypeDecl := TypeDecl.plain "IRRunViewCanary:Result"

private def constant (label : String) : GrammarRule :=
  { label
    category := "IRRunViewCanary:Result"
    params := []
    syntaxPattern := [] }

private def a : Pattern := .apply "IRRunViewCanary:A" []
private def b : Pattern := .apply "IRRunViewCanary:B" []
private def c : Pattern := .apply "IRRunViewCanary:C" []
private def d : Pattern := .apply "IRRunViewCanary:D" []

private def equationAB : Equation :=
  { name := "IRRunViewCanary:AB"
    typeContext := []
    premises := []
    left := a
    right := b }

private def equationCD : Equation :=
  { name := "IRRunViewCanary:CD"
    typeContext := []
    premises := []
    left := c
    right := d }

private def language : LanguageDef :=
  { name := "IRRunViewEquationCanary"
    types := [resultSort]
    terms := [
      constant "IRRunViewCanary:A",
      constant "IRRunViewCanary:B",
      constant "IRRunViewCanary:C",
      constant "IRRunViewCanary:D"]
    equations := [equationAB, equationCD]
    rewrites := [] }

private theorem language_validate : language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorEquationsAndRewrites
  all_goals
    simp [language, resultSort, constant, equationAB, equationCD, a, b, c, d,
      LanguageDef.typeNames, TypeDecl.plain, LanguageDef.validateEquation,
      LanguageDef.validatePatternConstructors,
      LanguageDef.validateRulePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, Pattern.constructorRefs,
      Pattern.constructorRefsList, Pattern.freeFvarNames,
      Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, TermParam.typeExpr]

private def ir : IRLanguage :=
  IRLanguage.ofValidated ⟨language, language_validate⟩

/-- The protocol itself recognizes only the literal representative `B`; its
closure under equations is supplied by `runView`, not hidden in the protocol. -/
private def protocol : RunProtocol where
  entry := _root_.id
  exit := fun state => if state = b then some c else none

private theorem equationAB_mem : equationAB ∈ language.equations := by
  simp [language]

private theorem equationCD_mem : equationCD ∈ language.equations := by
  simp [language]

private theorem nullary_matches (label : String) :
    ([] : Bindings) ∈ matchPattern (.apply label []) (.apply label []) := by
  rw [Mettapedia.OSLF.MeTTaIL.MatchSpec.matchPattern_iff_matchRel]
  exact Mettapedia.OSLF.MeTTaIL.MatchSpec.MatchRel.apply
    Mettapedia.OSLF.MeTTaIL.MatchSpec.MatchArgsRel.nil rfl

theorem a_equiv_b : ir.semantics.Equiv a b := by
  apply equationInstance_equivalent
  refine ⟨0, EquationInstanceAt.forward (equation := equationAB)
    (initialBindings := []) (finalBindings := []) equationAB_mem
    (nullary_matches _) (PremisesAt.nil _) ?_⟩
  simp [equationAB, b, applyBindings]

theorem c_equiv_d : ir.semantics.Equiv c d := by
  apply equationInstance_equivalent
  refine ⟨0, EquationInstanceAt.forward (equation := equationCD)
    (initialBindings := []) (finalBindings := []) equationCD_mem
    (nullary_matches _) (PremisesAt.nil _) ?_⟩
  simp [equationCD, d, applyBindings]

/-- With no authored rewrite, the represented GSLT has no operational step.
Its equations remain present and nontrivial. -/
private theorem no_semantics_step (source target : Pattern) :
    ¬ ir.semantics.Step source target := by
  rintro ⟨redex, contractum, _, primitive, _⟩
  rcases primitive with ⟨_, primitive⟩
  cases primitive with
  | rule ruleMember _ _ _ =>
      change _ ∈ ([] : List RewriteRule) at ruleMember
      exact List.not_mem_nil ruleMember

private theorem reaches_eq {source target : Pattern}
    (run : reaches ir source target) : source = target := by
  rcases Relation.ReflTransGen.cases_head run with equal | ⟨next, step, _⟩
  · exact equal
  · exact (no_semantics_step _ _ step).elim

theorem raw_b_to_c : RawRun ir protocol b c := by
  exact ⟨b, Relation.ReflTransGen.refl, by simp [protocol]⟩

/-- Negative control: the protocol does not secretly canonicalize its input
or output, so the raw run really cannot see the equivalent endpoints. -/
theorem not_raw_a_to_d : ¬ RawRun ir protocol a d := by
  rintro ⟨final, run, exits⟩
  have equal : a = final := reaches_eq run
  subst final
  simp [protocol, a, b] at exits

/-- Positive control: the generic run view exposes the hidden run by changing
representative at both endpoints. -/
theorem saturated_a_to_d : (runView ir protocol).Step a d := by
  exact ⟨b, c, a_equiv_b, raw_b_to_c, c_equiv_d⟩

theorem saturation_is_observable :
    (runView ir protocol).Step a d ∧ ¬ RawRun ir protocol a d :=
  ⟨saturated_a_to_d, not_raw_a_to_d⟩

#print axioms a_equiv_b
#print axioms c_equiv_d
#print axioms not_raw_a_to_d
#print axioms saturated_a_to_d
#print axioms saturation_is_observable

end Mettapedia.GSLT.LanguageDef.IRRunViewEquationCanary
