import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Boundary

/-!
# A premise over the whole store presents every question of the store

`Boundary.whole_presents_absence` presents "make `12` where `11` is absent" by one rewrite `{...rest} ⟶ {12,
...rest}` whose premise asks a relation environment of the whole store. A relation environment of the framework
is an arbitrary function of a relation's name and its instantiated arguments (`RelationEnv.tuples`). With the same
rewrite and the same proof, it presents "make `made` where `allowed` holds of the store" for **every** Boolean
predicate `allowed` on stores (`oracle_step_iff`; modulo the equations, for every predicate that does not depend
on the order of the store, `oracle_semanticStep_iff`): absence, the count of `Examples.countOne`
(`count_presented`), or any other question of the whole store.

So a presentation whose premises may ask the relation environment about the whole store is a presentation by an
oracle on the store: what it shows about absence it shows about every collect query, and it marks no limit of the format.
The boundary of `Boundary` is a boundary of presentations whose rewrites ask nothing of the store beyond what they
match.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Oracle

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv applyPremisesWithEnv premiseStepWithEnv relationQueryStep
  matchRelationArgs matchRelationArgument)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises NoncontextualPremises
  step_iff_rootStep_of_noncontextualRules RootStep)
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (matchPatternForRule_eq_syntactic)
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution (applyBindingsForRule_eq_syntactic)
open Mettapedia.OSLF.Framework.TypeSynthesis (langSemanticReducesUsing)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationEquiv StepModuloEquations)
open NamesOnTheStep (Expr)

/-- **An arbitrary question of the whole store**, as a relation environment. -/
def guardRelation (allowed : List Pattern → Bool) : RelationEnv where
  tuples relation arguments :=
    if relation = "allowed" then
      match arguments with
      | [.collection .hashBag elements none] => if allowed elements then [arguments] else []
      | _ => []
    else []

/-- **Make `made` where the store is allowed**, with the whole store in the premise's scope. -/
def guardedMake (made : List Expr) : RewriteRule where
  name := "GuardedMake"
  typeContext := [("rest", .bag (.base "Row"))]
  premises := [.relationQuery "allowed" [.fvar "rest"]]
  left := besideRest []
  right := besideRest made

/-- The language of that one rewrite, over the presentation's sorts and constructors. -/
def oracleStore (made : List Expr) : LanguageDef where
  name := "GuardedByTheWholeStore"
  types := ["Nat", "Row", "Store"]
  terms := rowFormers ++ [storeFormer]
  equations := []
  rewrites := [guardedMake made]

variable (allowed : List Pattern → Bool) (made : List Expr)

theorem premises_oracle (elements : List Pattern) :
    applyPremisesWithEnv (guardRelation allowed) (oracleStore made) (guardedMake made).premises
        [("rest", .collection .hashBag elements none)] =
      if allowed elements then [[("rest", .collection .hashBag elements none)]] else [] := by
  by_cases holds : allowed elements = true
  · simp [applyPremisesWithEnv, guardedMake, premiseStepWithEnv, relationQueryStep, guardRelation,
      Mettapedia.OSLF.NativeTypes.GeneratedLogic.builtinRelationTuples_single, applyBindings, holds,
      matchRelationArgs, matchRelationArgument, Bindings.lookup, mergeBindings]
  · simp [applyPremisesWithEnv, guardedMake, premiseStepWithEnv, relationQueryStep, guardRelation,
      Mettapedia.OSLF.NativeTypes.GeneratedLogic.builtinRelationTuples_single, applyBindings, holds]

theorem oracle_noncontextual : ∀ rule ∈ (oracleStore made).rewrites, NoncontextualPremises rule.premises := by
  intro rule member
  rw [List.mem_singleton.mp member]
  exact .relationQuery .nil

/-- **The primitive step of the oracle language from a store**: make `made` where `allowed` holds. -/
theorem oracle_step_iff {rows : List Expr} {target : Pattern} :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.Step (engineBasePremises (guardRelation allowed))
        (oracleStore made) (storeCode rows) target ↔
      allowed (rows.map rowCode) = true ∧ target = storeCode (made ++ rows) := by
  rw [step_iff_rootStep_of_noncontextualRules (oracle_noncontextual made)]
  constructor
  · rintro ⟨rule, member, initial, matched, final, premises, rfl⟩
    obtain rfl := List.mem_singleton.mp member
    rw [matchPatternForRule_eq_syntactic, matchPattern_iff_matchRel] at matched
    change MatchRel (.collection .hashBag [] (some "rest")) (.collection .hashBag (rows.map rowCode) none) initial
      at matched
    cases matched with
    | collection _ bagMatch =>
        cases bagMatch
        rw [premises_oracle] at premises
        by_cases holds : allowed (rows.map rowCode) = true
        · rw [if_pos holds, List.mem_singleton] at premises
          subst premises
          refine ⟨holds, ?_⟩
          rw [applyBindingsForRule_eq_syntactic, applyRuleBindings_eq_applyBindings _ _
            (ruleDepthAligned_of_binderFree _ (binderFree_besideRest _) (binderFree_besideRest _))]
          change applyBindings _ (besideRest made) = _
          rw [applyBindings_besideRest]
          simp [storeCode]
        · rw [if_neg holds] at premises
          exact absurd premises List.not_mem_nil
  · rintro ⟨holds, rfl⟩
    refine ⟨guardedMake made, List.mem_singleton_self _,
      [("rest", .collection .hashBag (rows.map rowCode) none)], ?_,
      [("rest", .collection .hashBag (rows.map rowCode) none)], ?_, ?_⟩
    · rw [matchPatternForRule_eq_syntactic, matchPattern_iff_matchRel]
      exact .collection (by decide) .nilRest
    · rw [premises_oracle, if_pos holds]
      exact List.mem_singleton_self _
    · rw [applyBindingsForRule_eq_syntactic, applyRuleBindings_eq_applyBindings _ _
        (ruleDepthAligned_of_binderFree _ (binderFree_besideRest _) (binderFree_besideRest _))]
      change applyBindings _ (besideRest made) = _
      rw [applyBindings_besideRest]
      simp [storeCode]

theorem oracle_equations : (oracleStore made).equations = [] := rfl

theorem oracle_noAlgebra : (oracleStore made).hasAlgebraDeclarations = false := rfl

theorem oracle_formers : rowFormers ⊆ (oracleStore made).terms := List.subset_append_left _ _

theorem oracle_store : storeFormer ∈ (oracleStore made).terms :=
  List.mem_append_right _ (List.mem_singleton_self _)

/-- **The framework's step of the oracle language**, for a question that does not depend on the order of the
store: make `made` where `allowed` holds, up to the equations. -/
theorem oracle_semanticStep_iff (invariant : ∀ l l' : List Pattern, l.Perm l' → allowed l = allowed l')
    {rows : List Expr} {target : Pattern} :
    langSemanticReducesUsing (guardRelation allowed) (oracleStore made) (storeCode rows) target ↔
      allowed (rows.map rowCode) = true ∧
        EquationEquiv (engineBasePremises (guardRelation allowed)) (oracleStore made)
          (storeCode (made ++ rows)) target := by
  change StepModuloEquations (engineBasePremises (guardRelation allowed)) (oracleStore made)
    (storeCode rows) target ↔ _
  constructor
  · rintro ⟨redex, contractum, before, step, after⟩
    obtain ⟨arranged, rfl, perm⟩ := storeCode_of_equationEquiv (oracle_equations made)
      (oracle_noAlgebra made) before
    obtain ⟨holds, rfl⟩ := (oracle_step_iff allowed made).mp step
    refine ⟨(invariant _ _ (perm.map rowCode)).trans holds, ?_⟩
    exact Relation.EqvGen.trans _ _ _
      (equationEquiv_storeCode_of_perm (oracle_formers made) (oracle_store made) (perm.append_left made))
      after
  · rintro ⟨holds, after⟩
    exact ⟨storeCode rows, storeCode (made ++ rows), Relation.EqvGen.refl _,
      (oracle_step_iff allowed made).mpr ⟨holds, rfl⟩, after⟩

/-! ## The count of `Examples.countOne` (make `12` where exactly one `11` is present) -/

/-- Exactly one row `11`. -/
def exactlyOneEleven (elements : List Pattern) : Bool := decide (elements.count (rowCode (.sym 11)) = 1)

theorem exactlyOneEleven_invariant (l l' : List Pattern) (perm : l.Perm l') :
    exactlyOneEleven l = exactlyOneEleven l' := by
  simp [exactlyOneEleven, perm.count_eq]

/-- **The count step is presented by the same device**: from a store, the oracle language steps exactly when the
store holds exactly one `11`, to the store with a `12` added. -/
theorem count_presented {rows : List Expr} {target : Pattern} :
    langSemanticReducesUsing (guardRelation exactlyOneEleven) (oracleStore [.sym 12]) (storeCode rows) target ↔
      rows.count (.sym 11) = 1 ∧
        EquationEquiv (engineBasePremises (guardRelation exactlyOneEleven)) (oracleStore [.sym 12])
          (storeCode (.sym 12 :: rows)) target := by
  rw [oracle_semanticStep_iff exactlyOneEleven [.sym 12] exactlyOneEleven_invariant]
  have counted : (rows.map rowCode).count (rowCode (.sym 11)) = rows.count (.sym 11) :=
    List.count_map_of_injective rows rowCode rowCode_injective (.sym 11)
  simp [exactlyOneEleven, counted]

#print axioms premises_oracle
#print axioms oracle_step_iff
#print axioms oracle_semanticStep_iff
#print axioms count_presented

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Oracle
