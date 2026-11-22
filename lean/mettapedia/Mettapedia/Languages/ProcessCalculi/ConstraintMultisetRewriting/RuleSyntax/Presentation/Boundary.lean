import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Spatial

/-!
# Where presentation without premises stops

**Absence is not presented by premise-free rewrites beside a rest.** Read on the composition terms of
`StoreComposition` through their leaves, the step of every presented program, under every reading, is closed
under parallel composition (`onTerms_parClosed`, from `Language.semanticStep_beside`; the rewrites of `present`
have no premise). So by the tree's `NullsOnTheStep.Composition.parClosed_not_absence` it is never the absence step
(`presented_not_absence`). On stores of configurations: no presented program has the generated possibility of the
absence program `Examples.spawn` (`absence_not_presented`).

**A premise over the whole store is an oracle.** A relation premise asks the framework's relation environment
(`RelationEnv.tuples`), which is an arbitrary function of the relation's name and its instantiated arguments.
The language `wholeStore` has one rewrite, `{...rest} ⟶ {12, ...rest}`, whose premise asks such a relation of the
whole store, "no row of this bag is `11`" (`absenceRelation`). Its step on stores is exactly "make `12` where `11`
is absent" (`whole_semanticStep_iff`), so read on composition terms it is the absence step
(`whole_presents_absence`), and it is not closed under parallel composition (`whole_not_parClosed`). The same
device presents every yes/no question of the store (`Oracle.oracle_step_iff`; the count of `Examples.countOne`,
`Oracle.count_presented`): it marks no limit of the format. The limit this module proves is a limit of
presentations whose rewrites ask nothing of the store beyond what they match: premise-free ones here, and ones
whose premises are the builtin equality on open bags and on matched terms (`Schematic.Boundary`).

**A guard or tell over a caller's unknown needs the knowledge in the term.** Two states of `RuleSyntax.step`
with the same present rows and labels, one with the knowledge `x = 5` and one without, are told apart by the step:
the guard `x₁ = 5`, reading the row `x`, is admitted at the first and refused at the second
(`knowledge_decides`). A term that records only the rows cannot present that step, whatever premises its rewrites
ask; a tell that binds a caller's unknown (`RuleSyntax.Examples.answer_binds_caller`) changes only the knowledge,
so its effect is visible only in a term that carries the knowledge.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv applyPremisesWithEnv premiseStepWithEnv relationQueryStep
  matchRelationArgs matchRelationArgument)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises NoncontextualPremises
  step_iff_rootStep_of_noncontextualRules RootStep)
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (matchPatternForRule_eq_syntactic)
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution (applyBindingsForRule_eq_syntactic)
open Mettapedia.OSLF.Framework.TypeSynthesis (langSemanticReducesUsing langDiamondUsing)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationEquiv StepModuloEquations)
open NamesOnTheStep (Expr)
open NamesOnTheStep.IssuingControls (ground Conf)
open LogicOverTheStep.ProgramAdequacy (program)
open LogicOverTheStep.StepSpan (Succ)
open NullsOnTheStep.Composition (ParClosed AbsentReduces AbsentStep parClosed_not_absence unionOf)
open OneFrame (bodies)

/-! ## Rewrites beside a rest are closed under parallel composition -/

/-- **A presented step read on composition terms**, through their leaves. -/
def onTerms (relEnv : RelationEnv) (L : LanguageDef) (t t' : StoreComposition.Term Expr) : Prop :=
  langSemanticReducesUsing relEnv L (storeCode t.leaves) (storeCode t'.leaves)

variable {R : Reading} {rules : List (Rule Rows)} {relEnv : RelationEnv}

/-- **The step of every presented program is closed under parallel composition.** -/
theorem onTerms_parClosed : ParClosed (onTerms relEnv (presentWith R rules)) :=
  fun _ _ u step => semanticStep_beside u.leaves step

/-- **No presented program steps as the absence step**: the corollary of
`NullsOnTheStep.Composition.parClosed_not_absence`, for every reading and every program. -/
theorem presented_not_absence (absent made : Expr) :
    ¬ ∀ t t', onTerms relEnv (presentWith R rules) t t' ↔ AbsentReduces absent made t t' :=
  parClosed_not_absence onTerms_parClosed absent made

/-- **No presented program has the generated possibility of the absence program**, for every reading and
every program: wherever the presented language steps from the empty store it also steps beside the row `11`,
and `spawn` does not. -/
theorem absence_not_presented (R : Reading) (rules : List (Rule Rows)) :
    ¬ ∀ C : Conf, Trivial C.equations →
      ((langDiamondUsing relEnv (presentWith R rules) (Examples.everything relEnv _)).1 (storeOf Prod.fst C) ↔
        ∃ C', Succ (program ground Prod.fst (bodies {r | r ∈ [Examples.spawn]})) C C') := by
  intro exact
  have atEmpty := (exact Examples.emptyConf (fun _ member => absurd member List.not_mem_nil)).mpr
    spawn_fires_alone
  rw [Examples.storeOf_emptyConf] at atEmpty
  obtain ⟨r, member, holds, rest, split, -⟩ := (diamond_storeCode_iff _ _).mp atEmpty
  have empty := List.append_eq_nil_iff.mp split.eq_nil
  apply spawn_refused_beside
  refine (exact (unionOf Examples.emptyConf elevenConf) (fun _ member => absurd member List.not_mem_nil)).mp ?_
  rw [storeOf_union_eleven]
  refine (diamond_storeCode_iff _ _).mpr ⟨r, member, holds, [.sym 11], ?_, trivial⟩
  simp only [empty.1, List.nil_append]
  exact List.Perm.refl _

/-! ## A premise over the whole store presents absence, as it presents every question of the store -/

/-- **"No row of this bag is `11`"**, as a relation environment: a decision on the bag, by an arbitrary function
of the framework's relation environments (`Oracle.guardRelation` is the general form). -/
def absenceRelation : RelationEnv where
  tuples relation arguments :=
    if relation = "noEleven" then
      match arguments with
      | [.collection .hashBag elements none] => if rowCode (.sym 11) ∈ elements then [] else [arguments]
      | _ => []
    else []

/-- **Make `12` where `11` is absent, with the whole store in scope**: the rest is the whole store, and the
premise asks the relation of it. -/
def spawnWhole : RewriteRule where
  name := "SpawnWhole"
  typeContext := [("rest", .bag (.base "Row"))]
  premises := [.relationQuery "noEleven" [.fvar "rest"]]
  left := besideRest []
  right := besideRest [.sym 12]

/-- The language of that one rewrite, over the same sorts and constructors. -/
def wholeStore : LanguageDef where
  name := "AbsenceWithTheWholeStore"
  types := ["Nat", "Row", "Store"]
  terms := rowFormers ++ [storeFormer]
  equations := []
  rewrites := [spawnWhole]

theorem premises_whole (elements : List Pattern) :
    applyPremisesWithEnv absenceRelation wholeStore spawnWhole.premises
        [("rest", .collection .hashBag elements none)] =
      if rowCode (.sym 11) ∈ elements then [] else [[("rest", .collection .hashBag elements none)]] := by
  by_cases eleven : rowCode (.sym 11) ∈ elements
  · simp [applyPremisesWithEnv, spawnWhole, premiseStepWithEnv, relationQueryStep, absenceRelation,
      Mettapedia.OSLF.NativeTypes.GeneratedLogic.builtinRelationTuples_single, applyBindings, eleven]
  · simp [applyPremisesWithEnv, spawnWhole, premiseStepWithEnv, relationQueryStep, absenceRelation,
      Mettapedia.OSLF.NativeTypes.GeneratedLogic.builtinRelationTuples_single, applyBindings, eleven,
      matchRelationArgs, matchRelationArgument, Bindings.lookup, mergeBindings]

theorem whole_noncontextual : ∀ rule ∈ wholeStore.rewrites, NoncontextualPremises rule.premises := by
  intro rule member
  rw [List.mem_singleton.mp member]
  exact .relationQuery .nil

/-- **The primitive step of the whole-store language from a store**: make `12` where `11` is absent. -/
theorem whole_step_iff {rows : List Expr} {target : Pattern} :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.Step (engineBasePremises absenceRelation) wholeStore (storeCode rows)
        target ↔
      Expr.sym 11 ∉ rows ∧ target = storeCode (.sym 12 :: rows) := by
  rw [step_iff_rootStep_of_noncontextualRules whole_noncontextual]
  constructor
  · rintro ⟨rule, member, initial, matched, final, premises, rfl⟩
    obtain rfl := List.mem_singleton.mp member
    rw [matchPatternForRule_eq_syntactic, matchPattern_iff_matchRel] at matched
    change MatchRel (.collection .hashBag [] (some "rest")) (.collection .hashBag (rows.map rowCode) none) initial
      at matched
    cases matched with
    | collection _ bagMatch =>
        cases bagMatch
        rw [premises_whole] at premises
        by_cases eleven : rowCode (.sym 11) ∈ rows.map rowCode
        · rw [if_pos eleven] at premises
          exact absurd premises List.not_mem_nil
        · rw [if_neg eleven, List.mem_singleton] at premises
          subst premises
          refine ⟨fun inside => eleven (List.mem_map_of_mem inside), ?_⟩
          rw [applyBindingsForRule_eq_syntactic, applyRuleBindings_eq_applyBindings _ _
            (ruleDepthAligned_of_binderFree _ (binderFree_besideRest _) (binderFree_besideRest _))]
          change applyBindings _ (besideRest [.sym 12]) = _
          rw [applyBindings_besideRest]
          rfl
  · rintro ⟨absent, rfl⟩
    have notEleven : rowCode (.sym 11) ∉ rows.map rowCode := fun inside => by
      obtain ⟨e, member, same⟩ := List.mem_map.mp inside
      rw [rowCode_injective same] at member
      exact absent member
    refine ⟨spawnWhole, List.mem_singleton_self _, [("rest", .collection .hashBag (rows.map rowCode) none)], ?_,
      [("rest", .collection .hashBag (rows.map rowCode) none)], ?_, ?_⟩
    · rw [matchPatternForRule_eq_syntactic, matchPattern_iff_matchRel]
      exact .collection (by decide) .nilRest
    · rw [premises_whole, if_neg notEleven]
      exact List.mem_singleton_self _
    · rw [applyBindingsForRule_eq_syntactic, applyRuleBindings_eq_applyBindings _ _
        (ruleDepthAligned_of_binderFree _ (binderFree_besideRest _) (binderFree_besideRest _))]
      change applyBindings _ (besideRest [.sym 12]) = _
      rw [applyBindings_besideRest]
      rfl

theorem whole_equations : wholeStore.equations = [] := rfl

theorem whole_noAlgebra : wholeStore.hasAlgebraDeclarations = false := rfl

theorem whole_formers : rowFormers ⊆ wholeStore.terms := List.subset_append_left _ _

theorem whole_store : storeFormer ∈ wholeStore.terms := List.mem_append_right _ (List.mem_singleton_self _)

/-- **The framework's step of the whole-store language**: make `12` where `11` is absent, up to the equations. -/
theorem whole_semanticStep_iff {rows : List Expr} {target : Pattern} :
    langSemanticReducesUsing absenceRelation wholeStore (storeCode rows) target ↔
      Expr.sym 11 ∉ rows ∧
        EquationEquiv (engineBasePremises absenceRelation) wholeStore (storeCode (.sym 12 :: rows)) target := by
  change StepModuloEquations (engineBasePremises absenceRelation) wholeStore (storeCode rows) target ↔ _
  constructor
  · rintro ⟨redex, contractum, before, step, after⟩
    obtain ⟨arranged, rfl, perm⟩ := storeCode_of_equationEquiv whole_equations whole_noAlgebra before
    obtain ⟨absent, rfl⟩ := whole_step_iff.mp step
    refine ⟨fun inside => absent (perm.subset inside), ?_⟩
    exact Relation.EqvGen.trans _ _ _
      (equationEquiv_storeCode_of_perm whole_formers whole_store (perm.cons _)) after
  · rintro ⟨absent, after⟩
    exact ⟨storeCode rows, storeCode (.sym 12 :: rows), Relation.EqvGen.refl _,
      whole_step_iff.mpr ⟨absent, rfl⟩, after⟩

/-- **The whole-store language presents absence, by an oracle premise**: read on composition terms, its step is
exactly the absence step of `11` making `12`. Its premise asks a relation environment of the whole store; the
same device presents every yes/no question of the store (`Oracle.oracle_step_iff`). -/
theorem whole_presents_absence (t t' : StoreComposition.Term Expr) :
    onTerms absenceRelation wholeStore t t' ↔ AbsentReduces (.sym 11) (.sym 12) t t' := by
  unfold onTerms AbsentReduces AbsentStep
  rw [whole_semanticStep_iff, equationEquiv_storeCode_iff whole_equations whole_noAlgebra whole_formers whole_store,
    StoreComposition.Term.heat_eq_leaves, StoreComposition.Term.heat_eq_leaves, Multiset.mem_coe]
  apply and_congr_right
  intro _
  rw [← Multiset.coe_singleton, Multiset.coe_add, Multiset.coe_eq_coe]
  exact ⟨fun perm => perm.symm.trans (List.perm_append_singleton _ _).symm,
    fun perm => (List.perm_append_singleton _ _).symm.trans perm.symm⟩

/-- **And it has no parallel context rule**: its step is not closed under parallel composition. -/
theorem whole_not_parClosed : ¬ ParClosed (onTerms absenceRelation wholeStore) := by
  intro closed
  have here : onTerms absenceRelation wholeStore .unit (.atom (.sym 12)) :=
    (whole_presents_absence _ _).mpr ⟨by simp, by simp⟩
  have beside := (whole_presents_absence _ _).mp (closed _ _ (.atom (.sym 11)) here)
  exact beside.1 (by simp)

/-! ## The knowledge decides guards over a caller's unknown -/

open RuleSyntax.Examples (X E demo openRequest boundRequest guardFiring everywhere guardFive_admitted)

/-- **The same firing, at two states with the same rows and labels, admitted at one and refused at the other**:
the guard `x₁ = 5` reads the row `x`; the knowledge `x = 5` decides it. -/
theorem knowledge_decides :
    openRequest.present = boundRequest.present ∧ openRequest.label = boundRequest.label ∧
      (step X ℕ E demo).Admits (s := boundRequest) (guardFiring 5 (Or.inr (Or.inr (Or.inl rfl)))) ∧
      ¬ (step X ℕ E demo).Admits (s := openRequest) (guardFiring 5 (Or.inr (Or.inr (Or.inl rfl)))) := by
  refine ⟨rfl, rfl, guardFive_admitted, ?_⟩
  intro admitted
  obtain ⟨-, -, -, -, checks, -⟩ := (admits_iff _).mp admitted
  have known : (guardFiring 5 (Or.inr (Or.inr (Or.inl rfl)))).information X openRequest =
      [(.var 1, RuleSyntax.Examples.x)] := rfl
  have solved : X.Models (a := PUnit.unit) (b := PUnit.unit) (everywhere 7)
      ((guardFiring 5 (Or.inr (Or.inr (Or.inl rfl)))).information X openRequest) := by
    rw [known]
    intro e inside
    rw [List.mem_singleton.mp inside]
    rfl
  have holds := checks (.equal (.var 1) (RuleSyntax.Examples.c 5)) (List.mem_singleton_self _) PUnit.unit _ solved
  have seven : (Mettapedia.Logic.LP.Term.const (7 : ℕ) : Mettapedia.Logic.LP.Term RuleSyntax.Controls.atoms) =
      (Mettapedia.Logic.LP.Term.const (5 : ℕ) : Mettapedia.Logic.LP.Term RuleSyntax.Controls.atoms) := holds
  exact absurd (Mettapedia.Logic.LP.Term.const.inj seven) (by decide)

#print axioms onTerms_parClosed
#print axioms presented_not_absence
#print axioms absence_not_presented
#print axioms premises_whole
#print axioms whole_step_iff
#print axioms whole_semanticStep_iff
#print axioms whole_presents_absence
#print axioms whole_not_parClosed
#print axioms knowledge_decides

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation
