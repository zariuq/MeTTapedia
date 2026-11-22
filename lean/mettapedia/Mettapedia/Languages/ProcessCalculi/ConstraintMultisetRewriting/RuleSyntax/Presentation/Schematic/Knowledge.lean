import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic.Boundary
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.Calculi

/-!
# The knowledge in the term, and why its rewrites cannot keep the parallel context rule

`Boundary.knowledge_needed` shows that a tell on a caller's unknown needs the knowledge in the term. Here the
knowledge is put in the term: a configuration is one bag of items (`configurationTerm`), a row item `Row(t)` for
each present row and an equation item `Eq(l, r)` for each equation of the knowledge, the caller's unknowns as data
(`dataCode`: `Var n`, not a metavariable). The tell program `Boundary.tellRule` (read `y`, tell `y = 5`, make `9`)
is presented by one rewrite (`tellKnowledgeRewrite`):

  `{Row(y), ...rest} ⟶ {Row(y), Row(9), Eq(y, 5), ...rest}` under the premise "the equations of the rest and
  `Eq(y, 5)` are jointly solvable" (`solvabilityEnv`).

That premise asks a relation environment about the whole rest: it is an oracle in the sense of
`Presentation.Oracle`, not a premise of the class of `presentSchematic`.

* **It presents the switch** (`knowledge_presents_switch`): at the term of a row labelled by the caller's `x` it
  steps, as `RuleSyntax.step` fires (`Boundary.tellFiring_admitted`); at the term of the same row beside the
  equation `x = 6` it does not step, as the step refuses (`Boundary.toldSix_refused`).
* **So its step is switched off by a parallel component** (`knowledge_switched_off`: the second term is the first
  beside the item `Eq(x, 6)`), and it is not closed under putting items beside (`knowledge_not_closed`).
* **No relation closed beside is that step** (`knowledge_no_context_rule`, the instance of
  `ParallelClosed.not_iff_of_switchedOff`): every presentation whose step is closed under parallel composition, as
  a parallel context rule makes it, differs from it at that pair. The knowledge in the term can be presented,
  by an oracle premise over the rest, and then the parallel context rule is lost; a presentation that keeps the
  context rule cannot present a tell on a shared unknown. Over first-order terms the same switch already separates
  the step from every presentation with a parallel context rule under uniform translations
  (`ParallelClosed.PositiveTell`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic.Knowledge

open Mettapedia.Logic.LP
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv premiseStepWithEnv relationQueryStep builtinRelationTuples
  matchRelationArgs matchRelationArgument)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises PremiseAt PremisesAt StepAt)
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (matchPatternForRule matchPatternForRule_eq_syntactic)
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution (applyBindingsForRule applyBindingsForRule_eq_syntactic)
open NullsOnTheStep.ParallelClosed (ClosedBeside SwitchedOffBeside not_iff_of_switchedOff
  not_closedBeside_of_switchedOff)
open NamesOnTheStep (Expr)
open Presentation.Schematic.Examples (x sym)
open Presentation.Schematic.Boundary (tellRule tellProgram openCaller toldSix tellFiring tellFiring_admitted
  toldSix_refused)

/-! ## Terms with the knowledge -/

/-- **The data code of a term**: its formers as constructors, and each unknown as data, `Var n`. -/
def dataCode : Tm → Pattern
  | .var n => .apply "Var" [Pattern.unary "Zero" "Succ" n]
  | .const (.sym k) => .apply "Sym" [Pattern.unary "Zero" "Succ" k]
  | .const (.name n) => .apply "Name" [Pattern.unary "Zero" "Succ" n]
  | .app .app ts => .apply "App" [dataCode (ts head), dataCode (ts tail)]
  | .app .code ts => .apply "Code" [dataCode (ts body)]

theorem dataCode_injective : Function.Injective dataCode := by
  intro first
  induction first with
  | var n =>
      intro second same
      cases second with
      | var m => exact congrArg Term.var (numeral_injective (List.cons.inj (Pattern.apply.inj same).2).1)
      | const c => cases c <;> exact absurd (Pattern.apply.inj same).1 (by decide)
      | app g us => cases g <;> exact absurd (Pattern.apply.inj same).1 (by decide)
  | const c =>
      intro second same
      cases c with
      | sym k =>
          cases second with
          | var _ => exact absurd (Pattern.apply.inj same).1 (by decide)
          | const c' =>
              cases c' with
              | sym j =>
                  have equal := numeral_injective (List.cons.inj (Pattern.apply.inj same).2).1
                  rw [equal]
              | name _ => exact absurd (Pattern.apply.inj same).1 (by decide)
          | app g us => cases g <;> exact absurd (Pattern.apply.inj same).1 (by decide)
      | name k =>
          cases second with
          | var _ => exact absurd (Pattern.apply.inj same).1 (by decide)
          | const c' =>
              cases c' with
              | sym _ => exact absurd (Pattern.apply.inj same).1 (by decide)
              | name j =>
                  have equal := numeral_injective (List.cons.inj (Pattern.apply.inj same).2).1
                  rw [equal]
          | app g us => cases g <;> exact absurd (Pattern.apply.inj same).1 (by decide)
  | app f ts ih =>
      intro second same
      cases f with
      | app =>
          cases second with
          | var _ => exact absurd (Pattern.apply.inj same).1 (by decide)
          | const c => cases c <;> exact absurd (Pattern.apply.inj same).1 (by decide)
          | app g us =>
              cases g with
              | app =>
                  have arguments := List.cons.inj (Pattern.apply.inj same).2
                  have first := ih head arguments.1
                  have second := ih tail (List.cons.inj arguments.2).1
                  refine congrArg (Term.app (σ := rowSig) RowFunction.app) (funext fun i => ?_)
                  rcases fin_app i with rfl | rfl
                  · exact first
                  · exact second
              | code => exact absurd (Pattern.apply.inj same).1 (by decide)
      | code =>
          cases second with
          | var _ => exact absurd (Pattern.apply.inj same).1 (by decide)
          | const c => cases c <;> exact absurd (Pattern.apply.inj same).1 (by decide)
          | app g us =>
              cases g with
              | app => exact absurd (Pattern.apply.inj same).1 (by decide)
              | code =>
                  have only := ih body (List.cons.inj (Pattern.apply.inj same).2).1
                  refine congrArg (Term.app (σ := rowSig) RowFunction.code) (funext fun i => ?_)
                  rw [fin_code i]
                  exact only

theorem applyBindings_apply_eq (b : Bindings) (c : String) (arguments : List Pattern) :
    applyBindings b (.apply c arguments) = .apply c (arguments.map (applyBindings b)) := by
  simp only [applyBindings]

/-- A data code binds nothing and is fixed by every instantiation. -/
theorem applyBindings_dataCode (b : Bindings) : ∀ t : Tm, applyBindings b (dataCode t) = dataCode t
  | .var n => by simp [dataCode, applyBindings]
  | .const (.sym k) => applyBindings_rowCode b (.sym k)
  | .const (.name n) => applyBindings_rowCode b (.name n)
  | .app .app ts => by
      simp [dataCode, applyBindings, applyBindings_dataCode b (ts head), applyBindings_dataCode b (ts tail)]
  | .app .code ts => by
      simp [dataCode, applyBindings, applyBindings_dataCode b (ts body)]

theorem binderFree_dataCode : ∀ t : Tm, binderFree (dataCode t) = true
  | .var n => by
      have numeral : binderFree (Pattern.unary "Zero" "Succ" n) = true := by
        have named := binderFree_rowCode (.name n)
        simp only [rowCode, binderFree, binderFreeList, Bool.and_true] at named
        exact named
      simp [dataCode, binderFree, binderFreeList, numeral]
  | .const (.sym k) => binderFree_rowCode (.sym k)
  | .const (.name n) => binderFree_rowCode (.name n)
  | .app .app ts => by
      simp [dataCode, binderFree, binderFreeList, binderFree_dataCode (ts head), binderFree_dataCode (ts tail)]
  | .app .code ts => by
      simp [dataCode, binderFree, binderFreeList, binderFree_dataCode (ts body)]

/-- A row item. -/
def rowItem (t : Tm) : Pattern := .apply "Row" [dataCode t]

/-- An equation item. -/
def eqItem (e : Tm × Tm) : Pattern := .apply "Eq" [dataCode e.1, dataCode e.2]

/-- A bag of items. -/
def bag (items : List Pattern) : Pattern := .collection .hashBag items none

/-- **A configuration as one bag**: its rows and its knowledge, side by side. -/
def configurationTerm (rows : List Tm) (knowledge : EquationStore Tm) : Pattern :=
  bag (rows.map rowItem ++ knowledge.map eqItem)

theorem eqItem_injective : Function.Injective eqItem := by
  intro first second same
  have arguments := List.cons.inj (Pattern.apply.inj same).2
  exact Prod.ext (dataCode_injective arguments.1) (dataCode_injective (List.cons.inj arguments.2).1)

/-! ## Joint solvability as a relation environment -/

/-- **The equations among some items are jointly solvable.** -/
def JointlySolvable (items : List Pattern) : Prop :=
  ∃ σ : Subst rowSig, ∀ e : Tm × Tm, eqItem e ∈ items → σ.applyTerm e.1 = σ.applyTerm e.2

/-- **Joint solvability of the rest with one more equation**, as a relation environment: a decision on the whole
rest, an oracle in the sense of `Presentation.Oracle`. It adds nothing to the builtin equality. -/
noncomputable def solvabilityEnv : RelationEnv where
  tuples relation arguments := by
    classical
    exact if relation = "solvable" then
      match arguments with
      | [.collection .hashBag items none, item] => if JointlySolvable (item :: items) then [arguments] else []
      | _ => []
    else []

theorem solvabilityEnv_holds {items : List Pattern} {item : Pattern} (holds : JointlySolvable (item :: items)) :
    solvabilityEnv.tuples "solvable" [bag items, item] = [[bag items, item]] := by
  simp [solvabilityEnv, bag, holds]

theorem solvabilityEnv_fails {items : List Pattern} {item : Pattern} (fails : ¬ JointlySolvable (item :: items)) :
    solvabilityEnv.tuples "solvable" [bag items, item] = [] := by
  simp [solvabilityEnv, bag, fails]

theorem builtin_solvable (L : LanguageDef) (arguments : List Pattern) :
    builtinRelationTuples L "solvable" arguments = [] := by
  simp [builtinRelationTuples]

theorem mem_relationQuery {relEnv : RelationEnv} {L : LanguageDef} {b res : Bindings} {relation : String}
    {arguments : List Pattern} :
    res ∈ premiseStepWithEnv relEnv L b (.relationQuery relation arguments) ↔
      ∃ tuple ∈ builtinRelationTuples L relation (arguments.map (applyBindings b)) ++
          relEnv.tuples relation (arguments.map (applyBindings b)),
        ∃ bPrem ∈ matchRelationArgs b arguments tuple, mergeBindings b bPrem = some res := by
  simp only [premiseStepWithEnv, relationQueryStep, List.mem_flatMap, List.mem_filterMap]

/-! ## The presentation of the tell program with the knowledge in the term -/

/-- The equation the rule tells, as a pattern over its metavariable `y`. -/
def toldPattern : Pattern := .apply "Eq" [.fvar "y", dataCode (sym 5)]

/-- **Read `y`, tell `y = 5`, make `9`, under joint solvability of the rest with `y = 5`.** -/
def tellKnowledgeRewrite : RewriteRule where
  name := "TellWithKnowledge"
  typeContext := [("rest", .bag (.base "Item"))]
  premises := [.relationQuery "solvable" [.fvar "rest", toldPattern]]
  left := .collection .hashBag [.apply "Row" [.fvar "y"]] (some "rest")
  right := .collection .hashBag [.apply "Row" [.fvar "y"], rowItem (sym 9), toldPattern] (some "rest")

/-- The language of that rewrite. -/
def knowledgeLanguage : LanguageDef where
  name := "TellWithTheKnowledgeInTheTerm"
  types := ["Item"]
  terms := []
  equations := []
  rewrites := [tellKnowledgeRewrite]

theorem tellKnowledge_aligned : ruleDepthAligned tellKnowledgeRewrite = true :=
  ruleDepthAligned_of_binderFree _ rfl (by simp [tellKnowledgeRewrite, toldPattern, rowItem, binderFree,
    binderFreeList, binderFree_dataCode])

/-- The step of the presentation, with the oracle environment. -/
abbrev knowledgeStep (p q : Pattern) : Prop :=
  Mettapedia.OSLF.MeTTaIL.ContextualStep.Step (engineBasePremises solvabilityEnv) knowledgeLanguage p q

theorem solvable_alone : JointlySolvable [eqItem (x, sym 5)] := by
  refine ⟨fun _ => sym 5, fun e inside => ?_⟩
  rw [List.mem_singleton] at inside
  rw [eqItem_injective inside]
  rfl

theorem not_solvable_beside : ¬ JointlySolvable [eqItem (x, sym 5), eqItem (x, sym 6)] := by
  rintro ⟨σ, solved⟩
  have five : σ.applyTerm x = sym 5 := solved (x, sym 5) List.mem_cons_self
  have six : σ.applyTerm x = sym 6 := solved (x, sym 6) (List.mem_cons_of_mem _ List.mem_cons_self)
  have same : (sym 5 : Tm) = sym 6 := five.symm.trans six
  exact absurd (RowConstant.sym.inj (Term.const.inj same)) (by decide)

/-- **The presentation steps at the term of the caller's row alone.** -/
theorem knowledge_steps_alone :
    knowledgeStep (bag [rowItem x]) (bag [rowItem x, rowItem (sym 9), eqItem (x, sym 5)]) := by
  let initial : Bindings := [("rest", bag []), ("y", dataCode x)]
  have headMatch : MatchRel (.apply "Row" [.fvar "y"]) (rowItem x) [("y", dataCode x)] :=
    .apply (.cons .fvar .nil (mergeBindings_nil _)) rfl
  have restAbsent : [("y", dataCode x)].find? (·.1 == "rest") = none := by simp
  have merged : mergeBindings [("y", dataCode x)] [("rest", bag [])] = some initial := by
    rw [mergeBindings_cons_none [] restAbsent]
    rfl
  have matched : initial ∈ matchPatternForRule knowledgeLanguage tellKnowledgeRewrite (bag [rowItem x]) := by
    rw [matchPatternForRule_eq_syntactic, matchPattern_iff_matchRel]
    exact .collection (by decide) (.cons 0 (by simp) headMatch .nilRest merged)
  have restFound : initial.find? (·.1 == "rest") = some ("rest", bag []) := by simp [initial]
  have yFound : initial.find? (·.1 == "y") = some ("y", dataCode x) := by simp [initial]
  have told : applyBindings initial toldPattern = eqItem (x, sym 5) := by
    rw [toldPattern, applyBindings_apply_eq, List.map_cons, List.map_cons, List.map_nil,
      applyBindings_fvar_some yFound, applyBindings_dataCode]
    rfl
  have h1 : [] ∈ matchRelationArgument initial (.fvar "rest") (bag []) := by
    rw [matchRelationArgument_fvar_bound _ restFound, if_pos rfl]
    exact List.mem_singleton_self _
  have toldMatch : MatchRel toldPattern (eqItem (x, sym 5)) [("y", dataCode x)] :=
    .apply (.cons .fvar (.cons (matchRel_self_rowCode (.sym 5)) .nil (mergeBindings_nil [])) rfl) rfl
  have h2 : [("y", dataCode x)] ∈ matchRelationArgument initial toldPattern (eqItem (x, sym 5)) := by
    rw [matchRelationArgument_other initial _ (fun _ different => by cases different), matchPattern_iff_matchRel]
    exact toldMatch
  have keep : mergeBindings initial [("y", dataCode x)] = some initial :=
    (mergeBindings_cons_some [] yFound rfl).trans (mergeBindings_nil initial)
  have premise : initial ∈ premiseStepWithEnv solvabilityEnv knowledgeLanguage initial
      (.relationQuery "solvable" [.fvar "rest", toldPattern]) := by
    refine mem_relationQuery.mpr ⟨[bag [], eqItem (x, sym 5)], ?_, [("y", dataCode x)], ?_, keep⟩
    · rw [List.map_cons, List.map_cons, List.map_nil, applyBindings_fvar_some restFound, told, builtin_solvable,
        List.nil_append, solvabilityEnv_holds solvable_alone]
      exact List.mem_singleton_self _
    · exact mem_matchRelationArgs_cons.mpr ⟨[], h1, initial, mergeBindings_nil initial, [("y", dataCode x)],
        mem_matchRelationArgs_one.mpr ⟨h2, initial, keep⟩, rfl⟩
  refine ⟨1, .rule (List.mem_singleton_self _) matched (.cons (.relationQuery premise) (.nil initial)) ?_⟩
  rw [applyBindingsForRule_eq_syntactic, applyRuleBindings_eq_applyBindings _ _ tellKnowledge_aligned]
  show applyBindings initial (.collection .hashBag [.apply "Row" [.fvar "y"], rowItem (sym 9), toldPattern]
    (some "rest")) = _
  rw [applyBindings_collection, restResolution_bound restFound]
  show Pattern.collection .hashBag ([applyBindings initial (.apply "Row" [.fvar "y"]),
    applyBindings initial (rowItem (sym 9)), applyBindings initial toldPattern] ++ []) none = _
  rw [told, List.append_nil, rowItem, applyBindings_apply_eq, applyBindings_apply_eq, List.map_cons, List.map_nil,
    List.map_cons, List.map_nil, applyBindings_fvar_some yFound, applyBindings_dataCode]
  rfl

/-- **The presentation does not step at the term of the same row beside the equation `x = 6`.** -/
theorem knowledge_refuses_beside (target : Pattern) :
    ¬ knowledgeStep (bag [rowItem x, eqItem (x, sym 6)]) target := by
  rintro ⟨fuel, stepAt⟩
  cases stepAt with
  | @rule fuel' source' target' rule initial final ruleMember matched premises targetEq =>
  obtain rfl := List.mem_singleton.mp ruleMember
  rw [matchPatternForRule_eq_syntactic, matchPattern_iff_matchRel] at matched
  change MatchRel (.collection .hashBag [.apply "Row" [.fvar "y"]] (some "rest"))
    (.collection .hashBag [rowItem x, eqItem (x, sym 6)] none) initial at matched
  cases matched with
  | collection _ bagMatch =>
  cases bagMatch with
  | cons index bound head tail merged =>
  have correct : Pattern.isMatchCorrect (.apply "Row" [.fvar "y"]) = true := rfl
  have reconstructed := matchRel_correct_of_extends head correct (extends_left merged)
  rcases index with _ | _ | index
  · -- the row item is taken; the rest is the equation `x = 6`
    cases tail
    have restFound : initial.find? (·.1 == "rest") = some ("rest", bag [eqItem (x, sym 6)]) :=
      extends_right merged _ _ (by simp [bag])
    have yValue : applyBindings initial (.fvar "y") = dataCode x := by
      rw [applyBindings_apply_eq, List.map_cons, List.map_nil] at reconstructed
      have rowEq : Pattern.apply "Row" [applyBindings initial (.fvar "y")] = rowItem x := reconstructed
      exact (List.cons.inj (Pattern.apply.inj rowEq).2).1
    have told : applyBindings initial toldPattern = eqItem (x, sym 5) := by
      rw [toldPattern, applyBindings_apply_eq, List.map_cons, List.map_cons, List.map_nil, yValue,
        applyBindings_dataCode]
      rfl
    cases premises with
    | cons first _ =>
    cases first with
    | relationQuery member =>
    obtain ⟨tuple, inTuples, -⟩ := mem_relationQuery.mp member
    rw [List.map_cons, List.map_cons, List.map_nil, applyBindings_fvar_some restFound, told, builtin_solvable,
      List.nil_append] at inTuples
    have fails : ¬ JointlySolvable (eqItem (x, sym 5) :: [eqItem (x, sym 6)]) := not_solvable_beside
    rw [solvabilityEnv_fails fails] at inTuples
    exact absurd inTuples List.not_mem_nil
  · -- the equation item does not match the row pattern
    rw [applyBindings_apply_eq, List.map_cons, List.map_nil] at reconstructed
    have rowEq : Pattern.apply "Row" [applyBindings initial (.fvar "y")] = eqItem (x, sym 6) := reconstructed
    exact absurd (Pattern.apply.inj rowEq).1 (by decide)
  · simp at bound

/-! ## The switch, and the context rule -/

/-- **The presentation with the knowledge in the term presents the switch of the tell program**, at the terms of
the two configurations of `Boundary`: it steps where `RuleSyntax.step` fires and does not step where the step
refuses. -/
theorem knowledge_presents_switch :
    (configurationTerm [x] [] = bag [rowItem x] ∧
      configurationTerm [x] [(x, sym 6)] = bag [rowItem x, eqItem (x, sym 6)]) ∧
    (knowledgeStep (bag [rowItem x]) (bag [rowItem x, rowItem (sym 9), eqItem (x, sym 5)]) ∧
      (schematicStep ℕ tellProgram).Admits (s := openCaller) tellFiring) ∧
    ((¬ ∃ target, knowledgeStep (bag [rowItem x, eqItem (x, sym 6)]) target) ∧
      ¬ ∃ g : Firing ℕ E {r | r ∈ tellProgram} toldSix.frame,
        (schematicStep ℕ tellProgram).Admits (s := toldSix) g) :=
  ⟨⟨rfl, rfl⟩, ⟨knowledge_steps_alone, tellFiring_admitted⟩,
    ⟨fun ⟨target, step⟩ => knowledge_refuses_beside target step, toldSix_refused⟩⟩

/-- **A parallel component switches the step off**: the term of the caller's row steps, and beside the item
`Eq(x, 6)` it does not. -/
theorem knowledge_switched_off :
    SwitchedOffBeside (fun l l' : List Pattern => knowledgeStep (bag l) (bag l')) (· ++ ·) :=
  ⟨[rowItem x], [rowItem x, rowItem (sym 9), eqItem (x, sym 5)], [eqItem (x, sym 6)], knowledge_steps_alone,
    fun step => knowledge_refuses_beside _ step⟩

/-- **The step of the presentation with the knowledge in the term is not closed under parallel composition.** -/
theorem knowledge_not_closed :
    ¬ ClosedBeside (fun l l' : List Pattern => knowledgeStep (bag l) (bag l')) (· ++ ·) :=
  not_closedBeside_of_switchedOff knowledge_switched_off

/-- **No relation closed under parallel composition is that step**: the instance of
`ParallelClosed.not_iff_of_switchedOff`. A presentation that keeps the parallel context rule, so that its step is
closed beside, does not present the tell on a shared unknown. -/
theorem knowledge_no_context_rule (step' : List Pattern → List Pattern → Prop) (closed : ClosedBeside step' (· ++ ·)) :
    ¬ ∀ l l', step' l l' ↔ knowledgeStep (bag l) (bag l') :=
  not_iff_of_switchedOff closed knowledge_switched_off

#print axioms dataCode_injective
#print axioms knowledge_steps_alone
#print axioms knowledge_refuses_beside
#print axioms knowledge_presents_switch
#print axioms knowledge_switched_off
#print axioms knowledge_not_closed
#print axioms knowledge_no_context_rule

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic.Knowledge
